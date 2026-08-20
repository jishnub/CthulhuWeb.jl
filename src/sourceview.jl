# Type-annotated source view.
#
# The terminal prints `::T` inline, which is why it has to fight line width and
# hide most annotations. A browser can attach the type to the *span* instead, so
# every subexpression carries its inferred type on hover and every call is a
# click target.
#
# The linkage is already provided by Cthulhu: `find_callsites(..., true)` returns
# `sourcenodes` INDEX-PARALLEL to the very same callsite list you get with
# `false` (reflection.jl:112-119), so a source span maps to a callsite by
# position -- no extra matching needed.

"""
    static_params(mi) -> Vector{Pair{String,String}}

The `where {T<:IEEEFloat}` bindings for this specialization, e.g. `T => Float64`.
The source text keeps the generic `T`, so without this the concrete binding is
visible in the caller's argument types but nowhere in the callee's source.

`mi.sparam_vals` is in declaration order, and unwrapping `UnionAll`s
outside-in yields the same order (`f(...) where {T,S}` nests as
`(Tuple{...} where S) where T`), so a plain `zip` lines them up.
"""
function static_params(mi::Union{Nothing,Core.MethodInstance})
    mi === nothing && return Pair{String,String}[]
    m = mi.def
    m isa Method || return Pair{String,String}[]
    vals = mi.sparam_vals
    isempty(vals) && return Pair{String,String}[]
    names = Symbol[]
    sig = m.sig
    while sig isa UnionAll
        push!(names, sig.var.name)
        sig = sig.body
    end
    n = min(length(names), length(vals))
    return [string(names[i]) => string(vals[i]) for i in 1:n]
end

# ---------------------------------------------------------------------------
# Lexical syntax highlighting.
#
# Done server-side with JuliaSyntax's own tokenizer (already a Cthulhu dep), so
# it is a real Julia lexer rather than a regex approximation in JS.
#
# Identifiers are deliberately left UNCOLOURED: they are what the type spans
# colour (red = unstable, amber = small union), and a token span nests inside a
# type span, so colouring identifiers would silently override the type
# information -- the whole point of the view. Note JuliaSyntax tokenizes `>` as
# an Identifier, so operator-like names stay plain too, which is consistent.
# ---------------------------------------------------------------------------

const TOKCLASS = ("kw", "com", "str", "num", "mac", "op", "pun")

function tokclass(k)::UInt8
    ks = string(k)
    ks == "Comment"                                    && return 0x02
    JS.is_keyword(k)                                   && return 0x01
    ks in ("String", "Char", "CmdString")              && return 0x03
    ks in ("\"", "'", "`", "\"\"\"")                     && return 0x03
    ks in ("Integer", "Float", "BinInt", "OctInt", "HexInt", "float") && return 0x04
    ks in ("MacroName", "@", "StringMacroName", "CmdMacroName")       && return 0x05
    JS.is_operator(k)                                  && return 0x06
    ks in ("(", ")", "[", "]", "{", "}", ",", ";")     && return 0x07
    return 0x00
end

"""
Byte -> token-class map for the method's source range. A flat array keeps the
emitter trivially correct: `walk_source` emits strictly left to right, and class
runs break only at token boundaries, which are always character boundaries.
"""
function token_classmap(src, first_b::Int, last_b::Int)
    n = last_b - first_b + 1
    cm = zeros(UInt8, max(n, 0))
    n <= 0 && return cm
    try
        text = String(src[first_b:last_b])
        for t in JS.tokenize(text)
            r = t.range
            isempty(r) && continue
            c = tokclass(JS.kind(t))
            c == 0x00 && continue
            for i in Int(first(r)):min(Int(last(r)), n)
                cm[i] = c
            end
        end
    catch
        # unparseable fragment: fall back to no lexical highlighting
    end
    return cm
end

classat(cm, i::Int, offset::Int) =
    (j = i - offset + 1; 1 <= j <= length(cm) ? cm[j] : 0x00)

"Emit `src[a:b]`, wrapping runs of same-class tokens in `<span class=\"tok-*\">`."
function emit_code(io::IO, src, a::Int, b::Int, cm, offset::Int)
    a > b && return
    i = a
    while i <= b
        c = classat(cm, i, offset)
        j = i
        while j < b && classat(cm, j + 1, offset) == c
            j += 1
        end
        txt = html_escape(String(src[i:j]))
        if c == 0x00
            print(io, txt)
        else
            print(io, "<span class=\"tok-", TOKCLASS[c], "\">", txt, "</span>")
        end
        i = j + 1
    end
end

"""
    source_html(session, node, cfg) -> String

Render the node's source with nested `<span>`s carrying inferred types, and
`data-node-id` on the spans that correspond to descendable callsites.
Falls back to the ANSI pipeline when no typed source is available.
"""
function source_html(s::Session, node::Node, cfg::CthulhuConfig)
    node.ci === nothing && return nothing
    result = lookup_cached!(s, node, false)   # :source implies optimize=false
    result === nothing && return nothing
    isa(result.src, Core.CodeInfo) || return nothing

    tsn = try
        t, _ = C.get_typed_sourcetext(node.mi, result.src, result.rt)
        t
    catch
        nothing
    end
    tsn === nothing && return nothing

    # Map source spans -> child node ids by position.
    callsite_map = Dict{Tuple{Int,Int},Int}()
    try
        callsites, sourcenodes = C.find_callsites(s.provider, result, node.ci, true)
        kids = expand!(s, node.id; optimize=false)
        if length(kids) == length(callsites) == length(sourcenodes)
            for (i, sn) in enumerate(sourcenodes)
                isa(sn, C.Callsite) && continue      # no source node for this callsite
                key = (JS.first_byte(sn), JS.last_byte(sn))
                # a span may cover several callsites (nested calls); first wins,
                # and the inner calls get their own narrower spans anyway.
                get!(callsite_map, key, kids[i])
            end
        end
    catch
        # annotation is best-effort; the un-clickable source is still useful
    end

    # Mirrors cthulhu_typed (codeview.jl:110-118): a method that only fills in
    # default arguments has an empty body, so stop after the signature.
    kids_tsn = JS.children(tsn)
    idxend = lastindex(tsn.source)
    truncated = false
    if kids_tsn !== nothing && length(kids_tsn) == 2
        sig, body = kids_tsn
        if C.is_leaf(body)
            idxend = JS.last_byte(sig)
            truncated = true
        end
    end

    src = tsn.source
    sparams = Dict{String,String}(static_params(node.mi))
    startb = JS.first_byte(tsn)
    cm = token_classmap(src, startb, idxend)
    io = IOBuffer()
    walk_source(io, tsn, startb, src, callsite_map, idxend, cfg, sparams, cm, startb)
    code = String(take!(io))

    firstline = JS.source_line(src, JS.first_byte(tsn))
    nlines = count(==('\n'), code) + 1
    gutter = join(string.(firstline:(firstline + nlines - 1)), "\n")

    file = node.label.file === nothing ? "" :
        "<div class=\"srcfile\">" * html_escape(node.label.file) * "</div>"
    note = truncated ? "<p class=\"note\">This method only fills in default " *
        "arguments; descend into the body method to see the full source.</p>" : ""

    sp = isempty(sparams) ? "" :
        "<div class=\"sparams\">where " *
        join(["<b>" * html_escape(k) * "</b> = " * html_escape(v)
              for (k, v) in sort!(collect(sparams))], ", ") * "</div>"

    return file * sp * note *
        "<div class=\"srcwrap\"><pre class=\"gutter\">" * gutter * "</pre>" *
        "<pre class=\"code src\">" * code * "</pre></div>"
end

"Recursively emit `node`'s byte range, wrapping typed sub-expressions in spans.
Returns the next byte position to emit. Ranges from a syntax tree nest properly
by construction, so the spans can never overlap-without-containment."
function walk_source(io::IO, node, pos::Int, src, callsite_map, idxend::Int,
                     cfg::CthulhuConfig, sparams::Dict{String,String}, cm, offset::Int)
    fb, lb = JS.first_byte(node), JS.last_byte(node)
    fb > idxend && return pos
    lb = min(lb, idxend)
    lb < fb && return pos

    # text between the previous sibling and this node (whitespace, operators, ...)
    pos < fb && emit_code(io, src, pos, fb - 1, cm, offset)

    opened = open_span(io, node, fb, lb, src, callsite_map, cfg, sparams)

    p = fb
    kids = JS.children(node)
    if kids !== nothing
        for c in kids
            p = walk_source(io, c, p, src, callsite_map, idxend, cfg, sparams, cm, offset)
        end
    end
    p <= lb && emit_code(io, src, p, lb, cm, offset)

    opened && print(io, "</span>")
    return lb + 1
end

"""
The callee position of every call is inferred as `Core.Const(sin)` etc. Annotating
it adds `::Core.Const(+)` to every operator, which is pure noise -- the name is
already right there in the source. Cthulhu's own renderer suppresses these too
(`is_callfunc` / `type_annotation_mode`, TypedSyntax/src/show.jl). Genuinely
interesting constants (`Core.Const(5)`) are kept.
"""
uninteresting_const(@nospecialize(typ)) =
    typ isa Core.Const && (typ.val isa Function || typ.val isa Type)

function open_span(io::IO, node, fb::Int, lb::Int, src, callsite_map,
                   cfg::CthulhuConfig, sparams::Dict{String,String})
    typ = node.typ
    typ !== nothing && uninteresting_const(typ) && (typ = nothing)
    nodeid = get(callsite_map, (fb, lb), 0)
    runtime = try TS.is_runtime(node) catch; false end

    # A `T` in the signature is plain source text with no inferred type. Bind it
    # to this specialization's static parameter so hovering it says `Float64`.
    issparam = false
    if typ === nothing && !isempty(sparams) && JS.kind(node) === JS.K"Identifier"
        val = get(sparams, String(src[fb:lb]), nothing)
        if val !== nothing
            typ = val
            issparam = true
        end
    end

    (typ === nothing && nodeid == 0 && !runtime) && return false

    classes = ["s"]
    issparam && push!(classes, "s-sparam")
    if typ !== nothing && !issparam
        if C.is_type_unstable(typ)
            push!(classes, is_expected_union_safe(typ) ? "s-union" : "s-unstable")
        else
            push!(classes, "s-stable")
        end
    end
    runtime && push!(classes, "s-runtime")
    nodeid != 0 && push!(classes, "s-call")

    print(io, "<span class=\"", join(classes, ' '), "\"")
    if typ !== nothing
        label = issparam ? "$(String(src[fb:lb])) = $(typ)   (static parameter)" :
                           "::" * string(typ)
        print(io, " data-type=\"", html_escape(label), "\"")
    end
    nodeid == 0 || print(io, " data-node-id=\"", nodeid, "\"")
    print(io, ">")
    return true
end
