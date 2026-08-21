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
    is_keyword(k)                                   && return 0x01
    ks in ("String", "Char", "CmdString")              && return 0x03
    ks in ("\"", "'", "`", "\"\"\"")                     && return 0x03
    ks in ("Integer", "Float", "BinInt", "OctInt", "HexInt", "float") && return 0x04
    ks in ("MacroName", "@", "StringMacroName", "CmdMacroName")       && return 0x05
    is_operator(k)                                  && return 0x06
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
        for t in tokenize(text)
            r = t.range
            isempty(r) && continue
            c = tokclass(kind(t))
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
Is this callsite Julia resolving a qualified name rather than performing a call?

`LAPACK.gesdd!(x)` lowers to `getproperty(LAPACK, :gesdd!)` and then the call, and
the `getproperty` callsite's source range is the callee *name* -- the most natural
place to click. Descending there lands in `getproperty(x::Module, f::Symbol) =
getglobal(x, f)`, which is name resolution, not the function that was clicked.
Dropping it from the click map lets the click reach the enclosing call span.

Only `Module` receivers qualify: `obj.field` on a struct is real property access
and stays clickable.
"""
function is_name_resolution(n::Node)
    mi = n.mi
    mi === nothing && return false
    sig = Base.unwrap_unionall(mi.specTypes)
    sig isa DataType || return false
    ps = sig.parameters
    return length(ps) == 3 && ps[1] === typeof(getproperty) &&
           ps[2] === Module && ps[3] === Symbol
end

"""
Choose which callsite a source range should descend into when several share it.

`eigen!(x; permute, scale, sortby)` produces a `NamedTuple` construction as well
as the call. Taking the first in SSA order landed the user in `boot.jl` at
`NamedTuple{names}(args::Tuple)` -- lowering plumbing, not the function they
clicked. Prefer, in order: a callee whose name matches what is written in the
source, then `Core.kwcall` (the real dispatch for a keyword call), then anything
that is not an obvious NamedTuple constructor.
"""
function pick_callsite(s::Session, cands::Vector{Int}, spantext::AbstractString)
    length(cands) == 1 && return only(cands)
    lead = match(r"^\s*([A-Za-z_][A-Za-z0-9_!]*)", spantext)
    leadname = lead === nothing ? nothing : String(lead.captures[1])
    function score(k)
        nm = s.nodes[k].label.name
        if leadname !== nothing && (nm == leadname || endswith(nm, "." * leadname))
            return 3
        end
        nm == "Core.kwcall" && return 2
        startswith(nm, "Type{NamedTuple") && return 0
        return 1
    end
    return cands[argmax(map(score, cands))]
end

"""
Is `child` the body method of `parent`? Julia lowers `f(x, n=1)` to a shim `f(x)`
calling `f(x, 1)`, and `f(x; kw=1)` to a shim calling a gensym `#f#NN`. Other
children of a shim are default-value computations (`eltype(A0)` in
`sqrt_quasitriu(A0; blockwidth = eltype(A0) <: Complex ? 512 : 256)`), which are
not what "descend into the body method" means.
"""
function is_body_method(parent::Core.MethodInstance, child::Core.MethodInstance)
    pd, cd = parent.def, child.def
    (pd isa Method && cd isa Method) || return false
    p, c = string(pd.name), string(cd.name)
    return c == p || startswith(c, "#" * p * "#") || startswith(c, "##" * p * "#")
end

"""
Readable label for a body-method button. Julia's keyword lowering produces names
like `LinearAlgebra.var"#sqrt_quasitriu#80"` and threads the function itself
through as a `::typeof(f)` argument; showing that verbatim is unreadable, so
recover the plain name and drop the plumbing argument.
"""
function body_label(n::Node)
    name = n.label.name
    m = match(r"var\"#+([^#\"]+)#\d+\"$", name)
    m === nothing || (name = String(m.captures[1]))
    args = [a for a in n.label.argtypes if !startswith(a, "typeof(")]
    args = [length(a) > 40 ? first(a, 37) * "…" : a for a in args]
    sig = join(["::" * a for a in args], ", ")
    isempty(n.label.kwargs) || (sig *= "; " * join(n.label.kwargs, ", "))
    return name * "(" * sig * ")"
end

"""
Note shown for a method that only fills in default arguments (or forwards keyword
arguments): its body is a single call to the real implementation, so there is no
source to annotate and nothing to click. Link the body method explicitly --
otherwise the pane is a dead end even though the tree does hold the child.
"""
function truncated_note(s::Session, node::Node, kids::Vector{Int})
    cand = [k for k in kids if s.nodes[k].descendable && s.nodes[k].mi !== nothing]
    # prefer the real body method; fall back to every descendable child so the
    # pane is never a dead end even when the heuristic misses
    body = node.mi === nothing ? Int[] :
           [k for k in cand if is_body_method(node.mi, s.nodes[k].mi)]
    targets = isempty(body) ? cand : body
    if isempty(targets)
        return "<p class=\"note\">This method only fills in default arguments; " *
               "descend into the body method to see the full source.</p>"
    end
    links = join(map(targets) do k
        "<button class=\"s-call bodylink\" data-node-id=\"$(k)\">" *
        html_escape(body_label(s.nodes[k])) * "</button>"
    end, " ")
    return "<p class=\"note\">This method only fills in default arguments. " *
           "Descend into the body method: " * links * "</p>"
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
        t, _ = get_typed_sourcetext(node.mi, result.src, result.rt)
        t
    catch
        nothing
    end
    tsn === nothing && return nothing

    # Map source spans -> child node ids by position.
    # Outside the try below: annotation is best-effort, but the truncated-source
    # note needs the real child list regardless of whether annotation succeeds.
    kids = expand!(s, node.id; optimize=false)

    callsite_map = Dict{Tuple{Int,Int},Int}()
    try
        callsites, sourcenodes = find_callsites(s.provider, result, node.ci, true)
        if length(kids) == length(callsites) == length(sourcenodes)
            # Several callsites can share ONE source range: `f(x; kw=1)` lowers to
            # a NamedTuple construction *and* the call itself. Collect the
            # candidates and choose, rather than letting SSA order decide.
            cands = Dict{Tuple{Int,Int},Vector{Int}}()
            for (i, sn) in enumerate(sourcenodes)
                isa(sn, Callsite) && continue      # no source node for this callsite
                is_name_resolution(s.nodes[kids[i]]) && continue
                push!(get!(cands, (first_byte(sn), last_byte(sn)), Int[]), kids[i])
            end
            for (key, ks) in cands
                callsite_map[key] = pick_callsite(s, ks, String(tsn.source[key[1]:key[2]]))
            end
        end
    catch
        # annotation is best-effort; the un-clickable source is still useful
    end

    # Mirrors cthulhu_typed (codeview.jl:110-118): a method that only fills in
    # default arguments has an empty body, so stop after the signature.
    kids_tsn = children(tsn)
    idxend = lastindex(tsn.source)
    truncated = false
    if kids_tsn !== nothing && length(kids_tsn) == 2
        sig, body = kids_tsn
        if is_leaf(body)
            idxend = last_byte(sig)
            truncated = true
        end
    end

    src = tsn.source
    sparams = Dict{String,String}(static_params(node.mi))
    startb = first_byte(tsn)
    cm = token_classmap(src, startb, idxend)
    io = IOBuffer()
    walk_source(io, tsn, startb, src, callsite_map, idxend, cfg, sparams, cm, startb)
    code = String(take!(io))

    firstline = source_line(src, first_byte(tsn))
    nlines = count(==('\n'), code) + 1
    gutter = join(string.(firstline:(firstline + nlines - 1)), "\n")

    file = node.label.file === nothing ? "" :
        "<div class=\"srcfile\">" * html_escape(node.label.file) * "</div>"
    note = truncated ? truncated_note(s, node, kids) : ""

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
                     cfg::CthulhuConfig, sparams::Dict{String,String}, cm, offset::Int,
                     iscallee::Bool = false)
    fb, lb = first_byte(node), last_byte(node)
    fb > idxend && return pos
    lb = min(lb, idxend)
    lb < fb && return pos

    # text between the previous sibling and this node (whitespace, operators, ...)
    pos < fb && emit_code(io, src, pos, fb - 1, cm, offset)

    opened = open_span(io, node, fb, lb, src, callsite_map, cfg, sparams, iscallee)

    p = fb
    kids = children(node)
    if kids !== nothing
        # The callee is the first child of a prefix call `f(x)`, but the SECOND
        # child of an infix one -- `a + b` parses as call(a, +, b). Missing that
        # put `::Core.Const(+)` back on every operator.
        calleeidx = kind(node) === K"call" ? (is_infix_op_call(node) ? 2 : 1) : 0
        isdot = kind(node) === K"."
        for (i, c) in enumerate(kids)
            # a dotted callee passes the flag down, so `Base.Math.sin` stays quiet
            # all the way to the leaf
            childcallee = (i == calleeidx) || (iscallee && isdot)
            p = walk_source(io, c, p, src, callsite_map, idxend, cfg, sparams, cm,
                            offset, childcallee)
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
(`is_callfunc` / `type_annotation_mode`, TypedSyntax/src/show.jl).

Restricted to CALLEE POSITION -- the first child of a `call`, propagated through
dotted access so `Base.Math.sin` stays quiet. Anything looser suppresses real
information: `typeof(...)` infers to `Core.Const(Float64)`, and so does the
variable `Tr` that stores it. Dropping those annotations left them with no span
at all, so they inherited the enclosing expression's type -- rendering amber, and
reporting the function's return type on hover.

`Module` is included for the same reason: in `LAPACK.gesdd!(x)` the qualifier is
part of the name being called, and `::Core.Const(LinearAlgebra.LAPACK)` says
nothing the source does not.
"""
uninteresting_const(@nospecialize(typ), iscallee::Bool) =
    iscallee && typ isa Core.Const &&
    (typ.val isa Function || typ.val isa Type || typ.val isa Module)

function open_span(io::IO, node, fb::Int, lb::Int, src, callsite_map,
                   cfg::CthulhuConfig, sparams::Dict{String,String}, iscallee::Bool)
    typ = node.typ
    # A callee whose annotation we deliberately drop is not an *untyped* node: it
    # must fall through to the enclosing call rather than raise a barrier.
    suppressed = typ !== nothing && uninteresting_const(typ, iscallee)
    suppressed && (typ = nothing)
    nodeid = get(callsite_map, (fb, lb), 0)
    runtime = try is_runtime(node) catch; false end

    # A `T` in the signature is plain source text with no inferred type. Bind it
    # to this specialization's static parameter so hovering it says `Float64`.
    issparam = false
    if typ === nothing && !isempty(sparams) && kind(node) === K"Identifier"
        val = get(sparams, String(src[fb:lb]), nothing)
        if val !== nothing
            typ = val
            issparam = true
        end
    end

    if typ === nothing && nodeid == 0 && !runtime
        # Correctness principle: never attribute a type (or a warning colour) to
        # something that does not have one. An untyped node is otherwise invisible
        # in the DOM, so the pointer and the CSS cascade fall through to whatever
        # distant ancestor happens to be typed -- which is how `=` reported the
        # enclosing function's return type and how stable calls rendered amber.
        #
        # Only COMPOSITE untyped nodes are barriers. An untyped leaf (the callee
        # name in `checksquare(A0)`) is part of the surrounding expression, so
        # reporting that expression's type for it is accurate, not a guess.
        # Barriering leaves too would silence the most natural hover target.
        # A dotted callee (`LAPACK.gesdd!`) is composite but not untyped -- see
        # `suppressed` above -- so it falls through here as well.
        (is_leaf(node) || suppressed) && return false
        print(io, "<span class=\"s-opaque\">")
        return true
    end

    classes = ["s"]
    issparam && push!(classes, "s-sparam")
    if typ !== nothing && !issparam
        if is_type_unstable(typ)
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
