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
    mi === nothing && return Pair{String,Any}[]
    m = mi.def
    m isa Method || return Pair{String,Any}[]
    vals = mi.sparam_vals
    isempty(vals) && return Pair{String,Any}[]
    names = Symbol[]
    sig = m.sig
    while sig isa UnionAll
        push!(names, sig.var.name)
        sig = sig.body
    end
    n = min(length(names), length(vals))
    # values, not strings: `T(x)` needs the binding to match `Type{Float64}` by
    # identity, and the display can stringify at the point of use
    return Pair{String,Any}[string(names[i]) => vals[i] for i in 1:n]
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
Byte range -> inferred type, for `pick_callsite` to compare a candidate's return
type against the type of the expression its span denotes.

**Outermost wins.** Nested nodes can share one range (`axes(B,1)[2:end]` is both
the `ref` and its callee subtree), and the range denotes the whole expression, so
the outer node's type is the one that says what the expression produces. Letting
an inner node overwrite it sent `axes(B,1)[2:end]` to `lastindex` -- the `end`
plumbing -- instead of `getindex`.

Reading `.typ` off the `sourcenodes` entry instead is not an option either: not
every entry is a `TypedSyntaxNode`. Cthulhu hands back plain `SyntaxNode`s for
some callsites, which have no `.typ` field at all, and there is no reason the
first callsite at a range should be the one that produced its value.
"""
function span_types!(d::Dict{Tuple{Int,Int},String}, node)
    typ = node.typ
    typ === nothing || get!(d, (first_byte(node), last_byte(node)), string(typ))
    kids = children(node)
    kids === nothing || for c in kids
        span_types!(d, c)
    end
    return d
end

"""
Which child of a call node is the callee. `f(x)` puts it first, `a + b` second
(the tree is `call(a, +, b)`), `x'` last. Returns 0 when the node is not a call.

One definition serves both the annotation suppression in `walk_source` and the
name matching in `pick_callsite`: getting it wrong in the first put
`::Core.Const(+)` back on every operator, and in the second it silently picks
the wrong callsite to descend into.
"""
function callee_index(node)
    k = kind(node)
    (k === K"call" || k === K"dotcall") || return 0
    kids = children(node)
    (kids === nothing || isempty(kids)) && return 0
    is_infix_op_call(node) && return 2
    is_postfix_op_call(node) && return length(kids)
    return 1
end

"""
What the callee position resolved to, or `nothing` if it is not a constant.

Inference already answers "which function is being called here" -- it is the
`Core.Const` on the callee node, the same one `uninteresting_const` declines to
print. Matching a candidate against *that* is exact, where matching against the
callee's spelling is lossy in every direction: `a % b` is `rem`, `i \u2264 j` is `<=`,
`T(x)` is `Type{Float64}`, `BoundsError(A, I)` is `Type{BoundsError}`, and
`PCRE.exec_r_data(...)` is `Base.PCRE.exec_r_data`.

`nothing` when the callee is computed (`(\$func)(x)`, `(h())(x)`) -- exactly the
cases where the type tiebreak has to decide instead.
"""
function callee_value(node, src = nothing, sparams = nothing)
    i = callee_index(node)
    i == 0 && return nothing
    kids = children(node)
    (kids === nothing || i > length(kids)) && return nothing
    c = kids[i]
    if c isa TypedSyntax.TypedSyntaxNode
        t = c.typ
        t isa Core.Const && return t.val
    end
    # `T(x)` in a `where {T}` method: the callee is a static parameter, which
    # carries no inferred type -- it is plain source text bound by the
    # specialization. This is the same binding `open_span` shows on hover.
    (src === nothing || sparams === nothing || !is_leaf(c)) && return nothing
    return get(sparams, String(src[first_byte(c):last_byte(c)]), nothing)
end

"Does this candidate dispatch on `v`, the function the callee position resolved to?"
function callee_matches(n::Node, @nospecialize(v))
    ct = callsite_callee(n)
    ct === nothing && return false
    if v isa Type
        # `Val(N)` is written with the UnionAll but dispatches on `Type{Val{N}}`
        c = constructed_type(n)
        return c !== nothing && c <: v
    end
    return ct === typeof(v)
end

"""
Was this region compiled out?

Inference produces no statement for unreachable code, so nothing in the subtree
gets a type -- `_any_tuple(f, false, itr...)` in `any(f, itr::Tuple)` is entirely
untyped once `itr isa NTuple` folds to `true`, and so is the short-circuited
`length(itr) > 32`. Live code always types something: a call has a return type,
a variable has its own.

Whole branches qualify, not just calls: in `_mul!`, `BlasFlag.SYRK` and the
`elseif` reaching `BlasFlag.HERK` are entirely untyped while the `block` holding
`BlasFlag.GEMM` is typed, so the taken branch is the one left at full strength.
Marking only the calls greyed the conditions and left the bodies between them
looking live.

Restricted to a fixed set of kinds on purpose -- a `where {T<:BlasFloat}` clause
and every `::` annotation in a signature are untyped without being dead -- and to
regions that hold something typeable at all, since a literal carries no type
whether it runs or not.
"""
const DEAD_KINDS = (K"call", K"dotcall", K"block", K"if", K"elseif", K"||", K"&&",
                    K".", K"return", K"for", K"while")

function is_dead_region(node)
    kind(node) in DEAD_KINDS || return false
    node.typ === nothing || return false
    has_typeable(node) || return false
    return !has_typed_descendant(node)
end

"""
Does this region contain anything that WOULD carry a type if it ran?

A literal never does. `return true` in `matmul2x2or3x3_nonzeroalpha!` is untyped
in exactly the way an unreachable statement is, so greying it claimed a `return`
on the taken path had been compiled out. Identifiers and calls do get types when
they run, so a region holding one is a region there is evidence about; a region
of pure literals is one we know nothing about either way.
"""
function has_typeable(node)
    k = kind(node)
    (k === K"Identifier" || k === K"call" || k === K"dotcall") && return true
    kids = children(node)
    kids === nothing && return false
    for c in kids
        has_typeable(c) && return true
    end
    return false
end

"""
Nothing in the body carries a type -- which is not evidence that anything was
compiled out.

`_chkstride1(ok::Bool, A, B...) = _chkstride1(ok & (stride1(A) == 1), B...)`
reached through semi-concrete evaluation has a known result
(`Core.Const(true)`) and an IR that never maps back to the source, so every node
in its body is untyped. Marking that unreachable is wrong twice over: nothing
was compiled out, and by the same test everything was.

Reachability is only a claim we can make about a body where inference DID map
something -- there the untyped parts are the parts it did not reach. Where it
mapped nothing, the honest answer is to annotate nothing and say why.
"""
nothing_mapped(body) = body === nothing || !has_typed_descendant(body)

"""
Is there work written here that annotating nothing would leave unexplained?

`isempty(x::Tuple{}) = true` and `map(f, t::Tuple{}) = ()` also carry no types --
a literal has none of its own -- but there is nothing to explain about them, and
a note saying so is noise. The silence is only confusing where the source makes
calls and none of them got annotated.
"""
function has_call(node)
    k = kind(node)
    (k === K"call" || k === K"dotcall") && return true
    kids = children(node)
    kids === nothing && return false
    for c in kids
        has_call(c) && return true
    end
    return false
end

"""
Note for a body inference never annotated. Compile-time evaluation is the usual
reason and worth naming, since the pane otherwise looks broken; for any other
kind, say only what is observed.
"""
function unmapped_note(node::Node)
    k = node.label.kind
    if k === :concrete || k === :semiconcrete || k === :constprop
        return "<p class=\"note\">Cthulhu evaluated this call at compile time (" *
               html_escape(string(k)) * "), so no statement in the body carries " *
               "its own type. The result is <code>" * html_escape(node.label.rt) *
               "</code>.</p>"
    end
    return "<p class=\"note\">Inference mapped no statement in this body back to " *
           "the source, so nothing here is annotated.</p>"
end

"Nodes whose children are consecutive statements or short-circuit operands --
places where one child being untyped says something about the others."
const REGION_PARENTS = (K"block", K"||", K"&&")

"""
The arms of a conditional: everything after the test.

Only the arms say which way the branch went. The test does not: `eltype(v) ===
Float64` mentions a typed `v` whether or not any arm ran, which is enough to make
a naive sibling check believe the branch was resolved.
"""
conditional_arms(node) =
    (k = children(node); k === nothing ? () : Iterators.drop(k, 1))

"Did any arm of this conditional run? `elseif` nests another conditional, so recurse."
arm_taken(node) = kind(node) === K"elseif" ?
    any(arm_taken, conditional_arms(node)) : has_typed_descendant(node)

"""
Byte ranges of the regions that were compiled out.

Outermost only: everything inside a dead region is dead too, and one span per
region keeps the fade from stacking on itself and makes an untaken branch a
single grey block rather than a scatter of grey fragments.

**Only where a sibling is live.** "This was not taken" is a claim about a choice,
and it needs the other side of the choice to be visible. When an `if` chain folds
whole -- `if eltype(v) === Float64` on a `Vector{Float64}` -- *no* arm carries
types, the arm that actually runs included, and greying them all would say the
method does nothing. That is the same mistake as greying `_chkstride1`, one level
down. The parent kind matters too: in `tag = if ...` the typed `tag` is the
folded *result*, not evidence that any arm ran.
"""
function collect_dead!(d::Set{Tuple{Int,Int}}, node)
    kids = children(node)
    kids === nothing && return d
    k = kind(node)
    live = if k === K"if" || k === K"elseif"
        any(arm_taken, conditional_arms(node))
    else
        k in REGION_PARENTS && any(has_typed_descendant, kids)
    end
    for c in kids
        if live && is_dead_region(c)
            push!(d, (first_byte(c), last_byte(c)))
        else
            collect_dead!(d, c)
        end
    end
    return d
end

function has_typed_descendant(node)
    node.typ === nothing || return true
    kids = children(node)
    kids === nothing && return false
    for c in kids
        has_typed_descendant(c) && return true
    end
    return false
end

"""
The callee as written: `f` in `f(x)`, `+` in `a + b`, `gesdd!` in
`LAPACK.gesdd!(x)`. `nothing` when the node is not a call or the callee is not a
plain name -- `(\$func)(x)` and `(h())(x)` have none, which is exactly when the
type tiebreak has to decide instead.

Reading the leading identifier of the span text instead is what it replaces, and
that is wrong in two common ways: it returns `p` for `p.x^2 + p.y^2`, and for
`PCRE.exec_r_data(re.regex, str, idx-1, opts)` it returns the module qualifier
`PCRE`, so the callsite that IS `Base.PCRE.exec_r_data` failed to match its own
name and lost the range to destructuring plumbing.
"""
function callee_name(node, src)
    i = callee_index(node)
    i == 0 && return nothing
    kids = children(node)
    i <= length(kids) || return nothing
    c = kids[i]
    # `Mod.f(x)`: the callee is the dotted access; its name is the last component
    while kind(c) === K"."
        cc = children(c)
        (cc === nothing || isempty(cc)) && return nothing
        c = last(cc)
    end
    is_leaf(c) || return nothing
    txt = strip(String(src[first_byte(c):last_byte(c)]))
    return isempty(txt) ? nothing : String(txt)
end

"""
The type of the function this callsite dispatches on, as written at the call.
`nothing` when the callsite has no MethodInstance.

Keyword calls are unwrapped: `f(x; kw=1)` dispatches as
`kwcall(::NamedTuple, ::typeof(f), ::X)`, and the callee the source names is `f`.
"""
function callsite_callee(n::Node)
    mi = n.mi
    mi === nothing && return nothing
    sig = Base.unwrap_unionall(mi.specTypes)
    (sig isa DataType && !isempty(sig.parameters)) || return nothing
    ps = sig.parameters
    ps[1] === typeof(Core.kwcall) && length(ps) >= 3 && return ps[3]
    return ps[1]
end

"""
The type a constructor callsite constructs, or `nothing` for an ordinary call.
Read off the callee -- `Val{2}()` specializes as `Tuple{Type{Val{2}}}` -- so
`Float64[1,2]`, which is `getindex(::Type{Float64}, ...)`, is correctly not one.
"""
function constructed_type(n::Node)
    T = callsite_callee(n)
    T === nothing && return nothing
    T = Base.unwrap_unionall(T)
    (T isa DataType && T.name === Type.body.name && !isempty(T.parameters)) || return nothing
    return T.parameters[1]
end

"""
Names a constructed type may be written under in source. `Vector{Float64}` is
`nameof`d `Array` but spelled `Vector`, so both spellings count.
"""
function ctor_names(@nospecialize(T))
    out = String[]
    m = match(r"^([A-Za-z_][A-Za-z0-9_!]*)", string(T))
    m === nothing || push!(out, String(m.captures[1]))
    t = Base.unwrap_unionall(T)
    t isa DataType && push!(out, string(nameof(t)))
    return out
end

"""
Is this callsite a constructor that lowering invented rather than one the user
wrote?

`x^2` lowers to `Base.literal_pow(^, x, Val(2))`, and the `Val{2}()` callsite is
attributed to whatever encloses it -- the assignment, or in `pow3(x) = x^3` the
whole method. Descending there lands in an empty singleton constructor, and it
was hijacking the click for the entire body. The same goes for the `NamedTuple`
built for a keyword call, which is attributed to the `; kw=...` clause.

A constructor the user actually wrote always has a `call` source node, so the
node kind separates the two without guessing at names.
"""
is_synthetic_construct(n::Node, k) =
    constructed_type(n) !== nothing && !(k === K"call" || k === K"dotcall")

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

Ties are broken on the inferred type. A span's type *is* the type of the
expression it denotes, so the candidate whose return type matches is the one
that produced the value; the others are lowering that happens to sit at the same
place. This is what separates the two callsites of
`(\$func)(copyto!(similar(parent(A)), A); kwargs...)`: splatted keywords lower to
`isempty(kws) ? f(args...) : kwcall(kws, f, args...)`, and the `isempty` test is
attributed to the whole call. Its `Bool` does not match the span's `SVD{...}`,
and the name heuristic cannot help because `(\$func)` has no name to match.
"""
function pick_callsite(s::Session, cands::Vector{Int}, sn, src,
                       spantype::Union{Nothing,String}, sparams::Dict{String,Any})
    length(cands) == 1 && return only(cands)
    # Prefer the callee as parsed; fall back to the leading identifier only for
    # nodes that are not calls at all (`; kw=...`, a generator, an assignment),
    # where there is no callee to read and any signal beats none.
    leadname = callee_name(sn, src)
    if leadname === nothing && callee_index(sn) == 0
        lead = match(r"^\s*([A-Za-z_][A-Za-z0-9_!]*)",
                     String(src[first_byte(sn):last_byte(sn)]))
        leadname = lead === nothing ? nothing : String(lead.captures[1])
    end
    # Lexicographic: the name/kind judgement first, the type match only as a
    # tiebreak, so a candidate named in the source is never overruled by one that
    # merely shares its return type.
    rtmatch(k) = spantype !== nothing && s.nodes[k].label.rt == spantype
    calleeval = callee_value(sn, src, sparams)
    function score(k)
        n = s.nodes[k]
        # Strongest: inference says this callsite IS the function named here.
        calleeval === nothing || callee_matches(n, calleeval) && return 4
        ctor = constructed_type(n)
        # a constructor's label is `Type{Val{2}}`; compare against how the type
        # would be spelled in source instead
        names = ctor === nothing ? [n.label.name] : ctor_names(ctor)
        if leadname !== nothing &&
           any(nm -> nm == leadname || endswith(nm, "." * leadname), names)
            return 3
        end
        # The real dispatch for a keyword call. Tested on the wrapper, not the
        # name: `signature_parts` rewrites the label to `f(...; kw)`, so
        # `label.name == "Core.kwcall"` was never true.
        :kw in n.label.wrappers && return 2
        # An unmatched constructor sharing a range with a real call is lowering
        # plumbing: `Pt2(a, a^2)` yields both `Type{Pt2}` and literal_pow's
        # `Type{Val{2}}`, and SSA order put `Val` first.
        ctor === nothing || return 0
        return 1
    end
    return cands[argmax([(score(k), rtmatch(k)) for k in cands])]
end

"""
Does the source text name this callee anywhere?

The test for whether an unlocated callsite is worth reporting. Cthulhu maps most
callsites to a source range, but not all: in
`generic_matmatmul_wrapper!` it locates `matmul2x2or3x3_nonzeroalpha!` and not
`matmul_size_check`, both of which are written plainly in the body. Those are
worth reporting; `literal_pow`, `setproperty!`, `convert`, `lastindex`, `pairs`
and the rest of the unlocated set are lowering the user never wrote, and their
names do not appear.

Membership in the token stream, not a substring search: `parent` must not match
inside `parentmodule`, a `-` inside `->` is not a call to `-`, and nothing in a
comment or a string literal counts at all.
"""
function names_in_source(n::Node, tokens::Set{String})
    ctor = constructed_type(n)
    cands = ctor === nothing ? [n.label.name] : ctor_names(ctor)
    return any(nm -> replace(nm, r"^.*\." => "") in tokens, cands)
end

"""
Identifier and operator tokens of a source fragment -- the names it actually
calls things by.

Text comes from `untokenize` rather than slicing on `t.range`: that range is in
BYTES, and `String` slicing rejects an index inside a multi-byte character, so
`α::Number` in `generic_matmatmul_wrapper!` throws two tokens in and takes the
whole set down with it. Letting JuliaSyntax cut its own token leaves no index
arithmetic to get wrong.
"""
function source_tokens(text::AbstractString)
    out = Set{String}()
    try
        for t in tokenize(text)
            k = kind(t)
            (is_operator(k) || k === K"Identifier") || continue
            push!(out, untokenize(t, text))
        end
    catch
        # unlexable fragment: report nothing rather than guess
    end
    return out
end

"""
Distinct callsites, keyed on MethodInstance.

`_mul!` tests `tA_uc` and `tB_uc` against six different characters, and each of
those is a separate callsite of the same `==(::Char, ::Char)`. Six identical
lines say nothing the first one did not.

Nodes without a MethodInstance -- a union split, a runtime dispatch -- fall back
to their printed signature, which is what distinguishes them in the tree too.
"""
function unique_callsites(s::Session, ids::Vector{Int})
    out, seen = Int[], Set{Any}()
    for k in ids
        n = s.nodes[k]
        key = n.mi === nothing ?
            (n.label.name, n.label.argtypes, n.label.kwargs) : n.mi
        key in seen && continue
        push!(seen, key)
        push!(out, k)
    end
    return out
end

"""
Callsites Cthulhu could not place in the source, listed rather than dropped.

The source pane is a view of the call tree, and silently omitting a call the
tree does hold makes it look like the call is not there. Naming them -- without
guessing at a span, which would be inventing information Cthulhu did not give
us -- keeps the pane honest and still reachable.
"""
function unlocated_note(s::Session, ids::Vector{Int})
    isempty(ids) && return ""
    # A list, not a run of buttons: these are separate calls, and the signatures
    # are long enough that side by side they read as one wrapped blob.
    items = join(map(ids) do k
        "<li><button class=\"s-call bodylink\" data-node-id=\"$(k)\">" *
        html_escape(body_label(s.nodes[k])) * "</button></li>"
    end)
    what = length(ids) == 1 ? "it" : "these"
    return "<p class=\"note unlocated\">Also called here, but Cthulhu could not " *
           "locate " * what * " in the source:</p>" *
           "<ul class=\"unlocated-list\">" * items * "</ul>"
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
    targets = unique_callsites(s, isempty(body) ? cand : body)
    if isempty(targets)
        # Say what actually happened rather than pointing at a body method that
        # is not there: from here the user has nowhere to click and no reason.
        return "<p class=\"note\">This method only fills in default arguments, " *
               "and Cthulhu found no call here to descend into.</p>"
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
    sparams = Dict{String,Any}(static_params(node.mi))

    callsite_map = Dict{Tuple{Int,Int},Int}()
    unplaced = Int[]
    try
        callsites, sourcenodes = find_callsites(s.provider, result, node.ci, true)
        if length(kids) == length(callsites) == length(sourcenodes)
            # Several callsites can share ONE source range: `f(x; kw=1)` lowers to
            # a NamedTuple construction *and* the call itself. Collect the
            # candidates and choose, rather than letting SSA order decide.
            cands = Dict{Tuple{Int,Int},Vector{Int}}()
            spannode = Dict{Tuple{Int,Int},Any}()
            for (i, sn) in enumerate(sourcenodes)
                if isa(sn, Callsite)               # no source node for this callsite
                    push!(unplaced, kids[i])
                    continue
                end
                kn = s.nodes[kids[i]]
                is_name_resolution(kn) && continue
                is_synthetic_construct(kn, kind(sn)) && continue
                key = (first_byte(sn), last_byte(sn))
                get!(spannode, key, sn)
                push!(get!(cands, key, Int[]), kids[i])
            end
            spantypes = span_types!(Dict{Tuple{Int,Int},String}(), tsn)
            for (key, ks) in cands
                callsite_map[key] = pick_callsite(s, ks, spannode[key], tsn.source,
                                                  get(spantypes, key, nothing), sparams)
            end
        end
    catch
        # annotation is best-effort; the un-clickable source is still useful
    end

    # Mirrors cthulhu_typed (codeview.jl:110-118): a method that only fills in
    # default arguments has an empty body, so stop after the signature.
    #
    # Upstream tests `is_leaf(body)` alone, and its own comment says why -- "we
    # empty the body when filling kwargs". But a real one-line method has a leaf
    # body too: `_unwrap(A::AbstractVecOrMat) = A` was being cut back to its
    # signature and captioned as a default-argument shim.
    #
    # "Emptied" is literal, and that is the test: the emptied body spans no bytes
    # at all (`56:55`), where `= A` spans the one byte `A` sits on.
    kids_tsn = children(tsn)
    idxend = lastindex(tsn.source)
    truncated = false
    body = nothing
    if kids_tsn !== nothing && length(kids_tsn) == 2
        sig, body = kids_tsn
        if is_leaf(body) && last_byte(body) < first_byte(body)
            idxend = last_byte(sig)
            truncated = true
        end
    end

    # Dead-code marking applies to the body only. A signature default like
    # `kwshim(v; width = eltype(v) <: Complex ? 512 : 256)` is untyped in the
    # shim's own IR, which is an artefact of where the code lives, not evidence
    # that anything was compiled out.
    deadspans = Set{Tuple{Int,Int}}()
    unmapped = !truncated && nothing_mapped(body) && body !== nothing && has_call(body)
    truncated || unmapped || collect_dead!(deadspans, body)

    src = tsn.source
    startb = first_byte(tsn)
    cm = token_classmap(src, startb, idxend)
    io = IOBuffer()
    walk_source(io, tsn, startb, src, callsite_map, idxend, cfg, sparams, cm, startb,
                deadspans)
    code = String(take!(io))

    firstline = source_line(src, first_byte(tsn))
    nlines = count(==('\n'), code) + 1
    gutter = join(string.(firstline:(firstline + nlines - 1)), "\n")

    file = node.label.file === nothing ? "" :
        "<div class=\"srcfile\">" * html_escape(node.label.file) * "</div>"
    note = truncated ? truncated_note(s, node, kids) :
           unmapped  ? unmapped_note(node) : ""

    # A truncated shim already links its body method, and every other callsite it
    # has is lowering; listing them there would only repeat and clutter.
    shown = truncated ? Set{String}() :
        source_tokens(String(src[startb:min(idxend, lastindex(src))]))
    unlocated = unique_callsites(s,
        [k for k in unplaced
         if (s.nodes[k].descendable || s.nodes[k].expandable) &&
            names_in_source(s.nodes[k], shown)])
    tail = unlocated_note(s, unlocated)

    sp = isempty(sparams) ? "" :
        "<div class=\"sparams\">where " *
        join(["<b>" * html_escape(k) * "</b> = " * html_escape(string(v))
              for (k, v) in sort!(collect(sparams), by=first)], ", ") * "</div>"

    return file * sp * note *
        "<div class=\"srcwrap\"><pre class=\"gutter\">" * gutter * "</pre>" *
        "<pre class=\"code src\">" * code * "</pre></div>" * tail
end

"Recursively emit `node`'s byte range, wrapping typed sub-expressions in spans.
Returns the next byte position to emit. Ranges from a syntax tree nest properly
by construction, so the spans can never overlap-without-containment."
function walk_source(io::IO, node, pos::Int, src, callsite_map, idxend::Int,
                     cfg::CthulhuConfig, sparams::Dict{String,Any}, cm, offset::Int,
                     deadspans::Set{Tuple{Int,Int}},
                     iscallee::Bool = false)
    fb, lb = first_byte(node), last_byte(node)
    fb > idxend && return pos
    lb = min(lb, idxend)
    lb < fb && return pos

    # text between the previous sibling and this node (whitespace, operators, ...)
    pos < fb && emit_code(io, src, pos, fb - 1, cm, offset)

    opened = open_span(io, node, fb, lb, src, callsite_map, cfg, sparams, deadspans, iscallee)

    p = fb
    kids = children(node)
    if kids !== nothing
        calleeidx = callee_index(node)
        isdot = kind(node) === K"."
        for (i, c) in enumerate(kids)
            # a dotted callee passes the flag down, so `Base.Math.sin` stays quiet
            # all the way to the leaf
            childcallee = (i == calleeidx) || (iscallee && isdot)
            p = walk_source(io, c, p, src, callsite_map, idxend, cfg, sparams, cm,
                            offset, deadspans, childcallee)
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
                   cfg::CthulhuConfig, sparams::Dict{String,Any},
                   deadspans::Set{Tuple{Int,Int}}, iscallee::Bool)
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

    if (fb, lb) in deadspans
        # Grey the whole subtree, and say why on hover -- an unexplained grey
        # block reads as a rendering failure.
        print(io, "<span class=\"s s-dead\" data-type=\"",
              "unreachable: compiled out for these argument types\">")
        return true
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
