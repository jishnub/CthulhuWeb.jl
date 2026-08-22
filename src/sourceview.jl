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
const DEAD_KINDS = (K"call", K"dotcall", K"block", K"if", K"elseif", K"?", K"||",
                    K"&&", K".", K"return", K"for", K"while")

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
Nodes whose children are the alternatives of one choice: exactly one runs, so an
untyped one next to a typed one was compiled out.

`?` belongs here as much as `if` does. Leaving it out is what left
`conjugate ? adjoint(A[i,j]) : transpose(A[i,j])` in `copytri!` at full strength
under `cos(ones(2,2))`, where `conjugate` is `Core.Const(false)`: `transpose(...)`
was typed `::Float64` and `adjoint(...)` carried no type at all, and the reader
was told nothing -- the call just silently refused to descend.
"""
const CHOICE_PARENTS = (K"if", K"elseif", K"?")

"""
The arms of a conditional: everything after the test.

Only the arms say which way the branch went. The test does not: `eltype(v) ===
Float64` mentions a typed `v` whether or not any arm ran, which is enough to make
a naive sibling check believe the branch was resolved.

`?` has the same shape -- `(? cond then else)` -- so the same drop applies.
"""
conditional_arms(node) =
    (k = children(node); k === nothing ? () : Iterators.drop(k, 1))

"Did any arm of this conditional run? A nested conditional -- `elseif`, or the
else-arm of a chained ternary -- has to be asked the same question rather than
scanned for types, since its own test is typed either way."
arm_taken(node) = kind(node) in (K"elseif", K"?") ?
    any(arm_taken, conditional_arms(node)) : has_typed_descendant(node)

"""
Was this branch decided before the code ran?

Only then is "the other arm was compiled out" a thing that can be true, and the
test is what says so: a test that produced a value is a test that ran. A folded
test leaves no value behind -- `conjugate` in `copytri!` carries no type at all
once it is `Core.Const(false)` -- or leaves a constant one.

Without this, `det(::LU)` was a false positive. `isodd(c) ? -one(T) : one(T)` has
`isodd(c)::Bool`, a real runtime test, and both arms run; but only `-one(T)` came
back typed, because two identical `one(T)` calls on one line are ambiguous to
`map_ssas_to_source` and an ambiguous mapping is dropped rather than guessed. A
sibling check alone reads that dropped mapping as "unreachable" and greys out
live code. Ternaries make this common in a way `if` blocks do not: both arms sit
on one line and are usually near-identical expressions.
"""
function branch_resolved(node)
    kids = children(node)
    (kids === nothing || isempty(kids)) && return false
    t = first(kids).typ
    return t === nothing || t isa Core.Const
end

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
    live = if k in CHOICE_PARENTS
        branch_resolved(node) && any(arm_taken, conditional_arms(node))
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
Does the source at this span name the function the callsite calls?

Normally the question does not arise: a callsite comes back attached to the
source node it was lowered from. When the result is optimized IR the attachment
is by line number instead (see `distrust_body!`), and lands anywhere on the line
-- in `m = n * 2 + length(string(n))` reached by semi-concrete evaluation,
`string`'s callsite was attached to the `+`, so the addition was a click target
for `string` and its tooltip read `::String`.

Confirmation is the same identity match `pick_callsite` scores highest, with the
callee's spelling as the fallback for a span that is not a call node -- an infix
operator arrives as its own bare leaf.
"""
function names_this_callsite(s::Session, k::Int, sn, src, sparams::Dict{String,Any})
    n = s.nodes[k]
    v = callee_value(sn, src, sparams)
    v === nothing || return callee_matches(n, v)
    nm = callee_name(sn, src)
    if nm === nothing && is_leaf(sn)
        t = strip(String(src[first_byte(sn):last_byte(sn)]))
        nm = isempty(t) ? nothing : String(t)
    end
    nm === nothing && return false
    ctor = constructed_type(n)
    names = ctor === nothing ? [n.label.name] : ctor_names(ctor)
    return any(x -> x == nm || endswith(x, "." * nm), names)
end

"""
Place callsites Cthulhu did not, where the source says unambiguously where.

`f!(dest, parent(src))` in `copyto_unaliased!` gets no source node, so the call
was neither clickable nor listed -- the list keys on the callee's name and the
source says `f!`. But inference typed that callee `Core.Const(adjoint!)` and the
callsite dispatches on `typeof(adjoint!)`, which is the same identity match
`pick_callsite` already uses to choose between callsites sharing a range.

Searched in the body only -- a method's own signature is a `call` node whose
callee is the method itself, and would tie with any recursive call.

Indexing counts as a call, in both directions: `B[j,i] = f(A[i,j])` in
`transpose_f!` is a `setindex!` and the `A[i,j]` is a `getindex`, neither of
which Cthulhu locates and neither of which the source names, so they were
invisible in the pane by both routes.

Required unique in both directions: one unmapped call node whose callee is this
function, and one unmapped callsite for that node. `_modify2x2!` under
`@stable_muladdmul` has two callsites for its one node, so it stays unplaced --
the pairing has to be forced by the data, not picked.

Compiled-out code is not a candidate. It cannot hold the callsite -- there is no
callsite for code that did not run -- so it can only break the uniqueness that
does the placing. `copytri!` writes `A[j,i] = ...` under `uplo == 'U'` and
`A[i,j] = ...` under `elseif uplo == 'L'`; with `uplo` known the second is
compiled out, but both looked like the one `setindex!`, so the tie left the live
assignment with no callsite at all.
"""
function place_by_callee!(callsite_map, s::Session, unplaced::Vector{Int}, tsn, src,
                          sparams::Dict{String,Any}, unowned::Set{Tuple{Int,Int}},
                          dead::Set{Tuple{Int,Int}} = Set{Tuple{Int,Int}}(),
                          recognised::Set{Int} = Set{Int}())
    isempty(unplaced) && return unplaced
    nodes = Any[]
    written = Set{Tuple{Int,Int}}()
    unmapped(nd) = !haskey(callsite_map, (first_byte(nd), last_byte(nd)))
    function scan(nd)
        # `dead` holds outermost regions, so this prunes the whole subtree
        (first_byte(nd), last_byte(nd)) in dead && return
        k = kind(nd)
        if (k === K"call" || k === K"dotcall") && unmapped(nd)
            v = callee_value(nd, src, sparams)
            v === nothing || push!(nodes, (v, nd))
        end
        # Assignment is a call too, and one the source never names: `B[j,i] = v`
        # is `setindex!(B, v, j, i)`, `x.f = v` is `setproperty!`. The whole
        # statement is the call -- its arguments are the target, the indices and
        # the right-hand side -- so the span covers it all, exactly as `f(x)`
        # covers its arguments.
        #
        # `X[I] *= s` counts as well. It is the same write, and it was the whole
        # reason `rmul!(::AbstractArray, ::Number)` had a `setindex!` in the tree
        # that appeared nowhere in the pane. Its children are (target, op, value)
        # rather than (target, value), which only changes where the target sits.
        #
        # A DOTTED assignment does not: `A[i] .= v` is `dotview` and
        # `materialize!`, not `setindex!`, so offering it here would only invent
        # ties for the writes that are.
        kids = children(nd)
        isassign = (k === K"=" && kids !== nothing && length(kids) == 2) ||
                   (k === K"op=" && kids !== nothing && length(kids) == 3)
        if isassign && !is_dotted(JuliaSyntax.head(nd))
            lk = kind(kids[1])
            # `A[i] = v` reads nothing through `A[i]`: that span is the write.
            # Recorded before descending, so the `ref` below sees it. `A[i] *= v`
            # is not recorded -- it really does read before it writes.
            lk === K"ref" && k === K"=" &&
                push!(written, (first_byte(kids[1]), last_byte(kids[1])))
            # Offered whether or not the range is already taken. In
            # `rmul!(::AbstractArray, ::Number)` the whole of `X[I] *= s` is
            # Cthulhu's span for the `*`, so the `setindex!` can never own it --
            # but the write is still written there, and saying so is what keeps
            # it out of nowhere. Placement checks the range separately.
            #
            # A swap -- `X[k,i], X[k,j] = X[k,j], X[k,i]` in `rcswap!` -- is two
            # writes in one statement. Offered once, so its two callsites tie and
            # neither is placed: which of them the statement is cannot be
            # answered. Offering it is still worth it for the same reason.
            istuple = lk === K"tuple" && (tk = children(kids[1]);
                                          tk !== nothing && any(c -> kind(c) === K"ref", tk))
            fn = (lk === K"ref" || istuple) ? setindex! :
                 lk === K"." ? setproperty! : nothing
            fn === nothing || push!(nodes, (fn, nd))
        end
        # And so is a read through `[]`: `A[i,j]` is `getindex(A, i, j)`, whose
        # name the source says no more than it says `setindex!`. Unlike the
        # assignment, the span's value IS the call's result, so it keeps the
        # annotation as an ordinary call does.
        #
        # `A[i] += 1` is deliberately included: the read really does happen
        # there. Only the bare `=` target is excluded.
        if k === K"ref" && unmapped(nd) &&
                !((first_byte(nd), last_byte(nd)) in written)
            push!(nodes, (getindex, nd))
        end
        kids === nothing || foreach(scan, kids)
    end
    scan(tsn)
    isempty(nodes) && return unplaced

    left = Int[]
    matches(n, v, nd) = callee_matches(n, v) && arity_matches(n, nd)
    for k in unplaced
        n = s.nodes[k]
        hits = [nd for (v, nd) in nodes if matches(n, v, nd)]
        # A form in the source matches this callee. Even where that is not enough
        # to say WHICH one, it is enough to say the call is written here, which
        # is what the unlocated list needs -- it otherwise keys on the callee's
        # name, and the source says `getindex` and `setindex!` nowhere.
        isempty(hits) || push!(recognised, k)
        free = [nd for nd in hits if unmapped(nd)]
        length(free) == 1 || (push!(left, k); continue)
        target = free[1]
        claimants = count(unplaced) do j
            any(((v, nd),) -> nd === target && matches(s.nodes[j], v, nd), nodes)
        end
        claimants == 1 || (push!(left, k); continue)
        rng = (first_byte(target), last_byte(target))
        haskey(callsite_map, rng) && (push!(left, k); continue)
        # `a[i] = v` evaluates to `v`, not to what `setindex!` returns, so the
        # statement gets the click but not the annotation. Nor does `a[i] *= v`
        # evaluate to it.
        kind(target) in (K"=", K"op=") && push!(unowned, rng)
        l = n.label
        callsite_map[rng] = (id = k, rt = l.rt,
                             unstable = l.unstable, union = l.expected_union)
    end
    return left
end

"""
Does this indexing form take as many arguments as this callsite?

`A[i]` and `A[i,j]` are both `getindex`, and the callee alone cannot tell them
apart -- so in any method with more than one index read, every read tied with
every other and none was placed. The count can: a `ref` with N children is a
call with N arguments, and `lhs = rhs` is that plus the value.

Only the forms `place_by_callee!` invents are counted. A written-out `f(x)` is
matched by its callee, which is already specific, and counting there would only
add ways to be wrong. A splat has no fixed count, so it is left to the callee
match alone.
"""
function arity_matches(n::Node, nd)
    k = kind(nd)
    (k === K"ref" || k === K"=" || k === K"op=") || return true
    kids = children(nd)
    kids === nothing && return true
    target = k === K"ref" ? nd : kids[1]
    kind(target) === K"tuple" && return true   # several writes, no single count
    tkids = children(target)
    tkids === nothing && return true
    any(c -> kind(c) === K"...", tkids) && return true
    want = k === K"ref" ? length(tkids) : length(tkids) + 1
    return want == length(n.label.argtypes)
end

"""
Does the source text name this callee anywhere?

One of two tests for whether an unlocated callsite is worth reporting; the other
is whether `place_by_callee!` recognised a form for it, which is how the calls
the source performs without naming -- `getindex`, `setindex!`, `setproperty!` --
get in. Cthulhu maps most callsites to a source range, but not all: in
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
    name = tidy(n.label.name)
    m = match(r"var\"#+([^#\"]+)#\d+\"$", name)
    m === nothing || (name = String(m.captures[1]))
    args = [tidy(a) for a in n.label.argtypes if !startswith(a, "typeof(")]
    args = [length(a) > 40 ? first(a, 37) * "…" : a for a in args]
    sig = join(["::" * a for a in args], ", ")
    isempty(n.label.kwargs) || (sig *= "; " * join(tidy.(n.label.kwargs), ", "))
    return name * "(" * sig * ")"
end

"""
A type or name as one line of text: leading and trailing space gone, internal
runs (a line break inside a long parametric type) collapsed to a single space.
These land in buttons, where stray whitespace shows as an indent.
"""
tidy(x::AbstractString) = strip(replace(x, r"\s+" => " "))

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
Everything `walk_source` needs that is fixed for one method render. A struct
rather than a dozen positional arguments, which is what this had grown into --
`cfg` was still being threaded through both functions without being read.
"""
struct RenderCtx
    src::Any
    callsites::Dict{Tuple{Int,Int},NamedTuple}
    dead::Set{Tuple{Int,Int}}
    unverified::Set{Tuple{Int,Int}}
    unowned::Set{Tuple{Int,Int}}
    sparams::Dict{String,Any}
    classmap::Vector{UInt8}
    offset::Int
    idxend::Int
end

"""
Spans one source range shares with several IR statements, so the type the
mapping picked for it is one of them rather than the range's own.

A macro is one way in: it can expand one range into several statements -- under
`@stable_muladdmul`, `_modify2x2!(...)` becomes a call in each of two branches --
so whichever type the mapping picks is arbitrary. It picked the `MulAddMul{...}`
the expansion constructs, and hovering the call reported a type object where the
call returns `Any`.

Where a callsite IS placed we take Cthulhu's return type and the question does
not arise; where none is and a macro could have multiplied the mapping, the
honest answer is no type at all. Outside macros the mapping is one-to-one, so
unplaced calls -- `sub_int`, `getfield`, the intrinsics, 1555 of them across the
corpus against 81 here -- keep their annotations.

Destructuring is the other way in, and needs no macro. `X′, Y′ = _subadd!!(X, Y)`
in `tanh(::AbstractMatrix)` lowers to an `indexed_iterate` per name plus a
`getfield` each, all on that one line, and the mapping handed the `=` range one
of them: the whole statement was annotated `::Matrix{Float64}`. That is a
component's type. The assignment's own value is the right-hand side, the
`Tuple{Matrix{Float64}, Matrix{Float64}}` already shown on the call -- and
nothing distinguishes the two, so the span reports neither. Every other
assignment in the method is untyped and renders as a barrier; this one was
reporting a type for the comma and the `=` sign.
"""
function collect_unverified!(d::Set{Tuple{Int,Int}}, node, callsites, inmacro::Bool)
    k = kind(node)
    kids = children(node)
    if inmacro && (k === K"call" || k === K"dotcall") && node.typ !== nothing &&
       !haskey(callsites, (first_byte(node), last_byte(node)))
        push!(d, (first_byte(node), last_byte(node)))
    elseif k === K"=" && kids !== nothing && length(kids) == 2 &&
           kind(kids[1]) === K"tuple"
        # Both halves, for the same reason. The right-hand side is handed
        # `indexed_iterate`'s `(element, state)` rather than its own return:
        # `_subadd!!(X, Y)` reads `Tuple{Matrix{Float64}, Int64}` where the call
        # returns two matrices, and `reim(z)` reads `Tuple{Float64, Int64}`
        # where it returns two Floats. A placed callsite overrides this and is
        # believed; where none is placed there is nothing left to check it
        # against.
        node.typ === nothing || push!(d, (first_byte(node), last_byte(node)))
        kids[2].typ === nothing ||
            push!(d, (first_byte(kids[2]), last_byte(kids[2])))
    end
    kids === nothing || for c in kids
        collect_unverified!(d, c, callsites, inmacro || k === K"macrocall")
    end
    return d
end

"""
Every annotated span in a body that was not analysed as written.

`optimize=false` is a request the provider need not honour. A semi-concretely
evaluated call is analysed as already-optimized IR, and `lookup` hands that back
whatever we ask for (`result.optimized` is then true). `get_typed_sourcetext`
maps those statements onto the source BY LINE NUMBER
(`append_targets_for_line!`, TypedSyntax/src/node.jl), and every statement
inlined into a call carries the line of the call that inlined it -- so a
callee's statement can be reported as the calling expression's type.

Measured: in ApproxFunBase's `view(A::Operator, ::Type{FiniteRange}, jr)`, the
tail call `view(A,1:cs,jr)` was annotated `::Tuple{Int64, Int64}` -- a size tuple
from inside the `SubOperator` inlined into it -- where the call returns a Union
of two `SubOperator`s, and `1:cs` was annotated `::Int64`.

Nothing in the result separates a real mapping from a coincidence, so the whole
body annotation goes. What survives is what does not come from the mapping: the
signature (`slottypes`), static parameters, the method's return type, and the
callsites Cthulhu located itself.
"""
function distrust_body!(d::Set{Tuple{Int,Int}}, node, callsites)
    fb, lb = first_byte(node), last_byte(node)
    node.typ === nothing || haskey(callsites, (fb, lb)) || push!(d, (fb, lb))
    kids = children(node)
    kids === nothing || for c in kids
        distrust_body!(d, c, callsites)
    end
    return d
end

"Note for a body rendered without annotation because the code analysed was not
the code shown. See `distrust_body!`."
inlined_note(node::Node) =
    "<p class=\"note\">Cthulhu analysed this call as already-optimized code (" *
    html_escape(string(node.label.kind)) * "), so the statements it inferred are " *
    "no longer this method's own -- an inlined callee's statement carries the " *
    "line of the call that inlined it. The body is left unannotated rather than " *
    "annotated with a guess; the arguments, the calls Cthulhu located, and the " *
    "return type <code>" * html_escape(node.label.rt) * "</code> still hold.</p>"

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

    callsite_map = Dict{Tuple{Int,Int},NamedTuple}()
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
                k = pick_callsite(s, ks, spannode[key], tsn.source,
                                  get(spantypes, key, nothing), sparams)
                # An optimized result attaches callsites by line, not by
                # provenance, so a span can be handed a call it does not name.
                # Keep only what the source confirms; the rest fall back to the
                # unlocated list, where they are at least honestly placed.
                if result.optimized && !names_this_callsite(s, k, spannode[key],
                                                            tsn.source, sparams)
                    append!(unplaced, ks)
                    continue
                end
                l = s.nodes[k].label
                # Carry Cthulhu's own return type for the callsite, not just the
                # id. See `open_span`: for a call the two can disagree, and the
                # syntax node is the one that is wrong.
                callsite_map[key] = (id = k, rt = l.rt,
                                     unstable = l.unstable, union = l.expected_union)
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
    #
    # It also reads "no type" as "never reached", which holds only where a missing
    # type means inference did not get there. When the result came back optimized
    # the mapping is line-based and lossy (see `distrust_body!`), so a missing
    # type means nothing at all and nothing may be marked.
    deadspans = Set{Tuple{Int,Int}}()
    unmapped = !truncated && nothing_mapped(body) && body !== nothing && has_call(body)
    inlined = !truncated && !unmapped && result.optimized && body !== nothing
    truncated || unmapped || inlined || collect_dead!(deadspans, body)

    # Body only: the method's own signature is a `call` node whose callee is the
    # method itself, and it would tie with a recursive call in the body.
    unowned = Set{Tuple{Int,Int}}()
    recognised = Set{Int}()
    unplaced = try
        body === nothing ? unplaced :
            place_by_callee!(callsite_map, s, unplaced, body, tsn.source, sparams,
                             unowned, deadspans, recognised)
    catch
        unplaced
    end

    src = tsn.source
    startb = first_byte(tsn)
    unverified = collect_unverified!(Set{Tuple{Int,Int}}(), tsn, callsite_map, false)
    inlined && distrust_body!(unverified, body, callsite_map)
    ctx = RenderCtx(src, callsite_map, deadspans, unverified,
                    collect_unowned!(unowned, tsn),
                    sparams, token_classmap(src, startb, idxend), startb, idxend)
    io = IOBuffer()
    walk_source(io, tsn, startb, ctx)
    code = String(take!(io))

    firstline = source_line(src, first_byte(tsn))
    nlines = count(==('\n'), code) + 1
    gutter = join(string.(firstline:(firstline + nlines - 1)), "\n")

    file = node.label.file === nothing ? "" :
        "<div class=\"srcfile\">" * html_escape(node.label.file) * "</div>"
    note = truncated ? truncated_note(s, node, kids) :
           unmapped  ? unmapped_note(node) :
           inlined   ? inlined_note(node) : ""

    # A truncated shim already links its body method, and every other callsite it
    # has is lowering; listing them there would only repeat and clutter.
    shown = truncated ? Set{String}() :
        source_tokens(String(src[startb:min(idxend, lastindex(src))]))
    unlocated = unique_callsites(s,
        [k for k in unplaced
         if (s.nodes[k].descendable || s.nodes[k].expandable) &&
            (k in recognised || names_in_source(s.nodes[k], shown))])
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
function walk_source(io::IO, node, pos::Int, ctx::RenderCtx, iscallee::Bool = false)
    fb, lb = first_byte(node), last_byte(node)
    fb > ctx.idxend && return pos
    lb = min(lb, ctx.idxend)
    lb < fb && return pos

    # text between the previous sibling and this node (whitespace, operators, ...)
    pos < fb && emit_code(io, ctx.src, pos, fb - 1, ctx.classmap, ctx.offset)

    opened = open_span(io, node, fb, lb, ctx, iscallee)

    p = fb
    kids = children(node)
    if kids !== nothing
        calleeidx = callee_index(node)
        isdot = kind(node) === K"."
        for (i, c) in enumerate(kids)
            # a dotted callee passes the flag down, so `Base.Math.sin` stays quiet
            # all the way to the leaf
            childcallee = (i == calleeidx) || (iscallee && isdot)
            p = walk_source(io, c, p, ctx, childcallee)
        end
    end
    p <= lb && emit_code(io, ctx.src, p, lb, ctx.classmap, ctx.offset)

    opened && print(io, "</span>")
    return lb + 1
end

"""
Spans whose type is not their own.

A `for` header is: its type is `iterate`'s return,
`Union{Nothing, Tuple{Int64, Int64}}`, which is the type of neither the loop
variable nor the iterable nor the header as an expression. In
`transpose_f!`, the inner `i` has no type of its own, inherited the header's, and
rendered amber -- reading as if the loop variable were type-unstable. The outer
`j` happened to be typed, so the same two loops disagreed.

An assignment placed as a `setindex!`/`setproperty!` call joins them: `a[i] = v`
evaluates to `v`, not to what `setindex!` returns.

The span stays in both cases -- `iterate` and `setindex!` are worth descending
into; only the annotation goes.
"""
function collect_unowned!(d::Set{Tuple{Int,Int}}, node)
    # The `=` / `in` child spans the same bytes as the header it sits in and gets
    # the same callsite, so record the range rather than testing the kind.
    kind(node) === K"iteration" && push!(d, (first_byte(node), last_byte(node)))
    kids = children(node)
    kids === nothing || for c in kids
        collect_unowned!(d, c)
    end
    return d
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

function open_span(io::IO, node, fb::Int, lb::Int, ctx::RenderCtx, iscallee::Bool)
    src, sparams = ctx.src, ctx.sparams
    typ = node.typ
    # Under a macro with no callsite to confirm it, the mapping may have handed
    # this range another statement's type. Better none than a wrong one.
    (fb, lb) in ctx.unverified && (typ = nothing)
    # A callee whose annotation we deliberately drop is not an *untyped* node: it
    # must fall through to the enclosing call rather than raise a barrier.
    suppressed = typ !== nothing && uninteresting_const(typ, iscallee)
    suppressed && (typ = nothing)
    cs = get(ctx.callsites, (fb, lb), nothing)
    nodeid = cs === nothing ? 0 : cs.id
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

    if (fb, lb) in ctx.dead
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
    if (fb, lb) in ctx.unowned
        # Keep the span (it is a callsite, and `iterate` is worth descending
        # into) but report no type, so nothing inherits one that is not its own.
        typ = nothing
    elseif cs !== nothing
        # This span IS a call, so report the type Cthulhu inferred for that call.
        # The syntax node's own type comes from mapping IR statements onto source
        # ranges, and that mapping goes wrong: under `@stable_muladdmul` the call
        # node for `_modify2x2!(...)` carries `Core.Const(MulAddMul{...})` -- the
        # type the macro's expansion constructs -- rather than the call's return
        # type. Using the callsite's own `rt` also keeps this pane and the tree
        # agreeing, which is how that mismatch was noticed in the first place.
        typ = cs.rt
        push!(classes, cs.unstable ? (cs.union ? "s-union" : "s-unstable") : "s-stable")
    elseif typ !== nothing && !issparam
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
