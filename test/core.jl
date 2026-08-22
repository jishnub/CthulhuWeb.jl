# Smoke tests for the headless core. Run with:  julia --project=web web/test_core.jl
using Test
using Cthulhu
using Cthulhu: CONFIG, CthulhuConfig, CthulhuState, AbstractProvider,
                find_method_instance
using CthulhuWeb
using LinearAlgebra: LinearAlgebra
using JuliaSyntax: JuliaSyntax, @K_str, children, first_byte, kind, last_byte
using JSON3: JSON3
# internals under test
using CthulhuWeb: ESC, NodeId, body_label, is_body_method, ROOT_ID, Session, ansi_to_html, expand!,
                  headless_config, lookup_cached!, node_record, render_body,
                  callee_index, callee_matches, callee_value, callsite_callee,
                  constructed_type, is_name_resolution, is_synthetic_construct,
                  EXPORT_VERSION, session_document, session_text, load_session,
                  branch_resolved, collect_unverified!, conditional_arms,
                  get_typed_sourcetext, is_dead_region,
                  has_call, has_typeable, names_in_source,
                  names_this_callsite, nothing_mapped,
                  source_tokens,
                  unique_callsites,
                  source_html, static_params, token_classmap

f() = (T = rand() > 0.5 ? Int64 : Float64; sin(rand(T)))
rec(n) = n <= 1 ? 1 : n * rec(n - 1)

struct TPBox{A,B}; a::A; b::B; end
tp_combine(p::TPBox{A,B}, q::A) where {A,B} = (p.a, q)

# A genuine default-argument method: Julia generates a `shim(x)` whose body is
# empty (it only forwards), which is what triggers the truncated source view.
# NB `shim(x) = shim(x, 2)` would NOT do -- that body is a real call expression.
shim(x, n=2) = x^n + length(string(x))

# keyword shim whose default value is itself a call, like sqrt_quasitriu's
kwshim(v; width = eltype(v) <: Complex ? 512 : 256) = length(v) + width

kwinner(v; scale=2, shift=0) = v .* scale .+ shift
kwouter(v) = kwinner(v; scale=3, shift=1)

# bindings of several shapes, all of which must carry their own annotation
function annotated(x)
    n = length(string(x))
    T = x > 0 ? Int64 : Float64
    Tr = typeof(sqrt(zero(Float64)))
    y = rand(T)
    return (n, T, Tr, y)
end

# a composite expression evaluating to a Type, inside an unstable expression
function constdemo(x)
    T = x > 0 ? Int64 : Float64
    Tr = typeof(sqrt(zero(Float64)))
    return (rand(T), Tr)
end

# a stable call nested inside an unstable expression
leaky(x) = (T = x > 0 ? Int64 : Float64; rand(T) + length(string(x)))

function syndemo(x)
    # pick a type based on the sign
    T = x > 0 ? Int64 : Float64
    y = rand(T) + 2.5
    s = "value=$y"
    return sin(y) + length(s)
end

# Nested loops with an indexed write. The `for` header's inferred type is
# `iterate`'s `Union{Nothing, Tuple{...}}`, which belongs to neither the loop
# variable nor the range; and `B[j,i] = ...` is a `setindex!` the source never
# names and Cthulhu locates nowhere.
function loopwrite(B::Matrix{Float64}, A::Matrix{Float64})
    for j in axes(A, 2)
        for i in axes(A, 1)
            B[j, i] = A[i, j]
        end
    end
    return B
end

# A callee held in a variable: the source never spells `sum`, so a name-based
# test cannot find it -- but inference typed `g` as `Core.Const(sum)`.
function viavariable(v::Vector{Float64})
    g = sum
    g(v)
end

# Cthulhu locates most callsites in the source, but not all: here it places
# `min` and not `unlocatable_helper`, which is written just as plainly.
unlocatable_helper(a::Int, b::Int) = a * b
function unlocatable(v::Vector{Float64})
    n = length(v)
    unlocatable_helper(n, 2)
    return min(n, 3)
end

# multi-byte identifiers in a signature: `t.range` is a BYTE range, so lexing
# this used to die partway through and report no tokens at all
function multibyte(α::Float64, β::Float64)
    γ = α + β
    return sqrt(γ)
end

# Nested conditionals where the test folds: only one arm survives, and it is the
# arms -- not just the conditions -- that should read as untaken.
function armpick(v::Vector{Float64})
    x = if eltype(v) === Float64
        length(v)
    elseif eltype(v) === Float32
        length(v) + 1
    else
        0
    end
    return x
end

# `return true` is untyped -- a literal has no type of its own -- and sits among
# typed statements, which is the shape of an unreachable statement.
function literalreturn(v::Vector{Float64})
    if length(v) > 2
        sum(v)
        return true
    end
    return false
end

# `X[i] *= s` is a `setindex!` as much as `X[i] = v` is -- but Cthulhu's span
# for the whole statement belongs to the `*`, since that is what the statement
# evaluates to, so the write can never own a span here.
function scaleall!(X::Vector{Float64}, s::Float64)
    for i in eachindex(X)
        X[i] *= s
    end
    return X
end

# ...and two writes in one statement, the shape of `LinearAlgebra.rcswap!`.
# Which of them the statement is cannot be answered, so neither is placed.
function swaprows!(X::Matrix{Float64}, i::Int, j::Int)
    for k in axes(X, 2)
        X[i,k], X[j,k] = X[j,k], X[i,k]
    end
    return X
end

# Destructuring: the one line lowers to an `indexed_iterate` per name plus a
# `getfield` each, so several IR statements share it and the mapping hands the
# `=` and the right-hand side whichever one it lands on. Measured: the `=` gets
# a component's type and the call gets `indexed_iterate`'s `(element, state)`.
_pairof(x::Float64) = (x + 1.0, x - 1.0)
function destructured(x::Float64)
    a, b = _pairof(x)
    return a * b
end

# Two writes through `setindex!`, one of them compiled out. The source never
# says `setindex!`, so the call can only be placed by matching the assignment --
# and with both branches offered as candidates the match was not unique, which
# left the live assignment with no callsite at all. This is `copytri!`, whose
# `A[j,i] = ...` under `uplo == 'U'` is shadowed by the `A[i,j] = ...` under the
# compiled-out `elseif uplo == 'L'`.
Base.@constprop :aggressive function twowrite!(A::Matrix{Float64}, up::Bool)
    if up
        A[1,2] = 2 * A[2,1]
    else
        A[2,1] = 2 * A[1,2]
    end
    return A
end
twowritecaller(A::Matrix{Float64}) = twowrite!(A, true)

# ...and the same method with nothing folded: two live reads and two live
# writes, none of which the source distinguishes by name. The pairing is not
# forced by the data, so nothing may be placed.
bothlive!(A::Matrix{Float64}, up::Bool) = up ? (A[1,2] = 2*A[2,1]) : (A[2,1] = 2*A[1,2])
bothlivecaller(A::Matrix{Float64}, up::Bool) = bothlive!(A, up)

# A ternary whose test folds away -- the shape of `copytri!`'s
# `conjugate ? adjoint(A[i,j]) : transpose(A[i,j])`, where `conjugate` arrives as
# `Core.Const(false)`. Both arms are calls of the same shape, which is what a
# ternary almost always looks like.
Base.@constprop :aggressive ternbody(v, flag::Bool) = flag ? maximum(v) : minimum(v)
terncaller(v) = ternbody(v, false)

# ...and a ternary whose test RUNS. Both arms are live, but the two identical
# `one(T)` calls on the line are ambiguous to `map_ssas_to_source`, so the else
# arm comes back untyped next to a typed `-one(T)`. This is `det(::LU)`, and a
# sibling check alone greys live code here.
ternlive(n::Int, T) = isodd(n) ? -one(T) : one(T)
ternlivecaller(n::Int) = ternlive(n, Float64)

# ...but here the whole conditional folds to a constant, so NO arm carries types,
# the arm that runs included. Nothing can be said about which way it went.
function branchpick(v::Vector{Float64})
    tag = if eltype(v) === Float64
        :f64
    elseif eltype(v) === Float32
        :f32
    else
        :other
    end
    return (tag, length(v))
end

# A branch that folds away: for an `NTuple` argument the first test is const
# `true`, so both `length(itr) > 32` and the fallthrough are compiled out.
function deadbranch(itr::Tuple)
    if itr isa NTuple || length(itr) > 32
        return sum(itr)
    end
    prod(itr)
end

# A one-line method whose body is a leaf -- but a real one, not a shim with an
# emptied body. Truncating this to its signature hid the whole method.
passthru(x::Vector{Float64}) = x

# Callee spellings that all disagree with the callsite's label: `%` is `rem`,
# `≤` is `<=`, and `T(n)` is `Type{Float64}`.
spelled(x::T, n::Int) where {T<:AbstractFloat} = (n % UInt, x ≤ one(T), T(n))

# A method whose callee is spelled by interpolation, as LinearAlgebra's
# `($func)(A::AbstractTriangular; kwargs...) = ($func)(...; kwargs...)` is.
# Splatted keywords lower to `isempty(kws) ? f(args...) : kwcall(kws, f, args...)`
# and the `isempty` test is attributed to the whole call, so two callsites share
# one range -- with no name in the source to tell them apart.
kwtarget(v::Vector{Float64}; scale=1.0) = sum(v) * scale
for fn in (:kwtarget,)
    @eval kwforward(v::Vector{Float64}; kwargs...) = ($fn)(copy(v); kwargs...)
end

# `x^n` with a literal exponent lowers to `literal_pow(^, x, Val(n))`. The
# `Val{n}()` callsite has no call of its own to hang off, so it is attributed to
# whatever encloses it -- here the entire method.
powbody(x::Float64) = x^3

struct Pt2D; x::Float64; y::Float64; end
# ...and here it shares a source range with a constructor the user really wrote.
ctor_and_pow(a::Float64) = Pt2D(a, a^2)

# `Mod.f(x)` lowers to `getproperty(Mod, :f)` and then the call. The getproperty
# callsite's source range is the callee *name*, so it used to swallow the click.
qualified(x) = Base.Math.sin(x)

function srcdemo(x)
    T = x > 0 ? Int64 : Float64
    y = rand(T)
    return sin(y) + length(string(y))
end


"Inner HTML of the <span> carrying data-node-id=`id`, found by matching tags.
Robust to token spans nested inside, unlike a literal-adjacency regex."
function span_content(html::AbstractString, id::Int)
    m = match(Regex("<span[^>]*data-node-id=\"$(id)\"[^>]*>"), html)
    m === nothing && return ""
    i = m.offset + length(m.match)
    depth = 1
    for t in eachmatch(r"<span\b[^>]*>|</span>", html[i:end])
        depth += startswith(t.match, "</") ? -1 : 1
        depth == 0 && return html[i:i + t.offset - 2]
    end
    return html[i:end]
end

# Semi-concrete evaluation: `n` is constant and the method is foldable, but the
# result is not, so inference runs the OPTIMIZER over it and Cthulhu hands back
# already-inlined IR. The body then has more statements than it has source, and
# they map back onto it by line number alone.
Base.@assume_effects :foldable function scbody(n::Int, x::Float64)
    m = n * 2 + length(string(n))
    return x + m
end
sccaller(x::Float64) = scbody(3, x)

"Every node of a given kind in a typed syntax tree, outermost first."
function nodes_of_kind(node, k, acc = Any[])
    kind(node) === k && push!(acc, node)
    kids = children(node)
    kids === nothing || for c in kids
        nodes_of_kind(c, k, acc)
    end
    return acc
end

"Just the rendered source, without the notes and the unlocated list around it."
code_region(html::AbstractString) =
    replace(html, r"^.*?<pre class=\"code src\">"s => "", r"</pre>.*$"s => "")

"Plain text of each `.s-dead` region, in order -- what a reader sees faded."
function dead_regions(html::AbstractString)
    body = replace(html, r"^.*?<pre class=\"code src\">"s => "", r"</pre></div>.*$"s => "")
    out, depth, at = String[], 0, -1
    buf = IOBuffer()
    for m in eachmatch(r"<span class=\"([^\"]*)\"[^>]*>|</span>|[^<]+", body)
        t = m.match
        if startswith(t, "<span")
            depth += 1
            at < 0 && occursin("s-dead", m.captures[1]) && (at = depth)
        elseif startswith(t, "</")
            depth == at && (push!(out, String(take!(buf))); at = -1)
            depth -= 1
        elseif at > 0
            print(buf, t)
        end
    end
    return out
end

provider = AbstractProvider(Base.Compiler.NativeInterpreter())
mi = find_method_instance(provider, f, Tuple{})

@testset "session core" begin
    s = Session(provider, mi)
    @test s.nodes[ROOT_ID].label.kind === :root
    @test s.integ.M === Cthulhu || nameof(s.integ.M) === :CthulhuCompilerExt

    kids = expand!(s, ROOT_ID)
    @test !isempty(kids)
    @test !haskey(s.nodes[ROOT_ID].errors, s.config.optimize)
    println("root children: ", length(kids))
    for k in kids
        n = s.nodes[k]
        l = n.label
        println("  ", rpad(l.kind, 14), rpad(l.name, 22),
                " rt=", rpad(l.rt, 26),
                " unstable=", rpad(l.unstable, 6),
                " exp=", n.expandable)
    end

    # memoised
    @test expand!(s, ROOT_ID) === kids

    # every label built without throwing, including get_exct on ConcreteCallInfo
    @test all(k -> s.nodes[k].label.rt isa String, kids)

    # MultiCallInfo must expand to its alternatives, never call get_ci
    multis = [k for k in kids if s.nodes[k].label.kind === :multi]
    if !isempty(multis)
        m = first(multis)
        @test s.nodes[m].ci === nothing
        alts = expand!(s, m)
        println("multi node $(m) -> $(length(alts)) alternatives")
        @test length(alts) == s.nodes[m].label.nalternatives
        @test all(a -> s.nodes[a].label.kind === :edge, alts)
    end

    # descend two levels
    deep = [k for k in kids if s.nodes[k].expandable]
    @test !isempty(deep)
    g = expand!(s, first(deep))
    println("grandchildren of node $(first(deep)): ", length(g))
end

@testset "cycle guard" begin
    # Two Cthulhu behaviours interact here, both verified empirically:
    #  1. Under optimize=true a self-recursive function yields ZERO callsites.
    #  2. On a COLD interpreter the recursive edge is missing even unoptimized;
    #     it only appears once the CodeInstance has been inferred already. So warm
    #     the provider first, then look at the unoptimized tree.
    provider2 = AbstractProvider(Base.Compiler.NativeInterpreter())
    rmi = find_method_instance(provider2, rec, Tuple{Int})
    warm = Session(provider2, rmi; config=headless_config(CONFIG; view=:typed, optimize=true))
    expand!(warm, ROOT_ID)

    s = Session(provider2, rmi; config=headless_config(CONFIG; view=:typed, optimize=false))
    kids = expand!(s, ROOT_ID)
    names = [s.nodes[k].label.name for k in kids]
    println("rec callsites (warm, unoptimized): ", names)
    @test "rec" in names

    ri = kids[findfirst(==("rec"), names)]
    rn = s.nodes[ri]
    # the recursive child's CodeInstance is a DIFFERENT object from the root's,
    # which is why the guard compares MethodInstance identity instead.
    @test rn.mi === s.nodes[ROOT_ID].mi
    @test rn.ci !== s.nodes[ROOT_ID].ci
    @test rn.recursive_ancestor == ROOT_ID

    rec_json = node_record(s, ri)
    @test rec_json["recursive"]
    @test !rec_json["expandable"]        # refuse automatic expansion
    @test rec_json["recursiveOf"] == ROOT_ID

    # non-recursive siblings are unaffected
    for (nm, k) in zip(names, kids)
        nm == "rec" && continue
        @test s.nodes[k].recursive_ancestor == 0
    end
end

@testset "ansi_to_html" begin
    E = ESC
    @test ansi_to_html("plain") == "plain"
    @test ansi_to_html("$(E)[31mred$(E)[39m") == "<span class=\"c-red\">red</span>"
    @test ansi_to_html("a<b&c") == "a&lt;b&amp;c"
    # CHA padding, not literal "10G". ESC[10G is 1-based: after "ab" (col 2) we
    # pad 7 so that "x" lands at 1-based column 10.
    out = ansi_to_html("ab$(E)[10Gx")
    @test !occursin("10G", out)
    @test out == "ab" * " "^7 * "x"
    @test findfirst('x', out) == 10
    # never pads backwards
    @test ansi_to_html("abcdef$(E)[3Gx") == "abcdefx"
    # unterminated / unknown finals are dropped
    @test !occursin(string(E), ansi_to_html("$(E)[1;31mx$(E)[0m"))
end

@testset "render bodies" begin
    s = Session(provider, mi)
    for view in (:typed, :llvm, :native, :source)
        cfg = headless_config(CONFIG; view, iswarn=true)
        html = render_body(s, s.nodes[ROOT_ID], cfg)
        @test html isa String
        @test !occursin(ESC, html)          # every escape consumed
        @test !occursin("class=\"err\"", html)
        nspan = length(collect(eachmatch(r"<span", html)))
        println(rpad(view, 8), " chars=", rpad(length(html), 7), " spans=", nspan,
                "  highlighter=", cfg.enable_highlighter)
        # balanced spans
        @test nspan == length(collect(eachmatch(r"</span>", html)))
    end
end

@testset "source view" begin
    smi = find_method_instance(provider, srcdemo, Tuple{Float64})
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    s = Session(provider, smi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing
    @test !occursin(ESC, html)

    # every span is closed
    @test length(collect(eachmatch(r"<span", html))) ==
          length(collect(eachmatch(r"</span>", html)))

    # the type-unstable variable is located IN THE SOURCE, not just in a type table
    @test occursin("s-union", html)
    @test occursin("Union{Float64, Int64}", html)

    # calls are click targets carrying real child node ids
    ids = [parse(Int, m.captures[1]) for m in eachmatch(r"data-node-id=\"(\d+)\"", html)]
    @test !isempty(ids)
    kids = expand!(s, ROOT_ID; optimize=false)
    @test all(in(kids), ids)
    println("clickable calls: ", length(ids), " -> node ids ", sort(unique(ids)))

    # nesting: string(y) sits inside length(string(y)); both are click targets.
    # Checked structurally by matching tags, so token spans can't break it.
    ids = [parse(Int, m.captures[1]) for m in eachmatch(r"data-node-id=\"(\d+)\"", html)]
    outer = nothing
    for i in ids
        inner = span_content(html, i)
        others = [j for j in ids if j != i && occursin("data-node-id=\"$(j)\"", inner)]
        isempty(others) || (outer = (i, others); break)
    end
    @test outer !== nothing
    println("nesting: node ", outer[1], " contains ", outer[2])

    # callee names are NOT annotated with ::Core.Const(f) noise
    @test !occursin("Core.Const(sin)", html)
    @test !occursin("Core.Const(+)", html)

    # line gutter is present and starts at the method's real first line
    @test occursin("class=\"gutter\"", html)

    # render_body routes :source through this path, not the ANSI fallback
    body = render_body(s, s.nodes[ROOT_ID], cfg)
    @test occursin("srcwrap", body)
    @test !occursin("<pre class=\"code\">", body)   # the ANSI wrapper

    # ...and a node with no typed source still falls back rather than erroring
    cfg2 = headless_config(CONFIG; view=:typed)
    @test occursin("<pre class=\"code\">", render_body(s, s.nodes[ROOT_ID], cfg2))
end

@testset "static parameters" begin
    # The reported case: descending into `+(x::T, y::T) where {T<:IEEEFloat}`.
    # The source text keeps the generic `T`, but this specialization binds it.
    pmi = find_method_instance(provider, +, Tuple{Float64,Float64})
    @test static_params(pmi) == ["T" => Float64]

    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    s = Session(provider, pmi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing

    # the argument variables carry the CONCRETE type, not T
    @test occursin("data-type=\"::Float64\">x</span>", html)
    @test occursin("data-type=\"::Float64\">y</span>", html)
    # and `T` itself resolves to its binding
    @test occursin("s-sparam", html)
    @test occursin("T = Float64", html)
    # header line
    @test occursin("<div class=\"sparams\">where <b>T</b> = Float64</div>", html)
    # a static parameter is a String, so it must not be run through is_type_unstable
    @test !occursin("s-sparam s-unstable", html)

    # ordering with two parameters (declaration order, not reversed)
    cmi = find_method_instance(provider, tp_combine, Tuple{TPBox{Int,String},Int})
    @test static_params(cmi) == ["A" => Int64, "B" => String]

    # methods with no `where` get no header
    smi = find_method_instance(provider, srcdemo, Tuple{Float64})
    @test isempty(static_params(smi))
    @test !occursin("class=\"sparams\"", source_html(s, Session(provider, smi; config=cfg).nodes[ROOT_ID], cfg))
end

@testset "no colour leak from nested spans" begin
    # A type-stable call nested inside an unstable expression must not LOOK
    # unstable. Reported case: `checksquare(A)::Int` rendering amber because its
    # enclosing expression was a Union, so it inherited the warning colour.
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    smi = find_method_instance(provider, leaky, Tuple{Float64})
    s = Session(provider, smi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing

    # the scenario must actually occur, or this test proves nothing
    stack = String[]; nested = 0
    for m in eachmatch(r"<span class=\"([^\"]*)\"[^>]*>|</span>", html)
        if startswith(m.match, "</")
            isempty(stack) || pop!(stack); continue
        end
        cls = m.captures[1]
        if occursin("s-stable", cls) &&
           any(c -> occursin("s-union", c) || occursin("s-unstable", c), stack)
            nested += 1
        end
        push!(stack, cls)
    end
    println("stable spans nested inside a warning span: ", nested)
    @test nested > 0

    css = read(joinpath(pkgdir(CthulhuWeb), "src", "assets", "style.css"), String)
    # the base class must set an explicit colour so nothing inherits a warning one
    @test occursin(r"\.s\s*\{[^}]*color:\s*var\(--fg\)", css)
    # and stable spans must never be handed `color: inherit`, which would undo it
    @test !occursin(r"\.s-stable\s*\{[^}]*color:\s*inherit", css)
end

@testset "default-argument shim links its body method" begin
    # A method that only fills in default arguments has a single forwarding call
    # as its body, so there is nothing in its source to click. The body method is
    # in the tree, so the note must link it -- otherwise the pane is a dead end.
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    smi = find_method_instance(provider, shim, Tuple{Float64})
    s = Session(provider, smi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing
    @test occursin("only fills in default arguments", html)

    ids = [parse(Int, m.captures[1]) for m in eachmatch(r"data-node-id=\"(\d+)\"", html)]
    @test !isempty(ids)                          # something to click
    @test occursin("bodylink", html)
    kids = expand!(s, ROOT_ID; optimize=false)
    @test all(in(kids), ids)                     # and it is a real child
    target = s.nodes[first(ids)]
    @test target.descendable
    @test target.mi !== s.nodes[ROOT_ID].mi      # the body method, not itself
    println("shim links -> ", target.mi)
end

@testset "keyword shim links only the body method" begin
    # `f(x; kw = <expr>)` lowers to a shim that BOTH computes the default and
    # calls a gensym body `#f#NN`. The note must offer the body method, not the
    # default-value computation (reported: `eltype(A0)` offered for
    # `sqrt_quasitriu(A0; blockwidth = eltype(A0) <: Complex ? 512 : 256)`).
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    kmi = find_method_instance(provider, kwshim, Tuple{Vector{Float64}})
    s = Session(provider, kmi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing
    @test occursin("only fills in default arguments", html)

    kids = expand!(s, ROOT_ID; optimize=false)
    names = [s.nodes[k].label.name for k in kids]
    println("  shim children: ", names)
    @test any(n -> occursin("eltype", n), names)      # the default-value call...
    ids = [parse(Int, m.captures[1]) for m in eachmatch(r"data-node-id=\"(\d+)\"", html)]
    @test length(ids) == 1                            # ...but only one link
    linked = s.nodes[first(ids)]
    @test !occursin("eltype", linked.label.name)      # and it is not that one
    @test is_body_method(kmi, linked.mi)

    # the gensym name is cleaned up for display
    lbl = body_label(linked)
    @test occursin("kwshim(", lbl)
    @test !occursin("var\"#", lbl)
    @test !occursin("typeof(", lbl)                   # plumbing arg dropped
    println("  link label: ", lbl)
end

@testset "composite Const results keep their annotation" begin
    # `typeof(sqrt(zero(Float64)))` infers to Core.Const(Float64). Suppressing
    # that (the filter exists to drop ::Core.Const(sin) from callee NAMES) left
    # the call with no span, so it inherited the enclosing expression's warning
    # colour and looked type-unstable. Reported against sqrt_quasitriu.
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    tmi = find_method_instance(provider, constdemo, Tuple{Float64})
    s = Session(provider, tmi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing

    # the enclosing expression really is warning-coloured, else this proves nothing
    @test occursin("s-union", html) || occursin("s-unstable", html)

    # effective class of `typeof`: its own if it has one, else nearest ancestor
    plain = replace(html, r"^.*?<pre class=\"code src\">"s=>"", r"</pre></div>.*$"s=>"")
    stack = String[]; eff = String[]
    for m in eachmatch(r"<span class=\"([^\"]*)\"[^>]*>|</span>|typeof", plain)
        if m.match == "typeof"
            i = findlast(c -> occursin("s-union",c) || occursin("s-unstable",c) ||
                              occursin("s-stable",c), stack)
            push!(eff, i === nothing ? "none" : stack[i])
        elseif startswith(m.match, "</")
            isempty(stack) || pop!(stack)
        else
            push!(stack, m.captures[1])
        end
    end
    println("  typeof effective classes: ", eff)
    @test !isempty(eff)
    @test all(c -> occursin("s-stable", c), eff)          # never amber/red
    @test !any(c -> occursin("s-union", c) || occursin("s-unstable", c), eff)

    # ...while CALLEE names are still stripped of their Const noise
    @test !occursin("Core.Const(sqrt)", html)
    @test !occursin("Core.Const(rand)", html)
    @test !occursin("Core.Const(typeof)", html)

    # A variable bound to a constant type must carry its OWN annotation. It is an
    # Identifier whose type is Core.Const(Float64), so a filter keyed on "is a
    # name" ate it; hovering then reported the enclosing function's return type.
    # `v` is a plain identifier, so no escaping needed -- keep the pattern simple
    own(v) = collect(eachmatch(
        Regex("<span class=\"[^\"]*\"(?: data-type=\"([^\"]*)\")?[^>]*>" * v * "</span>"),
        html))
    hits = own("Tr")
    @test !isempty(hits)                              # Tr has a span at all
    @test all(h -> h.captures[1] !== nothing, hits)   # ...carrying a type
    @test all(h -> occursin("Float64", h.captures[1]), hits)
    @test !any(h -> occursin("Union{", h.captures[1]), hits)   # not the ancestor's
    println("  Tr annotated as: ", unique(h.captures[1] for h in hits))
end

@testset "every typed binding carries its own annotation" begin
    # The invariant behind three separate reported bugs: an expression with no
    # span of its own inherits its ancestors' colour AND reports their type on
    # hover. Any future suppression rule must not strip a binding's annotation.
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    ami = find_method_instance(provider, annotated, Tuple{Float64})
    s = Session(provider, ami; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing

    span_for(v) = collect(eachmatch(
        Regex("<span class=\"[^\"]*\"(?: data-type=\"([^\"]*)\")?[^>]*>" * v * "</span>"),
        html))

    for (v, expect) in ("n" => "Int64", "T" => "Type", "Tr" => "Float64", "y" => "Float64")
        hits = span_for(v)
        @test !isempty(hits)                                   # has a span
        @test all(h -> h.captures[1] !== nothing, hits)         # carrying a type
        @test any(h -> occursin(expect, h.captures[1]), hits)   # a plausible one
        println("  ", rpad(v, 3), " -> ", unique(h.captures[1] for h in hits))
    end
end

@testset "keyword calls descend into the call, not the lowering" begin
    # `f(x; kw=1)` lowers to a NamedTuple construction AND the call. Both map to
    # the same source range, and taking the first in SSA order landed the user in
    # boot.jl at `NamedTuple{names}(args::Tuple)` instead of `f`.
    cfg = headless_config(CONFIG; view=:source)
    kmi = find_method_instance(provider, kwouter, Tuple{Vector{Float64}})
    s = Session(provider, kmi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing

    ids = [parse(Int, m.captures[1]) for m in eachmatch(r"data-node-id=\"(\d+)\"", html)]
    @test !isempty(ids)
    linked = [s.nodes[i] for i in ids]
    @test !any(n -> startswith(n.label.name, "Type{NamedTuple"), linked)
    @test !any(n -> n.label.name == "Core.kwcall", linked)   # relabelled, not raw

    # the keyword call is presented as written: name, positional args, keywords
    kw = findfirst(n -> :kw in n.label.wrappers, linked)
    @test kw !== nothing
    lab = linked[kw].label
    @test lab.name == "kwinner"
    @test lab.kwargs == ["scale", "shift"]
    @test !any(a -> occursin("NamedTuple", a), lab.argtypes)
    @test !any(a -> occursin("typeof(", a), lab.argtypes)    # plumbing arg dropped
    println("  links to: ", lab.name, "(",
            join("::" .* lab.argtypes, ", "), "; ", join(lab.kwargs, ", "), ")")

    # and it really is the callee, reachable from the tree
    @test linked[kw].descendable
end

@testset "qualified calls descend into the call, not the name lookup" begin
    # Clicking `LAPACK.gesdd!` in `LAPACK.gesdd!(x)` landed in
    # `getproperty(x::Module, f::Symbol)`, because the getproperty callsite's
    # source range is exactly the callee name and so nests inside the call span.
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    qmi = find_method_instance(provider, qualified, Tuple{Float64})
    s = Session(provider, qmi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing

    kids = expand!(s, ROOT_ID; optimize=false)
    # the plumbing really is there in the tree -- it is only the click map we filter
    @test any(k -> is_name_resolution(s.nodes[k]), kids)

    ids = [parse(Int, m.captures[1]) for m in eachmatch(r"data-node-id=\"(\d+)\"", html)]
    linked = [s.nodes[i] for i in ids]
    @test !isempty(linked)
    @test !any(is_name_resolution, linked)
    @test any(n -> n.label.name == "sin", linked)

    # the whole `Base.Math.sin(x)` is one click target, so clicking the name
    # descends into `sin` rather than into name resolution
    sinid = ids[findfirst(n -> n.label.name == "sin", linked)]
    inner = span_content(html, sinid)
    @test startswith(replace(inner, r"<[^>]*>" => ""), "Base.Math.sin(")
    # ...and the qualifier is not walled off by a barrier, which would kill hover
    callee = first(split(inner, "("))
    @test !occursin("s-opaque", callee)
    @test !occursin("Core.Const", callee)     # `::Core.Const(Base.Math)` is noise
end

@testset "an untaken branch greys whole, not just its condition" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    ami = find_method_instance(provider, armpick, Tuple{Vector{Float64}})
    s = Session(provider, ami; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing
    faded = join(dead_regions(html), "\n")

    # the arms that cannot be reached, bodies and `elseif`/`else` included
    @test occursin("length(v) + 1", faded)
    @test occursin("0", faded)
    @test occursin("Float32", faded)
    # ...and the arm that is taken is at full strength
    @test !occursin("=== Float64", faded)
    # as is the code after the conditional
    @test !occursin("return x", faded)

    # A conditional that folds WHOLE says nothing about which arm ran: no arm
    # carries types, so greying the untaken ones would grey the taken one too.
    bmi = find_method_instance(provider, branchpick, Tuple{Vector{Float64}})
    b = Session(provider, bmi; config=cfg)
    bhtml = source_html(b, b.nodes[ROOT_ID], cfg)
    @test bhtml !== nothing
    bfaded = join(dead_regions(bhtml), "\n")
    @test !occursin(":f64", bfaded)
    @test !occursin(":f32", bfaded)     # ...and so neither is claimed dead

    # A literal carries no type whether it runs or not, so `return true` on the
    # taken path is untyped in exactly the way an unreachable statement is.
    # Claiming it was compiled out is the one thing this view must never do.
    ps(t) = JuliaSyntax.parsestmt(JuliaSyntax.SyntaxNode, t)
    @test !has_typeable(ps("return true"))
    @test !has_typeable(ps("(1, 2)"))
    @test has_typeable(ps("return x"))
    @test has_typeable(ps("return f(1)"))

    lmi = find_method_instance(provider, literalreturn, Tuple{Vector{Float64}})
    l = Session(provider, lmi; config=cfg)
    lhtml = source_html(l, l.nodes[ROOT_ID], cfg)
    @test lhtml !== nothing
    @test !occursin("return true", join(dead_regions(lhtml), "\n"))
end

@testset "a ternary's untaken arm greys, but only once the test is known" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)

    # `?` is a choice like `if` is, and was not treated as one: the untaken arm
    # was left at full strength while refusing to descend, which says nothing to
    # the reader about why.
    tmi = find_method_instance(provider, terncaller, Tuple{Vector{Float64}})
    t = Session(provider, tmi; config=cfg)
    tkids = expand!(t, ROOT_ID; optimize=false)
    ti = findfirst(k -> t.nodes[k].label.name == "ternbody", tkids)
    @test ti !== nothing
    tnode = t.nodes[tkids[ti]]
    @test tnode.label.kind === :constprop
    thtml = source_html(t, tnode, cfg)
    @test thtml !== nothing
    tfaded = join(dead_regions(thtml), "\n")
    @test occursin("maximum(v)", replace(tfaded, r"<[^>]*>" => ""))
    @test !occursin("minimum", tfaded)          # the arm that runs stays live
    @test occursin("data-type=\"::Float64\"", thtml)

    # A test that produced a value is a test that ran, so neither arm may be
    # greyed -- however the mapping turned out. Without the check, the missing
    # type on the else arm read as "unreachable" and greyed live code.
    lmi2 = find_method_instance(provider, ternlivecaller, Tuple{Int})
    l2 = Session(provider, lmi2; config=cfg)
    l2kids = expand!(l2, ROOT_ID; optimize=false)
    li = findfirst(k -> l2.nodes[k].label.name == "ternlive", l2kids)
    @test li !== nothing
    lnode = l2.nodes[l2kids[li]]
    lres = lookup_cached!(l2, lnode, false)
    ltsn = first(get_typed_sourcetext(lnode.mi, lres.src, lres.rt))
    q = only(nodes_of_kind(ltsn, K"?"))
    arms = collect(conditional_arms(q))
    @test !branch_resolved(q)                   # `isodd(n)::Bool` ran
    @test first(children(q)).typ === Bool
    @test arms[1].typ !== nothing               # ...and the sibling check alone
    @test arms[2].typ === nothing               #    would have fired on this
    @test is_dead_region(arms[2])
    lhtml2 = source_html(l2, lnode, cfg)
    @test lhtml2 !== nothing
    @test !occursin("s-dead", lhtml2)

    # A folded test leaves either no value at all or a constant one.
    tres = lookup_cached!(t, tnode, false)
    ttsn = first(get_typed_sourcetext(tnode.mi, tres.src, tres.rt))
    @test branch_resolved(only(nodes_of_kind(ttsn, K"?")))
end

@testset "a call the source performs without naming is listed, not dropped" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)

    # The unlocated list keys on the callee's name appearing in the source, and
    # the source says `setindex!` nowhere -- so a write with no span to own was
    # dropped from the pane entirely, though the tree holds it.
    smi = find_method_instance(provider, scaleall!, Tuple{Vector{Float64},Float64})
    sc = Session(provider, smi; config=cfg)
    skids = expand!(sc, ROOT_ID; optimize=false)
    sid = only(k for k in skids if sc.nodes[k].label.name == "setindex!")
    gid = only(k for k in skids if sc.nodes[k].label.name == "getindex")
    mid = only(k for k in skids if sc.nodes[k].label.name == "*")
    shtml = source_html(sc, sc.nodes[ROOT_ID], cfg)
    @test shtml !== nothing
    scode = code_region(shtml)
    # the statement evaluates to `X[i]*s`, so the `*` keeps the span...
    @test occursin("data-node-id=\"$mid\"", scode)
    @test occursin("data-node-id=\"$gid\"", scode)     # ...the read keeps its own...
    @test !occursin("data-node-id=\"$sid\"", scode)    # ...and the write has none left
    @test occursin(">setindex!(::Vector{Float64}, ::Float64, ::Int64)<", shtml)

    # Two writes in one statement: neither can be placed, and both kinds still
    # have to be reachable.
    wmi = find_method_instance(provider, swaprows!, Tuple{Matrix{Float64},Int,Int})
    w = Session(provider, wmi; config=cfg)
    wkids = expand!(w, ROOT_ID; optimize=false)
    idx = [k for k in wkids if w.nodes[k].label.name in ("getindex", "setindex!")]
    @test length(idx) == 4
    whtml = source_html(w, w.nodes[ROOT_ID], cfg)
    @test whtml !== nothing
    wcode = code_region(whtml)
    for k in idx
        @test !occursin("data-node-id=\"$k\"", wcode)
    end
    @test occursin(">setindex!(::Matrix{Float64}, ::Float64, ::Int64, ::Int64)<", whtml)
    @test occursin(">getindex(::Matrix{Float64}, ::Int64, ::Int64)<", whtml)

    # A `for` header calls `iterate` twice -- once to start, once per step --
    # and names neither. Cthulhu places the first on the header, so the second
    # had no span left to take and was dropped.
    it1 = only(k for k in wkids if w.nodes[k].label.name == "iterate" &&
                                   length(w.nodes[k].label.argtypes) == 1)
    it2 = only(k for k in wkids if w.nodes[k].label.name == "iterate" &&
                                   length(w.nodes[k].label.argtypes) == 2)
    @test occursin("data-node-id=\"$it1\"", wcode)
    @test !occursin("data-node-id=\"$it2\"", wcode)
    @test occursin(">iterate(::Base.OneTo{Int64}, ::Int64)<", whtml)

    # `x.f` is `getproperty(x, :f)` on the same terms. `eigencopy_oftype` reads
    # `A.uplo` more often than Cthulhu finds spans for it.
    emi = find_method_instance(provider, LinearAlgebra.eigencopy_oftype,
                               Tuple{LinearAlgebra.Symmetric{Float64,Matrix{Float64}},
                                     Type{Float64}})
    @test emi !== nothing
    e = Session(provider, emi; config=cfg)
    ekids = expand!(e, ROOT_ID; optimize=false)
    gps = [k for k in ekids if e.nodes[k].label.name == "getproperty"]
    @test length(gps) > 1
    ehtml = source_html(e, e.nodes[ROOT_ID], cfg)
    @test ehtml !== nothing
    ecode = code_region(ehtml)
    @test any(k -> occursin("data-node-id=\"$k\"", ecode), gps)    # one has a span
    @test any(k -> !occursin("data-node-id=\"$k\"", ecode), gps)   # another has none
    # the label truncates a long argtype, so match the part that identifies it
    @test occursin("getproperty(::LinearAlgebra.Symmetric", ehtml)

    # Resolving a qualified name is not a call the reader wants, whichever route
    # reaches it: `Core.sizeof(x)` holds a `getproperty(::Module, ::Symbol)`
    # that the click map already drops, and the list must drop it too.
    zmi = find_method_instance(provider, sizeof, Tuple{Type{Float64}})
    @test zmi !== nothing
    z = Session(provider, zmi; config=cfg)
    zkids = expand!(z, ROOT_ID; optimize=false)
    @test any(k -> z.nodes[k].label.argtypes == ["Module", "Symbol"], zkids)
    zhtml = source_html(z, z.nodes[ROOT_ID], cfg)
    @test zhtml !== nothing
    @test !occursin("getproperty(::Module", zhtml)
end

@testset "an exported session carries the claims, not just the look" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    xmi = find_method_instance(provider, twowritecaller, Tuple{Matrix{Float64}})
    x = Session(provider, xmi; config=cfg)
    xkids = expand!(x, ROOT_ID; optimize=false)
    bi = findfirst(k -> x.nodes[k].label.name == "twowrite!", xkids)
    @test bi !== nothing
    bid = xkids[bi]
    bodykids = expand!(x, bid; optimize=false)
    doc = session_document(x, bid)

    @test doc["cthulhuweb"] == EXPORT_VERSION
    @test doc["open"] == bid
    @test doc["path"] == [ROOT_ID, bid]
    ids = [n["id"] for n in doc["nodes"]]
    @test ROOT_ID in ids && bid in ids
    @test all(k -> k in ids, bodykids)            # the open node's children survive a cap
    @test doc["explored"] == length(x.nodes)
    @test doc["truncated"] == 0

    src = doc["source"]
    @test src["available"]
    spans = src["spans"]
    # A screenshot shows what a span looks like; this has to say what it claims.
    @test any(sp -> "s-dead" in sp["classes"], spans)          # the folded branch
    @test any(sp -> sp["type"] == "Float64", spans)
    sid = only(k for k in bodykids if x.nodes[k].label.name == "setindex!")
    @test any(sp -> sp["node"] == sid, spans)

    # ...and they are the page's own claims: the export shares its walk, so every
    # click target it names is one the page emits.
    html = source_html(x, x.nodes[bid], cfg)
    for sp in spans
        sp["node"] === nothing && continue
        @test occursin("data-node-id=\"$(sp["node"])\"", html)
    end

    txt = session_text(doc)
    @test occursin("# Cthulhu web session", txt)
    @test occursin("<-- open", txt)
    @test occursin("<<compiled out>>", txt)
    @test occursin("setindex!", txt)
    @test occursin("A[1,2] = 2 * A[2,1]", txt)   # the body itself, line by line

    # A file written today has to read the same when it is loaded back.
    mktemp() do path, io
        write(io, JSON3.write(doc)); close(io)
        ws = load_session(path)
        @test session_text(ws) == txt
        @test ws["open"] == bid
        @test length(ws["nodes"]) == length(doc["nodes"])
    end

    # A cap costs the far edges, never the part being read: the path to the open
    # node and its children go in ahead of the sweep the cap stops.
    small = session_document(x, bid; cap = 1)
    sids = [n["id"] for n in small["nodes"]]
    @test ROOT_ID in sids
    @test bid in sids
    @test all(k -> k in sids, bodykids)
    @test small["truncated"] == small["explored"] - length(sids)
end

@testset "a destructuring assignment is not typed by one of its parts" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    dmi = find_method_instance(provider, destructured, Tuple{Float64})
    d = Session(provider, dmi; config=cfg)
    dnode = d.nodes[ROOT_ID]
    dres = lookup_cached!(d, dnode, false)
    dtsn = first(get_typed_sourcetext(dnode.mi, dres.src, dres.rt))
    asg = only(nodes_of_kind(dtsn, K"="))
    rhs = children(asg)[2]

    # what the mapping actually handed them: a component's type on the whole
    # statement, and `indexed_iterate`'s `(element, state)` on the call
    @test asg.typ === Float64
    @test occursin("Int64", string(rhs.typ))
    uv = collect_unverified!(Set{Tuple{Int,Int}}(), dtsn,
                             Dict{Tuple{Int,Int},NamedTuple}(), false)
    @test (first_byte(asg), last_byte(asg)) in uv
    @test (first_byte(rhs), last_byte(rhs)) in uv

    html = source_html(d, dnode, cfg)
    @test html !== nothing
    # the call keeps the type Cthulhu gave it, which overrides the mapping...
    @test occursin("data-type=\"::Tuple{Float64, Float64}\"", html)
    # ...the names keep their own...
    @test occursin("data-type=\"::Float64\">a</span>", html)
    @test occursin("data-type=\"::Float64\">b</span>", html)
    # ...and the statement claims nothing, so hovering the comma or the `=` is
    # silent rather than reporting one of the parts for the whole line.
    @test occursin(
        r"<span class=\"s-opaque\"><span class=\"s-opaque\"><span class=\"s s-stable\" data-type=\"::Float64\">a</span>",
        html)
    # the mismapped `(element, state)` never reaches the code
    @test !occursin("Int64", code_region(html))

    # The reads the destructuring performs are the calls the source does not
    # name. They lose the statement's span to `_pairof`, which does not mean
    # they are not called -- they must still be reachable.
    ii = [k for k in expand!(d, ROOT_ID; optimize=false)
          if occursin("indexed_iterate", String(d.nodes[k].label.name))]
    @test length(ii) == 2
    dcode = code_region(html)
    for k in ii
        @test !occursin("data-node-id=\"$k\"", dcode)
    end
    @test occursin(">Base.indexed_iterate(::Tuple{Float64, Float64}, ::Int64)<", html)
    @test occursin(">Base.indexed_iterate(::Tuple{Float64, Float64}, ::Int64, ::Int64)<", html)
end

@testset "compiled-out code does not shadow a call's only source node" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    wmi = find_method_instance(provider, twowritecaller, Tuple{Matrix{Float64}})
    w = Session(provider, wmi; config=cfg)
    wkids = expand!(w, ROOT_ID; optimize=false)
    wi = findfirst(k -> w.nodes[k].label.name == "twowrite!", wkids)
    @test wi !== nothing
    wnode = w.nodes[wkids[wi]]
    @test wnode.label.kind === :constprop
    kids2 = expand!(w, wkids[wi]; optimize=false)
    si = findfirst(k -> w.nodes[k].label.name == "setindex!", kids2)
    gi = findfirst(k -> w.nodes[k].label.name == "getindex", kids2)
    @test si !== nothing
    @test gi !== nothing
    sid, gid = kids2[si], kids2[gi]

    html = source_html(w, wnode, cfg)
    @test html !== nothing
    @test occursin("s-dead", html)                       # the else branch went
    # ...and the surviving assignment is the setindex! callsite, clickable
    @test occursin("data-node-id=\"$sid\"", html)
    placed = span_content(html, sid)
    @test occursin("1", replace(placed, r"<[^>]*>" => ""))
    @test occursin("[", replace(placed, r"<[^>]*>" => ""))
    @test !occursin("s-dead", placed)                    # not the dead write
    # `a[i] = v` evaluates to `v`, not to what `setindex!` returns, so the span
    # takes the click without claiming a type.
    @test !occursin("data-type", split(placed, "<span")[1])

    # The read is a call the source does not name either -- but its value IS
    # the call's result, so unlike the write it keeps its annotation.
    @test occursin("data-node-id=\"$gid\"", html)
    readspan = span_content(html, gid)
    @test replace(readspan, r"<[^>]*>" => "") == "A[2,1]"
    @test occursin(Regex("data-type=\"::Float64\"[^>]*data-node-id=\"$gid\""), html)

    # Nothing folded: two reads and two writes, and the source names none of
    # them. The pairing is not forced by the data, so none is placed -- a
    # guessed span would be worse than no span.
    bmi = find_method_instance(provider, bothlivecaller, Tuple{Matrix{Float64},Bool})
    b = Session(provider, bmi; config=cfg)
    bkids = expand!(b, ROOT_ID; optimize=false)
    bi = findfirst(k -> b.nodes[k].label.name == "bothlive!", bkids)
    @test bi !== nothing
    bkids2 = expand!(b, bkids[bi]; optimize=false)
    idx = [k for k in bkids2 if b.nodes[k].label.name in ("getindex", "setindex!")]
    @test length(idx) == 4
    bhtml = source_html(b, b.nodes[bkids[bi]], cfg)
    @test bhtml !== nothing
    @test !occursin("s-dead", bhtml)
    bcode = code_region(bhtml)
    for k in idx
        @test !occursin("data-node-id=\"$k\"", bcode)
    end
    # ...but the source does perform them, so they are listed rather than lost
    @test occursin(">setindex!(::Matrix{Float64}, ::Float64, ::Int64, ::Int64)<", bhtml)
    @test occursin(">getindex(::Matrix{Float64}, ::Int64, ::Int64)<", bhtml)
end

@testset "a body inference never annotated is explained, not greyed" begin
    # `_chkstride1(ok::Bool, A, B...)` reached by semi-concrete evaluation has a
    # known result and an IR that never maps back to source, so EVERY node in it
    # is untyped -- which by the dead-code test would grey the whole method.
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    cmi = find_method_instance(provider, LinearAlgebra.chkstride1, Tuple{Matrix{Float64}})
    @test cmi !== nothing
    s = Session(provider, cmi; config=cfg)
    kids = expand!(s, ROOT_ID; optimize=false)
    i = findfirst(k -> s.nodes[k].label.kind in (:semiconcrete, :concrete, :constprop), kids)
    @test i !== nothing
    html = source_html(s, s.nodes[kids[i]], cfg)
    @test html !== nothing
    @test !occursin("s-dead", html)
    @test occursin("evaluated this call at compile time", html)
    @test occursin(s.nodes[kids[i]].label.rt, replace(html, r"<[^>]*>" => ""))

    # `isempty(x::Tuple{}) = true` carries no types either, but there is nothing
    # to explain about it -- the note is for bodies that make calls
    ps(t) = JuliaSyntax.parsestmt(JuliaSyntax.SyntaxNode, t)
    @test !has_call(ps("true"))
    @test !has_call(ps("()"))
    @test has_call(ps("f(g(x))"))
    @test nothing_mapped(nothing)
end

@testset "a body analysed after inlining is not annotated from the leftovers" begin
    # `optimize=false` is a request the provider need not honour. A semi-concrete
    # result is optimized IR, and `get_typed_sourcetext` maps its statements onto
    # the source by LINE NUMBER, so a statement inlined into a call is reported as
    # that call's type. Found in ApproxFunBase's
    # `view(A::Operator, ::Type{FiniteRange}, jr)`, whose tail call was annotated
    # `::Tuple{Int64, Int64}` -- a size tuple from inside the `SubOperator` it
    # constructs -- where the call returns a Union of two `SubOperator`s.
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    scmi = find_method_instance(provider, sccaller, Tuple{Float64})
    @test scmi !== nothing
    s = Session(provider, scmi; config=cfg)
    kids = expand!(s, ROOT_ID; optimize=false)
    i = findfirst(k -> s.nodes[k].label.kind === :semiconcrete, kids)
    @test i !== nothing
    node = s.nodes[kids[i]]
    @test lookup_cached!(s, node, false).optimized
    html = source_html(s, node, cfg)
    @test html !== nothing
    @test occursin("already-optimized code", html)

    # the signature still carries types -- those come from `slottypes`, not from
    # the mapping -- and so does the method's return type
    @test occursin("data-type=\"::Core.Const(3)\"", html)
    @test occursin("data-type=\"::Float64\"", html)
    # ...but nothing in the body does
    code = replace(html, r"^.*<pre class=\"code src\">"s => "", r"</pre></div>.*$"s => "")
    body = code[something(findfirst("\n", code)).start:end]   # past the signature line
    @test !occursin("data-type", body)
    # in particular not the two that were wrong: `string`'s callsite had been
    # attached to the `+` (reporting `::String` for an `Int64` addition) and
    # `length`'s to the `*`
    @test !occursin("::String", code)
    @test !occursin("data-node-id", body)
    # and no dead-code marking: with a line-based mapping, an untyped node is not
    # evidence of anything
    @test !occursin("s-dead", html)

    # the calls are not lost, only honestly relocated
    @test occursin("unlocated", html)
    @test occursin("length(::String)", html)

    # a placement the source DOES name survives the same gate
    @test names_this_callsite(s, kids[i], JuliaSyntax.parsestmt(JuliaSyntax.SyntaxNode,
                                                                "scbody(3, x)"),
                              "scbody(3, x)", Dict{String,Any}())
end

@testset "a call span reports the callsite's return type" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    # The syntax node's own type comes from mapping IR statements onto source
    # ranges; where the span IS a callsite, Cthulhu's `rt` is what the tree shows
    # and what the tooltip must agree with.
    dmi = find_method_instance(provider, srcdemo, Tuple{Float64})
    s = Session(provider, dmi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing
    for m in eachmatch(r"data-type=\"::([^\"]*)\" data-node-id=\"(\d+)\"", html)
        @test m.captures[1] == s.nodes[parse(Int, m.captures[2])].label.rt
    end

    # A macro can expand one range into several statements, so an unplaced call
    # under one has no type we can vouch for -- better none than another
    # statement's. `@stable_muladdmul` duplicates its argument into two branches,
    # and the mapping handed the `_modify2x2!(...)` call the `MulAddMul{...}` the
    # expansion constructs; the call itself returns `Any`.
    mmi = find_method_instance(provider, LinearAlgebra.matmul2x2or3x3_nonzeroalpha!,
              Tuple{Matrix{Float64}, Char, Char, Matrix{Float64}, Matrix{Float64},
                    Bool, Bool})
    @test mmi !== nothing
    ms = Session(provider, mmi; config=cfg)
    mhtml = source_html(ms, ms.nodes[ROOT_ID], cfg)
    @test mhtml !== nothing
    @test occursin("_modify2x2!", mhtml)
    # the span opening at `_modify2x2!` carries no type at all...
    at = something(findfirst("_modify2x2!", mhtml)).start
    opener = match(r"<span[^>]*>$", mhtml[1:at-1])
    @test opener !== nothing
    @test !occursin("data-type", opener.match)
    # ...rather than the constructed type it used to report
    @test !occursin("data-type=\"::Core.Const(LinearAlgebra.MulAddMul", mhtml)

    # calls Cthulhu DID place keep theirs, macro or not
    @test occursin(r"data-type=\"::[^\"]*\" data-node-id=", mhtml)
end

@testset "a loop header's type is the protocol's, not the variable's" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    lmi = find_method_instance(provider, loopwrite, Tuple{Matrix{Float64}, Matrix{Float64}})
    s = Session(provider, lmi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing
    code = replace(html, r"^.*?<pre class=\"code src\">"s => "", r"</pre></div>.*$"s => "")

    # `iterate` returns Union{Nothing, Tuple{...}}; a loop variable that has no
    # type of its own inherited it and rendered amber, as if unstable.
    @test !occursin("Union{Nothing", code)
    @test !occursin("s-union", code)

    # the header stays a click target -- `iterate` is worth descending into --
    # it just carries no annotation
    linked = [s.nodes[parse(Int, m.captures[1])].label.name
              for m in eachmatch(r"data-node-id=\"(\d+)\"", code)]
    @test "iterate" in linked
    for m in eachmatch(r"<span class=\"([^\"]*)\"([^>]*)>", code)
        occursin("s-call", m.captures[1]) || continue
        # every annotated call span reports a real return type
        t = match(r"data-type=\"::([^\"]*)\"", m.captures[2])
        t === nothing || @test !startswith(t.captures[1], "Union{Nothing,")
    end

    # `B[j, i] = A[i, j]` is a setindex!: no call node in the source, no name in
    # the text, but the assignment is unambiguously where it goes
    @test "setindex!" in linked
    # The one call left over is the loop-continuation `iterate`: it shares the
    # header with the `iterate` Cthulhu placed and has no span of its own, so it
    # is listed rather than dropped. Nothing else is unaccounted for.
    @test occursin(">iterate(::Base.OneTo{Int64}, ::Int64)<", html)
    @test length(collect(eachmatch(r"<li><button", html))) == 1

    # the span covers the whole statement, as `f(x)` covers its arguments --
    # `setindex!(B, A[i,j], j, i)` takes the right-hand side as an argument
    sid = only(unique(m.captures[1] for m in eachmatch(r"data-node-id=\"(\d+)\"", code)
                      if s.nodes[parse(Int, m.captures[1])].label.name == "setindex!"))
    @test strip(replace(span_content(code, parse(Int, sid)), r"<[^>]*>" => "")) ==
          "B[j, i] = A[i, j]"
    # ...but carries no type: the statement evaluates to the right-hand side,
    # not to what `setindex!` returns
    opener = first(eachmatch(Regex("<span[^>]*data-node-id=\"$(sid)\"[^>]*>"), code))
    @test !occursin("data-type", opener.match)
    # the right-hand side keeps its own click target inside
    @test "getindex" in linked
end

@testset "unlocated callsites are placed by callee, then named" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)

    # A call in statement position whose result goes unused gets no source node
    # from Cthulhu -- but inference typed its callee, and exactly one call node in
    # the body has that callee, so the pairing is forced. It becomes clickable.
    umi = find_method_instance(provider, unlocatable, Tuple{Vector{Float64}})
    s = Session(provider, umi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing
    code = replace(html, r"^.*?<pre class=\"code src\">"s => "", r"</pre></div>.*$"s => "")
    placed = [s.nodes[parse(Int, m.captures[1])].label.name
              for m in eachmatch(r"data-node-id=\"(\d+)\"", code)]
    @test "unlocatable_helper" in placed
    @test !occursin("note unlocated", html)     # nothing left to list

    # ...and a call through a variable is placed the same way, since the match is
    # on the callee's identity rather than on how it is spelled
    cmi = find_method_instance(provider, viavariable, Tuple{Vector{Float64}})
    c = Session(provider, cmi; config=cfg)
    chtml = source_html(c, c.nodes[ROOT_ID], cfg)
    ccode = replace(chtml, r"^.*?<pre class=\"code src\">"s => "", r"</pre></div>.*$"s => "")
    @test "sum" in [c.nodes[parse(Int, m.captures[1])].label.name
                    for m in eachmatch(r"data-node-id=\"(\d+)\"", ccode)]

    # Where the pairing is NOT forced it stays a list: `@stable_muladdmul`
    # duplicates its argument, so one `_modify2x2!(...)` node has two callsites.
    mmi = find_method_instance(provider, LinearAlgebra.matmul2x2or3x3_nonzeroalpha!,
              Tuple{Matrix{Float64}, Char, Char, Matrix{Float64}, Matrix{Float64},
                    Bool, Bool})
    ms = Session(provider, mmi; config=cfg)
    mhtml = source_html(ms, ms.nodes[ROOT_ID], cfg)
    note = match(r"<p class=\"note unlocated\">.*?</ul>"s, mhtml)
    @test note !== nothing
    @test occursin("_modify2x2!", note.match)
    # named with working links, not merely mentioned
    ids = [parse(Int, m.captures[1]) for m in eachmatch(r"data-node-id=\"(\d+)\"", note.match)]
    @test !isempty(ids)
    @test all(i -> ms.nodes[i].descendable, ids)
    # one <li> per call, so several never run together into one wrapped blob
    @test occursin("<ul class=\"unlocated-list\">", note.match)
    @test length(collect(eachmatch(r"<li>", note.match))) == length(ids)
    # ...and the note sits after the source, not before it
    @test something(findfirst("note unlocated", mhtml)).start >
          something(findfirst("<pre class=\"code src\">", mhtml)).start

    # entries are one clean line each: no leading indent, no internal breaks
    for m in eachmatch(r"<button[^>]*>([^<]*)</button>", note.match)
        @test m.captures[1] == strip(m.captures[1])
        @test !occursin(r"\s\s|\n", m.captures[1])
    end
    # ...and the list is flush left rather than inset behind the button padding
    css2 = read(joinpath(pkgdir(CthulhuWeb), "src", "assets", "style.css"), String)
    @test occursin(r"\.unlocated-list \.bodylink \{[^}]*padding-left: 0", css2)

    # the same MethodInstance reached from several callsites is listed once
    @test length(unique(ids)) == length(ids)
    dupes = [k for k in expand!(ms, ROOT_ID; optimize=false) if ms.nodes[k].mi !== nothing]
    @test length(unique_callsites(ms, dupes)) ==
          length(unique(ms.nodes[k].mi for k in dupes))

    # `pw`'s `Base.literal_pow` and `idx`'s `lastindex` are unlocated too, but
    # they are lowering nobody wrote -- their names are not in the source.
    for (g, tt) in ((powbody, Tuple{Float64}), (deadbranch, Tuple{Tuple{Int,Int}}))
        t = Session(provider, find_method_instance(provider, g, tt); config=cfg)
        @test !occursin("note unlocated", source_html(t, t.nodes[ROOT_ID], cfg))
    end

    # the membership test is on tokens, so `parent` must not match inside
    # `parentmodule`, and `-` inside `->` is not a call to `-`
    toks = source_tokens("a -> parentmodule(x) # size")
    @test "parentmodule" in toks
    @test !("parent" in toks)
    @test "->" in toks
    @test !("-" in toks)
    @test !("size" in toks)          # in a comment, not called

    # multi-byte identifiers must not truncate the token scan
    mt = source_tokens("function multibyte(α::Float64, β::Float64)\n    γ = α + β\nend")
    @test "multibyte" in mt
    @test "α" in mt
    @test "γ" in mt
    @test "+" in mt

    mmi2 = find_method_instance(provider, multibyte, Tuple{Float64,Float64})
    ms2 = Session(provider, mmi2; config=cfg)
    @test source_html(ms2, ms2.nodes[ROOT_ID], cfg) !== nothing
end
@testset "code compiled out is greyed, not silently normal" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    dmi = find_method_instance(provider, deadbranch, Tuple{Tuple{Int,Int}})
    s = Session(provider, dmi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing
    @test occursin("s-dead", html)
    # the unreachable call is faded...
    dead = match(r"<span class=\"s s-dead\"[^>]*>((?:(?!</span>).)*)", html)
    @test dead !== nothing
    @test occursin("unreachable", html)
    # ...and the reachable one is still a live click target
    live = [s.nodes[parse(Int, m.captures[1])].label.name
            for m in eachmatch(r"data-node-id=\"(\d+)\"", html)]
    @test "sum" in live
    @test !("prod" in live)
    # only the OUTERMOST dead call gets a span: `length(itr) > 32` contains
    # `length(itr)`, and nesting the fade would multiply the opacities
    @test !occursin(r"s-dead(?:(?!</span>).)*s-dead"s, html)

    # the legend explains the fade, but only on pages that have any
    js = read(joinpath(pkgdir(CthulhuWeb), "src", "assets", "app.js"), String)
    @test occursin("#code .s-dead", js)
    @test occursin("compiled out for these argument types", js)

    # a signature default is untyped in a shim's own IR without being dead
    kmi = find_method_instance(provider, kwshim, Tuple{Vector{Float64}})
    k = Session(provider, kmi; config=cfg)
    khtml = source_html(k, k.nodes[ROOT_ID], cfg)
    @test !occursin("s-dead", khtml)
end

@testset "a real one-line method is not mistaken for a shim" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    pmi = find_method_instance(provider, passthru, Tuple{Vector{Float64}})
    s = Session(provider, pmi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing
    # the body is shown, not cut back to the signature...
    body = replace(html, r"^.*?<pre class=\"code src\">"s => "", r"</pre></div>.*$"s => "")
    @test occursin("=", replace(body, r"<[^>]*>" => ""))
    @test endswith(strip(replace(body, r"<[^>]*>" => "")), "= x")
    # ...and there is no default-argument caption
    @test !occursin("only fills in default arguments", html)

    # the genuine shim still truncates and still explains itself
    smi = find_method_instance(provider, shim, Tuple{Int})
    s2 = Session(provider, smi; config=cfg)
    h2 = source_html(s2, s2.nodes[ROOT_ID], cfg)
    @test occursin("only fills in default arguments", h2)
end

@testset "callees are matched on identity, not on spelling" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    smi = find_method_instance(provider, spelled, Tuple{Float64,Int})
    s = Session(provider, smi; config=cfg)
    byname = Dict(s.nodes[k].label.name => s.nodes[k]
                  for k in expand!(s, ROOT_ID; optimize=false))

    # what the source writes vs what the callsite is labelled
    @test callee_matches(byname["rem"], (%))
    @test callee_matches(byname["<="], (≤))
    @test callee_matches(byname["Type{Float64}"], Float64)
    @test !callee_matches(byname["rem"], (+))
    @test !callee_matches(byname["Type{Float64}"], Int)
    # the keyword wrapper is unwrapped, so `f(x; kw=1)` matches `f`
    @test callsite_callee(byname["rem"]) === typeof(%)

    # a constructor written through its UnionAll still matches: `Val(n)` is
    # spelled `Val` but dispatches on `Type{Val{n}}`
    p = Session(provider, find_method_instance(provider, powbody, Tuple{Float64});
                config=cfg)
    v = only(n for n in (p.nodes[k] for k in expand!(p, ROOT_ID; optimize=false))
             if constructed_type(n) !== nothing)
    @test callee_matches(v, Val)
    @test !callee_matches(v, Base.RefValue)

    # callee position: `f(x)` first, `a + b` second, `x'` last
    tsn = first(Cthulhu.get_typed_sourcetext(smi, lookup_cached!(s, s.nodes[ROOT_ID], false).src,
                                             lookup_cached!(s, s.nodes[ROOT_ID], false).rt))
    seen = Set{Any}()
    walk(nd) = (push!(seen, nd); ch = JuliaSyntax.children(nd);
                ch === nothing || foreach(walk, ch))
    walk(tsn)
    # `n % UInt` is infix (callee is child 2), `T(n)` is prefix (child 1); getting
    # that wrong is what put `::Core.Const(+)` on every operator.
    sp = Dict{String,Any}(static_params(smi))
    resolved = Set(callee_value(nd, tsn.source, sp) for nd in seen if callee_index(nd) != 0)
    @test (%) in resolved
    @test (≤) in resolved
    @test Float64 in resolved   # `T(n)`: bound by the specialization, not inferred
end

@testset "an interpolated callee descends into the call, not the kwargs test" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    fmi = find_method_instance(provider, kwforward, Tuple{Vector{Float64}})
    s = Session(provider, fmi; config=cfg)
    # the outer shim forwards; the body method is where the interpolation lives
    kids = expand!(s, ROOT_ID; optimize=false)
    bid = findfirst(k -> occursin("kwforward#", s.nodes[k].label.name), kids)
    @test bid !== nothing
    body = s.nodes[kids[bid]]

    html = source_html(s, body, cfg)
    @test html !== nothing
    linked = [s.nodes[parse(Int, m.captures[1])].label.name
              for m in eachmatch(r"data-node-id=\"(\d+)\"", html)]
    @test "kwtarget" in linked
    @test !("isempty" in linked)

    # both callsites really do share the range: this is a tie the name heuristic
    # cannot break, because `($fn)` has no name in it
    result = lookup_cached!(s, body, false)
    tsn = first(Cthulhu.get_typed_sourcetext(body.mi, result.src, result.rt))
    bkids = expand!(s, kids[bid]; optimize=false)
    cs, sn = Cthulhu.find_callsites(provider, result, body.ci, true)
    ranges = Dict{Tuple{Int,Int},Vector{String}}()
    for (i, x) in enumerate(sn)
        x isa Cthulhu.Callsite && continue
        push!(get!(ranges, (first_byte(x), last_byte(x)), String[]),
              s.nodes[bkids[i]].label.name)
    end
    shared = [v for v in values(ranges) if length(v) > 1]
    @test any(v -> "isempty" in v && "kwtarget" in v, shared)

    # the tiebreak is the inferred type of the span, which only `kwtarget` has
    tys = CthulhuWeb.span_types!(Dict{Tuple{Int,Int},String}(), tsn)
    rng = first(k for (k, v) in ranges if "isempty" in v && "kwtarget" in v)
    @test get(tys, rng, nothing) == "Float64"
    # ...and it is needed here precisely because `($fn)` resolves to no callee
    node = first(x for x in sn if !(x isa Cthulhu.Callsite) &&
                 (first_byte(x), last_byte(x)) == rng)
    @test CthulhuWeb.callee_value(node) === nothing
end

@testset "lowering-invented constructors are not click targets" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    linked(g, tt) = begin
        s = Session(provider, find_method_instance(provider, g, tt); config=cfg)
        html = source_html(s, s.nodes[ROOT_ID], cfg)
        (s, html, [s.nodes[parse(Int, m.captures[1])]
                   for m in eachmatch(r"data-node-id=\"(\d+)\"", something(html, ""))])
    end

    # `Val{3}()` is attributed to the whole of `powbody(x) = x^3`, so it used to
    # be the only click target in the method -- every click landed in an empty
    # singleton constructor.
    s, html, ls = linked(powbody, Tuple{Float64})
    @test html !== nothing
    @test !any(n -> occursin("Val", n.label.name), ls)
    # the callsite is still in the tree; it is only the source pane that filters
    kids = expand!(s, ROOT_ID; optimize=false)
    @test any(k -> constructed_type(s.nodes[k]) === Val{3}, kids)

    # sharing a range with a real constructor, `Val` must lose
    s, html, ls = linked(ctor_and_pow, Tuple{Float64})
    @test html !== nothing
    @test any(n -> n.label.name == "Type{Pt2D}", ls)   # what the user wrote...
    @test !any(n -> occursin("Val", n.label.name), ls) # ...not what lowering added

    # the discriminator is the source-node kind, so a constructor on a `call`
    # node is kept whatever its name
    pt = ls[findfirst(n -> n.label.name == "Type{Pt2D}", ls)]
    @test constructed_type(pt) === Pt2D
    @test !is_synthetic_construct(pt, K"call")
    @test is_synthetic_construct(pt, K"=")
end

@testset "no type is reported where none is known" begin
    # Correctness principle: never attribute a type to something that has none.
    # Untyped COMPOSITE nodes emit an `.s-opaque` barrier that stops both the
    # tooltip search and colour inheritance; untyped LEAVES do not, because a
    # callee name is part of the surrounding expression and reporting that
    # expression's type for it is accurate rather than a guess.
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    ami = find_method_instance(provider, annotated, Tuple{Float64})
    s = Session(provider, ami; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    plain = replace(html, r"^.*?<pre class=\"code src\">"s=>"", r"</pre></div>.*$"s=>"")
    @test occursin("s-opaque", plain)

    "what a browser would show when hovering the given token"
    function tip_at(needle)
        stack = []
        for m in eachmatch(r"<span class=\"([^\"]*)\"(?: data-type=\"([^\"]*)\")?[^>]*>|</span>|[^<]+", plain)
            t = m.match
            if startswith(t, "<span"); push!(stack, (m.captures[1], m.captures[2]))
            elseif startswith(t, "</"); isempty(stack) || pop!(stack)
            elseif strip(t) == needle
                j = findlast(x -> x[2] !== nothing || occursin("s-opaque", x[1]), stack)
                return j === nothing ? nothing :
                       (stack[j][2] === nothing ? nothing : stack[j][2])
            end
        end
        :notfound
    end

    # An assignment statement has no type of its own, so `=` reports nothing.
    # (`return` is NOT in this list: `return expr` really does have expr's type,
    # so reporting it there is accurate rather than a guess.)
    @test tip_at("=") === nothing
    # ...while names and variables resolve to the expression they belong to
    @test tip_at("n") !== nothing && occursin("Int64", tip_at("n"))
    @test tip_at("typeof") !== nothing && occursin("Float64", tip_at("typeof"))
    @test tip_at("length") !== nothing
    # the reported bug: `=` must not fall through to the function's return type
    fnty = match(r"<span class=\"[^\"]*\" data-type=\"([^\"]*)\"", plain).captures[1]
    @test tip_at("=") != fnty
    println("  = -> ", tip_at("="), " ; n -> ", tip_at("n"),
            " ; typeof -> ", tip_at("typeof"))
end

@testset "presentation mechanisms that silently regressed before" begin
    css = read(joinpath(pkgdir(CthulhuWeb), "src", "assets", "style.css"), String)
    js  = read(joinpath(pkgdir(CthulhuWeb), "src", "assets", "app.js"), String)

    # Tooltips were once a CSS ::after using `:hover:not(:has(...))`. That is
    # clipped by .srcwrap's scroll container (invisible on line 1) and the whole
    # rule is dropped by browsers without :has(). Must stay JS-driven.
    # no ::after tooltip hung off a type span (:has elsewhere is fine)
    @test !occursin(r"\[data-type\][^{]*::after", css)
    @test occursin("#tip", css)
    @test occursin("position: fixed", css)
    @test occursin("closest(\".s[data-type]\")", js)

    # `color: inherit` directly on a type class is what let a warning colour leak
    # into nested stable expressions. (Descendant rules like
    # `.s-union .tok-pun { color: inherit }` are deliberate and excluded.)
    for m in eachmatch(r"(?m)^\.s-(stable|union|unstable)\s*\{([^}]*)\}", css)
        @test !occursin("color: inherit", m.captures[2])
    end

    # The tooltip search must stop at `.s-opaque` barriers rather than walking to
    # any typed ancestor, and must not report a span that carries no type.
    @test occursin("closest(\".s[data-type], .s-opaque\")", js)
    @test occursin("dataset.type", js)
    @test occursin(".s-opaque", css)

    # Busy state must be raised on send, not on the server's ack: the first ack
    # can be seconds late, which is exactly when feedback matters.
    @test occursin(r"refreshBusy\(\);\s*\n\s*return p;", js)

    # A non-descendable callsite (union split, runtime dispatch) has no body, but
    # if it has alternatives the pane must offer them rather than dead-ending.
    @test occursin(r"n\.expandable && !childrenOf\.has\(id\)", js)
    @test occursin("Descend into one of its alternatives", js)
end

@testset "syntax highlighting" begin
    cfg = headless_config(CONFIG; view=:source, iswarn=true)
    smi = find_method_instance(provider, syndemo, Tuple{Float64})
    s = Session(provider, smi; config=cfg)
    html = source_html(s, s.nodes[ROOT_ID], cfg)
    @test html !== nothing

    # lexical classes actually appear
    for cls in ("tok-kw", "tok-com", "tok-str", "tok-num", "tok-op", "tok-pun")
        @test occursin(cls, html)
    end
    println("token spans: ", length(collect(eachmatch(r"<span class=\"tok-", html))))

    # keywords/comments/literals are highlighted...
    @test occursin("<span class=\"tok-kw\">function</span>", html)
    @test occursin("<span class=\"tok-kw\">end</span>", html)
    @test occursin("<span class=\"tok-num\">2.5</span>", html)
    @test occursin("tok-com", html) && occursin("pick a type", html)

    # ...but identifiers are NOT, so the type colouring still owns them.
    # `y` is a variable: it must carry data-type and no tok- class.
    @test occursin("data-type=\"::Float64\">y</span>", html)
    @test !occursin("<span class=\"tok-kw\">y</span>", html)

    # spans stay balanced once both systems are interleaved
    @test length(collect(eachmatch(r"<span", html))) ==
          length(collect(eachmatch(r"</span>", html)))

    # every character of the source survives -- tokenising must not drop or
    # duplicate text. Strip tags and unescape, then compare to the real source.
    plain = replace(html, r"^.*?<pre class=\"code src\">"s => "",
                          r"</pre></div>.*$"s => "")
    text = replace(replace(plain, r"<[^>]*>" => ""),
                   "&lt;"=>"<", "&gt;"=>">", "&quot;"=>"\"", "&amp;"=>"&")
    src_lines = filter(!isempty, strip.(split(text, "\n")))
    @test any(l -> occursin("function syndemo", l), src_lines)
    @test any(l -> occursin("rand(T)", l), src_lines)
    @test occursin("\"value=\$y\"", text)          # string literal intact

    # unparseable / odd input must degrade, not throw
    @test token_classmap("not valid julia )(", 1, 18) isa Vector{UInt8}
    @test isempty(token_classmap("x", 5, 1))
end

