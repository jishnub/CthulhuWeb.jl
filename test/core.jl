# Smoke tests for the headless core. Run with:  julia --project=web web/test_core.jl
using Test
using Cthulhu
using Cthulhu: CthulhuConfig, CthulhuState
using CthulhuWeb
# internals under test
using CthulhuWeb: C, ESC, NodeId, ROOT_ID, Session, ansi_to_html, expand!,
                  headless_config, lookup_cached!, node_record, render_body,
                  source_html, static_params, token_classmap

f() = (T = rand() > 0.5 ? Int64 : Float64; sin(rand(T)))
rec(n) = n <= 1 ? 1 : n * rec(n - 1)

struct TPBox{A,B}; a::A; b::B; end
tp_combine(p::TPBox{A,B}, q::A) where {A,B} = (p.a, q)

function syndemo(x)
    # pick a type based on the sign
    T = x > 0 ? Int64 : Float64
    y = rand(T) + 2.5
    s = "value=$y"
    return sin(y) + length(s)
end

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

provider = C.AbstractProvider(C.CC.NativeInterpreter())
mi = C.find_method_instance(provider, f, Tuple{})

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
    provider2 = C.AbstractProvider(C.CC.NativeInterpreter())
    rmi = C.find_method_instance(provider2, rec, Tuple{Int})
    warm = Session(provider2, rmi; config=headless_config(C.CONFIG; view=:typed, optimize=true))
    expand!(warm, ROOT_ID)

    s = Session(provider2, rmi; config=headless_config(C.CONFIG; view=:typed, optimize=false))
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
        cfg = headless_config(C.CONFIG; view, iswarn=true)
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
    smi = C.find_method_instance(provider, srcdemo, Tuple{Float64})
    cfg = headless_config(C.CONFIG; view=:source, iswarn=true)
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
    cfg2 = headless_config(C.CONFIG; view=:typed)
    @test occursin("<pre class=\"code\">", render_body(s, s.nodes[ROOT_ID], cfg2))
end

@testset "static parameters" begin
    # The reported case: descending into `+(x::T, y::T) where {T<:IEEEFloat}`.
    # The source text keeps the generic `T`, but this specialization binds it.
    pmi = C.find_method_instance(provider, +, Tuple{Float64,Float64})
    @test static_params(pmi) == ["T" => "Float64"]

    cfg = headless_config(C.CONFIG; view=:source, iswarn=true)
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
    cmi = C.find_method_instance(provider, tp_combine, Tuple{TPBox{Int,String},Int})
    @test static_params(cmi) == ["A" => "Int64", "B" => "String"]

    # methods with no `where` get no header
    smi = C.find_method_instance(provider, srcdemo, Tuple{Float64})
    @test isempty(static_params(smi))
    @test !occursin("class=\"sparams\"", source_html(s, Session(provider, smi; config=cfg).nodes[ROOT_ID], cfg))
end

@testset "syntax highlighting" begin
    cfg = headless_config(C.CONFIG; view=:source, iswarn=true)
    smi = C.find_method_instance(provider, syndemo, Tuple{Float64})
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

