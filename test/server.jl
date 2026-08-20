# End-to-end test: boots the real server and drives it over a real WebSocket.
# Run with:  julia --project=web --startup-file=no web/test_server.jl
using Test
using HTTP, JSON3
using CthulhuWeb
using CthulhuWeb: ESC, SERVERS

wsdemo() = (T = rand() > 0.5 ? Int64 : Float64; sin(rand(T)))
usermacro(x) = (T = x > 0 ? Int64 : Float64; sqrt(abs(rand(T))))

const PORT = 8765
descend_web(wsdemo, Tuple{}; port=PORT, view=:typed, iswarn=true)
sleep(1.0)

"Send one op and wait for the matching reply, skipping acks."
function rpc(ws, op; kw...)
    req = rand(1:10^6)
    HTTP.WebSockets.send(ws, JSON3.write(Dict("op"=>op, "req"=>req, kw...)))
    for raw in ws
        msg = JSON3.read(raw)
        get(msg, :op, "") == "ack" && continue
        return msg
    end
    error("no reply for $op")
end

try
    @testset "static files" begin
        for (path, frag) in (("/", "<title>Cthulhu</title>"),
                             ("/app.js", "WebSocket"),
                             ("/style.css", "ansi_to_html"))
            r = HTTP.get("http://localhost:$PORT$path")
            @test r.status == 200
            @test occursin(frag, String(r.body))
        end
        @test HTTP.get("http://localhost:$PORT/../session.jl";
                       status_exception=false).status == 404
    end

    @testset "websocket session" begin
        HTTP.WebSockets.open("ws://localhost:$PORT/") do ws
            # server seeds the client
            init = JSON3.read(first(ws))
            @test init.op == "init"
            @test init.root.kind == "root"
            @test init.config.view == "typed"
            println("root: ", init.root.name)

            kids = rpc(ws, "expand"; id=1)
            @test kids.op == "children"
            @test !isempty(kids.nodes)
            println("children: ", [n.name for n in kids.nodes])
            @test any(n -> n.unstable, kids.nodes)          # the rand(T) union
            @test any(n -> n.kind == "multi", kids.nodes)

            # every record round-trips through JSON with the fields the UI needs
            for n in kids.nodes
                for k in (:id,:kind,:name,:argtypes,:rt,:unstable,:expandable,:descendable)
                    @test haskey(n, k)
                end
            end

            body = rpc(ws, "body"; id=1)
            @test body.op == "body"
            @test occursin("<pre class=\"code\">", body.html)
            @test !occursin(ESC, body.html)
            println("body html chars: ", length(body.html))

            # descend one level
            target = first(n for n in kids.nodes if n.expandable)
            g = rpc(ws, "expand"; id=target.id)
            @test g.op == "children"
            println("grandchildren of ", target.name, ": ", length(g.nodes))

            # config: switching to :source forces optimize off (config.jl:24)
            c = rpc(ws, "config"; key="view", value="source")
            @test c.op == "config"
            @test c.config.view == "source"
            @test c.config.optimize == false
            println("view=source -> optimize=", c.config.optimize,
                    " treeInvalidated=", c.treeInvalidated)

            # ...and asking for optimize=true while in :source is a silent no-op,
            # which the server must report honestly rather than echoing the request
            c2 = rpc(ws, "config"; key="optimize", value=true)
            @test c2.config.optimize == false

            c3 = rpc(ws, "config"; key="view", value="typed")
            @test c3.config.view == "typed"

            # source view over the wire: real spans, real click targets
            rpc(ws, "config"; key="view", value="source")
            sbody = rpc(ws, "body"; id=1)
            @test occursin("srcwrap", sbody.html)
            @test occursin("data-type=", sbody.html)
            ids = [parse(Int, m.captures[1])
                   for m in eachmatch(r"data-node-id=\"(\d+)\"", sbody.html)]
            @test !isempty(ids)
            println("source view: ", length(ids), " clickable calls, ",
                    length(collect(eachmatch(r"data-type=", sbody.html))), " typed spans")
            # every id the source offers must be a node the client already knows
            kids2 = rpc(ws, "expand"; id=1)
            known = Set(n.id for n in kids2.nodes)
            @test all(in(known), ids)
            rpc(ws, "config"; key="view", value="typed")

            # --- ascend path (client-side, but the DATA must support it) ---
            rpc(ws, "config"; key="view", value="source")
            root_kids = rpc(ws, "expand"; id=1)
            @test all(n -> n.parent == 1, root_kids.nodes)   # parents chain to root
            @test init.root.parent == 0                       # ...and ascend stops there

            bodyids(html) = Set(parse(Int, m.captures[1])
                                for m in eachmatch(r"data-node-id=\"(\d+)\"", html))

            # THE invariant the ascend highlight relies on: every data-node-id in a
            # node's source is a genuine child of that node. A wrong id would jump
            # the user somewhere unrelated.
            checked = 0
            for n in vcat([init.root], collect(root_kids.nodes))
                n.descendable || continue
                kids = rpc(ws, "expand"; id=n.id)
                ids = bodyids(rpc(ws, "body"; id=n.id).html)
                known = Set(k.id for k in kids.nodes)
                @test all(in(known), ids)
                isempty(ids) || (checked += 1)
                @test all(k -> k.parent == n.id, kids.nodes)
                println("  ", rpad(n.name, 8), length(kids.nodes), " children, ",
                        length(ids), " highlightable",
                        isempty(ids) ? "  (source view fell back)" : "")
            end
            # at least one node must actually support the highlight, or the
            # feature is vacuous
            @test checked > 0
            rpc(ws, "config"; key="view", value="typed")

            bad = rpc(ws, "nonsense")
            @test bad.op == "error"
        end
    end
    @testset "@descend_web / lifecycle" begin
        # a user-defined function driven through the macro, kwargs and all
        @descend_web port=8766 view=:source iswarn=true usermacro(1.5)
        sleep(0.5)
        try
            @test HTTP.get("http://localhost:8766/"; status_exception=false).status == 200
            @test haskey(SERVERS, 8766)

            HTTP.WebSockets.open("ws://localhost:8766/") do ws
                init = JSON3.read(first(ws))
                @test occursin("usermacro", init.root.name)
                @test init.config.view == "source"     # macro kwargs reached the config
                @test init.config.iswarn == true
                k = rpc(ws, "expand"; id=1)
                @test !isempty(k.nodes)
                @test any(n -> n.unstable, k.nodes)
                println("  @descend_web usermacro(1.5) -> ",
                        [n.name for n in k.nodes])
            end

            # re-running on the same port replaces rather than failing to bind
            @descend_web port=8766 usermacro(1.5)
            sleep(0.5)
            @test HTTP.get("http://localhost:8766/"; status_exception=false).status == 200
            @test length([p for p in keys(SERVERS) if p == 8766]) == 1
        finally
            stop_web(8766)
        end
        @test !haskey(SERVERS, 8766)
        # the port is really released
        @test_throws Exception HTTP.get("http://localhost:8766/"; retry=false)
    end

    @testset "progress feedback" begin
        # The UI shows a spinner from the moment it sends, but the server should
        # still ack promptly and before the result, so a slow inference never
        # looks like a dropped connection.
        HTTP.WebSockets.open("ws://localhost:$PORT/") do ws
            JSON3.read(first(ws))
            HTTP.WebSockets.send(ws, JSON3.write(Dict("op"=>"expand","req"=>4242,"id"=>1)))
            saw_ack = false
            for raw in ws
                m = JSON3.read(raw)
                if get(m, :op, "") == "ack"
                    @test m.req == 4242
                    saw_ack = true
                    continue
                end
                @test saw_ack            # ack must precede the result
                @test m.op == "children"
                break
            end
            @test saw_ack
        end

        # the client-side machinery the spinner depends on
        js = read(joinpath(pkgdir(CthulhuWeb), "src", "assets", "app.js"), String)
        css = read(joinpath(pkgdir(CthulhuWeb), "src", "assets", "style.css"), String)
        @test occursin("refreshBusy", js)
        @test occursin("loadingNodes", js)      # per-row spinner
        @test occursin("showLoading", js)       # code-pane spinner
        @test occursin("spinner", css)
        @test occursin("@keyframes spin", css)
    end

    @testset "port handling" begin
        using Sockets
        f1(x) = sin(abs(x))
        # explicit port that a foreign process holds -> clear error, no silent move
        blocker = Sockets.listen(Sockets.localhost, 8791)
        try
            err = try
                descend_web(f1, Tuple{Float64}; port=8791); nothing
            catch e; sprint(showerror, e) end
            @test err !== nothing
            @test occursin("already in use", err)
            @test !occursin("TaskFailedException", err)
            @test !haskey(SERVERS, 8791)
        finally
            close(blocker)
        end

        # descend_web returns nothing, not the HTTP.Server (which echoes a huge
        # Session/LookupResult/CodeInfo at the REPL)
        @test descend_web(f1, Tuple{Float64}; port=8792) === nothing
        @test haskey(SERVERS, 8792)
        # ...and re-running the same port replaces rather than accumulating
        @test descend_web(f1, Tuple{Float64}; port=8792) === nothing
        @test count(==(8792), keys(SERVERS)) == 1
        stop_web(8792)
        @test !haskey(SERVERS, 8792)
    end

finally
    stop_web()
end
