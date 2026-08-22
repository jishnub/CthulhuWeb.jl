# End-to-end test: boots the real server and drives it over a real WebSocket.
# Run with:  julia --project=web --startup-file=no web/test_server.jl
using Test
using HTTP, JSON3
using CthulhuWeb
using CthulhuWeb: AUTO_PORT, DEFAULT_PORT, ESC, SERVERS, pick_port, port_free
using Sockets: Sockets

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

    @testset "replacing a server does not wait on the open tab" begin
        # `close(::HTTP.Server)` is graceful: it polls until every tracked
        # connection is idle, and an attached browser's WebSocket never is. So
        # re-running `descend_web` on a port a tab was watching sat inside
        # `stop_web` until that tab was refreshed -- and the refresh landed in
        # the gap between the two servers, which is the error the user saw
        # before a second refresh finally worked. Measured before the fix: still
        # blocked after 15s; `forceclose` returns in ~0.01s.
        #
        # The existing lifecycle test misses this because it re-runs with no
        # client attached, which is the one case that was never broken.
        f2(x) = sqrt(abs(x))
        descend_web(f2, Tuple{Float64}; port=8794)
        sleep(0.5)
        held = Channel{Bool}(1)          # holds the socket open
        client = Threads.@spawn try
            HTTP.WebSockets.open("ws://localhost:8794/") do ws
                first(ws)                # the init frame
                take!(held)
            end
        catch
        end
        try
            sleep(1.0)
            t0 = time()
            replaced = Threads.@spawn descend_web(f2, Tuple{Float64}; port=8794)
            @test timedwait(() -> istaskdone(replaced), 20.0) === :ok
            elapsed = time() - t0
            @test elapsed < 10
            println("  replaced a watched server in ", round(elapsed, digits=2), "s")
            # and the replacement really serves
            @test HTTP.get("http://localhost:8794/"; status_exception=false).status == 200
            HTTP.WebSockets.open("ws://localhost:8794/") do ws
                @test occursin("f2", JSON3.read(first(ws)).root.name)
            end
        finally
            close(held)
            stop_web(8794)
        end
        @test !haskey(SERVERS, 8794)
    end

    @testset "an automatic port is kept, so the tab is what gets replaced" begin
        # The point of reusing a port is that a browser tab is pointed at it.
        # Scanning up from `DEFAULT_PORT` every time does not do that: land on
        # 8001 once because something held 8000 for a moment, and the next run
        # drifts back to 8000 -- serving the new session where nobody is
        # looking and leaving the old one up on 8001 under the tab that is.
        # Observed in a REPL: two live servers, and the tab showing the
        # previous call's tree.
        f3(x) = abs(x) + 1
        saved = AUTO_PORT[]
        blocker = try Sockets.listen(Sockets.localhost, DEFAULT_PORT) catch; nothing end
        AUTO_PORT[] = nothing
        chosen = 0
        try
            descend_web(f3, Tuple{Float64})
            chosen = AUTO_PORT[]
            @test chosen > DEFAULT_PORT            # scanned past whatever holds 8000
            @test haskey(SERVERS, chosen)

            # 8000 comes free, and the next run must stay put anyway
            if blocker !== nothing
                close(blocker); blocker = nothing
                @test port_free(DEFAULT_PORT)
            end
            descend_web(f3, Tuple{Float64})
            @test AUTO_PORT[] == chosen
            @test haskey(SERVERS, chosen)
            @test !haskey(SERVERS, DEFAULT_PORT)   # not a second server
            HTTP.WebSockets.open("ws://localhost:$chosen/") do ws
                @test occursin("f3", JSON3.read(first(ws)).root.name)
            end

            # An explicit port is how trees run side by side, so it must not
            # capture the automatic one.
            @test pick_port(DEFAULT_PORT) == DEFAULT_PORT
            @test AUTO_PORT[] == chosen
        finally
            blocker === nothing || close(blocker)
            chosen == 0 || stop_web(chosen)
            AUTO_PORT[] = saved
        end
    end

    @testset "serves before analysing" begin
        # Regression: the session used to be built before `HTTP.listen!`, so a
        # slow entry point (LinearAlgebra, big generic calls) made descend_web
        # block, Ctrl-C useless, and the browser get connection-refused for the
        # whole analysis.
        slowtarget(A) = sqrt(A * A')
        descend_web(slowtarget, Tuple{Matrix{Float64}}; port=8793)
        try
            # reachable straight away, i.e. before analysis can have finished
            @test HTTP.get("http://localhost:8793/"; retry=false).status == 200

            ops = String[]
            HTTP.WebSockets.open("ws://localhost:8793/") do ws
                for raw in ws
                    m = JSON3.read(raw)
                    push!(ops, String(get(m, :op, "")))
                    last(ops) in ("init", "error") && break
                end
            end
            println("  handshake ops: ", ops)
            @test last(ops) == "init"
            # every op before `init` must be the initializing notice
            @test all(==("initializing"), ops[1:end-1])
        finally
            stop_web(8793)
        end
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

    @testset "worker death does not strand callers" begin
        # Without a supervisor a dead worker leaves every caller blocked in
        # take!(reply) forever: the queue stops draining and the UI looks hung
        # with no error reported anywhere.
        using CthulhuWeb: on_worker, WORKER, ensure_worker!, PENDING
        ensure_worker!()
        @test WORKER[] !== nothing && !istaskdone(WORKER[])

        # a job that throws must come back as an error, not hang
        r = on_worker(() -> error("boom"))
        @test r isa AbstractDict && r["op"] == "error"
        @test occursin("boom", r["msg"])
        @test isempty(PENDING)                       # caller deregistered

        # the worker survives a failing job and keeps serving
        @test on_worker(() -> 1 + 1) == 2
        @test !istaskdone(WORKER[])

        # kill it outright: pending callers must be failed, not stranded
        w = WORKER[]
        schedule(w, InterruptException(); error=true)
        t = @elapsed begin
            out = on_worker(() -> 42)     # respawns, or errors -- must not hang
        end
        @test t < 30
        println("  after worker kill, on_worker returned ", out, " in ",
                round(t, digits=2), "s")
    end

    @testset "web_status" begin
        using CthulhuWeb: web_status
        out = sprint(web_status)
        @test occursin("analysis worker", out)
        @test occursin("queued jobs", out)
        @test occursin("waiting callers", out)
        @test occursin("localhost:$PORT", out)       # the live server is listed
        println("  ", replace(strip(out), "\n" => " | "))
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
