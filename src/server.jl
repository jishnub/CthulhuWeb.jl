# Local HTTP + WebSocket front door for the headless Cthulhu core.
#
# Concurrency model: HTTP.jl spawns a task per connection, but type inference is
# not thread-safe -- CthulhuInterpreter holds five unsynchronised IdDicts that are
# mutated *during* inference (compiler/interpreter.jl:6-10), process_info can
# `@eval Main` (compiler/reflection.jl:246-252), and the llvm/native views enter
# codegen. So every Cthulhu call is funnelled through ONE worker task fed by a
# bounded channel. A plain lock would instead park every HTTP task inside its
# handler with no way to shed load.

# ---------------------------------------------------------------------------
# Worker
# ---------------------------------------------------------------------------

struct Job
    f::Function
    reply::Channel{Any}
end

const JOBS = Ref{Channel{Job}}()       # bounded -> back-pressure; see __init__
const WORKER = Ref{Union{Nothing,Task}}(nothing)

"Reply channels of callers currently waiting on the worker, so a worker death can
fail them instead of leaving them blocked forever."
const PENDING = Set{Channel{Any}}()
const PENDING_LOCK = ReentrantLock()

function ensure_worker!()
    w = WORKER[]
    (w !== nothing && !istaskdone(w)) && return w
    # Threads.@spawn, not @async: a 10-second inference must not freeze the REPL.
    # Only this task ever touches the compiler.
    worker = Threads.@spawn while true
        job = take!(JOBS[])
        result = try
            # invokelatest: the worker is a long-lived task, so its world age is
            # older than anything defined since it started. Calling job.f()
            # directly fails with "method too new to be called from this world
            # context" for work created after the first descend_web.
            Base.invokelatest(job.f)
        catch err
            Dict{String,Any}("op" => "error",
                             "msg" => sprint(showerror, err, catch_backtrace()))
        end
        # try/finally: if replying itself fails the caller must not be stranded
        try
            put!(job.reply, result)
        catch
            isopen(job.reply) && close(job.reply)
        end
    end
    WORKER[] = worker

    # Supervisor. Without it, a worker that dies leaves every caller blocked in
    # `take!(reply)` forever -- the queue simply stops draining and the UI looks
    # hung with no error anywhere.
    Threads.@spawn begin
        try; wait(worker); catch; end
        @lock PENDING_LOCK begin
            for ch in PENDING
                try
                    put!(ch, Dict{String,Any}("op" => "error",
                        "msg" => "the analysis worker died; run stop_web() and try again"))
                catch
                end
            end
            empty!(PENDING)
        end
        @error "CthulhuWeb: analysis worker died" exception=(
            worker.result isa Exception ? worker.result : ErrorException("unknown"))
    end
    return worker
end

"Run `f` on the single compiler worker and wait for its result."
function on_worker(f::Function)
    ensure_worker!()
    reply = Channel{Any}(1)
    @lock PENDING_LOCK push!(PENDING, reply)
    try
        put!(JOBS[], Job(f, reply))
        return take!(reply)
    finally
        @lock PENDING_LOCK delete!(PENDING, reply)
    end
end

"""
    web_status()

Report what the server is doing: running servers, the state of the single
analysis worker, and how much work is queued behind it. Inference is serialised,
so a page that sits on "initializing" is usually queued rather than hung.
"""
function web_status(io::IO = stdout)
    println(io, "servers        : ", isempty(SERVERS) ? "none" :
                join(("http://localhost:$p" for p in sort(collect(keys(SERVERS)))), ", "))
    w = WORKER[]
    println(io, "analysis worker: ", w === nothing ? "not started" :
                istaskfailed(w) ? "FAILED" : istaskdone(w) ? "finished" : "running")
    println(io, "queued jobs    : ", isassigned(JOBS) ? Base.n_avail(JOBS[]) : 0)
    println(io, "waiting callers: ", @lock PENDING_LOCK length(PENDING))
    return nothing
end

# ---------------------------------------------------------------------------
# Ops
# ---------------------------------------------------------------------------

function op_tree(s::Session, id::NodeId)
    kids = expand!(s, id; optimize = s.config.optimize)
    node = s.nodes[id]
    err = get(node.errors, s.config.optimize, nothing)
    return Dict{String,Any}(
        "op"       => "children",
        "id"       => id,
        "nodes"    => [node_record(s, k) for k in kids],
        "error"    => err,
    )
end

op_body(s::Session, id::NodeId) = Dict{String,Any}(
    "op"   => "body",
    "id"   => id,
    "html" => render_body(s, s.nodes[id], s.config),
)

function op_config(s::Session, key::String, value)
    sym = Symbol(key)
    val = value
    # `debuginfo` and `view` are Symbols; the rest are Bools.
    (sym === :view || sym === :debuginfo) && (val = Symbol(value))
    prev_opt = s.config.optimize
    s.config = headless_config(set_config(s.config, NamedTuple((sym => val,))))
    # Only `optimize` changes the child set. `view` reaches the data solely via
    # `optimize &= view !== :source` (config.jl:24), which is why we compare the
    # RESULTING optimize bit rather than the requested one -- setting optimize=true
    # while view===:source is a silent no-op and would otherwise desync the client.
    return Dict{String,Any}(
        "op"              => "config",
        "config"          => config_record(s.config),
        "treeInvalidated" => s.config.optimize != prev_opt,
        "root"            => node_record(s, ROOT_ID),
    )
end

function handle(s::Session, msg)
    op = get(msg, :op, nothing)
    op == "expand" && return op_tree(s, Int(msg[:id]))
    op == "body"   && return op_body(s, Int(msg[:id]))
    op == "config" && return op_config(s, String(msg[:key]), msg[:value])
    return Dict{String,Any}("op" => "error", "msg" => "unknown op: $op")
end

# ---------------------------------------------------------------------------
# HTTP / WebSocket
# ---------------------------------------------------------------------------

const MIMES = Dict(".html" => "text/html; charset=utf-8",
                   ".js"   => "text/javascript; charset=utf-8",
                   ".css"  => "text/css; charset=utf-8")

function static_handler(req::HTTP.Request)
    path = HTTP.URI(req.target).path
    path == "/" && (path = "/index.html")
    name = basename(path)
    file = joinpath(ASSETS, name)
    (isfile(file) && name in ("index.html", "app.js", "style.css")) ||
        return HTTP.Response(404, "not found")
    ctype = get(MIMES, splitext(name)[2], "application/octet-stream")
    return HTTP.Response(200, ["Content-Type" => ctype], read(file))
end

"""Servers started by `descend_web`, keyed by port, so re-running on the same
port in a REPL replaces the old one instead of failing to bind."""
const SERVERS = Dict{Int,Any}()

const DEFAULT_PORT = 8000
const PORT_SCAN = 50

"Is `port` bindable right now? Racy by nature, but enough to give a good error
instead of a TaskFailedException out of HTTP's listener task."
function port_free(port::Int)
    try
        close(Sockets.listen(Sockets.localhost, port))
        return true
    catch
        return false
    end
end

"""
Resolve the port to serve on.

- `nothing` (the default): reuse `DEFAULT_PORT` if we already own it — so
  successive runs replace in place and the browser tab keeps working — otherwise
  the first free port at or after it.
- an explicit port: that port or nothing. Silently moving would be worse than
  failing when the caller named one.
"""
function pick_port(requested::Union{Nothing,Int})
    if requested !== nothing
        (haskey(SERVERS, requested) || port_free(requested)) && return requested
        error("port $requested is already in use by another process. " *
              "Pass a different `port`, or omit `port` to pick a free one automatically.")
    end
    for p in DEFAULT_PORT:(DEFAULT_PORT + PORT_SCAN)
        (haskey(SERVERS, p) || port_free(p)) && return p
    end
    error("no free port found in $DEFAULT_PORT:$(DEFAULT_PORT + PORT_SCAN); pass `port` explicitly.")
end

"""
    stop_web()          # stop every server
    stop_web(port)      # stop the one on `port`
"""
function stop_web(port::Union{Nothing,Int} = nothing)
    for p in (port === nothing ? collect(keys(SERVERS)) : [port])
        srv = pop!(SERVERS, p, nothing)
        srv === nothing && continue
        try close(srv) catch end
        @info "Stopped Cthulhu web UI on port $p"
    end
    return nothing
end

"""
    @descend_web f(args...)
    @descend_web port=9000 view=:typed f(args...)

Evaluate the arguments, determine their types, and serve the call tree for that
call at http://localhost:port. The web counterpart of `Cthulhu.@descend`.
"""
macro descend_web(ex0...)
    InteractiveUtils.gen_call_with_extracted_types_and_kwargs(__module__, :descend_web, ex0)
end

"""
    descend_web(f, argtypes; port=nothing, kwargs...)
    descend_web(tt::Type{<:Tuple}; ...)
    descend_web(mi::MethodInstance; ...)

Serve Cthulhu's call tree as a clickable nested list at http://localhost:port.

With no `port`, serves on $DEFAULT_PORT, reusing it if this session already owns
it — so re-running replaces the previous server in place and an open browser tab
keeps working — or the next free port if something else holds it. Pass `port`
explicitly to demand a specific one, or to run several side by side.

Other keyword arguments are the usual `Cthulhu.CONFIG` options (`view`,
`optimize`, `iswarn`, ...).

Returns `nothing`; use [`stop_web`](@ref) to shut the server down. The running
servers live in `CthulhuWeb.SERVERS`, keyed by port, if you need the handle.
"""
function descend_web(@nospecialize(args...); port::Union{Nothing,Int} = nothing,
                     interp = Base.Compiler.NativeInterpreter(),
                     provider = AbstractProvider(interp),
                     open_browser::Bool = false, kwargs...)
    mi = _resolve_mi(provider, args...)
    cfg = headless_config(CONFIG; kwargs...)
    port = pick_port(port)
    haskey(SERVERS, port) && stop_web(port)

    # Build the session in the BACKGROUND and bring the server up first.
    # Constructing it runs full type inference on the entry point, which for
    # something like `sqrt(::Matrix{Float64})` can take a long time. Doing it
    # before listening meant the REPL appeared to hang, Ctrl-C could not help
    # (the work is on a worker task), and the browser got connection-refused for
    # the whole duration.
    session_task = Threads.@spawn begin
        try
            res = on_worker(() -> Session(provider, mi; config = cfg))
            res isa Session || error("failed to start session: $res")
            res
        catch err
            @error "CthulhuWeb: could not analyse $mi" exception=(err, catch_backtrace())
            rethrow()
        end
    end

    # HTTP.listen! (not serve!) is the STREAM-level entry point; serve! would hand the
    # handler a Request, and WebSockets.upgrade needs a Stream. One handler serves
    # both the static files and the WS upgrade,
    # so the whole UI lives on a single port.
    function apphandler(stream::HTTP.Stream)
        req = stream.message
        if HTTP.WebSockets.isupgrade(req)
            return HTTP.WebSockets.upgrade(stream) do ws
                serve_ws(ws, session_task)
            end
        end
        resp = static_handler(req)
        HTTP.setstatus(stream, resp.status)
        for (k, v) in resp.headers
            HTTP.setheader(stream, k => v)
        end
        HTTP.startwrite(stream)
        write(stream, resp.body)
        return nothing
    end

    server = try
        HTTP.listen!(apphandler, "127.0.0.1", port)
    catch err
        # HTTP binds inside a task, so a bind failure surfaces wrapped
        error("could not serve on port $port: " *
              first(sprint(showerror, err), 200))
    end
    SERVERS[port] = server

    url = "http://localhost:$port"
    @info "Cthulhu web UI at $url  —  $(mi)  (stop_web() to shut down)"
    open_browser && try run(`xdg-open $url`; wait=false) catch end
    # Return nothing, like `Cthulhu.descend`: echoing the HTTP.Server at the REPL
    # dumps the whole Session, LookupResult and CodeInfo. The server is kept in
    # `SERVERS` and torn down with `stop_web()`.
    return nothing
end

_resolve_mi(provider, mi::Core.MethodInstance) = mi
function _resolve_mi(provider, @nospecialize(args...))
    world = Base.tls_world_age()
    mi = find_method_instance(provider, args..., world)
    isa(mi, Core.MethodInstance) || error("No method instance found for $(join(args, ", "))")
    return mi
end

function serve_ws(ws, session_task::Task)
    # HTTP.WebSockets sockets are not safe for concurrent writes: give the
    # connection a single writer draining an outbox.
    outbox = Channel{String}(64)
    writer = @async try
        for text in outbox
            HTTP.WebSockets.send(ws, text)
        end
    catch
    end
    try
        # The page is reachable before analysis finishes; say so rather than
        # leaving the browser staring at an empty tree.
        istaskdone(session_task) ||
            put!(outbox, JSON3.write(Dict{String,Any}("op" => "initializing")))

        session = try
            fetch(session_task)
        catch err
            e = err isa TaskFailedException ? err.task.exception : err
            isopen(outbox) && put!(outbox, JSON3.write(Dict{String,Any}(
                "op" => "error", "msg" => sprint(showerror, e))))
            return
        end

        # seed the client
        put!(outbox, JSON3.write(Dict{String,Any}(
            "op" => "init",
            "root" => node_record(session, ROOT_ID),
            "config" => config_record(session.config))))

        for raw in ws
            msg = try
                JSON3.read(raw)
            catch err
                put!(outbox, JSON3.write(Dict("op"=>"error","msg"=>"bad JSON")))
                continue
            end
            req = get(msg, :req, nothing)
            # ack immediately so the UI can show a spinner while inference runs
            req === nothing || put!(outbox, JSON3.write(Dict("op"=>"ack","req"=>req)))
            @async begin
                out = on_worker(() -> handle(session, msg))
                out isa AbstractDict && req !== nothing && (out = merge(out, Dict("req"=>req)))
                # The viewer may have closed the tab while this was computing;
                # `isopen` alone races with the writer shutting down.
                try
                    isopen(outbox) && put!(outbox, JSON3.write(out))
                catch
                end
            end
        end
    catch err
        err isa HTTP.WebSockets.WebSocketError || @warn "ws error" exception=err
    finally
        close(outbox)
    end
end
