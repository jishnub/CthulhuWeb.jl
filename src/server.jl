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

function ensure_worker!()
    w = WORKER[]
    (w !== nothing && !istaskdone(w)) && return w
    # Threads.@spawn, not @async: a 10-second inference must not freeze the REPL.
    # Only this task ever touches the compiler.
    WORKER[] = Threads.@spawn while true
        job = take!(JOBS[])
        result = try
            job.f()
        catch err
            Dict{String,Any}("op" => "error",
                             "msg" => sprint(showerror, err, catch_backtrace()))
        end
        put!(job.reply, result)
    end
    return WORKER[]
end

"Run `f` on the single compiler worker and wait for its result."
function on_worker(f::Function)
    ensure_worker!()
    reply = Channel{Any}(1)
    put!(JOBS[], Job(f, reply))
    return take!(reply)
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
    s.config = headless_config(C.set_config(s.config, NamedTuple((sym => val,))))
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
    descend_web(f, argtypes; port=8000, kwargs...)
    descend_web(tt::Type{<:Tuple}; ...)
    descend_web(mi::MethodInstance; ...)

Serve Cthulhu's call tree as a clickable nested list at http://localhost:port.
Keyword arguments are the usual `Cthulhu.CONFIG` options (`view`, `optimize`,
`iswarn`, ...). Blocks until interrupted; Ctrl-C to stop.
"""
function descend_web(@nospecialize(args...); port::Int = 8000,
                     interp = C.CC.NativeInterpreter(),
                     provider = C.AbstractProvider(interp),
                     open_browser::Bool = false, kwargs...)
    mi = _resolve_mi(provider, args...)
    cfg = headless_config(C.CONFIG; kwargs...)
    session = on_worker(() -> Session(provider, mi; config = cfg))
    session isa Session || error("failed to start session: $session")

    # HTTP.listen! (not serve!) is the STREAM-level entry point; serve! would hand the
    # handler a Request, and WebSockets.upgrade needs a Stream. One handler serves
    # both the static files and the WS upgrade,
    # so the whole UI lives on a single port.
    function apphandler(stream::HTTP.Stream)
        req = stream.message
        if HTTP.WebSockets.isupgrade(req)
            return HTTP.WebSockets.upgrade(stream) do ws
                serve_ws(ws, session)
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

    haskey(SERVERS, port) && stop_web(port)
    server = HTTP.listen!(apphandler, "127.0.0.1", port)
    SERVERS[port] = server

    url = "http://localhost:$port"
    @info "Cthulhu web UI at $url  —  $(mi)  (stop_web() to shut down)"
    open_browser && try run(`xdg-open $url`; wait=false) catch end
    return server
end

_resolve_mi(provider, mi::Core.MethodInstance) = mi
function _resolve_mi(provider, @nospecialize(args...))
    world = Base.tls_world_age()
    mi = C.find_method_instance(provider, args..., world)
    isa(mi, Core.MethodInstance) || error("No method instance found for $(join(args, ", "))")
    return mi
end

function serve_ws(ws, session::Session)
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
                isopen(outbox) && put!(outbox, JSON3.write(out))
            end
        end
    catch err
        err isa HTTP.WebSockets.WebSocketError || @warn "ws error" exception=err
    finally
        close(outbox)
    end
end
