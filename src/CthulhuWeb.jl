"""
    CthulhuWeb

A browser front end for [Cthulhu](https://github.com/JuliaDebug/Cthulhu.jl)'s
call tree: a nested, lazily-expanding list of callsites where clicking descends
into a function, alongside a type-annotated source view.

```julia
julia> using CthulhuWeb

julia> @descend_web f(1.0)
[ Info: Cthulhu web UI at http://localhost:8000 — MethodInstance for f(::Float64)
```
"""
module CthulhuWeb

using Cthulhu
using Cthulhu: AbstractProvider, CthulhuConfig, CthulhuState, Callsite
using CodeTracking: CodeTracking
using Logging: Logging, NullLogger, with_logger
using InteractiveUtils: InteractiveUtils
using REPL
using HTTP
using JSON3
using Sockets

export descend_web, @descend_web, stop_web

const C = Cthulhu
const TS = Cthulhu.TypedSyntax
const JS = Cthulhu.JuliaSyntax

const ASSETS = joinpath(@__DIR__, "assets")

include("session.jl")
include("render.jl")
include("sourceview.jl")
include("server.jl")

function __init__()
    # Built here rather than at precompile time: a Channel owns task/condition
    # state that must not be baked into the cache image, and the terminal shim
    # wraps IO handles.
    JOBS[] = Channel{Job}(64)
    WORKER[] = nothing
    NULL_TERMINAL[] = REPL.Terminals.TTYTerminal(
        "dumb", devnull,
        IOContext(devnull, :color => true, :displaysize => (40, 200)),
        devnull)
    empty!(SERVERS)
    return nothing
end

end # module
