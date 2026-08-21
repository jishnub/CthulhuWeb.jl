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
# Everything reached for inside Cthulhu, in one place. Most of these are
# non-exported internals and the `AbstractProvider` docstring calls the interface
# experimental, so keeping the surface visible here is deliberate: if any of them
# is renamed upstream we get a load-time error naming the symbol, rather than a
# MethodError somewhere deep in a request handler.
using Cthulhu: AbstractProvider, CONFIG, Callsite, CthulhuConfig, CthulhuState,
               find_callsites, find_method_instance, generate_code_instance,
               get_ci, get_mi, get_override, get_rt, get_typed_sourcetext,
               is_type_unstable, lookup, set_config, source_slotnames, stringify,
               view_function
# NB: `is_type_unstable` also exists in TypedSyntax; we want Cthulhu's.
using JuliaSyntax: JuliaSyntax, @K_str, children, first_byte, is_infix_op_call,
                   is_keyword, is_leaf, is_operator, is_postfix_op_call, kind,
                   last_byte, source_line,
                   tokenize
using TypedSyntax: TypedSyntax, is_runtime
using CodeTracking: CodeTracking
using InteractiveUtils: InteractiveUtils, is_expected_union
using Logging: Logging, NullLogger, with_logger
using REPL
using HTTP
using JSON3
using Sockets

export descend_web, @descend_web, stop_web, web_status

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
    empty!(PENDING)
    return nothing
end

end # module
