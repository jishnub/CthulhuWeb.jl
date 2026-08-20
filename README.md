# CthulhuWeb.jl

A browser front end for [Cthulhu.jl](https://github.com/JuliaDebug/Cthulhu.jl).

The call tree becomes a nested, lazily-expanding list of callsites, next to a
type-annotated source view where every expression shows its inferred type on
hover and every call is a link you can descend into.

## Install

```julia
pkg> add https://github.com/jishnub/CthulhuWeb.jl
```

## Use

It works like `@descend`:

```julia
julia> using CthulhuWeb

julia> function f(x)
           T = x > 0 ? Int64 : Float64
           sin(rand(T))
       end

julia> @descend_web f(1.0)
[ Info: Cthulhu web UI at http://localhost:8000 — MethodInstance for f(::Float64)
```

<img width="1903" height="646" alt="image" src="https://github.com/user-attachments/assets/d733e257-e19f-4411-af5a-a9228ce531fb" />


Options are the usual `Cthulhu.CONFIG` keywords, plus `port`:

```julia
julia> @descend_web port=9000 view=:typed iswarn=true optimize=false f(1.0)

julia> descend_web(f, Tuple{Float64})   # non-macro form
julia> descend_web(mi)                  # or a MethodInstance

julia> stop_web()                       # shut every server down
julia> web_status()                     # what is running, and what is queued
```

Re-running on the same port replaces the running server, so you can keep
re-issuing `@descend_web` as you work. Pass different ports to compare two calls
side by side.

## The interface

**Left pane — the call tree.** Click a caret to expand a callsite, or a row to
show its code. Type-unstable returns are flagged, and `multi`, `runtime`,
`constprop` and similar callsites are badged. Recursive calls are marked rather
than expanded forever.

**Right pane — the code.** Five views: `source`, `typed`, `ast`, `llvm`,
`native`. In the source view, hover an expression for its inferred type and click
a call to descend into it. A breadcrumb trail, an **↑ caller** button and
**Backspace** take you back up.

**Toolbar.** *Data* options (`optimize`, `debuginfo`) refetch from Julia; display
options (`warn`, `effects`, `syntax`, …) apply instantly in the browser.

## Notes

- Inference runs on a single worker, so a second `@descend_web` issued while a
  slow one is still analysing waits its turn. `web_status()` shows whether a page
  is queued or genuinely stuck.
- The server starts before analysis finishes, so the page is reachable
  immediately and reports progress while a cold first descent compiles.
- The source view falls back to plain rendering for macro-generated code and
  anything whose source cannot be retrieved.
- Not implemented: `ascend` (backedges), and Revise support — after
  `Revise.revise()`, restart the session.

## Tests

```julia
pkg> test CthulhuWeb
```

`DESIGN.md` records why parts of the implementation work the way they do, if you
plan to change them.
