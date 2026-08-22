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

## Handing a session over

To ask someone — or something — about what you are looking at without
describing it, *Export* it. **Download JSON** saves the session; **Copy for an
LLM** puts the same document on the clipboard as text.

Either carries the tree as you explored it, which rows you have open, and the
source of the node you are reading — with every claim the pane makes about it:
the type reported for each span, the callsite it descends into, and the regions
greyed as compiled out. A screenshot shows what a span looks like; this says
what it says.

```julia
julia> ws = load_session("cthulhuweb-tanh_Matrix_Float64.json")
WebSession(MethodInstance for tanh(::Matrix{Float64}), 147 nodes)

julia> ws                                  # showing it prints the readable form
# Cthulhu web session
entry    MethodInstance for tanh(::Matrix{Float64})
...
605 |             A[j,i] = conjugate ? adjoint(A[i,j]) : transpose(A[i,j])
    |     adjoint(A[i,j])           <<compiled out>>
    |     transpose(A[i,j])         ::Float64   -> node 47 transpose(::Float64) ::Float64

julia> ws["source"]["spans"]               # or query the document directly
```

`export_web("session.json")` writes the same thing from the REPL, without the
browser — though only the browser knows which rows are open on screen. A `.txt`
or `.md` path gets the text rendering instead.

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
