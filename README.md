# CthulhuWeb.jl

A browser front end for [Cthulhu.jl](https://github.com/JuliaDebug/Cthulhu.jl):
the call tree as a nested, lazily-expanding list of callsites where clicking
descends into a function, next to a type-annotated source view with hover types
and click-to-descend.

Cthulhu itself is unmodified — this package is built entirely on its
`AbstractProvider` interface and the same `lookup` / `find_callsites` data path
the terminal UI uses.

## Install

```julia
pkg> dev /path/to/CthulhuWeb.jl
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

Options are the usual `Cthulhu.CONFIG` keywords, plus `port`:

```julia
julia> @descend_web port=9000 view=:typed iswarn=true optimize=false f(1.0)
julia> descend_web(f, Tuple{Float64})     # non-macro form
julia> descend_web(Tuple{typeof(f), Float64})
julia> descend_web(mi::MethodInstance)
julia> stop_web()                          # shut every server down
```

Re-running on the same port replaces the running server, so you can keep
re-issuing `@descend_web` as you edit.

## Tests

```julia
pkg> test CthulhuWeb
```

## How it works

| File | Role |
|---|---|
| `src/session.jl` | Node registry + `expand!` — replaces `descend!`'s recursion |
| `src/render.jl` | Structured callsite records + ANSI→HTML for code bodies |
| `src/sourceview.jl` | Type-annotated source: spans with types, calls as click targets |
| `src/server.jl` | HTTP + WebSocket, single compiler worker, `@descend_web` |
| `src/assets/` | Vanilla-JS frontend, no build step |

Cthulhu's v3 design already separates data (`AbstractProvider`) from display, and
every renderer writes to a plain `IO`. The headless data path is unchanged:

```julia
result = lookup(provider, something(override, ci), optimize)
callsites, _ = find_callsites(provider, result, ci, false)
```

Only the **event loop** is replaced. `descend!` (`Cthulhu.jl src/descend.jl:45`) descends by
calling itself, using the Julia call stack as the ascend stack; a server can't
park inside a nested call, so `Session` keeps an explicit table keyed by tree
position — `SlotKey(parent, optimize, stmt_id, slot)`.

### Notes worth keeping

Things that were verified against the source and cost real debugging time:

- **Node identity is tree position, not `(mi, ci, override)`.** That triple is the
  *descend state*: non-injective, undefined for `MultiCallInfo`, and its
  `override` is reallocated per `find_callsites` call.
- **Recursion is detected on `MethodInstance`, not `CodeInstance`.** For
  `rec(n) = n<=1 ? 1 : n*rec(n-1)` the recursive callsite's `CodeInstance` is a
  *different object* from the root's, so `ci === ci` never fires. Two further
  quirks: under `optimize=true` a self-recursive function yields **zero**
  callsites, and on a **cold** interpreter the recursive edge is missing even
  unoptimized — it appears only once the `CodeInstance` has been inferred.
- **The ANSI is not pure SGR.** The typed view emits cursor-column codes
  (`ESC[1G`, `ESC[176G`) for IRShow's gutter. A naive converter prints `176G` as
  text. `ansi_to_html` tracks the column and pads.
- **`enable_highlighter` should be ON for `:llvm`/`:native`.** `highlight`
  (`src/compiler/codeview.jl:4-21`) uses in-process `print_llvm`/`print_native`
  for those and only forks `pygmentize` for julia. Off, they render with zero
  colour; on, LLVM gets ~330 colour spans for free.
- **`get_exct(::ConcreteCallInfo)` throws** — `Cthulhu.jl src/compiler/callsite.jl:154` binds
  `cici` but references `ceci` (`UndefVarError`). The TUI never calls it; building
  labels from accessors does. Worth a one-character PR upstream.
- **`get_ci` is a minefield**: throws for `MultiCallInfo`, warns-then-`nothing` for
  `Failed`/`Generated`. Hence `try_get_ci`.
- **`set_config(cfg; optimize=true)` is a silent no-op while `view === :source`**
  (`Cthulhu.jl src/config.jl:24`), so the server echoes the *resulting* config back and the
  client reflects it rather than letting the checkbox lie.
- **`stringify(f, ::IOContext)` does not add `:color=>true`** (only the `::IO`
  method does) — without it you silently get uncoloured text.
- **`:llvm`/`:native` are disabled on const-prop / semi-concrete nodes**: those
  pass `state.mi` with an `ir_to_src` `src` using synthetic slotnames, and the
  mismatch risks a codegen abort that kills the process, not just the request.
- **One compiler worker.** `CthulhuInterpreter` holds five unsynchronised
  `IdDict`s mutated during inference; `process_info` can `@eval Main`.

### Correctness principle: never invent a type

Every annotation bug found in this view had the same shape — a construct with no
type of its own inheriting one from a distant ancestor, because it was invisible
in the DOM. A stable call rendered amber inside an unstable expression; hovering
`=` reported the enclosing function's return type.

So untyped **composite** nodes emit an explicit `.s-opaque` barrier span, which
stops both the tooltip search and colour inheritance. If the analysis said
nothing about a construct, the UI says nothing about it.

Untyped **leaves** are deliberately not barriers: the callee name in
`checksquare(A0)` is part of the surrounding expression, so reporting that
expression's type when hovering it is accurate rather than a guess — and it is
the most natural thing to point at. The line is between *the expression you are
pointing at* and *some unrelated ancestor*, not between typed and untyped.

Two corollaries worth keeping in mind when extending this:

- Anything that suppresses an annotation must be justified by **position** (is
  this a callee?) rather than by the value's type — otherwise it silently strips
  real information and reopens the inheritance hole.
- `return expr` genuinely has `expr`'s type, so reporting it there is correct.
  The principle forbids guessing, not reporting.

### The source view

`:source` is rendered as real markup, not converted ANSI. The key fact is that
`find_callsites(provider, result, ci, true)` returns `sourcenodes`
**index-parallel to the identical callsite list** you get with `false`
(`src/compiler/reflection.jl:112-119`) — so a source span maps to a callsite by
position, with no extra matching. `sourceview.jl` walks the `TypedSyntaxNode`
tree and emits nested spans:

```html
<span class="s s-union s-call" data-type="::Union{Float64, Int64}" data-node-id="3">rand(T)</span>
```

Byte ranges from a syntax tree nest by construction, so spans can never
overlap-without-containment. That gives three things the terminal cannot do:
hover any subexpression for its inferred type, see instability highlighted
*where it occurs* rather than in a separate table, and click a call to descend.

**Static parameters.** `+(x::T, y::T) where {T<:IEEEFloat}` shows a generic `T`
in its source text, so the concrete binding was visible in the caller's argument
types but nowhere in the callee. `static_params(mi)` reads `mi.sparam_vals` and
pairs it with the `UnionAll` variable names (both in declaration order, so a
plain `zip` is correct), producing a `where T = Float64` header and making the
`T` tokens themselves hoverable.

**Tooltips are JS, deliberately not CSS.** The first implementation used
`.s[data-type]:hover:not(:has(.s[data-type]:hover))::after`, which fails twice
over: an absolutely-positioned tooltip is clipped by `.srcwrap`'s scroll
container — worst on line 1, where it sits above the content box, so a one-line
method like `+` showed nothing at all — and the `:has()` trick for picking the
innermost span makes browsers without `:has()` drop the entire rule. A single
`position: fixed` element driven by `mouseover` has neither problem, and
`e.target.closest(".s[data-type]")` picks the innermost span for free.

**No colour leak between nested spans.** Type spans nest, and CSS colour
inherits, so a type-stable call sitting inside an unstable expression would
render amber purely by inheritance — `checksquare(A)::Int` looking unstable
because its enclosing expression was a `Union`. The base `.s` class therefore
resets colour and weight explicitly, and only the spans that earned a warning
override it. A false instability signal is the one thing this view must not
produce.

**Default-argument and keyword shims link their body method.** Such a method's
body is a single forwarding call, so there is no source to annotate and nothing
to click; the note carries a button to the body method, which is already a child
in the tree. Two wrinkles: a keyword shim also *computes its defaults*, so
`sqrt_quasitriu(A0; blockwidth = eltype(A0) <: Complex ? 512 : 256)` has
`eltype(A0)` among its children — `is_body_method` picks the real body (`f` with
more arguments, or the gensym `#f#NN`) and ignores the rest, falling back to
listing every descendable child if the heuristic misses. And the gensym name plus
its `::typeof(f)` plumbing argument are cleaned up for display, so the button
reads `sqrt_quasitriu(::Int64, ::UpperTriangular{…})` rather than
`LinearAlgebra.var"#sqrt_quasitriu#80"(::Int64, ::typeof(…), …)`.

Two more things worth knowing if you extend it:

- **Do not route this through `cthulhu_typed`.** `CthulhuConfig` hard-ANDs the
  annotation flags with VSCode availability (`src/config.jl:22-23`), so
  `set_config(cfg; inlay_types_vscode=true)` silently yields `false` and
  `cthulhu_typed` then passes `nothing` as the sink
  (`src/compiler/codeview.jl:120-122`), overriding your `IOContext`.
- **Suppress `Core.Const` in callee POSITION only.** Every call's callee infers as
  `Core.Const(sin)`; annotating it puts `::Core.Const(+)` on every operator. But
  the filter must key on *position*, not on what the value happens to be.
  `typeof(sqrt(real(zero(T))))` infers to `Core.Const(Float64)`, and so does the
  variable `Tr` that stores it; suppressing those left them with no span at all,
  so they inherited the enclosing expression's type — rendering amber, and
  reporting the function's return type on hover. The callee is the first child of
  a prefix call but the **second** child of an infix one (`a + b` parses as
  `call(a, +, b)`), and the flag propagates through dotted access so
  `Base.Math.sin` stays quiet to the leaf.

  This is the same class of bug as the colour leak above: an expression with no
  span of its own is at the mercy of its ancestors, visually *and* on hover.

### Syntax highlighting

Lexical highlighting is done server-side with **JuliaSyntax's own tokenizer**
(already a Cthulhu dependency), so it is a real Julia lexer rather than a regex
approximation in JS. `token_classmap` builds a flat byte → class array for the
method's range; `emit_code` then emits runs of same-class bytes. A flat array
keeps the emitter trivially correct, because `walk_source` emits strictly left
to right and class runs break only at token boundaries — which are always
character boundaries.

**Identifiers are deliberately left uncoloured.** They are what the *type* spans
colour (red = unstable, amber = small union), and a token span nests *inside* a
type span, so colouring identifiers would silently override the type signal —
the whole point of the view. Two consequences worth knowing: JuliaSyntax
tokenizes `>` as an `Identifier`, so operator-like names stay plain too (which is
consistent); and inside a flagged expression the punctuation and operators are
forced back to `inherit`, so "this whole call is unstable" still reads as one
unit rather than being broken up by grey parens.

The syntax palette is defined as its own set of CSS variables, disjoint from the
type palette, so lexical colour can never be mistaken for a type signal. A
**syntax** checkbox turns it off client-side.

### Startup is non-blocking

`descend_web` starts the HTTP server **before** analysing the entry point, and
builds the session on a background task. Constructing it runs full type
inference, which for something like `sqrt(::Matrix{Float64})` takes seconds;
doing that first meant the REPL appeared to hang, Ctrl-C could not help (the work
is on a worker task, not the main one), and the browser got connection-refused
for the whole duration.

Now the page is up immediately and the client is told `initializing` until the
root is ready. Measured on `sqrt(::Matrix{Float64})`: `descend_web` returns in
~1 s, `initializing` reaches the browser at +0.07 s, `init` at +5.7 s.

One consequence worth knowing: inference runs on a single worker, so issuing a
second `@descend_web` while a slow one is still analysing queues behind it rather
than running in parallel.

### Progress feedback

Inference runs server-side with no incremental progress to report, so the UI
shows *where* it is busy rather than a fake percentage: a spinner on the clicked
row, a spinner in the code pane, and the tree dimming after a beat.

Two details that matter:

- **Busy state is set when the request is sent, not when the server acks.** The
  client does not need permission to show a spinner, and tying it to the ack
  makes the indicator hostage to round-trip latency.
- **Dimming is delayed ~300 ms.** Cached clicks return in well under a
  millisecond and would otherwise just flicker.

The code pane escalates its explanation while waiting — "Running type
inference…", then a note that the first descent also compiles Cthulhu's own
inference code — because a cold first click takes seconds and silence reads as a
hang. Measured on a small function: first expand ~0.6 s, subsequent cached
requests ~0.3 ms.

### Ascending

Descending is only half of navigation, so the code pane carries a **breadcrumb
trail** of the path from the root, an **↑ caller** button, and **Backspace**
(matching the terminal UI's backspace / `↩`). Ascending highlights the call you
just came back from and scrolls it into view, so "where was I called from?" is
answered without re-reading the source.

All of this is client-side — every node record already carries `parent`, so
retracing the path needs no server round-trip.

Note this is **not** `Cthulhu.ascend`. This retraces the path you descended in
this session; `ascend` follows *backedges* to find callers anywhere in the
system, which is a different (and still unimplemented) feature — see below.

The invariant the highlight depends on is tested: every `data-node-id` in a
node's rendered source must be a genuine child of that node.

### Not done

- **`ascend` (backedges) has no UI.** `src/backedges.jl` + `find_caller_of` can
  answer "who calls this?" for any `MethodInstance`, not just the path you came
  down. That is a genuinely different navigation mode (a tree of *callers*) and
  would want its own pane.
- The `:source` view no longer falls back to ANSI for ordinary methods, but it
  still does for macro-generated code, missing source files, and IRCode-only
  results. That fallback is silent by design.
- No Revise handling: after `Revise.revise()` every cached `CodeInstance` is
  stale and the session should be rebuilt from scratch.
