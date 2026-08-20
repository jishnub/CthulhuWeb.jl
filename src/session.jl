# Headless replacement for Cthulhu's `descend!` loop.
#
# `descend!` (src/descend.jl:45) descends by calling itself, using the Julia call
# stack as the ascend stack. An event-driven server cannot park inside a nested
# recursive call, so we keep an explicit node table keyed by tree position.

const NodeId = Int
const ROOT_ID = 1

# ---------------------------------------------------------------------------
# Compiler-integration module resolution.
#
# src/compiler/*.jl is included into `Cthulhu` and, when the Compiler stdlib
# diverges from Base.Compiler, AGAIN into CthulhuCompilerExt. `get_ci`/`get_rt`/
# `get_override`/`lookup`/`find_callsites` are shared generics (imported at
# src/CthulhuCompiler.jl:3), but `get_effects` and `get_exct` are NOT -- the
# former is defined fresh at src/CthulhuCompiler.jl:28. So the CallInfo types and
# those two accessors must be taken from whichever module actually produced the
# data. Deriving it from the data needs no `use_compiler_stdlib` guesswork.
# ---------------------------------------------------------------------------
struct Integration
    M::Module
    MultiCallInfo::Type
    RTCallInfo::Type
    PureCallInfo::Type
    TaskCallInfo::Type
    FailedCallInfo::Type
    GeneratedCallInfo::Type
    ConstPropCallInfo::Type
    SemiConcreteCallInfo::Type
    ConcreteCallInfo::Type
    ReturnTypeCallInfo::Type
    InvokeCallInfo::Type
    OCCallInfo::Type
    WrappedCallInfo::Type
    get_effects::Function
    get_exct::Function
    ignorewrappers::Function
end

const _INTEG_NAMES = (:MultiCallInfo, :RTCallInfo, :PureCallInfo, :TaskCallInfo,
    :FailedCallInfo, :GeneratedCallInfo, :ConstPropCallInfo, :SemiConcreteCallInfo,
    :ConcreteCallInfo, :ReturnTypeCallInfo, :InvokeCallInfo, :OCCallInfo,
    :WrappedCallInfo, :get_effects, :get_exct, :ignorewrappers)

Integration(M::Module) = Integration(M, (getglobal(M, n) for n in _INTEG_NAMES)...)
integration_for(result) = Integration(parentmodule(typeof(result)))

# ---------------------------------------------------------------------------
# Guarded accessors. Several of these throw or warn in normal operation.
# ---------------------------------------------------------------------------

"`get_ci` throws for MultiCallInfo (callsite.jl:97) and warns-then-nothings for
Failed/Generated (callsite.jl:66-79). Never let either reach the server loop."
function try_get_ci(@nospecialize(info))
    try
        ci = with_logger(NullLogger()) do
            get_ci(info)
        end
        return ci isa Core.CodeInstance ? ci : nothing
    catch
        return nothing
    end
end

safe_string(f, @nospecialize(x)) = try string(f(x)) catch; nothing end

"get_effects(::MultiCallInfo) is a mapreduce with no `init` (callsite.jl:100) and
throws on empty callinfos, which descend.jl:172-176 shows does happen."
safe_effects(integ::Integration, @nospecialize(info)) = safe_string(integ.get_effects, info)

"get_exct(::ConcreteCallInfo) is a live bug -- callsite.jl:154 binds `cici` but
references `ceci`, so it throws UndefVarError. The TUI never calls it."
safe_exct(integ::Integration, @nospecialize(info)) = safe_string(integ.get_exct, info)

# ---------------------------------------------------------------------------
# Node + Session
# ---------------------------------------------------------------------------

"Uniquely names a child slot by tree position. All Int/Bool: stable across
recompilation, unlike (mi, ci, override). `optimize` is in the key because the
child *set* depends on it."
struct SlotKey
    parent::NodeId
    optimize::Bool
    stmt_id::Int
    slot::Int
end

"Config-independent presentational record. Because it carries the raw pieces
rather than a rendered line, the client can implement the iswarn / effects /
exception_types / head toggles in CSS with zero server round-trips."
struct CallLabel
    kind::Symbol
    wrappers::Vector{Symbol}
    name::String
    argtypes::Vector{String}
    kwargs::Vector{String}
    rt::String
    exct::Union{Nothing,String}
    effects::Union{Nothing,String}
    unstable::Bool
    expected_union::Bool
    stmt_id::Int
    head::Symbol
    nalternatives::Int
    file::Union{Nothing,String}
    line::Int
end

mutable struct Node
    const id::NodeId
    const parent::NodeId
    const depth::Int
    const mi::Union{Nothing,Core.MethodInstance}
    const ci::Union{Nothing,Core.CodeInstance}
    const override::Any
    const info::Any
    const label::CallLabel
    const descendable::Bool          # can render a code body
    const expandable::Bool           # can produce children
    const recursive_ancestor::NodeId # 0 if none
    children::Dict{Bool,Vector{NodeId}}
    errors::Dict{Bool,String}
end

mutable struct Session
    const provider::AbstractProvider
    const integ::Integration
    config::CthulhuConfig
    const nodes::Vector{Node}
    const byslot::Dict{SlotKey,NodeId}
    const results::IdDict{Any,Dict{Bool,Any}}   # something(override,ci) => optimize => LookupResult
    const bodies::Dict{Tuple{NodeId,UInt},String}
    const max_depth::Int
end

# Nothing ever writes to this; it exists only to satisfy CthulhuState's field
# type. `raw!` would ccall on in_stream.handle, but it is reached only from
# TerminalMenus.request, which we never call. Filled in `__init__`.
const NULL_TERMINAL = Ref{REPL.Terminals.TTYTerminal}()

"Force off the settings that would let a browser toggle run an editor or a
subprocess on the host. jump_always calls edit() (descend.jl:66-76); the vscode
flags are normally false but are TRUE when launched from a VSCode Julia REPL."
function headless_config(base::CthulhuConfig = CONFIG; kwargs...)
    cfg = set_config(base; kwargs...)
    return set_config(cfg;
        jump_always        = false,
        inlay_types_vscode = false,
        diagnostics_vscode = false,
        # llvm/asm use in-process print_llvm/print_native (codeview.jl:8-10);
        # only the julia lexer forks pygmentize.
        enable_highlighter = cfg.view === :llvm || cfg.view === :native)
end

function Session(provider::AbstractProvider, mi::Core.MethodInstance;
                 config::CthulhuConfig = headless_config(), max_depth::Int = 64)
    ci = generate_code_instance(provider, mi)
    result = lookup(provider, ci, config.optimize)
    result === nothing && error("Initial lookup failed for $mi")
    integ = integration_for(result)

    label = CallLabel(:root, Symbol[], sprint(show, mi), String[], String[], string(result.rt),
                      nothing, nothing, false, false, -1, :call, 0,
                      whereis_file(mi)..., )
    root = Node(ROOT_ID, 0, 0, mi, ci, nothing, nothing, label, true, true, 0,
                Dict{Bool,Vector{NodeId}}(), Dict{Bool,String}())
    s = Session(provider, integ, config, Node[root], Dict{SlotKey,NodeId}(),
                IdDict{Any,Dict{Bool,Any}}(), Dict{Tuple{NodeId,UInt},String}(), max_depth)
    s.results[ci] = Dict{Bool,Any}(config.optimize => result)
    return s
end

function whereis_file(mi::Core.MethodInstance)
    def = mi.def
    isa(def, Method) || return (nothing, 0)
    try
        file, line = CodeTracking.whereis(def)
        return (file === nothing ? nothing : string(file), Int(line))
    catch
        return (string(def.file), Int(def.line))
    end
end
whereis_file(::Nothing) = (nothing, 0)

# ---------------------------------------------------------------------------
# Lookup cache. Keyed on `something(override, ci)` in an IdDict -- the same
# choice upstream makes (InferenceDict = IdDict, lookup.jl:73-74).
# ---------------------------------------------------------------------------
function lookup_cached!(s::Session, node::Node, optimize::Bool)
    key = something(node.override, node.ci)
    per = get!(() -> Dict{Bool,Any}(), s.results, key)
    return get!(per, optimize) do
        lookup(s.provider, key, optimize)   # may return nothing (descend.jl:63)
    end
end

# ---------------------------------------------------------------------------
# Classification. Mirrors descend.jl:118-149 but never lets get_ci throw.
# ---------------------------------------------------------------------------
function classify(s::Session, @nospecialize(info))
    integ = s.integ
    inner = integ.ignorewrappers(info)
    wrappers = Symbol[]
    info !== inner && push!(wrappers, :limited)

    if inner isa integ.MultiCallInfo
        n = length(inner.callinfos)
        return (kind=:multi, wrappers, mi=nothing, ci=nothing, override=nothing,
                descendable=false, expandable=(n > 0), nalt=n)
    end

    # RTCallInfo: get_ci === nothing by definition; the TUI refuses descent
    # (descend.jl:129-133). PureCallInfo likewise has no ci.
    if inner isa integ.RTCallInfo || inner isa integ.PureCallInfo
        return (kind=(inner isa integ.RTCallInfo ? :runtime : :pure), wrappers,
                mi=nothing, ci=nothing, override=nothing,
                descendable=false, expandable=false, nalt=0)
    end

    if inner isa integ.TaskCallInfo
        push!(wrappers, :task)
        wrapped = integ.ignorewrappers(inner.ci)
        if wrapped isa integ.MultiCallInfo
            # `callinfo()` (reflection.jl:289) really can return a MultiCallInfo
            # here; descend.jl:126's `::CodeInstance` assertion would throw.
            n = length(wrapped.callinfos)
            return (kind=:task_multi, wrappers, mi=nothing, ci=nothing, override=nothing,
                    descendable=false, expandable=(n > 0), nalt=n)
        end
        ci = try_get_ci(wrapped)
        # NB: descend.jl:126 sets state.ci but NOT state.mi -- an upstream bug that
        # makes the renderers use the parent's mi with the task's ci. Set both.
        return (kind=:task, wrappers, mi=(ci === nothing ? nothing : get_mi(ci)), ci,
                override=nothing, descendable=(ci !== nothing),
                expandable=(ci !== nothing), nalt=0)
    end

    ci = try_get_ci(inner)
    # Pass the RAW info, not `inner`: get_override has no WrappedCallInfo method
    # (compiler/interface.jl:23-25), so a LimitedCallInfo(ConstPropCallInfo(...))
    # yields nothing in the TUI too. Matching that keeps the web tree identical to
    # `@descend` rather than quietly better.
    override = get_override(s.provider, info)

    ci !== nothing && is_kwcall(get_mi(ci)) && push!(wrappers, :kw)
    kind = inner isa integ.ConstPropCallInfo    ? :constprop    :
           inner isa integ.SemiConcreteCallInfo ? :semiconcrete :
           inner isa integ.ConcreteCallInfo     ? :concrete     :
           inner isa integ.ReturnTypeCallInfo   ? :returntype   :
           inner isa integ.InvokeCallInfo       ? :invoke       :
           inner isa integ.OCCallInfo           ? :oc           :
           inner isa integ.FailedCallInfo       ? :failed       :
           inner isa integ.GeneratedCallInfo    ? :generated    : :edge

    # descend.jl:138: `ci === nothing && override === nothing && continue`. The TUI
    # still DISPLAYS such a callsite (the menu is built from all of them,
    # descend.jl:102-106); it only refuses to enter. So list it, mark it inert.
    dead = ci === nothing && override === nothing
    return (; kind, wrappers, mi=(ci === nothing ? nothing : get_mi(ci)), ci, override,
            descendable=!dead, expandable=!dead, nalt=0)
end

# ---------------------------------------------------------------------------
# Labels: built from the accessors, never from show_as_line/build_options, which
# read displaysize(stdout) (ui.jl:18,65) and let __show_limited truncate away
# real information (compiler/callsite.jl:206).
# ---------------------------------------------------------------------------
function make_label(s::Session, @nospecialize(info), c, stmt_id::Int, head::Symbol)
    integ = s.integ
    rt = try get_rt(info) catch; Any end
    name, argtypes, kwargs = signature_parts(s, info, c)
    file, line = whereis_file(c.mi)
    return CallLabel(c.kind, c.wrappers, name, argtypes, kwargs, string(rt),
                     safe_exct(integ, info), safe_effects(integ, info),
                     is_type_unstable(rt), is_expected_union_safe(rt),
                     stmt_id, head, c.nalt, file, line)
end

is_expected_union_safe(@nospecialize(rt)) =
    try rt isa Union && is_expected_union(rt) catch; false end

"Recover (function name, argument types) from the callee's specTypes when we have
one, else from the CallInfo's own `sig`/`argtyps` fields."
function signature_parts(s::Session, @nospecialize(info), c)
    integ = s.integ
    inner = integ.ignorewrappers(info)

    if c.mi !== nothing
        kw = kwcall_parts(c.mi.specTypes)
        kw === nothing || return kw
        return tuple_to_parts(c.mi.specTypes)
    end
    if inner isa integ.MultiCallInfo
        return tuple_to_parts(inner.sig)
    end
    if inner isa integ.RTCallInfo
        f = inner.f
        nm = f isa Type ? string(f) : string(nameof_safe(f))
        return (nm, String[string(T) for T in inner.argtyps], String[])
    end
    if inner isa integ.PureCallInfo
        ats = inner.argtypes
        nm = isempty(ats) ? "?" : type_head_name(first(ats))
        return (nm, String[string(T) for T in ats[2:end]], String[])
    end
    for fld in (:sig,)
        if hasproperty(inner, fld)
            return tuple_to_parts(getproperty(inner, fld))
        end
    end
    return (string(nameof(typeof(inner))), String[], String[])
end

nameof_safe(@nospecialize(f)) = try nameof(f) catch; Symbol(string(f)) end

"""
Rewrite a `Core.kwcall` signature into the call the user actually wrote.

`eigen!(x; permute, scale, sortby)` dispatches through
`Core.kwcall(::NamedTuple{(:permute,:scale,:sortby)}, ::typeof(eigen!), ::Matrix)`.
Showing that verbatim buries the callee among lowering plumbing; the tree should
say `eigen!(::Matrix; permute=, scale=, sortby=)`.
"""
function kwcall_parts(@nospecialize(tt))
    try
        t = Base.unwrap_unionall(tt)
        (t isa DataType && t <: Tuple) || return nothing
        ps = collect(t.parameters)
        length(ps) >= 3 || return nothing
        first(ps) === typeof(Core.kwcall) || return nothing
        name = type_head_name(ps[3])
        args = String[string(T) for T in ps[4:end]]
        kws = String[]
        ntu = Base.unwrap_unionall(ps[2])
        if ntu isa DataType && ntu <: NamedTuple && !isempty(ntu.parameters)
            append!(kws, string.(ntu.parameters[1]))
        end
        return (name, args, kws)
    catch
        return nothing
    end
end

"Does this MethodInstance come from a `Core.kwcall` dispatch?"
function is_kwcall(mi)
    mi === nothing && return false
    try
        t = Base.unwrap_unionall(mi.specTypes)
        return t isa DataType && !isempty(t.parameters) &&
               first(t.parameters) === typeof(Core.kwcall)
    catch
        return false
    end
end

function tuple_to_parts(@nospecialize(tt))
    try
        t = Base.unwrap_unionall(tt)
        t isa DataType && t <: Tuple || return (string(tt), String[], String[])
        ps = collect(t.parameters)
        isempty(ps) && return (string(tt), String[], String[])
        # find_callsites can hand back sigs whose first parameter is a CodeInstance
        # (the invoke form), in which case the callee is the second parameter.
        first(ps) === Core.CodeInstance && length(ps) > 1 && (ps = ps[2:end])
        return (type_head_name(first(ps)), String[string(T) for T in ps[2:end]], String[])
    catch
        return (string(tt), String[], String[])
    end
end

function type_head_name(@nospecialize(T))
    try
        T isa Type && T <: Type && return string(T)
        if T isa DataType && T.name === Type.body.name
            return string(T)
        end
        s = string(T)
        # `typeof(sin)` -> `sin`
        m = match(r"^typeof\((.+)\)$", s)
        m !== nothing && return String(m.captures[1])
        return s
    catch
        return "?"
    end
end

# ---------------------------------------------------------------------------
# Cycle detection: identity is per root path, computation is shared globally.
#
# Compare on the MethodInstance, NOT the CodeInstance. Verified empirically: for
# `rec(n) = n <= 1 ? 1 : n * rec(n-1)` the recursive callsite's CodeInstance is a
# *different object* from the root's, so `ci === ci` never fires. MethodInstances
# are interned by Julia per specialization, so `mi === mi` is the reliable test.
#
# Deliberately ignores `override`: const-prop recursion allocates a fresh
# InferenceResult at every level, so including it would fail to detect the cycle
# exactly where runaway expansion is most likely.
# ---------------------------------------------------------------------------
function find_recursive_ancestor(s::Session, parent::Node, mi::Core.MethodInstance)
    n = parent
    while true
        n.mi === mi && return n.id
        n.parent == 0 && return 0
        n = s.nodes[n.parent]
    end
end

function intern_child!(s::Session, parent::Node, @nospecialize(info),
                       stmt_id::Int, head::Symbol, slot::Int, optimize::Bool)
    key = SlotKey(parent.id, optimize, stmt_id, slot)
    haskey(s.byslot, key) && return s.byslot[key]

    c = classify(s, info)
    anc = c.mi === nothing ? 0 : find_recursive_ancestor(s, parent, c.mi)
    id = length(s.nodes) + 1
    node = Node(id, parent.id, parent.depth + 1, c.mi, c.ci, c.override, info,
                make_label(s, info, c, stmt_id, head),
                c.descendable, c.expandable, anc,
                Dict{Bool,Vector{NodeId}}(), Dict{Bool,String}())
    push!(s.nodes, node)
    s.byslot[key] = id
    return id
end

"""
    expand!(session, id; optimize) -> Vector{NodeId}

The replacement for `descend!`'s recursive step. Memoised per `optimize` bit,
which is the only config field that changes the child set (`view` reaches the
data only via `optimize &= view !== :source`, config.jl:24).
"""
function expand!(s::Session, id::NodeId; optimize::Bool = s.config.optimize)
    node = s.nodes[id]
    haskey(node.children, optimize) && return node.children[optimize]

    kids = NodeId[]
    try
        if !node.expandable
            node.children[optimize] = kids
            return kids
        end
        node.depth >= s.max_depth && error("max depth $(s.max_depth) reached")

        if node.label.kind === :multi || node.label.kind === :task_multi
            # No lookup needed. Mirrors select_callsite (descend.jl:166-188): the
            # alternatives inherit the parent's stmt_id and head.
            inner = s.integ.ignorewrappers(node.info)
            infos = node.label.kind === :multi ? inner.callinfos :
                    s.integ.ignorewrappers(inner.ci).callinfos
            for (i, sub) in enumerate(infos)
                push!(kids, intern_child!(s, node, sub, node.label.stmt_id,
                                          node.label.head, i, optimize))
            end
        else
            ci = node.ci::Core.CodeInstance
            result = lookup_cached!(s, node, optimize)
            result === nothing && error("Descent into $(node.mi) failed (lookup returned nothing)")
            # find_callsites needs the node's ORIGINAL ci even when `result` came
            # from an override -- cf. descend.jl:62 vs :98. `annotate_source=false`:
            # the 4th arg only populates the parallel sourcenodes vector.
            callsites, _ = find_callsites(s.provider, result, ci, false)
            for (i, cs) in enumerate(callsites)
                push!(kids, intern_child!(s, node, cs.info, cs.id, cs.head, i, optimize))
            end
        end
    catch err
        # process_info errors (and @eval Main's) on unhandled Compiler.CallInfo
        # kinds (reflection.jl:246-253). A server must never let that escape.
        node.errors[optimize] = sprint(showerror, err)
        empty!(kids)
    end
    node.children[optimize] = kids
    return kids
end
