# Rendering: structured records for the callsite tree, ANSI -> HTML for code bodies.

# ---------------------------------------------------------------------------
# ANSI -> HTML.
#
# Measured escape inventory for the :typed view: SGR 0 1 22 31 32 33 36 39 90,
# PLUS cursor-column codes ESC[1G and ESC[176G. The latter come from IRShow's
# gutter alignment and are exactly what descend.jl:88-94 strips the tail of. A
# naive SGR-only converter renders "176G" as literal text.
# ---------------------------------------------------------------------------

const SGR_CLASS = Dict(
    30 => "c-black",   31 => "c-red",     32 => "c-green",  33 => "c-yellow",
    34 => "c-blue",    35 => "c-magenta", 36 => "c-cyan",   37 => "c-white",
    90 => "c-gray",    91 => "c-red",     92 => "c-green",  93 => "c-yellow",
    94 => "c-blue",    95 => "c-magenta", 96 => "c-cyan",   97 => "c-white",
)

html_escape(s::AbstractString) = replace(s,
    '&' => "&amp;", '<' => "&lt;", '>' => "&gt;", '"' => "&quot;")

# The literal ESC byte. Written this way so the source file stays 7-bit clean.
const ESC = Char(0x1B)

"""
    strip_trailing_indent(str)

Reproduces the cleanup at descend.jl:88-94: IRShow leaves a trailing
`ESC[90m ESC[nG <spaces> ESC[1G ESC[39m ...` artifact that would render as
visible garbage in HTML.
"""
function strip_trailing_indent(str::AbstractString)
    re = Regex("$(ESC)\\[90m$(ESC)\\[(\\d+)G( *)$(ESC)\\[1G$(ESC)\\[39m$(ESC)\\[90m( *)$(ESC)\\[39m\$")
    m = findfirst(re, str)
    m === nothing && return str
    return str[begin:prevind(str, first(m))]
end

"""
    ansi_to_html(str) -> String

Converts SGR colour runs to `<span class=...>` and cursor-column (CHA) codes to
padding. Operates line by line so column tracking stays correct.
"""
function ansi_to_html(str::AbstractString)
    out = IOBuffer()
    for (i, line) in enumerate(split(strip_trailing_indent(str), '\n'))
        i > 1 && print(out, '\n')
        print(out, ansi_line_to_html(line))
    end
    return String(take!(out))
end

function ansi_line_to_html(line::AbstractString)
    out   = IOBuffer()
    col   = 0          # visible columns emitted so far on this line
    bold  = false
    color = nothing
    span_open = false      # a <span> is currently open
    span_bold = false      # ...with these styles
    span_color = nothing

    # Open/close lazily and only when text is actually about to be written, so a
    # run of style changes with nothing between them emits no empty spans.
    function sync_style()
        (span_open && span_bold == bold && span_color === color) && return
        span_open && (print(out, "</span>"); span_open = false)
        (color === nothing && !bold) && return
        classes = String[]
        color === nothing || push!(classes, color)
        bold && push!(classes, "c-bold")
        print(out, "<span class=\"", join(classes, ' '), "\">")
        span_open = true
        span_bold = bold
        span_color = color
    end

    function emit(str::AbstractString)
        isempty(str) && return
        sync_style()
        print(out, str)
    end

    i = firstindex(line)
    lastidx = lastindex(line)
    while i <= lastidx
        ch = line[i]
        if ch == ESC && i < lastidx && line[nextind(line, i)] == '['
            j = nextind(line, nextind(line, i))
            k = j
            while k <= lastidx && (isdigit(line[k]) || line[k] == ';')
                k = nextind(line, k)
            end
            k > lastidx && break
            final = line[k]
            params = j <= prevind(line, k) ? line[j:prevind(line, k)] : ""
            if final == 'm'
                for p in split(isempty(params) ? "0" : params, ';')
                    n = tryparse(Int, p)
                    n === nothing && continue
                    if n == 0
                        bold = false
                        color = nothing
                    elseif n == 1
                        bold = true
                    elseif n == 22
                        bold = false
                    elseif n == 39
                        color = nothing
                    elseif haskey(SGR_CLASS, n)
                        color = SGR_CLASS[n]
                    end
                end
            elseif final == 'G'
                # CHA: move to absolute column (1-based). Pad forward; never back.
                target = something(tryparse(Int, params), 1) - 1
                if target > col
                    # padding is unstyled -- close any open span first
                    span_open && (print(out, "</span>"); span_open = false)
                    print(out, " "^(target - col))
                    col = target
                end
            end
            # any other final byte: drop the sequence entirely
            i = nextind(line, k)
        else
            emit(html_escape(string(ch)))
            col += textwidth(ch)
            i = nextind(line, i)
        end
    end
    span_open && print(out, "</span>")
    return String(take!(out))
end

# ---------------------------------------------------------------------------
# Code bodies
# ---------------------------------------------------------------------------

"Config fields that actually change a rendered body."
bodykey(c::CthulhuConfig) = hash((c.view, c.optimize, c.debuginfo, c.iswarn,
    c.hide_type_stable, c.remarks, c.effects, c.exception_types, c.inlining_costs,
    c.type_annotations, c.pretty_ast, c.asm_syntax, c.enable_highlighter))

"""
    render_body(session, node, config) -> String (HTML)

Builds a fresh `CthulhuState` per render: it is mutable, so sharing one across
concurrent renders would race.
"""
function render_body(s::Session, node::Node, cfg::CthulhuConfig)
    if node.ci === nothing
        return "<p class=\"note\">This node has no code body (it is a " *
               string(node.label.kind) * " callsite).</p>"
    end

    key = (node.id, bodykey(cfg))
    haskey(s.bodies, key) && return s.bodies[key]

    # :llvm/:native pass state.mi together with result.src. For override nodes that
    # src came from ir_to_src with synthetic slotnames _1,_2,... (lookup.jl:150-153),
    # so the (mi, src) pair is mismatched and _dump_function_llvm can abort codegen,
    # taking down the process -- not just the request.
    if node.override !== nothing && cfg.view in (:llvm, :native)
        return "<p class=\"note\">The " * string(cfg.view) * " view is disabled " *
               "for const-prop / semi-concrete nodes (a mismatched mi/src pair " *
               "risks a codegen abort).</p>"
    end

    # Preferred path for :source -- real spans with types and click targets.
    # Falls through to the ANSI pipeline when there is no typed source (macro-
    # generated code, missing source file, IRCode-only results, ...).
    if cfg.view === :source
        html = try
            source_html(s, node, cfg)
        catch err
            @warn "source view failed, falling back to ANSI" exception=err
            nothing
        end
        if html !== nothing
            s.bodies[key] = html
            return html
        end
    end

    result = lookup_cached!(s, node, cfg.optimize)
    result === nothing && return "<p class=\"err\">lookup failed for " *
                                 html_escape(string(node.mi)) * "</p>"

    state = CthulhuState(s.provider; terminal=NULL_TERMINAL[], config=cfg,
                         ci=node.ci, mi=node.mi, override=node.override)

    ansi = try
        # NB: stringify(f, ::IOContext) does NOT add :color=>true (ui.jl:98 only
        # does so for the ::IO method). Without it you silently get plain text.
        stringify(IOContext(IOBuffer(),
                :color            => true,
                :limit            => true,
                :displaysize      => (40, 200),
                :SOURCE_SLOTNAMES => source_slotnames(result),
                :effects          => cfg.effects,
                :exception_types  => cfg.exception_types)) do io
            view_function(state)(io, s.provider, state, result)
        end
    catch err
        return "<p class=\"err\">" * html_escape(sprint(showerror, err)) * "</p>"
    end

    html = "<pre class=\"code\">" * ansi_to_html(ansi) * "</pre>"
    s.bodies[key] = html
    return html
end

# ---------------------------------------------------------------------------
# JSON-ready records
# ---------------------------------------------------------------------------

function node_record(s::Session, id::NodeId)
    n = s.nodes[id]
    l = n.label
    return Dict{String,Any}(
        "id"            => n.id,
        "parent"        => n.parent,
        "depth"         => n.depth,
        "kind"          => string(l.kind),
        "wrappers"      => String[string(w) for w in l.wrappers],
        "name"          => l.name,
        "argtypes"      => l.argtypes,
        "kwargs"        => l.kwargs,
        "rt"            => l.rt,
        "exct"          => l.exct,
        "effects"       => l.effects,
        "unstable"      => l.unstable,
        "expectedUnion" => l.expected_union,
        "stmtId"        => l.stmt_id,
        "head"          => string(l.head),
        "nalternatives" => l.nalternatives,
        "file"          => l.file,
        "line"          => l.line,
        "descendable"   => n.descendable,
        "expandable"    => n.expandable && n.recursive_ancestor == 0,
        "recursive"     => n.recursive_ancestor != 0,
        "recursiveOf"   => n.recursive_ancestor,
    )
end

config_record(c::CthulhuConfig) = Dict{String,Any}(
    "view" => string(c.view), "optimize" => c.optimize, "iswarn" => c.iswarn,
    "debuginfo" => string(c.debuginfo), "hide_type_stable" => c.hide_type_stable,
    "effects" => c.effects, "exception_types" => c.exception_types,
    "remarks" => c.remarks, "inlining_costs" => c.inlining_costs,
    "type_annotations" => c.type_annotations,
)
