# ---------------------------------------------------------------------------
# Session export
#
# What the page shows, without the page: the tree as explored, and the open
# node's source together with every claim the pane makes about it. Two
# renderings over one document -- JSON to load back into Julia, text to paste
# into a conversation -- so the two can never disagree about what was on screen.
# ---------------------------------------------------------------------------

"Bump when a field changes meaning, so a reader can tell. New fields do not."
const EXPORT_VERSION = 1

"""
How many nodes an export carries before it starts leaving some out.

A session that has been clicked through for a while holds thousands; an
afternoon on `svd` reached 15692 in testing. The open node's path and children
are taken first and are never the ones dropped, so the cap costs breadth far
from where the reader is looking, and `truncated` says how much.
"""
const EXPORT_NODE_CAP = 3000

"The ids from the root down to `id`, root first."
function node_path(s::Session, id::NodeId)
    path = NodeId[]
    while id != 0
        pushfirst!(path, id)
        id = s.nodes[id].parent
    end
    return path
end

"""
Which nodes to carry, most relevant first.

Breadth-first from the root over the expansions that were actually performed --
`node.children` is the memo, so this is exactly what the session explored, not
what it could have. The open node's path and its children go in ahead of that
sweep: a cap should cost the far edges of the tree, never the part being read.
"""
function export_nodes(s::Session, id::NodeId, cap::Int)
    seen = Set{NodeId}()
    out = NodeId[]
    keep!(k) = (k in seen || (push!(seen, k); push!(out, k)))
    for k in node_path(s, id)
        keep!(k)
    end
    for kids in values(s.nodes[id].children), k in kids
        keep!(k)
    end
    queue = NodeId[ROOT_ID]
    while !isempty(queue) && length(out) < cap
        n = s.nodes[popfirst!(queue)]
        for kids in values(n.children), k in kids
            length(out) < cap && keep!(k)
            push!(queue, k)
        end
    end
    return out, length(s.nodes) - length(out)
end

"""
    session_document(s, id; expanded = nothing, cap = EXPORT_NODE_CAP) -> Dict

A JSON-shaped record of the session as explored, plus the open node's source
with the claims the pane makes about it -- span by span, with the type reported
for each, the callsite it descends into, and whether it was greyed as compiled
out. That last part is the point: a screenshot shows what a span looks like, and
this shows what the span says.

`expanded` is the browser's own open/closed state, which the server does not
otherwise know; pass `nothing` from the REPL and the field is simply absent.
"""
function session_document(s::Session, id::NodeId;
                          expanded::Union{Nothing,Vector{NodeId}} = nothing,
                          cap::Int = EXPORT_NODE_CAP)
    id = (1 <= id <= length(s.nodes)) ? id : ROOT_ID
    ids, dropped = export_nodes(s, id, cap)
    doc = Dict{String,Any}(
        "cthulhuweb"     => EXPORT_VERSION,
        "julia"          => string(VERSION),
        "entry"          => s.nodes[ROOT_ID].label.name,
        "config"         => config_record(s.config),
        "open"           => id,
        "path"           => node_path(s, id),
        "nodes"          => [node_record(s, k) for k in ids],
        "explored"       => length(s.nodes),
        "truncated"      => dropped,
        "source"         => source_document(s, id),
    )
    expanded === nothing || (doc["expanded"] = expanded)
    return doc
end

"""
The open node's body, as facts rather than as markup.

For the source view that is the span list `source_html` records -- the same
pass, so the export cannot drift from the page. For the other views there are no
spans to speak of, and the text of the body is what there is to carry.
"""
function source_document(s::Session, id::NodeId)
    node = s.nodes[id]
    node.descendable || return Dict{String,Any}("available" => false,
                                                "why" => "node is not descendable")
    if s.config.view === :source
        report = Dict{String,Any}()
        html = try
            source_html(s, node, s.config; report = report)
        catch err
            return Dict{String,Any}("available" => false,
                                    "why" => first(sprint(showerror, err), 200))
        end
        html === nothing && return Dict{String,Any}("available" => false,
                                                    "why" => "no typed source for this method")
        report["available"] = true
        report["view"] = "source"
        haskey(report, "spans") && (report["spans"] = [span_record(sp) for sp in report["spans"]])
        return report
    end
    body = try
        render_body(s, node, s.config)
    catch err
        return Dict{String,Any}("available" => false,
                                "why" => first(sprint(showerror, err), 200))
    end
    return Dict{String,Any}(
        "available" => true,
        "view"      => string(s.config.view),
        "file"      => node.label.file,
        "firstline" => node.label.line,
        "text"      => html_to_text(body),
    )
end

span_record(sp) = Dict{String,Any}(
    "first" => sp.first, "last" => sp.last, "text" => sp.text,
    "type" => sp.type, "sparam" => sp.sparam,
    "node" => sp.node == 0 ? nothing : sp.node,
    "classes" => sp.classes,
)

"Plain text of rendered markup -- for the views whose body is already a `<pre>`."
html_to_text(html::AbstractString) =
    replace(replace(html, r"<[^>]*>" => ""),
            "&lt;" => "<", "&gt;" => ">", "&quot;" => "\"", "&#39;" => "'",
            "&amp;" => "&")

# ---------------------------------------------------------------------------
# The readable rendering
#
# Built from the DOCUMENT, not from the session, so a file loaded back months
# later prints exactly what it printed the day it was written.
# ---------------------------------------------------------------------------

_get(d, k, default = nothing) = (d !== nothing && haskey(d, k) && d[k] !== nothing) ? d[k] : default

"`name(::A, ::B) ::rt`, plus whatever else distinguishes this callsite."
function node_line(n)
    kind = String(_get(n, "kind", "edge"))
    # The root's name is already the whole `MethodInstance for f(::T)`, so
    # putting an argument list after it produces `f()()`.
    kind == "root" && return string(_get(n, "name", "?"), " ::", _get(n, "rt", "?"))
    args = join(["::" * String(a) for a in _get(n, "argtypes", String[])], ", ")
    kw = _get(n, "kwargs", String[])
    isempty(kw) && (kw = String[])
    kwtxt = isempty(kw) ? "" : "; " * join([String(k) for k in kw], ", ")
    out = string(_get(n, "name", "?"), "(", args, kwtxt, ") ::", _get(n, "rt", "?"))
    kind == "edge" || (out *= "  [" * kind * "]")
    _get(n, "unstable", false) && (out *= _get(n, "expectedUnion", false) ?
                                          "  [small union]" : "  [unstable]")
    _get(n, "recursive", false) && (out *= "  [recursive]")
    return out
end

"The explored tree, indented, with the open node marked."
function tree_text(doc)
    byid = Dict{Int,Any}()
    for n in _get(doc, "nodes", [])
        byid[Int(n["id"])] = n
    end
    kids = Dict{Int,Vector{Int}}()
    for (i, n) in byid
        p = Int(_get(n, "parent", 0))
        p == 0 && continue
        haskey(byid, p) && push!(get!(kids, p, Int[]), i)
    end
    for v in values(kids); sort!(v); end
    open = Int(_get(doc, "open", 1))
    lines = String[]
    function emit(id, prefix, isbranch, islast)
        mark = id == open ? "   <-- open" : ""
        head = isbranch ? (islast ? "└─ " : "├─ ") : ""
        push!(lines, prefix * head * node_line(byid[id]) * mark)
        ks = get(kids, id, Int[])
        childprefix = prefix * (isbranch ? (islast ? "   " : "│  ") : "")
        for (i, k) in enumerate(ks)
            emit(k, childprefix, true, i == length(ks))
        end
    end
    haskey(byid, 1) ? emit(1, "", false, true) :
        for id in sort(collect(keys(byid))); push!(lines, node_line(byid[id])); end
    return lines
end

"Which line of the body a byte offset falls on."
function line_of(text::AbstractString, offset::Int, byte::Int, firstline::Int)
    i = byte - offset + 1
    (i < 1 || i > ncodeunits(text)) && return firstline
    return firstline + count(==(UInt8('\n')), codeunits(text)[1:i-1])
end

_oneline(t, n = 46) = (t = replace(strip(String(t)), r"\s+" => " ");
                       length(t) > n ? first(t, n - 1) * "…" : t)

"""
The body, line by line, with what the pane claims about each line under it.

Every span that makes a claim -- a type, a callsite to descend into, or a grey
"compiled out" -- and nothing that does not, since a barrier span is the pane
saying nothing and there are a great many of them. This is the half a screenshot
cannot carry: what the colours and the hovers actually said.
"""
function source_text(doc)
    src = _get(doc, "source")
    src === nothing && return ["(no source captured)"]
    _get(src, "available", false) || return ["(no source: " * String(_get(src, "why", "unknown")) * ")"]
    lines = String[]
    file = _get(src, "file")
    file === nothing || push!(lines, String(file) * ":" * string(_get(src, "firstline", 0)))
    note = String(_get(src, "note", ""))
    isempty(note) || (push!(lines, ""); push!(lines, "note: " * note))
    sp = _get(src, "sparams", Dict{String,Any}())
    isempty(sp) || push!(lines, "where " * join([string(k, " = ", v) for (k, v) in sp], ", "))
    if _get(src, "view", "source") != "source"
        push!(lines, ""); append!(lines, split(String(_get(src, "text", "")), '\n'))
        return lines
    end

    labels = Dict{Int,String}()
    for n in _get(doc, "nodes", [])
        labels[Int(n["id"])] = node_line(n)
    end
    text = String(_get(src, "text", ""))
    offset = Int(_get(src, "offset", 1))
    firstline = Int(_get(src, "firstline", 1))
    claims = Dict{Int,Vector{String}}()
    for s in _get(src, "spans", [])
        cls = [String(c) for c in _get(s, "classes", String[])]
        typ = _get(s, "type")
        nid = _get(s, "node")
        dead = "s-dead" in cls
        (typ !== nothing || nid !== nothing || dead) || continue
        what = dead ? "<<compiled out>>" :
               typ === nothing ? "(no type claimed)" :
               _get(s, "sparam", false) ? String(typ) * "   (static parameter)" :
               "::" * String(typ)
        nid === nothing || (what *= "   -> node " * string(nid) *
                                    " " * get(labels, Int(nid), ""))
        ln = line_of(text, offset, Int(_get(s, "first", offset)), firstline)
        push!(get!(claims, ln, String[]), rpad(_oneline(_get(s, "text", "")), 48) * what)
    end

    push!(lines, "")
    w = length(string(firstline + count(==('\n'), text)))
    for (i, l) in enumerate(split(text, '\n'))
        n = firstline + i - 1
        push!(lines, lpad(string(n), w) * " | " * l)
        for c in get(claims, n, String[])
            push!(lines, " "^w * " |     " * c)
        end
    end
    ul = _get(src, "unlocated", [])
    if !isempty(ul)
        push!(lines, "")
        push!(lines, "called here, but Cthulhu could not locate it in the source:")
        for e in ul
            push!(lines, "  node " * string(_get(e, "node", 0)) * "  " * String(_get(e, "label", "")))
        end
    end
    return lines
end

"""
    session_text(doc) -> String

The whole document as something to read, or to paste into a conversation.
"""
function session_text(doc)
    cfg = _get(doc, "config", Dict{String,Any}())
    open = Int(_get(doc, "open", 1))
    byid = Dict(Int(n["id"]) => n for n in _get(doc, "nodes", []))
    out = String[
        "# Cthulhu web session",
        "entry    " * String(_get(doc, "entry", "?")),
        "julia    " * String(_get(doc, "julia", "?")),
        "config   " * join([string(k, "=", v) for (k, v) in sort!(collect(pairs(cfg)), by = x -> String(first(x)))], " "),
        "open     node " * string(open) * "  " *
            (haskey(byid, open) ? node_line(byid[open]) : "?"),
    ]
    dropped = Int(_get(doc, "truncated", 0))
    push!(out, "explored " * string(_get(doc, "explored", 0)) * " nodes" *
               (dropped > 0 ? "  ($(dropped) not carried: export node cap)" : ""))
    push!(out, "")
    push!(out, "## Call tree")
    append!(out, tree_text(doc))
    push!(out, "")
    push!(out, "## Source of the open node")
    append!(out, source_text(doc))
    return join(out, "\n") * "\n"
end

# ---------------------------------------------------------------------------
# Loading one back
# ---------------------------------------------------------------------------

"""
    load_session(path) -> WebSession

Read an exported session. `ws.doc` is the raw document (a `JSON3.Object`, so
`ws.doc["nodes"]`, `ws.doc["source"]["spans"]` and so on); showing it prints the
readable rendering, which is what to paste into a conversation.
"""
struct WebSession
    doc::Any
end

load_session(path::AbstractString) = WebSession(JSON3.read(read(path, String)))

Base.show(io::IO, ::MIME"text/plain", ws::WebSession) = print(io, session_text(ws.doc))
Base.show(io::IO, ws::WebSession) =
    print(io, "WebSession(", _get(ws.doc, "entry", "?"), ", ",
          length(_get(ws.doc, "nodes", [])), " nodes)")
Base.getindex(ws::WebSession, k::AbstractString) = ws.doc[k]
session_text(ws::WebSession) = session_text(ws.doc)
