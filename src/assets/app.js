// Cthulhu web frontend.
//
// The server ships a *structured* record per callsite rather than a rendered
// line, so the iswarn / effects / exception-types / head toggles are pure CSS
// here -- zero round-trips. Only `optimize` (and `view` via its coupling to
// optimize) actually changes the tree, and only `view`/debuginfo change a body.

const nodes = new Map();     // id -> record
const childrenOf = new Map(); // id -> [ids]
const expanded = new Set();
let selected = null;
let ws, reqSeq = 1;
const pending = new Map();   // req -> resolve

const $ = (s) => document.querySelector(s);
const status = (t) => { $("#status").textContent = t || ""; };

// ---------------------------------------------------------------- transport

function connect() {
  ws = new WebSocket(`ws://${location.host}/`);
  ws.onmessage = (ev) => onMessage(JSON.parse(ev.data));
  ws.onclose = () => status("disconnected");
  ws.onerror = () => status("connection error");
}

function send(op, extra = {}) {
  const req = reqSeq++;
  const p = new Promise((resolve) => {
    pending.set(req, resolve);
    ws.send(JSON.stringify({ op, req, ...extra }));
  });
  // Go busy the moment we send, NOT when the server acks. The first ack can be
  // seconds late (cold compilation on both ends), which is precisely when the
  // user most needs to see that something is happening.
  refreshBusy();
  return p;
}

function onMessage(msg) {
  if (msg.op === "ack") { refreshBusy(); return; }
  if (msg.op === "initializing") {
    // Server is up but the entry point is still being inferred. Say so instead
    // of showing an empty tree.
    $("#root-sig").textContent = "analysing…";
    document.body.classList.add("busy");
    showLoading("Analysing the entry point…");
    $("#tree").innerHTML = `<li class="node"><div class="row">` +
      `<span class="caret"><span class="spinner"></span></span>` +
      `<span class="label note">waiting for type inference…</span></div></li>`;
    return;
  }
  if (msg.op === "init") {
    clearLoading();
    document.body.classList.remove("busy");
    nodes.set(msg.root.id, msg.root);
    $("#root-sig").textContent = msg.root.name;
    applyConfig(msg.config);
    renderTree();
    toggleExpand(msg.root.id, true);
    select(msg.root.id);
    return;
  }
  if (msg.op === "error") { pending.clear(); refreshBusy(); showError(msg.msg); return; }
  const resolve = msg.req != null ? pending.get(msg.req) : null;
  if (resolve) { pending.delete(msg.req); resolve(msg); }
  refreshBusy();
}

// Busy state is derived from outstanding requests rather than set/cleared ad hoc,
// so overlapping requests can't clear each other's indicator early.
let busySince = 0;
function refreshBusy() {
  const busy = pending.size > 0;
  document.body.classList.toggle("busy", busy);
  if (busy) {
    if (!busySince) busySince = Date.now();
    $("#status").innerHTML = `<span class="spinner"></span>analysing…`;
  } else {
    busySince = 0;
    $("#status").textContent = "";
  }
}

// ---------------------------------------------------------------- tree

const loadingNodes = new Set();

async function toggleExpand(id, forceOpen = false) {
  const node = nodes.get(id);
  if (!node || !node.expandable) return;
  if (expanded.has(id) && !forceOpen) { expanded.delete(id); renderTree(); return; }

  if (!childrenOf.has(id)) {
    // Show the spinner on the row that was actually clicked: inference for a
    // cold callsite can take many seconds, and the header alone is easy to miss.
    loadingNodes.add(id);
    renderTree();
    try {
      const res = await send("expand", { id });
      if (res.error) showError(res.error);
      const ids = [];
      for (const rec of res.nodes || []) { nodes.set(rec.id, rec); ids.push(rec.id); }
      childrenOf.set(id, ids);
    } finally {
      loadingNodes.delete(id);
    }
  }
  expanded.add(id);
  renderTree();
}

function labelHTML(n) {
  const parts = [];
  if (n.kind === "root") {
    parts.push(`<span class="fname">${esc(n.name)}</span>`);
    return parts.join("");
  }
  if (n.stmtId >= 0) parts.push(`<span class="ssa">%${n.stmtId}</span>`);
  parts.push(`<span class="head">${esc(n.head)}</span>`);
  for (const w of n.wrappers) parts.push(`<span class="wrap">${esc(w)}</span>`);
  if (n.kind !== "edge") parts.push(`<span class="kind k-${esc(n.kind)}">${esc(n.kind)}</span>`);
  parts.push(`<span class="fname">${esc(n.name)}</span>`);
  const pos = n.argtypes.map((t) => `::${esc(t)}`).join(", ");
  const kws = (n.kwargs || []).length ? "; " + n.kwargs.map(esc).join(", ") : "";
  parts.push(`<span class="args">(${pos}${kws})</span>`);
  parts.push(`<span class="rt">::${esc(n.rt)}</span>`);
  if (n.effects) parts.push(`<span class="effects">${esc(n.effects)}</span>`);
  if (n.exct) parts.push(`<span class="exct">(↑::${esc(n.exct)})</span>`);
  if (n.nalternatives > 0) parts.push(`<span class="alt">${n.nalternatives} alternatives</span>`);
  if (n.recursive) parts.push(`<span class="rec" title="already on this path">↺ recursive</span>`);
  return parts.join("");
}

function renderTree() {
  const root = $("#tree");
  root.innerHTML = "";
  const rootId = [...nodes.keys()].find((k) => nodes.get(k).kind === "root");
  if (rootId != null) root.appendChild(renderNode(rootId));
}

function renderNode(id) {
  const n = nodes.get(id);
  const li = document.createElement("li");
  li.className = "node";
  li.dataset.nodeId = id;
  if (n.unstable) li.classList.add("unstable");
  if (n.expectedUnion) li.classList.add("expected-union");
  if (n.recursive) li.classList.add("is-recursive");
  if (!n.descendable) li.classList.add("inert");

  const row = document.createElement("div");
  row.className = "row" + (selected === id ? " selected" : "");

  const caret = document.createElement("span");
  if (loadingNodes.has(id)) {
    caret.className = "caret";
    caret.innerHTML = `<span class="spinner"></span>`;
  } else {
    caret.className = "caret" + (n.expandable ? "" : " leaf") +
                      (expanded.has(id) ? " open" : "");
    caret.textContent = n.expandable ? "▸" : "·";
    caret.onclick = (e) => { e.stopPropagation(); toggleExpand(id); };
  }
  row.appendChild(caret);

  const label = document.createElement("span");
  label.className = "label";
  label.innerHTML = labelHTML(n);
  label.onclick = () => { select(id); if (n.expandable && !expanded.has(id)) toggleExpand(id); };
  row.appendChild(label);

  if (n.file) {
    const loc = document.createElement("span");
    loc.className = "loc";
    loc.textContent = `${n.file.split("/").pop()}:${n.line}`;
    row.appendChild(loc);
  }
  li.appendChild(row);

  if (expanded.has(id) && childrenOf.has(id)) {
    const ul = document.createElement("ul");
    ul.className = "children";
    for (const c of childrenOf.get(id)) ul.appendChild(renderNode(c));
    li.appendChild(ul);
  }
  return li;
}

// ---------------------------------------------------------------- code pane

// Inference and codegen happen on the server with no incremental progress to
// report, so the honest thing is a spinner plus an escalating explanation: the
// first descent is dominated by compiling Cthulhu's own inference paths and can
// take tens of seconds, which otherwise reads as a hang.
let hintTimers = [];
function showLoading(what) {
  hintTimers.forEach(clearTimeout);
  hintTimers = [];
  $("#code").innerHTML =
    `<div class="loading"><span class="spinner big"></span>` +
    `<div><div class="loading-main">${esc(what)}</div>` +
    `<div class="loading-hint" id="loading-hint"></div></div></div>`;
  const hint = $("#loading-hint");
  const say = (ms, text) => hintTimers.push(setTimeout(() => { if (hint) hint.textContent = text; }, ms));
  say(1500, "Running type inference…");
  say(5000, "Still going — the first descent also compiles Cthulhu's inference code.");
  say(15000, "Cold compilation can take a while on the first run. Later clicks are cached.");
}
function clearLoading() {
  hintTimers.forEach(clearTimeout);
  hintTimers = [];
}

async function select(id, cameFrom = 0) {
  selected = id;
  renderTree();
  renderCrumbs(id);
  const n = nodes.get(id);
  $("#code-title").textContent = n.name + (n.file ? `  —  ${n.file}:${n.line}` : "");
  if (!n.descendable) {
    // A union-split callsite has no body of its own, but it does have
    // alternatives -- and clicking it in the source pane used to dead-end here
    // even though the tree could expand it. Offer the alternatives directly.
    if (n.expandable && !childrenOf.has(id)) {
      showLoading("Analysing " + n.name + "…");
      await toggleExpand(id, true);
      if (selected !== id) return;
    }
    clearLoading();
    const alts = n.expandable ? (childrenOf.get(id) || []) : [];
    const links = alts.map((k) => {
      const c = nodes.get(k);
      const pos = c.argtypes.map((t) => `::${esc(t)}`).join(", ");
      return `<button class="s-call bodylink" data-node-id="${k}">${esc(c.name)}(${pos})</button>`;
    }).join(" ");
    $("#code").innerHTML =
      `<p class="note">No code body: this is a <b>${esc(n.kind)}</b> callsite.` +
      (links ? ` Descend into one of its alternatives: ${links}` : "") + `</p>`;
    wireSourceSpans();
    return;
  }
  // Up before any awaiting, so the pane never sits blank while the tree expands.
  showLoading("Analysing " + n.name + "…");

  // The server maps source spans onto child node ids, so the children must have
  // been materialised for those ids to mean anything on the client.
  const cfgView = document.querySelector("input[name=view]:checked");
  if (cfgView && cfgView.value === "source") {
    const n0 = nodes.get(id);
    if (n0 && n0.expandable && !childrenOf.has(id)) await toggleExpand(id, true);
  }
  const res = await send("body", { id });
  clearLoading();
  if (selected !== id) return;          // superseded by a later click
  $("#code").innerHTML = res.html || `<p class="err">no output</p>`;
  wireSourceSpans();
  // When ascending, mark the call we just came back from so "where was I?" is
  // answered without re-reading the source.
  if (cameFrom) {
    const el = $(`#code [data-node-id="${cameFrom}"]`);
    if (el) { el.classList.add("sel-src"); el.scrollIntoView({ block: "center" }); }
  }
}

// ---------------------------------------------------------------- ascend
//
// Purely client-side: every node record carries `parent`, so walking back up the
// path we descended needs no server round-trip. (This is *not* Cthulhu's
// `ascend`, which follows backedges to find callers anywhere in the system --
// this only retraces the path in this session.)

function ascend() {
  const n = nodes.get(selected);
  if (!n || !n.parent) return false;
  select(n.parent, n.id);
  return true;
}

function pathTo(id) {
  const chain = [];
  let cur = nodes.get(id);
  while (cur) { chain.push(cur); cur = cur.parent ? nodes.get(cur.parent) : null; }
  return chain.reverse();
}

function renderCrumbs(id) {
  const bar = $("#crumbs");
  const chain = pathTo(id);
  bar.innerHTML = "";
  if (chain.length < 2) { bar.classList.add("empty"); return; }
  bar.classList.remove("empty");

  const up = document.createElement("button");
  up.className = "crumb-up";
  up.textContent = "↑ caller";
  up.title = "Ascend to the calling frame (Backspace)";
  up.onclick = ascend;
  bar.appendChild(up);

  chain.forEach((n, i) => {
    if (i) {
      const sep = document.createElement("span");
      sep.className = "crumb-sep";
      sep.textContent = "›";
      bar.appendChild(sep);
    }
    const c = document.createElement("button");
    c.className = "crumb" + (n.id === id ? " current" : "") +
                  (n.unstable ? " unstable" : "");
    c.textContent = n.kind === "root" ? shortName(n.name) : n.name;
    c.title = `${n.name}${n.argtypes.length ? "(" + n.argtypes.map((t) => "::" + t).join(", ") + ")" : ""}::${n.rt}`;
    c.onclick = () => select(n.id, id === n.id ? 0 : childOnPath(chain, i));
    bar.appendChild(c);
  });
}

// when jumping to an ancestor, highlight the call that continues the path
function childOnPath(chain, i) {
  return i + 1 < chain.length ? chain[i + 1].id : 0;
}

const shortName = (s) => s.replace(/^MethodInstance for /, "");

// In the :source view every call is a <span data-node-id>. Clicking one descends
// into that callsite -- the same action as clicking the row in the tree, which is
// what makes the source view the primary navigation surface rather than a readout.
function wireSourceSpans() {
  wireTooltips();
  const spans = document.querySelectorAll("#code .s-call[data-node-id]");
  if (!spans.length) return;
  for (const el of spans) {
    el.onclick = (e) => {
      // innermost span wins: string(y) inside length(string(y))
      e.stopPropagation();
      const id = Number(el.dataset.nodeId);
      revealInTree(id);
      select(id);
    };
  }
  // Only when there is real annotated source to explain -- a truncated shim page
  // has nothing but the body-method button.
  if (!document.querySelector("#code .s-call[data-node-id]:not(.bodylink)")) return;
  const legend = document.createElement("p");
  legend.className = "srclegend";
  legend.innerHTML = "Hover any expression (or a <b>where</b> parameter) for its type · " +
    "click a <b>call</b> to descend · " +
    "<b class=\"k-u\">red</b> = type-unstable, <b class=\"k-n\">amber</b> = small union" +
    // only mentioned when the page actually has some -- an unexplained legend
    // entry is worse than none
    (document.querySelector("#code .s-dead")
      ? ", <span class=\"s-dead\">faded</span> = compiled out for these argument types"
      : "");
  $("#code").appendChild(legend);
}

// Type tooltips. `mouseover` fires on the INNERMOST element under the cursor, so
// `closest(".s[data-type]")` picks the tightest annotated span for free -- no
// :has() needed. The tooltip is position:fixed, so .srcwrap's scroll container
// cannot clip it (which it did for anything on the first line).
let tipEl = null, hotEl = null;
function wireTooltips() {
  if (!tipEl) {
    tipEl = document.createElement("div");
    tipEl.id = "tip";
    document.body.appendChild(tipEl);
  }
  const pane = $("#code");
  // Show a type only when the tightest enclosing annotated span really covers
  // what the pointer is on. `.s-opaque` marks a node the analysis said nothing
  // about, and stops the search: better to show nothing than to report an
  // unrelated ancestor's type. This is what makes hovering `=` silent while
  // hovering inside `sin(y)` still reports the call's type.
  pane.onmousemove = (e) => {
    const hit = e.target.closest ? e.target.closest(".s[data-type], .s-opaque") : null;
    const el = hit && hit.dataset && hit.dataset.type ? hit : null;
    if (!el) return hideTip();
    if (el !== hotEl) {
      hotEl && hotEl.classList.remove("hot");
      hotEl = el;
      hotEl.classList.add("hot");
      tipEl.textContent = el.dataset.type;
      // Wrap at the source pane's width: a deeply parameterised type is one
      // unbroken line otherwise, and a line wider than the screen cannot be
      // read at all. Recomputed with the text since the pane is resizable.
      tipEl.style.maxWidth = tipMaxWidth() + "px";
    }
    tipEl.classList.add("on");
    // clamp to the viewport so long Union{...} types stay readable
    const w = tipEl.offsetWidth, h = tipEl.offsetHeight;
    let x = e.clientX + 12, y = e.clientY - h - 8;
    if (x + w > window.innerWidth - 8) x = window.innerWidth - w - 8;
    if (x < 4) x = 4;
    if (y < 4) y = e.clientY + 18;
    // a wrapped tooltip can be tall enough to run off the bottom too
    if (y + h > window.innerHeight - 4) y = Math.max(4, window.innerHeight - h - 4);
    tipEl.style.left = x + "px";
    tipEl.style.top = y + "px";
  };
  pane.onmouseleave = hideTip;
}
// Never wider than the source pane, never wider than the viewport, and never
// so narrow that it wraps every couple of characters.
function tipMaxWidth() {
  const pane = $("#code-pane");
  const paneW = pane ? pane.getBoundingClientRect().width : window.innerWidth;
  return Math.max(240, Math.min(paneW - 16, window.innerWidth - 16));
}
function hideTip() {
  if (tipEl) tipEl.classList.remove("on");
  if (hotEl) { hotEl.classList.remove("hot"); hotEl = null; }
}

// Make sure a node clicked in the source is visible in the tree: open every
// ancestor, then scroll it into view.
function revealInTree(id) {
  const chain = [];
  let cur = nodes.get(id);
  while (cur && cur.parent) { chain.push(cur.parent); cur = nodes.get(cur.parent); }
  for (const p of chain.reverse()) expanded.add(p);
  renderTree();
  const row = document.querySelector(`li[data-node-id="${id}"] > .row`);
  if (row) row.scrollIntoView({ block: "nearest" });
}

function showError(msg) {
  $("#code").innerHTML = `<pre class="err">${esc(msg)}</pre>`;
}

const esc = (s) => String(s).replace(/[&<>"]/g,
  (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));

// ---------------------------------------------------------------- toggles

// Data toggles: round-trip, and drop the memoised tree when `optimize` flips.
async function setServerConfig(key, value) {
  const res = await send("config", { key, value });
  applyConfig(res.config);
  if (res.treeInvalidated) {
    childrenOf.clear();
    const keep = nodes.get([...nodes.keys()].find((k) => nodes.get(k).kind === "root"));
    nodes.clear(); nodes.set(keep.id, keep);
    expanded.clear();
    await toggleExpand(keep.id, true);
    select(keep.id);
  } else if (selected != null) {
    select(selected);
  }
}

function applyConfig(cfg) {
  $("#optimize").checked = cfg.optimize;
  $("#debuginfo").value = cfg.debuginfo;
  const r = document.querySelector(`input[name=view][value="${cfg.view}"]`);
  if (r) r.checked = true;
  // optimize is forced off while view === :source (config.jl:24); reflect that
  // rather than letting the checkbox lie.
  $("#optimize").disabled = cfg.view === "source";
}

// Display toggles: pure CSS, no server involvement.
function applyDisplayFlags() {
  const b = document.body;
  b.classList.toggle("show-warn", $("#iswarn").checked);
  b.classList.toggle("show-effects", $("#showEffects").checked);
  b.classList.toggle("show-exct", $("#showExct").checked);
  b.classList.toggle("show-head", $("#showHead").checked);
  b.classList.toggle("hide-stable", $("#hideStable").checked);
  b.classList.toggle("no-syntax", !$("#syntax").checked);
}

function wire() {
  for (const el of document.querySelectorAll("input[name=view]")) {
    el.onchange = () => setServerConfig("view", el.value);
  }
  $("#optimize").onchange = (e) => setServerConfig("optimize", e.target.checked);
  $("#debuginfo").onchange = (e) => setServerConfig("debuginfo", e.target.value);
  for (const id of ["iswarn", "showEffects", "showExct", "showHead", "hideStable", "syntax"]) {
    $("#" + id).onchange = applyDisplayFlags;
  }
  applyDisplayFlags();

  // Backspace ascends, matching Cthulhu's terminal UI (backspace / the ↩ entry).
  document.addEventListener("keydown", (e) => {
    const t = e.target;
    if (t && (t.tagName === "INPUT" || t.tagName === "SELECT" || t.isContentEditable)) return;
    if (e.key === "Backspace" || (e.altKey && e.key === "ArrowLeft")) {
      e.preventDefault();
      ascend();
    }
  });
}

wire();
connect();
