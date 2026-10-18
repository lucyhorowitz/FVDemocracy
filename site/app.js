(function () {
  "use strict";

  const C = window.CONTENT;
  const L = window.LEAN;
  const esc = (s) => String(s).replace(/[&<>"]/g, (ch) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[ch]);
  const slug = (id) => id.replace(/ /g, "-");
  const clauseId = (sec, cl) => sec.cite + (cl.full || cl.cite);

  // ---------------------------------------------------------------- indices

  const phraseLean = (id) => { const p = C.phrases[id]; return Array.isArray(p) ? p : p.lean; };
  const phraseFocus = (id) => { const p = C.phrases[id]; return Array.isArray(p) ? {} : p.focus || {}; };
  const phraseNote = (id) => { const p = C.phrases[id]; return Array.isArray(p) ? null : p.note || null; };

  const targets = new Set();          // clause ids and section cites that can be linked to
  const home = new Map();             // declaration name -> clause id, or "model"
  const parentOf = new Map();         // declaration or member name -> declaration name

  for (const n of C.model) home.set(n, "model");
  for (const sec of C.sections) {
    targets.add(sec.cite);
    for (const cl of sec.clauses) {
      const id = clauseId(sec, cl);
      targets.add(id);
      for (const n of cl.decls || []) home.set(n, id);
    }
  }
  for (const [name, d] of Object.entries(L)) {
    parentOf.set(name, name);
    for (const m of d.members) parentOf.set(m, name);
  }
  // Unqualified names that identify exactly one shown declaration or member. Constructors of
  // Prop-valued inductive types are left out.
  const short = new Map();
  const ambiguous = new Set();
  function addShort(s, key) {
    if (ambiguous.has(s)) return;
    if (short.has(s) && short.get(s) !== key) { short.delete(s); ambiguous.add(s); return; }
    short.set(s, key);
  }
  for (const [name, d] of Object.entries(L)) {
    addShort(name.split(".").pop(), name);
    const header = d.code.split("\n").find((l) => /^(inductive|structure|def|theorem|mutual)\b/.test(l)) || "";
    const propValued = d.kind === "inductive" && /Prop\s*(where)?\s*$/.test(header);
    if (!propValued) for (const m of d.members) addShort(m.split(".").pop(), m);
  }

  // The declaration a dotted identifier (or one of its components) refers to.
  function resolveParts(tok) {
    const lead = tok.startsWith(".") ? "." : "";
    const parts = (lead ? tok.slice(1) : tok).split(".");
    const out = [];
    let i = 0;
    while (i < parts.length) {
      let matched = 0;
      for (let k = parts.length; k > i + 1; k--) {
        const q = parts.slice(i, k).join(".");
        if (parentOf.has(q)) { out.push({ text: q, key: q }); matched = k - i; break; }
      }
      if (!matched) {
        out.push({ text: parts[i], key: parentOf.has(parts[i]) ? parts[i] : short.get(parts[i]) || null });
        matched = 1;
      }
      i += matched;
    }
    return { lead, parts: out };
  }

  // ---------------------------------------------------------------- Lean highlighting

  const KEYWORDS = new Set(["def", "theorem", "structure", "inductive", "where", "deriving", "match", "with",
    "fun", "if", "then", "else", "abbrev", "instance", "namespace", "end", "section", "let", "have", "by",
    "termination_by", "mutual"]);
  const TYPES = new Set(["Nat", "List", "Option", "Prop", "Bool", "Type", "Repr", "DecidableEq", "Rat", "Int"]);
  const CONSTS = new Set(["some", "none", "True", "False"]);
  const TOKEN = /(\/-[\s\S]*?-\/)|(--[^\n]*)|("(?:[^"\\]|\\.)*")|(\.?[A-Za-z_][A-Za-z0-9_'!?₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*)*)|(\d+)|(\s+)|([\s\S])/g;

  function declHref(key) {
    return "#lean-" + parentOf.get(key);
  }

  function identHTML(tok) {
    if (KEYWORDS.has(tok)) return `<span class="tk-kw">${tok}</span>`;
    if (TYPES.has(tok)) return `<span class="tk-ty">${tok}</span>`;
    if (CONSTS.has(tok)) return `<span class="tk-const">${tok}</span>`;
    const { lead, parts } = resolveParts(tok);
    return lead + parts.map((p) => p.key
      ? `<a class="tk-ref" href="${esc(declHref(p.key))}" title="${esc(p.key)}">${esc(p.text)}</a>`
      : esc(p.text)).join(".");
  }

  // Note text with `name` shown as code, linked when `name` is a shown declaration or member.
  function noteHTML(text) {
    return text.split(/(`[^`]+`)/).map((part) => {
      const m = part.match(/^`([^`]+)`$/);
      if (!m) return esc(part);
      return parentOf.has(m[1]) || short.has(m[1])
        ? `<a class="tk-ref" href="${esc(declHref(parentOf.has(m[1]) ? m[1] : short.get(m[1])))}"><code>${esc(m[1])}</code></a>`
        : `<code>${esc(m[1])}</code>`;
    }).join("");
  }

  function docHTML(text) {
    // Joins wrapped lines, keeping blank lines and starting each list item on its own line.
    const flowed = text.replace(/([^\n])\n(?![ \t]*(\n|[*-] ))[ \t]*/g, "$1 ")
      .replace(/\n[ \t]*[*-] /g, "\n• ");
    const linked = (line) => line.split(/(`[^`]+`)/).map((part) => {
      const m = part.match(/^`([^`]+)`$/);
      if (m && parentOf.has(m[1])) return `<a class="tk-ref" href="${esc(declHref(m[1]))}">${esc(part)}</a>`;
      return esc(part);
    }).join("");
    // List items are blocks with a hanging indent, so they need no line breaks around them.
    const lines = flowed.split("\n");
    const item = (line) => line.startsWith("• ");
    return lines.map((line, i) => item(line)
      ? `<span class="doc-li">${linked(line)}</span>`
      : linked(line) + (i < lines.length - 1 && !item(lines[i + 1]) ? "\n" : "")).join("");
  }

  function leanHTML(src) {
    let out = "";
    TOKEN.lastIndex = 0;
    let m;
    while ((m = TOKEN.exec(src))) {
      if (m[1]) out += `<span class="tk-doc">${docHTML(m[1])}</span>`;
      else if (m[2]) out += `<span class="tk-com">${esc(m[2])}</span>`;
      else if (m[3]) out += `<span class="tk-str">${esc(m[3])}</span>`;
      else if (m[4]) out += identHTML(m[4]);
      else if (m[5]) out += `<span class="tk-num">${m[5]}</span>`;
      else if (m[6]) out += m[6];
      else out += /[∃∀¬∧∨↔→←∈≠≤≥·⟨⟩|]/.test(m[7]) ? `<span class="tk-op">${esc(m[7])}</span>` : esc(m[7]);
    }
    return out;
  }

  // ---------------------------------------------------------------- rendering

  const KIND = { def: "Definition", structure: "Structure", inductive: "Inductive type", theorem: "Theorem", lemma: "Theorem", abbrev: "Definition" };

  function missing(name) {
    return `<div class="decl decl-missing" id="lean-${esc(name)}"><code>${esc(name)}</code> is not in lean.js. Run <code>python3 site/extract.py</code>.</div>`;
  }

  // Lean source with the given excerpts marked.
  function focusedHTML(code, excerpts) {
    const ranges = [];
    for (const x of excerpts || []) {
      const i = code.indexOf(x);
      if (i < 0) console.error(`excerpt not found: ${x}`);
      else ranges.push([i, i + x.length]);
    }
    ranges.sort((a, b) => a[0] - b[0]);
    let out = "", pos = 0;
    for (const [a, b] of ranges) {
      if (a < pos) continue;
      out += leanHTML(code.slice(pos, a)) + `<mark class="focus">${leanHTML(code.slice(a, b))}</mark>`;
      pos = b;
    }
    return out + leanHTML(code.slice(pos));
  }

  function declCard(name, focus) {
    const d = L[name];
    if (!d) return missing(name);
    const theorem = d.kind === "theorem" || d.kind === "lemma";
    const status = theorem
      ? (d.sorry ? `<span class="status status-sorry" title="The proof contains sorry">sorry</span>`
                 : `<span class="status status-ok" title="Proved, without sorry">✓</span>`)
      : "";
    return `<section class="decl" id="lean-${esc(name)}">
      <header class="decl-head">
        <span class="decl-kind">${KIND[d.kind] || d.kind}</span>
        <code class="decl-name">${esc(name)}</code>
        ${status}
        <span class="decl-src">${esc(d.file.split("/").pop())}:${d.line}</span>
      </header>
      <pre class="lean"><code>${focusedHTML(d.code, focus)}</code></pre>
    </section>`;
  }

  // Clause text with {target|words} links and nested [[id|words]] phrases.
  function statuteHTML(text, where) {
    let i = 0;
    function parse(inPhrase) {
      let html = "";
      while (i < text.length) {
        if (text.startsWith("[[", i)) {
          const bar = text.indexOf("|", i);
          const id = text.slice(i + 2, bar);
          i = bar + 1;
          const inner = parse(true);
          if (!C.phrases[id]) console.error(`${where}: unknown phrase ${id}`);
          html += `<span class="phrase" data-phrase="${esc(id)}">${inner}</span>`;
        } else if (inPhrase && text.startsWith("]]", i)) {
          i += 2;
          return html;
        } else if (text[i] === "{") {
          const bar = text.indexOf("|", i), close = text.indexOf("}", i);
          const target = text.slice(i + 1, bar), words = text.slice(bar + 1, close);
          i = close + 1;
          if (!targets.has(target)) {
            console.error(`${where}: link to unknown clause ${target}`);
            html += `<span class="bad-link">${esc(words)}</span>`;
          } else {
            const term = /^AS 15\.15\.350\(g\)/.test(target) && !/^[(A-Z\d]/.test(words);
            html += `<a class="xref${term ? " term" : ""}" href="#${esc(slug(target))}">${esc(words)}</a>`;
          }
        } else {
          html += esc(text[i]);
          i++;
        }
      }
      return html;
    }
    return parse(false);
  }

  function secHeading(sec) {
    const num = sec.cite.startsWith("AS ") ? `Sec. ${sec.cite.slice(3)}.` : `${sec.cite}.`;
    return `<h2 class="sec-head"><span class="sec-num">${esc(num)}</span> ${esc(sec.title)}${/[.\]]$/.test(sec.title) ? "" : "."}</h2>`;
  }

  // A clause with marked phrases shows Lean only for its phrases. A clause with Lean but no marked
  // phrase is selected as a whole: clause id (or "model") -> its own declarations, then its refs.
  const panelDecls = new Map([["model", C.model]]);
  const anchorOf = new Map([["model", "model"]]); // clause id -> element id in the statute column
  const noteOf = new Map(); // clause id -> note
  const clauseOf = new Map(); // clause id -> [clause object in CONTENT, its path in CONTENT]

  function renderStatute() {
    const secIndex = C.sections.filter((s) => s.group !== "referenced")
      .map((s) => `<a href="#${esc(slug(s.cite))}">${esc(s.cite)}</a>`).join("");
    let html = `<nav class="sec-index"><a href="#model">Model</a>${secIndex}<a href="#referenced">Referenced provisions</a></nav>
      <div class="clause formal whole model-clause" id="model" data-clause="model"><p class="ctext"><span class="cite">Model</span></p></div>`;
    let inReferenced = false;
    for (const [si, sec] of C.sections.entries()) {
      if (sec.group === "referenced" && !inReferenced) {
        inReferenced = true;
        html += `<h2 class="group-head" id="referenced">Referenced provisions</h2>`;
      }
      html += `<section class="sec${sec.group === "referenced" ? " sec-referenced" : ""}" id="${esc(slug(sec.cite))}">${secHeading(sec)}`;
      for (const [ci, cl] of sec.clauses.entries()) {
        const id = clauseId(sec, cl);
        clauseOf.set(id, [cl, ["sections", si, "clauses", ci]]);
        const hasPhrases = [...cl.text.matchAll(/\[\[([^|\]]+)\|/g)].some((m) => C.phrases[m[1]]);
        const names = [...(cl.decls || []), ...(cl.refs || []).map((r) => parentOf.get(r) || r)];
        const whole = !hasPhrases && names.length > 0;
        const formal = hasPhrases || whole;
        if (whole) panelDecls.set(id, [...new Set(names)]);
        if (cl.note) noteOf.set(id, cl.note);
        const elId = cl.cite ? slug(id) : slug(sec.cite) + "-text";
        anchorOf.set(id, elId);
        html += `<div class="clause lvl-${cl.level}${formal ? " formal" : ""}${whole ? " whole" : ""}" id="${esc(elId)}"${formal ? ` data-clause="${esc(id)}"` : ""}>
          <p class="ctext">${cl.cite ? `<span class="cite">${esc(cl.cite)}</span> ` : ""}${statuteHTML(cl.text, id)}</p>
        </div>`;
      }
      html += `</section>`;
    }
    document.getElementById("statute").innerHTML = html;
  }

  // ---------------------------------------------------------------- selection

  const panel = document.getElementById("panel");
  const narrow = window.matchMedia("(max-width: 900px)");
  // { clause, phrase, only }: phrase is null when a whole clause is selected; only, when set, lists
  // the declarations to show in place of the selection's own.
  let selected = null;

  function shownNames(sel) {
    if (sel.only) return sel.only;
    if (!sel.phrase) return panelDecls.get(sel.clause);
    return [...new Set(phraseLean(sel.phrase).map((n) => parentOf.get(n) || n))];
  }

  function select(clause, phrase, focusDecl, only) {
    if (!phrase && !only && !panelDecls.has(clause)) return;
    selected = { clause, phrase: phrase || null, only: only || null };
    for (const el of document.querySelectorAll(".clause.selected, .phrase.selected")) {
      el.classList.remove("selected");
    }
    const clauseEl = document.getElementById(anchorOf.get(clause));
    let quote = "";
    note = null;
    if (phrase) {
      const els = clauseEl.querySelectorAll(`.phrase[data-phrase="${CSS.escape(phrase)}"]`);
      for (const el of els) el.classList.add("selected");
      quote = `<p class="panel-phrase">“${esc(els[0].textContent)}”</p>`;
      if (!only) note = { text: phraseNote(phrase) || "", path: ["phrases", phrase, "note"] };
    } else {
      clauseEl.classList.add("selected");
      if (!only) note = { text: noteOf.get(clause) || "", path: clauseOf.has(clause) ? [...clauseOf.get(clause)[1], "note"] : null };
    }
    panel.innerHTML = `<h2 class="panel-head">${clause === "model" ? "Model" : esc(clause)}</h2>${quote}${noteBlock()}${shownNames(selected).map((n) => declCard(n, phrase && !only ? phraseFocus(phrase)[n] : null)).join("")}`;
    placePanel();
    if (focusDecl) {
      const card = document.getElementById("lean-" + focusDecl);
      if (card) {
        card.scrollIntoView({ block: "start" });
        card.classList.remove("flash");
        void card.offsetWidth;
        card.classList.add("flash");
      }
    } else if (!narrow.matches) {
      panel.scrollTop = 0;
    }
  }

  // ---------------------------------------------------------------- note editing

  // Notes can be edited when the page is served by site/serve.py, which answers /api/ping.
  let canEdit = false;
  let note = null; // { text, path }: the selection's note and its path in CONTENT

  function noteBlock() {
    if (!note) return "";
    const shown = note.text ? `<p class="panel-note">${noteHTML(note.text)}</p>` : "";
    if (!canEdit || !note.path) return shown;
    return `<div class="note-edit">${shown}<button type="button" class="note-btn">${note.text ? "Edit note" : "Add note"}</button></div>`;
  }

  function reselect() {
    if (selected) select(selected.clause, selected.phrase, null, selected.only);
  }

  function openNoteEditor() {
    const box = panel.querySelector(".note-edit");
    box.innerHTML = `<textarea class="note-input" rows="6">${esc(note.text)}</textarea>
      <div class="note-bar"><button type="button" class="note-save">Save</button><button type="button" class="note-cancel">Cancel</button><span class="note-msg"></span></div>`;
    const input = box.querySelector(".note-input");
    input.focus();
    input.addEventListener("keydown", (e) => {
      if (e.key === "Escape") reselect();
      else if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) { e.preventDefault(); saveNote(); }
    });
  }

  async function saveNote() {
    const box = panel.querySelector(".note-edit");
    const text = box.querySelector(".note-input").value.trim();
    const msg = box.querySelector(".note-msg");
    msg.textContent = "Saving…";
    let res;
    try {
      res = await fetch("/api/edit", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ path: note.path, old: note.text, new: text }),
      });
    } catch (e) {
      msg.textContent = "Could not reach the server.";
      return;
    }
    if (!res.ok) {
      msg.textContent = (await res.json().catch(() => ({}))).error || `Error ${res.status}`;
      return;
    }
    if (note.path[0] === "phrases") {
      const id = note.path[1];
      if (Array.isArray(C.phrases[id])) C.phrases[id] = { lean: C.phrases[id] };
      if (text) C.phrases[id].note = text;
      else delete C.phrases[id].note;
    } else {
      const [cl] = clauseOf.get(selected.clause);
      if (text) { cl.note = text; noteOf.set(selected.clause, text); }
      else { delete cl.note; noteOf.delete(selected.clause); }
    }
    reselect();
  }

  panel.addEventListener("click", (e) => {
    if (e.target.closest(".note-btn")) openNoteEditor();
    else if (e.target.closest(".note-save")) saveNote();
    else if (e.target.closest(".note-cancel")) reselect();
  });

  fetch("/api/ping").then((r) => (r.ok ? r.json() : null)).then((j) => {
    if (j && j.edit) { canEdit = true; reselect(); }
  }).catch(() => {});

  function placePanel() {
    if (narrow.matches && selected) document.getElementById(anchorOf.get(selected.clause)).after(panel);
    else if (!narrow.matches) document.getElementById("panel-col").append(panel);
  }
  narrow.addEventListener("change", placePanel);

  function inView(el) {
    const r = el.getBoundingClientRect();
    return r.top >= 60 && r.bottom <= window.innerHeight;
  }

  // The phrase of `clause` that lists the declaration `name`, if any.
  function phraseListing(clause, name) {
    const clauseEl = document.getElementById(anchorOf.get(clause));
    for (const el of clauseEl.querySelectorAll(".phrase[data-phrase]")) {
      if (C.phrases[el.dataset.phrase] && phraseLean(el.dataset.phrase).some((n) => (parentOf.get(n) || n) === name)) return el.dataset.phrase;
    }
    return null;
  }

  // Hash targets: a clause or section id, or lean-<declaration>.
  function followHash() {
    const h = decodeURIComponent(location.hash.slice(1));
    if (!h) return;
    if (h.startsWith("lean-")) {
      const name = h.slice(5);
      if (selected && shownNames(selected).includes(name)) {
        select(selected.clause, selected.phrase, name, selected.only);
        return;
      }
      const at = home.get(name);
      if (!at) return;
      if (panelDecls.has(at)) select(at, null, name);
      else {
        const phrase = phraseListing(at, name);
        if (phrase) select(at, phrase, name);
        else select(at, null, name, [name]);
      }
      const clauseEl = document.getElementById(anchorOf.get(at));
      if (!inView(clauseEl)) clauseEl.scrollIntoView({ block: "center" });
      return;
    }
    const el = document.getElementById(h);
    if (!el) return;
    el.scrollIntoView({ block: "start" });
    if (el.dataset.clause) select(el.dataset.clause);
  }

  // Marks the innermost phrase under the pointer.
  let hovered = null;
  function hover(el) {
    if (hovered === el) return;
    if (hovered) hovered.classList.remove("hover");
    hovered = el;
    if (el) el.classList.add("hover");
  }

  function wire() {
    document.getElementById("statute").addEventListener("click", (e) => {
      if (e.target.closest("a")) return;
      const cl = e.target.closest(".clause[data-clause]");
      if (!cl) return;
      if (cl.classList.contains("whole")) {
        select(cl.dataset.clause);
        return;
      }
      const ph = e.target.closest(".phrase");
      if (ph) select(cl.dataset.clause, ph.dataset.phrase);
    });
    document.getElementById("statute").addEventListener("mouseover", (e) => {
      hover(e.target.closest("a") ? null : e.target.closest(".clause[data-clause]:not(.whole) .phrase"));
    });
    document.getElementById("statute").addEventListener("mouseleave", () => hover(null));
    window.addEventListener("hashchange", followHash);
  }

  for (const n of [...home.keys()]) if (!L[n]) console.error(`${n} is listed in content.js but not in lean.js`);
  renderStatute();
  wire();
  if (location.hash) followHash();
  if (!selected) panel.innerHTML = `<p class="panel-empty">Select a phrase.</p>`;
})();
