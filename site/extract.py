"""Write site/lean.js with the Lean source of every declaration that site/content.js names.

    python3 site/extract.py           # write site/lean.js
    python3 site/extract.py --check   # exit 1 if site/lean.js is out of date

Declarations are read from FVDemocracy/Alaska/Statute/*.lean and FVDemocracy/Alaska/Statute/Examples/*.lean. A theorem is shown up to its `:=`,
without the proof. A declaration inside a `mutual` block is shown as the whole block. The
script fails if a name in content.js is not declared exactly once, and warns about
declarations from these files that the shown code (outside comments) uses but content.js does
not list.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

from serve import CONTENT, parse

SITE = Path(__file__).resolve().parent
ROOT = SITE.parent
SOURCES = sorted((ROOT / "FVDemocracy" / "Alaska" / "Statute").glob("*.lean")) + sorted(
    (ROOT / "FVDemocracy" / "Alaska" / "Statute" / "Examples").glob("*.lean"))
OUT = SITE / "lean.js"
ROOT_NAMESPACE = "Alaska"

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*"
    r"(def|theorem|lemma|structure|inductive|abbrev|instance|class)\b\s*([^\s(:{\[⦃]*)"
)
# Lines at column 0 that continue the declaration above them.
CONTINUATION = re.compile(r"^(termination_by|decreasing_by|deriving)\b")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*)*")


class ExtractError(Exception):
    pass


@dataclass
class Decl:
    name: str
    kind: str
    file: str
    line: int
    lines: list[str]
    head: int = 0
    mutual: tuple[int, int] | None = None
    members: list[str] = field(default_factory=list)


def scan(path: Path) -> list[Decl]:
    """Every named declaration in the file, with its docstring and full source."""
    text = path.read_text(encoding="utf-8").split("\n")
    rel = str(path.relative_to(ROOT))
    blocks: list[tuple[str, str]] = []  # (kind, name) for namespace / section / mutual
    decls: list[Decl] = []
    doc_start = None
    mutual_start = None
    mutual_decls: list[Decl] = []
    current: Decl | None = None

    def close():
        nonlocal current
        if current is not None:
            while current.lines and not current.lines[-1].strip():
                current.lines.pop()
            current = None

    i = 0
    while i < len(text):
        line = text[i]
        top = line[:1] not in ("", " ", "\t")
        if top and not CONTINUATION.match(line):
            close()
            m = DECL.match(line)
            if line.startswith("/-"):
                doc_start = i if line.startswith("/--") else None
                while "-/" not in text[i]:
                    i += 1
                i += 1
                continue
            if m and m.group(2) and m.group(1) != "instance":
                ns = [part for k, n in blocks if k == "namespace" for part in n.split(".")]
                if ns and ns[0] == ROOT_NAMESPACE:
                    ns = ns[1:]
                start = doc_start if doc_start is not None and doc_start < i else i
                current = Decl(".".join(ns + [m.group(2)]), m.group(1), rel, i + 1, text[start:i + 1], i - start)
                decls.append(current)
                if mutual_start is not None:
                    mutual_decls.append(current)
            elif line.startswith("namespace "):
                blocks.append(("namespace", line.split()[1]))
            elif line.startswith("section"):
                blocks.append(("section", ""))
            elif line.startswith("mutual"):
                blocks.append(("mutual", ""))
                mutual_start = i
                mutual_decls = []
            elif line.startswith("end"):
                kind, _ = blocks.pop()
                if kind == "mutual":
                    for d in mutual_decls:
                        d.mutual = (mutual_start, i + 1)
                    mutual_start = None
            doc_start = None
        elif current is not None:
            current.lines.append(line)
        i += 1
    close()

    for d in decls:
        if d.mutual:
            d.lines = text[d.mutual[0]:d.mutual[1]]
            d.members = [o.name for o in decls if o.mutual == d.mutual and o is not d]
        elif d.kind == "structure":
            d.members = [d.name + "." + m.group(1) for l in d.lines
                         if (m := re.match(r"^  ([A-Za-z_][\w']*)\s*:", l))]
        elif d.kind == "inductive":
            d.members = [d.name + "." + m.group(1) for l in d.lines
                         if (m := re.match(r"^  \| ([A-Za-z_][\w']*)", l))]
    return decls


def statement(d: Decl) -> str:
    """The declaration's source, cut before `:=` when it is a theorem and before
    `decreasing_by` otherwise."""
    src = "\n".join(d.lines)
    if d.kind not in ("theorem", "lemma"):
        return re.split(r"^decreasing_by\b", src, flags=re.M)[0].rstrip()
    head = len("\n".join(d.lines[:d.head]))
    depth = 0
    for j in range(head, len(src)):
        ch = src[j]
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩":
            depth -= 1
        elif depth == 0 and src.startswith(":=", j):
            return src[:j].rstrip()
    raise ExtractError(f"{d.name}: no `:=` found in {d.file}:{d.line}")


def names_in_content(tree) -> list[str]:
    out = [n.value for n in tree["model"]]
    for sec in tree["sections"]:
        for cl in sec["clauses"]:
            out += [n.value for n in cl.get("decls", [])]
    return out


def refs_in_content(tree) -> list[str]:
    out = []
    for sec in tree["sections"]:
        for cl in sec["clauses"]:
            out += [n.value for n in cl.get("refs", [])]
    return out


def build() -> str:
    tree = parse(CONTENT.read_text(encoding="utf-8"))
    all_decls: dict[str, list[Decl]] = {}
    for path in SOURCES:
        for d in scan(path):
            all_decls.setdefault(d.name, []).append(d)

    wanted = names_in_content(tree)
    dupes = sorted({n for n in wanted if wanted.count(n) > 1})
    if dupes:
        raise ExtractError(f"listed under more than one clause in content.js: {', '.join(dupes)}")
    out = {}
    for name in wanted:
        found = all_decls.get(name, [])
        if len(found) != 1:
            raise ExtractError(f"{name}: declared {len(found)} times in {', '.join(str(p.relative_to(ROOT)) for p in SOURCES)}")
        d = found[0]
        code = statement(d)
        out[name] = {
            "kind": d.kind,
            "file": d.file,
            "line": d.line,
            "code": code,
            "members": d.members,
            "sorry": d.kind in ("theorem", "lemma") and bool(re.search(r"\b(sorry|admit)\b", "\n".join(d.lines))),
        }

    shown = set(out) | {m for v in out.values() for m in v["members"]}
    for r in refs_in_content(tree):
        if r not in shown:
            raise ExtractError(f"refs entry {r} in content.js is not a shown declaration or member")
    phrases = tree.get("phrases", {})
    for pid, entry in phrases.items():
        names = entry["lean"] if isinstance(entry, dict) else entry
        for n in names:
            if n.value not in shown:
                raise ExtractError(f"phrase {pid} in content.js lists {n.value}, which is not a shown declaration or member")
        for n, excerpts in (entry.get("focus", {}) if isinstance(entry, dict) else {}).items():
            for x in excerpts:
                if n not in out or x.value not in out[n]["code"]:
                    raise ExtractError(f"phrase {pid} in content.js highlights {x.value!r}, which is not in the code of {n}")
    marked = {m for sec in tree["sections"] for cl in sec["clauses"]
              for m in re.findall(r"\[\[([^|\]]+)\|", cl["text"].value)}
    if marked != set(phrases):
        raise ExtractError(f"phrases marked in the text and listed under `phrases` differ: {sorted(marked ^ set(phrases))}")
    missing: dict[str, set[str]] = {}
    for name, v in out.items():
        for tok in IDENT.findall(re.sub(r"/-.*?-/|--[^\n]*", "", v["code"], flags=re.S)):
            for k in range(len(tok.split(".")), 0, -1):
                prefix = ".".join(tok.split(".")[:k])
                if prefix in all_decls and prefix not in shown:
                    missing.setdefault(prefix, set()).add(name)
                    break
    for prefix, users in sorted(missing.items()):
        print(f"warning: {', '.join(sorted(users))} {'uses' if len(users) == 1 else 'use'} {prefix}, which content.js does not list", file=sys.stderr)

    body = json.dumps(out, ensure_ascii=False, indent=1)
    return (
        "// Generated by site/extract.py from FVDemocracy/Alaska/Statute.\n"
        f"window.LEAN = {body};\n"
    )


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true", help="exit 1 if lean.js is out of date")
    args = ap.parse_args()
    try:
        js = build()
    except ExtractError as e:
        sys.exit(f"error: {e}")
    if args.check:
        if not OUT.exists() or OUT.read_text(encoding="utf-8") != js:
            sys.exit("error: site/lean.js is out of date; run python3 site/extract.py")
        return
    OUT.write_text(js, encoding="utf-8")


if __name__ == "__main__":
    main()
