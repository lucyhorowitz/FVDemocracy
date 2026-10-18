"""Serve the statute site locally, with in-page editing of the prose in content.js.

    python3 site/serve.py [--port 8000]

The page shows Edit buttons when `GET /api/ping` answers, which only this server does.
Saving sends `POST /api/edit` with a path into `window.CONTENT` (object keys and array
indices), the value the page last saw, and the new value. The string literal at that
path is replaced in content.js and the rest of the file is kept byte for byte. A `note`
can also be added where there is none (the page last saw ""), and saving an empty note
removes the `note` field. Adding a note to a phrase listed as an array of names turns it
into `{ lean: names, note: text }`.

The server listens on 127.0.0.1 only. To edit from another machine, forward the port
with `ssh -L 8000:localhost:8000`.
"""

from __future__ import annotations

import argparse
import http.server
import json
import os
import tempfile
from dataclasses import dataclass
from pathlib import Path

SITE = Path(__file__).resolve().parent
CONTENT = SITE / "content.js"
PREFIX = "window.CONTENT ="

# Fields holding formalizer prose. The last key of an edit path must be one of these.
EDITABLE = {"note", "gloss", "title", "current", "rationale", "consequence", "text", "name", "caption"}


class EditError(Exception):
    pass


@dataclass
class Str:
    """A string literal in content.js: its decoded value and its span in the source."""

    value: str
    start: int
    end: int


class Obj(dict):
    """An object literal: its fields, its span, and the span of each `key: value` entry."""

    def __init__(self, start: int):
        super().__init__()
        self.start = start
        self.end = start
        self.entries: dict[str, tuple[int, int]] = {}


class Arr(list):
    """An array literal and its span."""

    def __init__(self, start: int):
        super().__init__()
        self.start = start
        self.end = start


class Parser:
    """Reads the object literal assigned to window.CONTENT.

    The accepted language is what content.js uses: objects with identifier or
    double-quoted keys, arrays, double-quoted strings, template literals without
    `${`, numbers, true/false/null, trailing commas, and // and /* */ comments.
    Strings come back as `Str` so that edits can be made in place.
    """

    def __init__(self, src: str):
        self.src = src
        self.i = 0

    def fail(self, msg: str):
        line = self.src.count("\n", 0, self.i) + 1
        raise EditError(f"content.js line {line}: {msg}")

    def skip(self):
        s = self.src
        while self.i < len(s):
            if s[self.i].isspace():
                self.i += 1
            elif s.startswith("//", self.i):
                j = s.find("\n", self.i)
                self.i = len(s) if j < 0 else j + 1
            elif s.startswith("/*", self.i):
                j = s.find("*/", self.i + 2)
                if j < 0:
                    self.fail("unterminated comment")
                self.i = j + 2
            else:
                return

    def peek(self) -> str:
        self.skip()
        return self.src[self.i] if self.i < len(self.src) else ""

    def expect(self, ch: str):
        if self.peek() != ch:
            self.fail(f"expected {ch!r}")
        self.i += 1

    def value(self):
        ch = self.peek()
        if ch == "{":
            return self.obj()
        if ch == "[":
            return self.arr()
        if ch == '"':
            return self.dq()
        if ch == "`":
            return self.tl()
        return self.atom()

    def obj(self) -> Obj:
        self.peek()
        out = Obj(self.i)
        self.expect("{")
        while self.peek() != "}":
            key_start = self.i
            if self.peek() == '"':
                key = self.dq().value
            else:
                j = self.i
                while j < len(self.src) and (self.src[j].isalnum() or self.src[j] in "_$"):
                    j += 1
                if j == self.i:
                    self.fail("expected a key")
                key, self.i = self.src[self.i : j], j
            self.expect(":")
            out[key] = self.value()
            out.entries[key] = (key_start, self.i)
            if self.peek() == ",":
                self.i += 1
            elif self.peek() != "}":
                self.fail("expected ',' or '}'")
        self.i += 1
        out.end = self.i
        return out

    def arr(self) -> Arr:
        self.peek()
        out = Arr(self.i)
        self.expect("[")
        while self.peek() != "]":
            out.append(self.value())
            if self.peek() == ",":
                self.i += 1
            elif self.peek() != "]":
                self.fail("expected ',' or ']'")
        self.i += 1
        out.end = self.i
        return out

    def dq(self) -> Str:
        start = self.i
        j = start + 1
        s = self.src
        while j < len(s) and s[j] != '"':
            j += 2 if s[j] == "\\" else 1
        if j >= len(s):
            self.fail("unterminated string")
        self.i = j + 1
        try:
            return Str(json.loads(s[start : self.i]), start, self.i)
        except json.JSONDecodeError as e:
            self.fail(f"string is not JSON-compatible: {e}")

    def tl(self) -> Str:
        start = self.i
        j = start + 1
        s = self.src
        buf = []
        while j < len(s) and s[j] != "`":
            if s.startswith("${", j):
                self.fail("template substitutions are not supported")
            if s[j] == "\\" and j + 1 < len(s):
                buf.append(s[j + 1])
                j += 2
            else:
                buf.append(s[j])
                j += 1
        if j >= len(s):
            self.fail("unterminated template literal")
        self.i = j + 1
        return Str("".join(buf), start, self.i)

    def atom(self):
        j = self.i
        while j < len(self.src) and (self.src[j].isalnum() or self.src[j] in "._-+"):
            j += 1
        word = self.src[self.i : j]
        if not word:
            self.fail("unexpected character")
        self.i = j
        if word in ("true", "false", "null"):
            return {"true": True, "false": False, "null": None}[word]
        try:
            return float(word) if "." in word else int(word)
        except ValueError:
            self.fail(f"unexpected {word!r}")


def parse(src: str):
    at = src.find(PREFIX)
    if at < 0:
        raise EditError(f"content.js does not contain {PREFIX!r}")
    p = Parser(src)
    p.i = at + len(PREFIX)
    tree = p.value()
    if p.peek() != ";":
        p.fail("expected ';' after the content object")
    return tree


def lookup(tree, path: list):
    node = tree
    for key in path:
        if isinstance(node, dict) and isinstance(key, str) and key in node:
            node = node[key]
        elif isinstance(node, list) and isinstance(key, int) and 0 <= key < len(node):
            node = node[key]
        else:
            raise EditError(f"no field at {path}")
    return node


def remove_entry(src: str, obj: Obj, key: str) -> str:
    """content.js source without the `key: value` entry of `obj` and its comma. An entry that
    starts a line is removed with the line break before it."""
    start, end = obj.entries[key]
    while end < len(src) and src[end] in " \t":
        end += 1
    if src.startswith(",", end):
        end += 1
    while end < len(src) and src[end] in " \t":
        end += 1
    line_start = src.rfind("\n", 0, start) + 1
    if line_start > 0 and not src[line_start:start].strip():
        return src[: line_start - 1] + ("" if src.startswith("\n", end) else " ") + src[end:]
    return src[:start] + src[end:]


def add_entry(src: str, obj: Obj, key: str, literal: str) -> str:
    """content.js source with `key: literal` added as the last entry of `obj`, on its own
    line when the last entry starts a line."""
    entry = f"{key}: {literal}"
    if not obj.entries:
        return src[: obj.start + 1] + f" {entry} " + src[obj.start + 1 :]
    last_start, last_end = obj.entries[list(obj.entries)[-1]]
    line_start = src.rfind("\n", 0, last_start) + 1
    indent = src[line_start:last_start]
    j = last_end
    while j < len(src) and src[j] in " \t":
        j += 1
    has_comma = src.startswith(",", j)
    if has_comma and not indent.strip():
        return src[: j + 1] + f"\n{indent}{entry}," + src[j + 1 :]
    if has_comma:
        return src[: j + 1] + f" {entry}," + src[j + 1 :]
    return src[:last_end] + f", {entry}" + src[last_end:]


def apply_edit(src: str, path: list, old: str, new: str) -> str:
    """content.js source with the string at `path` changed from `old` to `new`."""
    if not path or path[-1] not in EDITABLE:
        raise EditError(f"{path} is not an editable field")
    if not isinstance(new, str):
        raise EditError("the new value must be a string")
    stale = EditError("content.js changed since the page was loaded; reload the page and edit again")
    key = path[-1]
    parent = lookup(parse(src), path[:-1])
    literal = json.dumps(new, ensure_ascii=False)
    if isinstance(parent, Obj) and key in parent:
        node = parent[key]
        if not isinstance(node, Str):
            raise EditError(f"{path} is not a string")
        if node.value != old:
            raise stale
        if key == "note" and not new:
            out = remove_entry(src, parent, key)
        else:
            out = src[: node.start] + literal + src[node.end :]
    elif key == "note" and isinstance(parent, Obj):
        if old:
            raise stale
        if not new:
            return src
        out = add_entry(src, parent, key, literal)
    elif key == "note" and isinstance(parent, Arr) and len(path) == 3 and path[0] == "phrases":
        if old:
            raise stale
        if not new:
            return src
        out = src[: parent.start] + f"{{ lean: {src[parent.start : parent.end]}, note: {literal} }}" + src[parent.end :]
    else:
        raise EditError(f"no field at {path}")
    parse(out)
    return out


def write_atomic(path: Path, text: str):
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=".content-", suffix=".js")
    with os.fdopen(fd, "w", encoding="utf-8", newline="") as f:
        f.write(text)
    os.replace(tmp, path)


class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(SITE), **kwargs)

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def send_json(self, status: int, obj):
        body = json.dumps(obj).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if self.path == "/api/ping":
            self.send_json(200, {"edit": True})
        else:
            super().do_GET()

    def do_POST(self):
        if self.path != "/api/edit":
            self.send_json(404, {"error": "not found"})
            return
        try:
            req = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))))
            src = CONTENT.read_text(encoding="utf-8")
            write_atomic(CONTENT, apply_edit(src, req["path"], req["old"], req["new"]))
        except (EditError, KeyError, ValueError) as e:
            self.send_json(409 if isinstance(e, EditError) else 400, {"error": str(e)})
            return
        self.send_json(200, {"ok": True})


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--port", type=int, default=8000)
    args = ap.parse_args()
    parse(CONTENT.read_text(encoding="utf-8"))
    server = http.server.ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    print(f"Serving {SITE} with editing at http://localhost:{args.port}/")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
