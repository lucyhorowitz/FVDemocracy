import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import serve  # noqa: E402

SAMPLE = '''// header
window.CONTENT = {
  // a comment
  annotations: {
    a: { kind: "rule", note: "Old “quoted” note.", refs: ["X"] },
  },
  decls: [
    { name: "X", gloss: "first", code: `def X : Nat :=
  \\`1\\``, },
  ],
};
'''


class ApplyEdit(unittest.TestCase):
    def test_parse_values(self):
        t = serve.parse(SAMPLE)
        self.assertEqual(t["annotations"]["a"]["note"].value, "Old “quoted” note.")
        self.assertEqual(t["decls"][0]["code"].value, "def X : Nat :=\n  `1`")

    def test_only_the_literal_changes(self):
        out = serve.apply_edit(SAMPLE, ["annotations", "a", "note"], "Old “quoted” note.", 'New "note".')
        self.assertEqual(out, SAMPLE.replace('"Old “quoted” note."', '"New \\"note\\"."'))
        self.assertEqual(serve.parse(out)["annotations"]["a"]["note"].value, 'New "note".')

    def test_array_index(self):
        out = serve.apply_edit(SAMPLE, ["decls", 0, "gloss"], "first", "second")
        self.assertIn('gloss: "second"', out)

    def test_stale_old_value_is_refused(self):
        with self.assertRaises(serve.EditError):
            serve.apply_edit(SAMPLE, ["decls", 0, "gloss"], "not what is there", "x")

    def test_non_prose_field_is_refused(self):
        with self.assertRaises(serve.EditError):
            serve.apply_edit(SAMPLE, ["decls", 0, "code"], "def X : Nat :=\n  `1`", "x")

    def test_missing_path_is_refused(self):
        with self.assertRaises(serve.EditError):
            serve.apply_edit(SAMPLE, ["annotations", "b", "note"], "", "x")

    def test_add_note_on_its_own_line(self):
        src = 'window.CONTENT = {\n  c: { cite: "(a)",\n    text: "t", },\n};\n'
        out = serve.apply_edit(src, ["c", "note"], "", "N")
        self.assertEqual(out, 'window.CONTENT = {\n  c: { cite: "(a)",\n    text: "t",\n    note: "N", },\n};\n')
        self.assertEqual(serve.apply_edit(out, ["c", "note"], "N", ""), src)

    def test_add_note_to_phrase_array(self):
        src = 'window.CONTENT = {\n  phrases: {\n    "p": ["X", "Y"],\n  },\n};\n'
        out = serve.apply_edit(src, ["phrases", "p", "note"], "", "N")
        self.assertIn('"p": { lean: ["X", "Y"], note: "N" },', out)
        self.assertEqual(serve.parse(out)["phrases"]["p"]["note"].value, "N")

    def test_add_note_when_one_exists_is_refused(self):
        with self.assertRaises(serve.EditError):
            serve.apply_edit(SAMPLE, ["annotations", "a", "note"], "", "x")

    def test_add_only_note(self):
        with self.assertRaises(serve.EditError):
            serve.apply_edit(SAMPLE, ["decls", 0, "title"], "", "x")

    def test_real_content_note_round_trip(self):
        src = serve.CONTENT.read_text(encoding="utf-8")
        tree = serve.parse(src)
        for path in (["phrases", next(iter(tree["phrases"])), "note"], ["sections", 0, "clauses", 0, "note"]):
            out = serve.apply_edit(src, path, "", "A note.")
            self.assertEqual(serve.lookup(serve.parse(out), path).value, "A note.")
            back = serve.apply_edit(out, path, "A note.", "")
            if path[0] == "sections":
                self.assertEqual(back, src)

    def test_real_content_parses(self):
        tree = serve.parse(serve.CONTENT.read_text(encoding="utf-8"))
        self.assertIn("model", tree)


if __name__ == "__main__":
    unittest.main()
