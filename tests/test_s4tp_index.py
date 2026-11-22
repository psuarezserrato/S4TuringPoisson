import tempfile
import unittest
from pathlib import Path
import sys

TOOLS_DIR = Path(__file__).resolve().parent.parent / "tools"
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import s4tp_index as bm25_index


class TestS4TPIndex(unittest.TestCase):
    def test_extract_declarations_and_exclusion(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            sample_file = root / "Sample.lean"
            sample_file.write_text(
                "namespace S4TuringPoisson\n\n"
                "/-- Shift sequence by zero is identity. -/\n"
                "theorem shiftSeq_zero (s : Int → Nat) : s = s :=\n"
                "  rfl\n\n"
                "private theorem shiftSeq_zero' (s : Int → Nat) : s = s :=\n"
                "  rfl\n\n"
                "theorem shiftSeq_add_aux (s : Int → Nat) : s = s :=\n"
                "  rfl\n\n"
                "theorem shiftSeq_add (s : Int → Nat) : s = s :=\n"
                "  shiftSeq_add_aux s\n\n"
                "theorem unproved_lemma (s : Int → Nat) : s = s := by\n"
                "  sorry\n\n"
                "end S4TuringPoisson\n",
                encoding="utf-8",
            )
            decls, proofs = bm25_index.extract_declarations_from_file(sample_file, root, origin="s4tp")
            names = [d["name"] for d in decls]
            # Private and sorry declarations must be excluded
            self.assertIn("S4TuringPoisson.shiftSeq_zero", names)
            self.assertIn("S4TuringPoisson.shiftSeq_add", names)
            self.assertIn("S4TuringPoisson.shiftSeq_add_aux", names)
            self.assertNotIn("S4TuringPoisson.shiftSeq_zero'", names)
            self.assertNotIn("S4TuringPoisson.unproved_lemma", names)
            self.assertEqual(len(proofs), 3)

            idx = bm25_index.InvertedBM25()
            idx.fit(decls)

            # Query without exclusion
            hits = idx.search("shiftSeq_add Int Nat", top_k=5)
            hit_names = [h["name"] for h in hits]
            self.assertIn("S4TuringPoisson.shiftSeq_add", hit_names)

            # Query with --exclude shiftSeq_add must hide both shiftSeq_add and shiftSeq_add_aux
            hits_ex = idx.search(
                "shiftSeq_add Int Nat",
                top_k=5,
                exclude=["S4TuringPoisson.shiftSeq_add"],
            )
            hit_ex_names = [h["name"] for h in hits_ex]
            self.assertNotIn("S4TuringPoisson.shiftSeq_add", hit_ex_names)
            self.assertNotIn("S4TuringPoisson.shiftSeq_add_aux", hit_ex_names)


if __name__ == "__main__":
    unittest.main()
