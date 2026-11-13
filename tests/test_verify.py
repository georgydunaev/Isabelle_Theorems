import os
import re
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
import verify


class TestIsabelleTheorems(unittest.TestCase):
    def setUp(self):
        self.thy_files = [
            os.path.join(ROOT, "Jech.thy"),
            os.path.join(ROOT, "Jech_clean.thy"),
            os.path.join(ROOT, "examples", "Example1.thy"),
            os.path.join(ROOT, "examples", "Example2.thy"),
            os.path.join(ROOT, "examples", "example1.thy"),
        ]

    def test_all_thy_files_valid(self):
        self.assertEqual(verify.main(), 0)

    def test_all_files_exist(self):
        for path in self.thy_files:
            self.assertTrue(os.path.isfile(path), f"File missing: {path}")

    def test_theory_syntax_and_headers(self):
        for path in self.thy_files:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            ok, msg = verify.check_theory_header(content, path)
            self.assertTrue(ok, f"Header check failed for {path}: {msg}")
            self.assertRegex(content, r"\bend\b", f"Missing 'end' keyword in {path}")

    def test_structured_isar_in_jech_theories(self):
        for fname in ["Jech.thy", "Jech_clean.thy"]:
            path = os.path.join(ROOT, fname)
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()

            # Ensure lemma ex_1_2' is present
            self.assertIn("ex_1_2'", content, f"Lemma ex_1_2' missing in {fname}")

            # Verify structured Isar keywords
            self.assertIn("proof", content, f"Missing 'proof' in {fname}")
            self.assertIn("assume", content, f"Missing 'assume' in {fname}")
            self.assertIn("have", content, f"Missing 'have' in {fname}")
            self.assertIn("show", content, f"Missing 'show' in {fname}")
            self.assertIn("qed", content, f"Missing 'qed' in {fname}")

            # Verify absence of legacy procedural apply/done
            self.assertNotRegex(
                content,
                r"\bapply\b",
                f"Legacy 'apply' found in {fname}; expected structured Isar",
            )
            self.assertNotRegex(
                content,
                r"\bdone\b",
                f"Legacy 'done' found in {fname}; expected structured Isar",
            )

    def test_valid_isar_block_closures(self):
        for path in self.thy_files:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            ok, msg = verify.check_proof_closures(content)
            self.assertTrue(ok, f"Proof closure check failed for {path}: {msg}")

    def test_absence_of_oops_and_sorry(self):
        for path in self.thy_files:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            ok, msg = verify.check_no_unproved(content)
            self.assertTrue(ok, f"Unproved marker found in {path}: {msg}")

    def test_symbol_integrity_and_encoding(self):
        for path in self.thy_files:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            ok, msg = verify.check_symbol_integrity(content)
            self.assertTrue(ok, f"Symbol integrity check failed for {path}: {msg}")

            # Specifically check that Jech and Jech_clean contain proper set theory symbols
            if "Jech" in os.path.basename(path):
                self.assertIn("∈", content, f"Expected membership symbol '∈' in {path}")
                self.assertIn("∉", content, f"Expected non-membership symbol '∉' in {path}")
                self.assertIn("⊆", content, f"Expected subset symbol '⊆' in {path}")
                self.assertIn("Pow(S)", content, f"Expected Pow(S) in {path}")

    def test_zf_import_purity(self):
        for path in self.thy_files:
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            # Ensure no extraneous HOL imports
            self.assertNotIn(
                "imports Main",
                content,
                f"Extraneous HOL 'Main' import found in {path}",
            )
            self.assertNotIn(
                "imports HOL",
                content,
                f"Extraneous HOL import found in {path}",
            )


if __name__ == "__main__":
    unittest.main()
