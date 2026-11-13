#!/usr/bin/env python3
"""Automated sanity check and verification script for Isabelle_Theorems."""

import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))

ISABELLE_FILES = [
    os.path.join(ROOT, "Jech.thy"),
    os.path.join(ROOT, "Jech_clean.thy"),
    os.path.join(ROOT, "examples", "Example1.thy"),
    os.path.join(ROOT, "examples", "Example2.thy"),
    os.path.join(ROOT, "examples", "example1.thy"),
]

ALLOWED_IMPORTS = {"ZF", "Jech", "Jech_clean"}
DISALLOWED_IMPORTS = {"Main", "HOL"}


def check_theory_header(content: str, file_path: str) -> tuple[bool, str]:
    match = re.search(r"theory\s+(\w+)\s+imports\s+([\w\s]+)\bbegin", content)
    if not match:
        return False, "Missing or invalid theory declaration"
    theory_name, imports_str = match.group(1), match.group(2)
    imported_theories = [imp.strip() for imp in imports_str.split() if imp.strip()]
    for imp in imported_theories:
        if imp in DISALLOWED_IMPORTS:
            return False, f"Extraneous HOL import detected: {imp} (expected ZF base)"
        if imp not in ALLOWED_IMPORTS:
            return False, f"Unexpected import: {imp}"
    return True, f"Header OK (theory {theory_name} imports {' '.join(imported_theories)})"


def check_proof_closures(content: str) -> tuple[bool, str]:
    proof_count = len(re.findall(r"\bproof\b", content))
    qed_count = len(re.findall(r"\bqed\b", content))
    if proof_count != qed_count:
        return False, f"Mismatched proof/qed count: {proof_count} proof vs {qed_count} qed"
    return True, f"Proof blocks balanced ({proof_count} proof/qed pairs)"


def check_no_unproved(content: str) -> tuple[bool, str]:
    if re.search(r"\b(?:sorry|oops)\b", content):
        return False, "Unfinished proof marker found (sorry or oops)"
    return True, "No sorry or oops"


def check_symbol_integrity(content: str) -> tuple[bool, str]:
    mangled_patterns = [
        (r"\bWW\b", "Mangled membership token WW (missing \\<in> / in symbol)"),
        (r"\bWPow\b", "Mangled membership token WPow (missing \\<in> / in symbol)"),
    ]
    for pattern, desc in mangled_patterns:
        if re.search(pattern, content):
            return False, desc
    return True, "Symbol integrity OK"


def check_isabelle_file(file_path: str) -> tuple[bool, str]:
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    ok, msg = check_theory_header(content, file_path)
    if not ok:
        return False, msg

    if not re.search(r"(?:lemma|theorem|axiomatization|definition|locale)\b", content):
        return False, "Missing formal item"

    if not re.search(r"\bend\b", content):
        return False, "Missing end keyword"

    ok, msg = check_proof_closures(content)
    if not ok:
        return False, msg

    ok, msg = check_no_unproved(content)
    if not ok:
        return False, msg

    ok, msg = check_symbol_integrity(content)
    if not ok:
        return False, msg

    return True, "All structural and syntax checks passed"


def main() -> int:
    has_isabelle = shutil.which("isabelle") is not None
    ok_all = True
    for file in ISABELLE_FILES:
        if os.path.exists(file):
            ok, message = check_isabelle_file(file)
            print(f"{os.path.basename(file)}: {message}")
            if not ok:
                ok_all = False
            if has_isabelle:
                try:
                    subprocess.run(["isabelle", "build", "-b", file], check=True)
                except subprocess.CalledProcessError as exc:
                    print(f"Isabelle build check failed for {file}: {exc}")
                    ok_all = False
        else:
            print(f"{file}: File does not exist")
            ok_all = False
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
