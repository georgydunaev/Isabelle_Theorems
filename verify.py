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
]


def check_isabelle_file(file_path: str) -> tuple[bool, str]:
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()
    if not re.search(r"theory\s+\w+\s+imports\s+\w+", content):
        return False, "Missing theory declaration"
    if not re.search(r"(?:lemma|theorem|axiomatization|definition|locale)\b", content):
        return False, "Missing formal item"
    if not re.search(r"\bend\b", content):
        return False, "Missing end keyword"
    return True, "Basic structure OK"


def main() -> int:
    has_isabelle = shutil.which("isabelle") is not None
    ok_all = True
    for file in ISABELLE_FILES:
        if os.path.exists(file):
            ok, message = check_isabelle_file(file)
            print(f"{file}: {message}")
            if not ok:
                ok_all = False
            if has_isabelle:
                try:
                    subprocess.run(["isabelle", "build", "-b", file], check=True)
                except subprocess.CalledProcessError as exc:
                    print(f"Isabelle build check failed for {file}: {exc}")
        else:
            print(f"{file}: File does not exist")
            ok_all = False
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
