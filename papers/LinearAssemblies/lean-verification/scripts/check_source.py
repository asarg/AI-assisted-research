#!/usr/bin/env python3
"""Reject proof placeholders and unapproved shortcuts in delivered Lean sources."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
files = sorted((root / "LinearAssemblies").rglob("*.lean"))
files += [root / "LinearAssemblies.lean", root / "Audit.lean"]


def without_comments(text):
    result = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(result)


for path in files:
    source = without_comments(path.read_text())
    match = re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b", source)
    if match:
        raise SystemExit(f"Disallowed proof token {match.group()} in {path.relative_to(root)}")
    if "set_option autoImplicit false" not in source and path.name != "LinearAssemblies.lean":
        raise SystemExit(f"Missing autoImplicit guard in {path.relative_to(root)}")

print(f"Source policy checks passed for {len(files)} Lean files.")
