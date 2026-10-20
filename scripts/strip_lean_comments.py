#!/usr/bin/env python3
# Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
"""Print a Lean file with comments and string literals blanked, so a grep sees code only."""
import sys


def strip(src: str) -> str:
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif src.startswith("/-", i):
            depth += 1; out.append("  "); i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1; out.append("  "); i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " "); i += 1
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""' + "".join("\n" for c in src[i + 1:j] if c == "\n")); i = j + 1
        else:
            out.append(src[i]); i += 1
    return "".join(out)


for path in sys.argv[1:]:
    for k, line in enumerate(strip(open(path, encoding="utf-8").read()).split("\n"), 1):
        print("%s:%d:%s" % (path, k, line))
