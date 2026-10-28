#!/usr/bin/env python3
"""Structural checks on the kernel's source that the compiler cannot make.

1. No unsafe constructs: no Obj, Marshal, unsafe_* accessors, external declarations, -unsafe flag.
2. One construction site per kind of evidence: each function of Evidence.Mint is referenced exactly once outside
   evidence.ml, from the module that is its minter.
3. The switches that weaken a check are referenced only where they belong.

Exit status 1 with a list of violations.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "src"

MINTERS = {
    "is_type": "tc.ml",
    "typing": "tc.ml",
    "conv": "tc.ml",
    "is_prop": "tc.ml",
    "ind_ok": "ind.ml",
    "quot_ok": "quot.ml",
}

FORBIDDEN = [
    (r"\bObj\.", "Obj"),
    (r"\bMarshal\.", "Marshal"),
    (r"\bunsafe_(get|set|blit|fill|of_string|to_string)\b", "unsafe_* accessor"),
    (r"^\s*external\b", "external declaration"),
    (r"\bLazy\.from_val\b.*\bObj\b", "Obj"),
]

# (pattern, files allowed to contain it)
RESTRICTED = [
    (
        r"Prim\.trust_all",
        {"src/prim.ml", "tools/gen_prims/gen_prims.ml", "test/test_prim.ml"},
    ),
    (r"Env\.assume\b", {"src/ind.ml", "src/env.ml"}),
    (r"Env\.overlay\b", {"src/ind.ml", "src/quot.ml", "src/env.ml"}),
    (r"Tc\.make ~allow_unsafe", {"src/check.ml"}),
]


def strip_comments(text):
    """Blank out OCaml comments (nested) and string literals' contents so prose cannot trigger a rule."""
    out, i, depth = [], 0, 0
    while i < len(text):
        two = text[i : i + 2]
        if two == "(*":
            depth += 1
            out.append("  ")
            i += 2
        elif two == "*)" and depth:
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main():
    problems = []
    files = [p for d in ("src", "bin", "tools", "test") for p in (ROOT / d).rglob("*.ml") if p.is_file()]
    for p in files:
        text = strip_comments(p.read_text(encoding="utf-8"))
        rel = str(p.relative_to(ROOT))
        for pat, what in FORBIDDEN:
            if re.search(pat, text, re.M):
                problems.append(f"{rel}: uses {what}")
        for pat, allowed in RESTRICTED:
            if re.search(pat, text) and rel not in allowed:
                problems.append(f"{rel}: references {pat}, allowed only in {sorted(allowed)}")
    for dune in ROOT.rglob("dune"):
        if "_build" in dune.parts:
            continue
        if re.search(r"-unsafe\b|-unboxed|-nodynlink -unsafe", dune.read_text(encoding="utf-8")):
            problems.append(f"{dune.relative_to(ROOT)}: unsafe compiler flag")
    for fn, owner in MINTERS.items():
        sites = []
        for p in sorted(SRC.glob("*.ml")):
            if p.name == "evidence.ml":
                continue
            text = strip_comments(p.read_text(encoding="utf-8"))
            sites += [p.name for _ in re.finditer(rf"Evidence\.Mint\.{fn}\b", text)]
        if sites != [owner]:
            problems.append(f"Mint.{fn}: construction sites {sites}, expected exactly [{owner!r}]")
    for p in sorted(ROOT.rglob("*.ml")):
        if "_build" in p.parts or p.name == "evidence.ml" or p.parent.name == "src":
            continue
        if re.search(r"Evidence\.Mint", strip_comments(p.read_text(encoding="utf-8"))):
            problems.append(f"{p.relative_to(ROOT)}: constructs evidence outside src/")
    for line in problems:
        print("lint:", line)
    print(f"{len(problems)} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
