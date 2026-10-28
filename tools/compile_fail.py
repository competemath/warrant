#!/usr/bin/env python3
"""Each file in tests/compile-fail must FAIL to compile, with the error the file's first line expects.

They are attempts to do what the evidence discipline forbids: build an evidence value, a cached term field or a name by
hand, or add a declaration while leaving out one of the facts it needs. If one of them compiles, a check can be
forged or skipped without the compiler noticing, and this exits 1.

usage: compile_fail.py   (after `dune build`; uses ocamlfind from the active opam switch)
"""

import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
OBJS = ROOT / "_build" / "default" / "src" / ".warrant.objs" / "byte"


def main():
    bad = 0
    files = sorted((ROOT / "tests" / "compile-fail").glob("*.ml"))
    for f in files:
        text = f.read_text(encoding="utf-8")
        m = re.match(r"\(\* expect: (.*) \*\)", text)
        expect = m.group(1) if m else ""
        with tempfile.TemporaryDirectory() as tmp:
            cmd = [
                "ocamlfind",
                "ocamlc",
                "-package",
                "zarith,yojson",
                "-I",
                str(OBJS),
                "-c",
                "-o",
                str(pathlib.Path(tmp) / "x.cmo"),
                str(f),
            ]
            p = subprocess.run(cmd, capture_output=True, text=True, check=False)
        out = p.stdout + p.stderr
        if p.returncode == 0:
            print(f"FAIL {f.name}: compiled, but it must not")
            bad += 1
        elif expect and expect not in out:
            print(f"FAIL {f.name}: failed to compile, but not with {expect!r}:\n{out}")
            bad += 1
        else:
            print(f"ok   {f.name}")
    print(f"{len(files)} snippets, {bad} problem(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
