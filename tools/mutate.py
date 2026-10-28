#!/usr/bin/env python3
"""Mutation test of the kernel's own tests: apply one small source mutation at a time, rebuild, run the arena corpus
(without the slow perf files), the regressions and a short forge round, and report which mutants nothing noticed.

usage: mutate.py --work DIR [--count N] [--seed S] [--files src/tc.ml src/level.ml ...] [--allow tools/mutation_equivalents.json]

DIR is a scratch copy of the repository (it is rewritten). A mutant is KILLED when the build still succeeds and some test
fails, UNVIABLE when it does not build, SURVIVED otherwise. Survivors are the test suite's blind spots: each one is either
an equivalent mutant or a missing test. With --allow, a survivor listed there (same file, same source line, same
replacement, with the reason it changes nothing observable) is not a failure; any other survivor makes the exit code 1.
"""

import argparse
import json
import pathlib
import random
import re
import subprocess
import sys

OPERATORS = [
    (r"&&", "||"),
    (r"\|\|", "&&"),
    (r"<>", "="),
    (r"(?<![<>=!])=(?![=>])", "<>"),
    (r"\bnot \(", "("),
    (r"\bk <= j\b", "k < j"),
    (r"\btrue\b", "false"),
    (r"\bfalse\b", "true"),
    (r"\bi < np\b", "i <= np"),
    (r"\bi = np\b", "i = np + 1"),
    (r"List\.length args <> np\b", "List.length args = np"),
    (r"\bf != f0\b", "f == f0"),
    (r"!=", "=="),
]


def sh(cmd, cwd, timeout=600):
    return subprocess.run(cmd, cwd=cwd, shell=True, capture_output=True, text=True, timeout=timeout, check=False)


def candidates(path):
    text = path.read_text(encoding="utf-8")
    out = []
    in_comment = 0
    pos = 0
    for lineno, line in enumerate(text.splitlines(keepends=True)):
        stripped = line
        was_in_comment = in_comment > 0
        in_comment += stripped.count("(*") - stripped.count("*)")
        if was_in_comment or in_comment > 0 or "(*" in stripped or '"' in stripped:
            pos += len(line)
            continue
        for pat, rep in OPERATORS:
            if pat.startswith("(?<![<>=!])=") and not re.search(r"\bif\b|&&|\|\||\bwhen\b", line):
                continue  # a binding, not a comparison: the mutant would not compile
            for m in re.finditer(pat, line):
                out.append((str(path), pos + m.start(), pos + m.end(), rep, lineno + 1))
        pos += len(line)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", required=True)
    ap.add_argument("--count", type=int, default=40)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--files", nargs="*", default=["src/tc.ml", "src/level.ml", "src/ind.ml", "src/quot.ml"])
    ap.add_argument("--out", default="mutants.json")
    ap.add_argument("--allow", default=None, help="JSON list of known equivalent mutants")
    args = ap.parse_args()
    work = pathlib.Path(args.work)
    cands = []
    for f in args.files:
        cands += candidates(work / f)
    random.Random(args.seed).shuffle(cands)
    results = []
    sh("dune build 2>&1 | tail -3", work)
    for path, a, b, rep, lineno in cands[: args.count]:
        p = pathlib.Path(path)
        original = p.read_text(encoding="utf-8")
        p.write_text(original[:a] + rep + original[b:], encoding="utf-8")
        try:
            built = sh("dune build 2>&1 | head -3", work)
            if built.stdout.strip():
                status = "unviable"
            else:
                binary = work / "_build/default/bin/main.exe"
                arena = sh(
                    f"python3 tools/arena.py --binary {binary} --timeout 20 --jobs 4 --quiet tests/arena tests/regressions",
                    work,
                    timeout=1200,
                )
                killed = arena.returncode != 0
                if not killed:
                    forge = sh(
                        f"python3 tools/forge/forge.py --binary {binary} --seconds 15 --seed 5 --out /tmp/mut-forge --prelude tests/arena/good/init-prelude.ndjson --inductive-sources tests/arena/good/tutorial/044_natDef.ndjson tests/arena/good/tutorial/045_rbTreeDef.ndjson tests/arena/good/tutorial/069_eqRec.ndjson tests/arena/good/tutorial/121_rTreeRec.ndjson tests/arena/good/tutorial/070_nRec.ndjson tests/arena/good/tutorial/074_existsRec.ndjson tests/arena/good/tutorial/123_accRecType.ndjson tests/arena/good/tutorial/068_punitRec.ndjson",
                        work,
                        timeout=300,
                    )
                    killed = forge.returncode != 0
                if not killed:
                    unit = sh("dune test --force", work, timeout=600)
                    killed = unit.returncode != 0
                status = "killed" if killed else "survived"
        except subprocess.TimeoutExpired:
            status = "killed"  # a mutant that hangs the tests is noticed
        finally:
            p.write_text(original, encoding="utf-8")
        context = original.splitlines()[lineno - 1].strip()
        rec = {
            "file": str(p.relative_to(work)),
            "line": lineno,
            "context": context,
            "from": original[a:b],
            "to": rep,
            "status": status,
        }
        results.append(rec)
        print(json.dumps(rec), flush=True)
    summary = {s: sum(1 for r in results if r["status"] == s) for s in ("killed", "survived", "unviable")}
    pathlib.Path(args.out).write_text(json.dumps({"summary": summary, "mutants": results}, indent=1), encoding="utf-8")
    print(json.dumps(summary))
    allowed = json.loads(pathlib.Path(args.allow).read_text(encoding="utf-8")) if args.allow else []
    known = {(a["file"], a["context"], a["from"], a["to"]) for a in allowed}
    new = [
        r for r in results if r["status"] == "survived" and (r["file"], r["context"], r["from"], r["to"]) not in known
    ]
    for r in new:
        print(f"SURVIVOR not in the allow list: {r['file']}:{r['line']}  {r['context']}   [{r['from']} -> {r['to']}]")
    return 1 if new else 0


if __name__ == "__main__":
    sys.exit(main())
