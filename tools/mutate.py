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
    (r"(?<![<>=!:|])==(?!=)", "!="),
    (r"<=", "<"),
    (r">=", ">"),
    (r"(?<![-<>=|])>(?![=>|])", ">="),
    (r"(?<![<\-])<(?![=>\-])", "<="),
    (r"\bList\.for_all\b", "List.exists"),
    (r"\bList\.exists\b", "List.for_all"),
    (r"\bi \+ 1\b", "i"),
]


def sh(cmd, cwd, timeout=600):
    return subprocess.run(cmd, cwd=cwd, shell=True, capture_output=True, text=True, timeout=timeout, check=False)


def code_mask(text):
    """mask[i] is True when text[i] is code: not inside a comment (they nest) or a string literal."""
    mask = [True] * len(text)
    i, depth, n = 0, 0, len(text)
    while i < n:
        two = text[i : i + 2]
        if depth == 0 and text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                mask[k] = False
            i = j + 1
        elif two == "(*":
            depth += 1
            mask[i] = mask[i + 1] = False
            i += 2
        elif depth > 0 and two == "*)":
            depth -= 1
            mask[i] = mask[i + 1] = False
            i += 2
        elif depth > 0:
            mask[i] = False
            if text[i] == '"':  # a string inside a comment may contain "*)"
                j = i + 1
                while j < n and text[j] != '"':
                    mask[j] = False
                    j += 2 if text[j] == "\\" else 1
                if j < n:
                    mask[j] = False
                i = j + 1
            else:
                i += 1
        else:
            i += 1
    return mask


def candidates(path):
    text = path.read_text(encoding="utf-8")
    mask = code_mask(text)
    out = []
    pos = 0
    for lineno, line in enumerate(text.splitlines(keepends=True)):
        for pat, rep in OPERATORS:
            if pat.startswith("(?<![<>=!])=") and not re.search(r"\bif\b|&&|\|\||\bwhen\b", line):
                continue  # a binding, not a comparison: the mutant would not compile
            for m in re.finditer(pat, line):
                a, b = pos + m.start(), pos + m.end()
                if all(mask[a:b]):
                    out.append((str(path), a, b, rep, lineno + 1))
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
    ap.add_argument(
        "--shard", default="0/1", help="K/N: take every N-th mutant starting at K (to run N copies side by side)"
    )
    ap.add_argument(
        "--only",
        default=None,
        help="JSON list of {file, context, from, to}: try just these (survivors of an earlier run)",
    )
    ap.add_argument("--fast", action="store_true", help="first stage only on the arena's bad files and the regressions")
    args = ap.parse_args()
    work = pathlib.Path(args.work)
    cands = []
    for f in args.files:
        cands += candidates(work / f)
    if args.only:
        wanted = {
            (w["file"], w["context"], w["from"], w["to"]) for w in json.loads(pathlib.Path(args.only).read_text())
        }

        def key(c):
            path, a, b, rep, lineno = c
            text = pathlib.Path(path).read_text(encoding="utf-8")
            return (str(pathlib.Path(path).relative_to(work)), text.splitlines()[lineno - 1].strip(), text[a:b], rep)

        cands = [c for c in cands if key(c) in wanted]
    random.Random(args.seed).shuffle(cands)
    shard, shards = (int(x) for x in args.shard.split("/"))
    cands = [c for k, c in enumerate(cands) if k % shards == shard]
    results = []
    sh("dune build 2>&1 | tail -3", work)
    for path, a, b, rep, lineno in cands[: args.count or None]:
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
                    f"python3 tools/arena.py --binary {binary} --timeout 20 --jobs 4 --quiet --filter bad/ --filter bugs/ tests/arena",
                    work,
                    timeout=1200,
                )
                killed = arena.returncode != 0
                if not killed:
                    regress = sh(
                        f"python3 tools/arena.py --binary {binary} --timeout 20 --jobs 4 --quiet tests/regressions",
                        work,
                        timeout=1200,
                    )
                    killed = regress.returncode != 0
                if not killed and not args.fast:
                    arena = sh(
                        f"python3 tools/arena.py --binary {binary} --timeout 20 --jobs 4 --quiet tests/arena",
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
