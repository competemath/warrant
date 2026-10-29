#!/usr/bin/env python3
"""Runs WARRANT and a second, independent checker on the same files and reports every disagreement.

usage: differential.py --binary WARRANT --other 'CMD' [--dirs DIR...] [--forge-seconds N --prelude FILE] [--out DIR]

CMD is a shell command that reads one export file on standard input where {file} appears as the redirected path, for
example   'nanoda_bin cfg.json < {file}'   (exit status 0 means the other checker accepts, anything else rejects).
Files come from corpora with a manifest.json (as tools/arena.py) and, with --forge-seconds, from the forge's generators.

WARRANT's decline (exit 2) is not a disagreement. Two kinds of disagreement matter:
  WARRANT accepts, other rejects   the one to chase first: either a bug in WARRANT or a difference of rules
  WARRANT rejects, other accepts   WARRANT is stricter, or incomplete, or the other checker is unsound
A disagreement is a lead, not a verdict: read both explanations. Disagreeing generated files are saved under --out.
"""

import argparse
import gzip
import json
import os
import random
import shlex
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "forge"))


def run_warrant(binary, path, timeout):
    try:
        if path.endswith(".gz"):
            with gzip.open(path, "rb") as f:
                p = subprocess.run([binary, "-"], input=f.read(), capture_output=True, timeout=timeout, check=False)
            err = p.stderr.decode("utf-8", "replace").strip()
        else:
            p = subprocess.run([binary, path], capture_output=True, timeout=timeout, check=False)
            err = p.stderr.decode("utf-8", "replace").strip()
    except subprocess.TimeoutExpired:
        return "timeout", ""
    return {0: "accept", 1: "reject", 2: "decline"}.get(p.returncode, f"crash({p.returncode})"), err[:160]


def run_other(cmd, path, timeout):
    if path.endswith(".gz"):
        with gzip.open(path, "rb") as f, tempfile.NamedTemporaryFile(suffix=".ndjson", delete=False) as t:
            t.write(f.read())
        try:
            return run_other(cmd, t.name, timeout)
        finally:
            os.remove(t.name)
    try:
        p = subprocess.run(
            cmd.replace("{file}", shlex.quote(path)),
            shell=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return "timeout", ""
    out = (p.stderr or p.stdout).decode("utf-8", "replace").strip().splitlines()
    return ("accept" if p.returncode == 0 else "reject"), (out[-1][:160] if out else "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--other", required=True)
    ap.add_argument("--dirs", nargs="*", default=[])
    ap.add_argument("--forge-seconds", type=int, default=0)
    ap.add_argument("--prelude", default=None)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--out", default="differential-out")
    ap.add_argument("--known", default=None, help="JSON list of {file, why}: disagreements already understood")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    cases = []  # (label, path, expectation or None)
    for root in args.dirs:
        with open(os.path.join(root, "manifest.json"), encoding="utf-8") as f:
            for e in json.load(f)["files"]:
                cases.append((os.path.join(root, e["path"]), e["path"], e["expect"]))
    known = {k["file"] for k in json.load(open(args.known, encoding="utf-8"))} if args.known else set()
    stats = {"agree": 0, "decline": 0, "skip": 0, "timeout": 0, "known": 0}
    leads = []

    def judge(label, path, expect, generated=False):
        w, wmsg = run_warrant(args.binary, path, args.timeout)
        o, omsg = run_other(args.other, path, args.timeout)
        if w == "decline":
            stats["decline"] += 1
        elif "skip" in (w, o):
            stats["skip"] += 1
        elif "timeout" in (w, o):
            stats["timeout"] += 1
        elif w == o:
            stats["agree"] += 1
        elif label in known:
            stats["known"] += 1
        else:
            leads.append((label, expect, w, o, wmsg, omsg))
            print(f"DISAGREE {label}: expected {expect}, WARRANT {w} ({wmsg}), other {o} ({omsg})", flush=True)
            if generated:
                dst = os.path.join(args.out, f"{len(leads):03d}-{os.path.basename(label)}.ndjson")
                with open(path, "rb") as src, open(dst, "wb") as out:
                    out.write(src.read())

    for path, label, expect in cases:
        judge(label, path, expect)
    if args.forge_seconds:
        import forge

        prelude = forge.load_lines(args.prelude) if args.prelude else None
        rng = random.Random(args.seed)
        deadline = time.time() + args.forge_seconds
        gens = ["levels", "prop", "stlc"] + (["nat", "natterm", "pirrel", "eta", "quot"] if prelude else [])
        rnd = 0
        with tempfile.TemporaryDirectory() as work:
            while time.time() < deadline:
                rnd += 1
                for g in gens:
                    made = forge.generate(g, rng, min(1 + rnd // 3, 6), prelude, [])
                    if not made:
                        continue
                    text, expect, note = made
                    path = os.path.join(work, "case.ndjson")
                    with open(path, "w", encoding="utf-8") as f:
                        f.write(text)
                    judge(f"{g}-{rnd} ({note})", path, expect, generated=True)
    print(json.dumps({"stats": stats, "disagreements": len(leads)}))
    return 1 if leads else 0


if __name__ == "__main__":
    sys.exit(main())
