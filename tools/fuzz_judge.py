#!/usr/bin/env python3
"""Asks a second checker about the files the fuzzer found.

usage: fuzz_judge.py --binary WARRANT --other 'CMD < {file}' DIR...

For each .ndjson file under DIR (usually fuzz-out/accepted) WARRANT's verdict is taken again with the plain build and the other
checker is run on the same file. A file WARRANT accepts and the other rejects is printed as ACCEPTED-ONLY-BY-WARRANT: either a
soundness bug of WARRANT or a rule the other checker does not have; read both explanations. Files WARRANT refuses and the other
accepts are printed as REFUSED-ONLY-BY-WARRANT (WARRANT is stricter or incomplete). Exit status 1 when there is a first kind.
"""

import argparse
import glob
import os
import shlex
import subprocess
import sys


def warrant(binary, path, timeout):
    try:
        p = subprocess.run([binary, path], capture_output=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return "timeout", ""
    return {0: "accept", 1: "reject", 2: "decline"}.get(p.returncode, f"crash({p.returncode})"), (
        p.stderr.decode("utf-8", "replace").strip().splitlines() or [""]
    )[0][:140]


def other(cmd, path, timeout):
    try:
        p = subprocess.run(
            cmd.replace("{file}", shlex.quote(path)), shell=True, capture_output=True, timeout=timeout, check=False
        )
    except subprocess.TimeoutExpired:
        return "timeout", ""
    out = (p.stderr or p.stdout).decode("utf-8", "replace").strip().splitlines()
    return ("accept" if p.returncode == 0 else "reject"), (out[-1][:140] if out else "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--other", required=True)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("dirs", nargs="+")
    args = ap.parse_args()
    bad = 0
    n = 0
    for d in args.dirs:
        for path in sorted(glob.glob(os.path.join(d, "**", "*.ndjson"), recursive=True)):
            n += 1
            w, wm = warrant(args.binary, path, args.timeout)
            o, om = other(args.other, path, args.timeout)
            if w == "accept" and o == "reject":
                bad += 1
                print(f"ACCEPTED-ONLY-BY-WARRANT {path}\n    other: {om}", flush=True)
            elif w == "reject" and o == "accept":
                print(f"REFUSED-ONLY-BY-WARRANT {path}\n    warrant: {wm}", flush=True)
    print(f"{n} files, {bad} accepted only by WARRANT")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
