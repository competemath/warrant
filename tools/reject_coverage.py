#!/usr/bin/env python3
"""Every place the checker can refuse or decline a file must be reached by some test, or be listed as unreachable with the reason.

usage: reject_coverage.py --binary PATH [--allow tools/reject_unreachable.json] DIR...

The checker's refusals are `reject "..."` calls in src/*.ml, its declines are `decline "..."` and `malformed "..."` calls
and `Declined "..."` values. Each message is cut at its format specifiers (%s, %d, ...)
and the longest literal piece is the needle. The files of every DIR (a corpus with a manifest.json, as tools/arena.py
reads) are run, and a site counts as reached when its needle occurs in the explanation of some refusal. A site no file
reaches, and that the allow list does not explain, is a check without a test: the exit status is 1.

The allow list holds {file, needle, why}; "why" says why no input can reach the site (an internal invariant, a
guard that the types already enforce, ...). A check that merely lacks a test does not belong there: write the test.
"""

import argparse
import glob
import gzip
import json
import os
import re
import subprocess
import sys

SITE = re.compile(r'\b(?:reject|decline|malformed|Declined)\s+"((?:[^"\\]|\\.)*)"', re.S)
SPEC = re.compile(r"%[0-9]*[sdl]")


def sites(src_dir):
    out = []
    for path in sorted(glob.glob(os.path.join(src_dir, "*.ml"))):
        text = open(path, encoding="utf-8").read()
        for m in SITE.finditer(text):
            raw = re.sub(r"\\\n[ \t]*", "", m.group(1)).replace("\\n", "\n").replace("\\ ", " ").replace('\\"', '"')
            pieces = [p for p in SPEC.split(raw) if p.strip()]
            needle = max(pieces, key=len).strip() if pieces else raw
            out.append((os.path.relpath(path), text[: m.start()].count("\n") + 1, needle))
    return out


def explanations(binary, dirs, timeout):
    seen = []
    for root in dirs:
        with open(os.path.join(root, "manifest.json"), encoding="utf-8") as f:
            entries = json.load(f)["files"]
        for e in entries:
            path = os.path.join(root, e["path"])
            env = {**os.environ, **e["env"]} if e.get("env") else None
            try:
                if path.endswith(".gz"):
                    with gzip.open(path, "rb") as f:
                        p = subprocess.run([binary, "-"], input=f.read(), capture_output=True, timeout=timeout, env=env)
                else:
                    p = subprocess.run([binary, path], capture_output=True, timeout=timeout, env=env)
            except subprocess.TimeoutExpired:
                continue
            seen.append(p.stderr.decode("utf-8", "replace"))
    return "\n".join(seen)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--src", default="src")
    ap.add_argument("--allow", default=None)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("dirs", nargs="+")
    args = ap.parse_args()
    allowed = json.load(open(args.allow, encoding="utf-8")) if args.allow else []
    known = {(a["file"], a["needle"]) for a in allowed}
    blob = explanations(args.binary, args.dirs, args.timeout)
    every = sites(args.src)
    missing = [(f, ln, n) for f, ln, n in every if n not in blob and (f, n) not in known]
    stale = [a for a in allowed if a["needle"] in blob]
    print(f"{len(every)} refusal sites, {len(known)} listed as unreachable, {len(missing)} without a test")
    for f, ln, n in missing:
        print(f"NO TEST REACHES {f}:{ln}  {n[:100]!r}")
    for a in stale:
        print(f"listed as unreachable but reached: {a['file']}  {a['needle'][:80]!r}")
    return 1 if missing or stale else 0


if __name__ == "__main__":
    sys.exit(main())
