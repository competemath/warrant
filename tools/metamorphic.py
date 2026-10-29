#!/usr/bin/env python3
"""Metamorphic test of the checker: the same file written differently must get the same verdict.

usage: metamorphic.py --binary PATH [--seed N] [--max-bytes N] [--timeout S] DIR...

Each DIR is a corpus with a manifest.json (as tools/arena.py reads). Every file is run unchanged and then in variants
that say the same thing in other words:
  renumber   every name, level and expression index is replaced by another number (order kept, gaps added)
  reorder    the keys of every object are in another order, with other spacing, and the lines end in CRLF
  both       the two together
A .gz file is read compressed. A variant the checker judges differently from the original (accept, reject or decline) is a finding: the verdict depended
on something that is not the meaning of the file (an index, a key order, a line ending). Files that are larger
than --max-bytes, or that the checker does not finish in --timeout seconds are left out.
"""

import argparse
import gzip
import json
import os
import random
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

NAME_KEYS = {"name", "pre", "typeName", "induct", "ctor", "param"}
NAME_LIST_KEYS = {"all", "ctors", "levelParams"}
LEVEL_KEYS = {"sort", "succ"}
LEVEL_LIST_KEYS = {"us", "max", "imax"}
EXPR_KEYS = {"type", "value", "body", "fn", "arg", "struct", "expr", "rhs"}


def renumber(o, kind_of_line, f):
    """The object with every index mapped; [f] is a dict of three functions, one per kind of index."""
    if isinstance(o, dict):
        out = {}
        for k, v in o.items():
            if k in ("in", "il", "ie") and isinstance(v, int):
                if v < 0:
                    raise ValueError("a negative index: the file is about exactly that")
                out[k] = f[{"in": "name", "il": "level", "ie": "expr"}[k]](v)
            elif k in NAME_KEYS and isinstance(v, int) and not isinstance(v, bool):
                out[k] = f["name"](v)
            elif k in NAME_LIST_KEYS and isinstance(v, list):
                out[k] = [f["name"](x) if isinstance(x, int) else renumber(x, kind_of_line, f) for x in v]
            elif k in LEVEL_KEYS and isinstance(v, int) and not isinstance(v, bool):
                out[k] = f["level"](v)
            elif k in LEVEL_LIST_KEYS and isinstance(v, list):
                out[k] = [f["level"](x) if isinstance(x, int) else renumber(x, kind_of_line, f) for x in v]
            elif k in EXPR_KEYS and isinstance(v, int) and not isinstance(v, bool):
                out[k] = f["expr"](v)
            else:
                out[k] = renumber(v, kind_of_line, f)
        return out
    if isinstance(o, list):
        return [renumber(x, kind_of_line, f) for x in o]
    return o


def reorder(o, rng):
    if isinstance(o, dict):
        items = list(o.items())
        rng.shuffle(items)
        return {k: reorder(v, rng) for k, v in items}
    if isinstance(o, list):
        return [reorder(x, rng) for x in o]
    return o


def no_duplicates(pairs):
    keys = [k for k, _ in pairs]
    if len(keys) != len(set(keys)):
        raise ValueError("a repeated key: the file is about exactly that")
    return dict(pairs)


def variant(text, kind, rng):
    maps = {
        "name": lambda i: 0 if i == 0 else i * 3 + 11,
        "level": lambda i: 0 if i == 0 else i * 5 + 2,
        "expr": lambda i: i * 7 + 3,
    }
    out = []
    for line in text.split("\n"):
        if not line.strip():
            if kind == "renumber":
                out.append(line)  # a blank line is skipped; one made of a carriage return only is not (declined)
            continue
        o = json.loads(line, object_pairs_hook=no_duplicates)
        if kind in ("renumber", "both") and "meta" not in o:
            o = renumber(o, None, maps)
        if kind in ("reorder", "both"):
            o = reorder(o, rng)
            sep = rng.choice([(",", ":"), (", ", ": "), (" , ", " : ")])
            out.append(json.dumps(o, separators=sep, ensure_ascii=rng.random() < 0.5))
        else:
            out.append(json.dumps(o, separators=(",", ":")))
    return ("\r\n" if kind in ("reorder", "both") else "\n").join(out)


def verdict(binary, path, timeout):
    try:
        p = subprocess.run([binary, path], capture_output=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return "timeout", ""
    return {0: "accept", 1: "reject", 2: "decline"}.get(p.returncode, f"crash({p.returncode})"), (
        p.stderr.decode("utf-8", "replace").strip().splitlines() or [""]
    )[0][:120]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--max-bytes", type=int, default=3_000_000)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--work", default="/tmp/metamorphic")
    ap.add_argument("dirs", nargs="+")
    args = ap.parse_args()
    os.makedirs(args.work, exist_ok=True)
    files = []
    for root in args.dirs:
        with open(os.path.join(root, "manifest.json"), encoding="utf-8") as f:
            for e in json.load(f)["files"]:
                path = os.path.join(root, e["path"])
                if os.path.getsize(path) <= args.max_bytes:
                    files.append((path, e["path"]))

    def one(item):
        path, label = item
        rng = random.Random(f"{args.seed}:{label}")
        if path.endswith(".gz"):
            with gzip.open(path, "rt", encoding="utf-8") as f:
                text = f.read()
            path = os.path.join(args.work, label.replace("/", "_") + ".plain")
            with open(path, "w", encoding="utf-8", newline="") as f:
                f.write(text)
        else:
            with open(path, encoding="utf-8") as f:
                text = f.read()
        base, bmsg = verdict(args.binary, path, args.timeout)
        if base == "timeout":
            return []
        found = []
        for kind in ("renumber", "reorder", "both"):
            try:
                v = variant(text, kind, rng)
            except (json.JSONDecodeError, KeyError, TypeError, ValueError):
                continue  # a file that is not well-formed JSON on every line is its own test
            vp = os.path.join(args.work, f"{label.replace('/', '_')}.{kind}.ndjson")
            with open(vp, "w", encoding="utf-8", newline="") as f:
                f.write(v)
            got, msg = verdict(args.binary, vp, args.timeout)
            os.remove(vp)
            if got != base and got != "timeout":
                found.append((label, kind, base, bmsg, got, msg))
        return found

    findings = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for r in pool.map(one, files):
            for label, kind, base, bmsg, got, msg in r:
                print(f"DIFFERENT {label} [{kind}]: {base} ({bmsg}) became {got} ({msg})", flush=True)
                findings.append(label)
    print(f"{len(files)} files, {len(findings)} variants judged differently")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
