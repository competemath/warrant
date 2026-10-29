#!/usr/bin/env python3
"""Runs the checker over a corpus of lean4export files and compares each verdict with the manifest.

usage: arena.py --binary PATH [--timeout SECONDS] [--jobs N] DIR...

Each DIR holds a manifest.json: {"files": [{"path": "bad/x.ndjson", "expect": "reject", ...}]}.
  expect:       accept | reject | either   (either: accept or reject, but never crash)
  may_decline:  true when the checker is allowed to exit 2 (decline) instead of the expected verdict
  may_timeout:  true when running out of time is acceptable (a timeout counts as a decline)
  msg:          a substring the checker's explanation must contain (pins a test to the check that must fire)
  env:          environment variables to set for this file (e.g. WARRANT_FUEL, WARRANT_CACHE_LIMIT, OCAMLRUNPARAM)
Exit codes of the checker: 0 accept, 1 reject, 2 decline. Anything else (crash, signal) is a failure, and so is any
verdict that contradicts the manifest: accepting what must be rejected is the failure that matters most.
"""

import argparse
import gzip
import json
import os
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor

VERDICT = {0: "accept", 1: "reject", 2: "decline"}


def run_one(binary, root, entry, timeout, extra_env=None):
    path = os.path.join(root, entry["path"])
    start = time.time()
    proc_out = ""
    env = {**os.environ, **(extra_env or {}), **entry.get("env", {})} if (extra_env or entry.get("env")) else None
    try:
        if path.endswith(".gz"):  # large files are stored compressed and fed on standard input
            with gzip.open(path, "rb") as f:
                data = f.read()
            proc = subprocess.run([binary, "-"], input=data, capture_output=True, timeout=timeout, check=False, env=env)
            proc.stdout, proc.stderr = proc.stdout.decode("utf-8", "replace"), proc.stderr.decode("utf-8", "replace")
        else:
            proc = subprocess.run([binary, path], capture_output=True, text=True, timeout=timeout, check=False, env=env)
        code, msg = proc.returncode, (proc.stderr.strip() or proc.stdout.strip())[:300]
        proc_out = proc.stderr + proc.stdout
    except subprocess.TimeoutExpired:
        code, msg = "timeout", "timeout"
    got = VERDICT.get(code, "timeout" if code == "timeout" else f"crash({code})")
    expect = entry["expect"]
    if got == expect or (expect == "either" and got in ("accept", "reject")):
        ok = True
    elif got == "decline" and entry.get("may_decline"):
        ok = True
    elif got == "timeout" and entry.get("may_timeout"):
        ok = True
    else:
        ok = False
    if ok and entry.get("msg") and entry["msg"] not in (proc_out if code != "timeout" else ""):
        ok = False
    return {
        "path": entry["path"],
        "expect": expect,
        "got": got,
        "ok": ok,
        "secs": round(time.time() - start, 1),
        "msg": msg,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument(
        "--filter", action="append", default=[], help="only the entries whose path contains this (repeatable)"
    )
    ap.add_argument(
        "--exclude", action="append", default=[], help="leave out the entries whose path contains this (repeatable)"
    )
    ap.add_argument(
        "--fail-fast", action="store_true", help="stop starting files after the first failure (the mutation tester)"
    )
    ap.add_argument("--env", action="append", default=[], help="KEY=VALUE set for every file (repeatable)")
    ap.add_argument("dirs", nargs="+")
    args = ap.parse_args()
    extra_env = dict(kv.split("=", 1) for kv in args.env)
    stop = threading.Event()

    def one(e, r):
        if stop.is_set():
            return {"path": e["path"], "expect": e["expect"], "got": "skipped", "ok": True, "secs": 0, "msg": ""}
        res = run_one(args.binary, r, e, args.timeout, extra_env)
        if args.fail_fast and not res["ok"]:
            stop.set()
        return res

    results = []
    for root in args.dirs:
        with open(os.path.join(root, "manifest.json"), encoding="utf-8") as f:
            entries = json.load(f)["files"]
        if args.exclude:
            entries = [e for e in entries if not any(x in e["path"] for x in args.exclude)]
        if args.filter:
            entries = [e for e in entries if any(x in e["path"] for x in args.filter)]
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            results += list(pool.map(lambda e, r=root: one(e, r), entries))
    bad = [r for r in results if not r["ok"]]
    for r in results:
        if not r["ok"] or not args.quiet:
            flag = "ok  " if r["ok"] else "FAIL"
            print(
                f"{flag} {r['path']:62} expect={r['expect']:7} got={r['got']:8} {r['secs']:6}s {r['msg'][:100] if not r['ok'] else ''}"
            )
    accepted_bad = [r for r in bad if r["expect"] == "reject" and r["got"] == "accept"]
    print(
        f"total {len(results)}  ok {len(results) - len(bad)}  fail {len(bad)}  (accepted-but-must-reject: {len(accepted_bad)})"
    )
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
