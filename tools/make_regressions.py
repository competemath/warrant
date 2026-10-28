#!/usr/bin/env python3
"""Regenerates tests/regressions: one small file per unexpected behaviour found, each pinned to the check that must
fire (the manifest's `msg`). Every entry says what happened. Run from the repository root; the output is committed.
"""

import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "forge"))
from ndjson import Builder  # noqa: E402

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tests", "regressions")
os.makedirs(OUT, exist_ok=True)
files = []


def add(name, text, expect, why, msg=None, may_decline=False):
    with open(os.path.join(OUT, name), "w", encoding="utf-8") as f:
        f.write(text)
    e = {"path": name, "expect": expect, "why": why}
    if msg:
        e["msg"] = msg
    if may_decline:
        e["may_decline"] = True
    files.append(e)


META = Builder.META
head = json.dumps(META, separators=(",", ":"))

add(
    "negative-nat-literal.ndjson",
    head + '\n{"ie":0,"natVal":"-5"}\n',
    "reject",
    "Z.of_string accepts a sign and a 0x prefix: a negative natural literal would reach the arithmetic. Literals are digits only.",
    msg="bad natural literal",
    may_decline=True,
)
add(
    "hex-nat-literal.ndjson",
    head + '\n{"ie":0,"natVal":"0x10"}\n',
    "reject",
    "same, hexadecimal.",
    msg="bad natural literal",
    may_decline=True,
)
add(
    "duplicate-key.ndjson",
    head + '\n{"in":1,"in":2,"str":{"pre":0,"str":"x"}}\n',
    "reject",
    "an object with a repeated key is read differently by different tools; refused instead of picking one reading.",
    msg="duplicate key",
    may_decline=True,
)
add(
    "negative-bvar.ndjson",
    head + '\n{"ie":0,"bvar":-1}\n',
    "reject",
    "a negative de Bruijn index would corrupt the cached loose-variable range.",
    msg="natural number",
    may_decline=True,
)
add(
    "negative-projection-index.ndjson",
    head
    + '\n{"in":1,"str":{"pre":0,"str":"S"}}\n{"ie":0,"bvar":0}\n{"ie":1,"proj":{"typeName":1,"idx":-1,"struct":0}}\n',
    "reject",
    "a negative projection index raised Invalid_argument from List.nth, exiting with the runtime's own code 2.",
    msg="natural number",
    may_decline=True,
)

add(
    "empty-file.ndjson",
    "",
    "decline",
    "an empty file was accepted: with no declarations there is nothing to accept, and no format was declared.",
    msg="empty file",
)
add(
    "no-meta.ndjson",
    '{"in":1,"str":{"pre":0,"str":"x"}}\n',
    "decline",
    "a file whose first line is not the meta line does not say which format version it is.",
    msg="meta line",
)

from forge import load_lines, nat_claim  # noqa: E402

PRELUDE = load_lines(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tests", "arena", "good", "init-prelude.ndjson")
)
for op, x, y, why in [
    ("Nat.pow", 2, 100000000, "an exponent of a hundred million would build a number of that many bits"),
    ("Nat.pow", 10**30, 5000000, "a base of a hundred bits to a five-million power overruns the size cap"),
]:
    text, _, _ = nat_claim(PRELUDE, op, x, y, 1, True)
    add(
        f"nat-{op.split('.')[1]}-too-large-{y}.ndjson",
        text,
        "decline",
        why + ": the result is refused (a decline), never computed and never guessed.",
        msg="too large",
    )

# a type written as a beta redex must still be compared as what it reduces to
b = Builder()
b.definition(
    "d",
    [],
    ("app", ("lam", ("sort", ("succ", 0)), ("sort", ("succ", 0))), ("sort", 0)),
    ("sort", ("succ", ("succ", ("succ", ("succ", 0))))),
)
add(
    "beta-sort-mismatch.ndjson",
    b.text(),
    "reject",
    "Sort 4 is declared to have type (fun x => Sort 1) Prop, which reduces to Sort 1 while Sort 4 : Sort 5. A quick 'different sorts' "
    "verdict after reduction must stay a rejection (found by mutation testing: flipping it to 'equal' survived every test).",
    msg="the value does not have the declared type",
)

# a safe declaration may not mention an unsafe constant
b = Builder()
b.axiom("U", [], ("sort", 0), unsafe=True)
b.axiom("T", [], ("sort", ("succ", 0)), unsafe=False)
b.definition("d", [], ("sort", ("succ", 0)), ("const", "U", []))
add(
    "safe-uses-unsafe.ndjson",
    b.text(),
    "reject",
    "an unsafe or partial constant is recorded with its type only, and no safe declaration can mention it.",
    msg="unsafe or partial",
)


# a file that redefines Nat.add keeps no arithmetic shortcut for it
def fake_nat_add():
    src = os.path.join(
        os.path.dirname(os.path.abspath(__file__)),
        "..",
        "tests",
        "arena",
        "good",
        "other",
        "nat-lit-add.ndjson",
    )
    lines = open(src, encoding="utf-8").read().splitlines()
    objs = [json.loads(x) for x in lines]
    names = {}
    for o in objs:
        if "in" in o and "str" in o:
            pre = names.get(o["str"]["pre"], "")
            names[o["in"]] = (pre + "." if pre else "") + o["str"]["str"]
    inv = {v: k for k, v in names.items()}
    nat_expr = next(
        o["ie"]
        for o in objs
        if "ie" in o and "const" in o and o["const"]["name"] == inv["Nat"] and not o["const"]["us"]
    )
    top = max(o["ie"] for o in objs if "ie" in o)
    nm = max(o["in"] for o in objs if "in" in o) + 1
    bv1 = {"ie": top + 1, "bvar": 1}
    inner = {
        "ie": top + 2,
        "lam": {
            "binderInfo": "default",
            "body": top + 1,
            "name": inv["Nat"],
            "type": nat_expr,
        },
    }
    outer = {
        "ie": top + 3,
        "lam": {
            "binderInfo": "default",
            "body": top + 2,
            "name": inv["Nat"],
            "type": nat_expr,
        },
    }
    out = []
    for ln, o in zip(lines, objs):
        if "def" in o and names.get(o["def"]["name"]) == "Nat.add":
            for extra in (bv1, inner, outer):
                out.append(json.dumps(extra, separators=(",", ":"), sort_keys=True))
            o["def"]["value"] = top + 3
            out.append(json.dumps(o, separators=(",", ":"), sort_keys=True))
        else:
            out.append(ln)
    del nm
    return "\n".join(out) + "\n"


add(
    "fake-nat-add.ndjson",
    fake_nat_add(),
    "reject",
    "Nat.add is redefined as fun a b => a, and the file claims Nat.add 123456789 987654321 = 1111111110 by rfl. With the "
    "shortcut keyed on the name the kernel would take the sum from GMP and accept; the fingerprint of the redefined "
    "constant is not the genuine one, so literals are unfolded through the file's own definition and the claim fails.",
    msg="the value does not have the declared type",
)

# files cut from an official export with tools/slice.py (kept compressed; arena.py feeds them on standard input)
files.append(
    {
        "path": "init-int32-rxc-hassize.ndjson.gz",
        "expect": "accept",
        "why": "Init's _private.Init.Data.Range.Polymorphic.SInt.0.Int32.instRxcHasSize_eq (toolchain 4.34.0-rc2) never "
        "finished: comparing `Nat.sub A B` with `inst.1 a b` unfolded Nat.sub, which forces whnf of B = a bit-vector "
        "value mod 2^32 and peels 2^31 successors. The kernel reduces the projection application first "
        "(type_checker.cpp try_unfold_proj_app). Cut with: tools/slice.py init.ndjson out.ndjson "
        "_private.Init.Data.Range.Polymorphic.SInt.0.Int32.instRxcHasSize_eq",
    }
)

with open(os.path.join(OUT, "manifest.json"), "w", encoding="utf-8") as f:
    json.dump(
        {
            "description": "One file per unexpected behaviour; each is pinned to the check that must fire.",
            "files": files,
        },
        f,
        indent=1,
    )
    f.write("\n")
print(len(files), "regressions")
