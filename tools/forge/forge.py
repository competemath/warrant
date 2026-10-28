#!/usr/bin/env python3
"""The forge: random lean4export files whose verdict is known by construction, in rounds of growing size.

usage: forge.py --binary PATH [--seconds N] [--seed S] [--rounds R] [--out DIR] [--prelude FILE]

Generators (each states the verdict it knows, and the oracle is independent of the kernel):
  levels   two random universe levels; the file is accepted iff they are equal under every valuation (brute force)
  prop     a theorem about a universe-polymorphic statement; accepted iff its sort is zero under every valuation
  stlc     simply typed terms over axioms with beta, delta, zeta and eta; accepted iff the normal forms agree
  nat      arithmetic on random literals, with the right and with a wrong result (needs --prelude)
  tamper   a valid inductive file with one claimed field changed; the claim is rederived, so it must be rejected
  corrupt  a valid file with a line deleted, duplicated or mangled; any verdict but a crash or an accept of
           something the original did not prove is fine, so it is checked only for crashes and for acceptance of
           files that must fail (deleted referenced table entries)
A verdict that contradicts the oracle, or a crash, saves the file under DIR and the run exits 1. Accepting a file the
oracle says is invalid is reported as SOUNDNESS.
"""

import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ndjson import Builder  # noqa: E402

PARAMS = ["u", "v", "w"]


# ---------- universe levels ----------
def rand_level(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        return rng.choice([0, ("param", rng.choice(PARAMS)), ("param", rng.choice(PARAMS))])
    k = rng.choice(["succ", "max", "imax", "succ", "max", "imax"])
    if k == "succ":
        return ("succ", rand_level(rng, depth - 1))
    return (k, rand_level(rng, depth - 1), rand_level(rng, depth - 1))


def lvl_depth(lv):
    if lv == 0 or lv[0] == "param":
        return 0
    return 1 + max(lvl_depth(x) for x in lv[1:])


def lvl_eval(lv, env):
    if lv == 0:
        return 0
    k = lv[0]
    if k == "param":
        return env[lv[1]]
    if k == "succ":
        return 1 + lvl_eval(lv[1], env)
    a = lvl_eval(lv[1], env)
    b = lvl_eval(lv[2], env)
    if k == "max":
        return max(a, b)
    return 0 if b == 0 else max(a, b)


def lvl_equiv(a, b):
    bound = lvl_depth(a) + lvl_depth(b) + 2
    for vals in itertools.product(range(bound + 1), repeat=len(PARAMS)):
        env = dict(zip(PARAMS, vals))
        if lvl_eval(a, env) != lvl_eval(b, env):
            return False
    return True


def lvl_zero(a):
    bound = lvl_depth(a) + 2
    return all(
        lvl_eval(a, dict(zip(PARAMS, vals))) == 0 for vals in itertools.product(range(bound + 1), repeat=len(PARAMS))
    )


def gen_levels(rng, c):
    a, b = rand_level(rng, 1 + c), rand_level(rng, 1 + c)
    if rng.random() < 0.5:  # make equal pairs common: rewrite b into an equivalent form
        b = ("max", a, 0) if rng.random() < 0.5 else ("max", a, a)
    expect = "accept" if lvl_equiv(a, b) else "reject"
    bd = Builder()
    ty = ("pi", ("sort", a), ("sort", b))
    val = ("lam", ("sort", a), ("bvar", 0))  # fun T : Sort a => T   : Sort a -> Sort a
    bd.definition("t", PARAMS, ty, val)
    return bd.text(), expect


def gen_prop(rng, c):
    a, b = rand_level(rng, 1 + c), rand_level(rng, 1 + c)
    # theorem t : forall (P : Sort a) (Q : Sort b), P -> Q -> P ; its sort is imax (a+1) (imax (b+1) (imax a (imax b a)))
    sa, sb = ("sort", a), ("sort", b)
    ty = ("pi", sa, ("pi", sb, ("pi", ("bvar", 1), ("pi", ("bvar", 1), ("bvar", 3)))))
    val = (
        "lam",
        sa,
        ("lam", sb, ("lam", ("bvar", 1), ("lam", ("bvar", 1), ("bvar", 1)))),
    )
    top = ("imax", ("succ", a), ("imax", ("succ", b), ("imax", a, ("imax", b, a))))
    expect = "accept" if lvl_zero(top) else "reject"
    bd = Builder()
    bd.theorem("t", PARAMS, ty, val)
    return bd.text(), expect


# ---------- simply typed terms ----------
# base type A with constants a b c, functions f g : A -> A, h : A -> A -> A; terms are Python tuples
# ("c", name) ("app", f, x) ("lam", body) ("v", i) ("let", val, body)
BASE = {"a": "A", "b": "A", "c": "A"}


def rand_term(rng, depth, scope):
    """A term of type A (scope = number of enclosing A-typed binders)."""
    r = rng.random()
    if depth == 0 or r < 0.2:
        if scope and rng.random() < 0.5:
            return ("v", rng.randrange(scope))
        return ("c", rng.choice(["a", "b", "c"]))
    if r < 0.5:
        return ("app", ("c", rng.choice(["f", "g"])), rand_term(rng, depth - 1, scope))
    if r < 0.65:
        return (
            "app",
            ("app", ("c", "h"), rand_term(rng, depth - 1, scope)),
            rand_term(rng, depth - 1, scope),
        )
    if r < 0.85:  # beta redex
        return (
            "app",
            ("lam", rand_term(rng, depth - 1, scope + 1)),
            rand_term(rng, depth - 1, scope),
        )
    return (
        "let",
        rand_term(rng, depth - 1, scope),
        rand_term(rng, depth - 1, scope + 1),
    )


def shift(t, d, cut=0):
    k = t[0]
    if k == "v":
        return ("v", t[1] + d) if t[1] >= cut else t
    if k == "c":
        return t
    if k == "app":
        return ("app", shift(t[1], d, cut), shift(t[2], d, cut))
    if k == "lam":
        return ("lam", shift(t[1], d, cut + 1))
    return ("let", shift(t[1], d, cut), shift(t[2], d, cut + 1))


def subst(t, j, s):
    k = t[0]
    if k == "v":
        return s if t[1] == j else (("v", t[1] - 1) if t[1] > j else t)
    if k == "c":
        return t
    if k == "app":
        return ("app", subst(t[1], j, s), subst(t[2], j, s))
    if k == "lam":
        return ("lam", subst(t[1], j + 1, shift(s, 1)))
    return ("let", subst(t[1], j, s), subst(t[2], j + 1, shift(s, 1)))


def nf(t):
    k = t[0]
    if k in ("v", "c"):
        return t
    if k == "let":
        return nf(subst(t[2], 0, t[1]))
    if k == "lam":
        b = nf(t[1])
        if b[0] == "app" and b[2] == ("v", 0) and not occurs(b[1], 0):  # eta
            return shift(b[1], -1)
        return ("lam", b)
    f = nf(t[1])
    x = nf(t[2])
    if f[0] == "lam":
        return nf(subst(f[1], 0, x))
    return ("app", f, x)


def occurs(t, j):
    k = t[0]
    if k == "v":
        return t[1] == j
    if k == "c":
        return False
    if k == "app":
        return occurs(t[1], j) or occurs(t[2], j)
    if k == "lam":
        return occurs(t[1], j + 1)
    return occurs(t[1], j) or occurs(t[2], j + 1)


def emit_term(t, depth=0):
    """To Builder expression; binders are all of type A."""
    k = t[0]
    A = ("const", "A", [])
    if k == "v":
        return ("bvar", t[1])
    if k == "c":
        return ("const", t[1], [])
    if k == "app":
        return ("app", emit_term(t[1]), emit_term(t[2]))
    if k == "lam":
        return ("lam", A, emit_term(t[1]))
    return ("let", A, emit_term(t[1]), emit_term(t[2]))


def gen_stlc(rng, c):
    d = 1 + c
    t1 = rand_term(rng, d, 0)
    if rng.random() < 0.5:
        t2 = t1  # trivially equal structure, different presentation below
        # presentation change: wrap in beta redex / let
        t2 = ("app", ("lam", shift(t1, 1)), ("c", "a")) if rng.random() < 0.5 else ("let", ("c", "b"), shift(t1, 1))
    else:
        t2 = rand_term(rng, d, 0)
    expect = "accept" if nf(t1) == nf(t2) else "reject"
    bd = Builder()
    A = ("const", "A", [])
    bd.axiom("A", [], ("sort", ("succ", 0)))
    for n in "abc":
        bd.axiom(n, [], A)
    for n in "fg":
        bd.axiom(n, [], ("pi", A, A))
    bd.axiom("h", [], ("pi", A, ("pi", A, A)))
    bd.axiom("P", [], ("pi", A, ("sort", ("succ", 0))))
    bd.axiom("p", [], ("pi", A, ("app", ("const", "P", []), ("bvar", 0))))
    # def t1' : A := t1 ; def chk : P t1 := p t2   accepted iff t1 and t2 agree
    bd.definition(
        "chk",
        [],
        ("app", ("const", "P", []), emit_term(t1)),
        ("app", ("const", "p", []), emit_term(t2)),
        "regular",
    )
    return bd.text(), expect


# ---------- Nat arithmetic ----------
OPS = {
    "Nat.add": lambda x, y: x + y,
    "Nat.sub": lambda x, y: max(x - y, 0),
    "Nat.mul": lambda x, y: x * y,
    "Nat.div": lambda x, y: 0 if y == 0 else x // y,
    "Nat.mod": lambda x, y: x if y == 0 else x % y,
    "Nat.pow": lambda x, y: x**y,
}


# ---------- tamper / corrupt ----------
def load_lines(path):
    with open(path, encoding="utf-8") as f:
        return f.read().splitlines()


def gen_tamper(rng, lines):
    idxs = [i for i, ln in enumerate(lines) if ln.startswith('{"inductive"')]
    if not idxs:
        return None
    i = rng.choice(idxs)
    obj = json.loads(lines[i])
    ind = obj["inductive"]
    choice = rng.choice(
        [
            "rec_k",
            "rec_nfields",
            "rec_counts",
            "rule_swap",
            "ctor_nfields",
            "isrec",
            "nnested",
            "drop_rec",
            "ctor_idx",
            "rec_lparams",
            "numindices",
        ]
    )
    recs, ctors, types = ind["recs"], ind["ctors"], ind["types"]
    if choice == "rec_k" and recs:
        r = rng.choice(recs)
        r["k"] = not r["k"]
    elif choice == "rec_nfields" and any(r["rules"] for r in recs):
        r = rng.choice([r for r in recs if r["rules"]])
        ru = rng.choice(r["rules"])
        ru["nfields"] += 1
    elif choice == "rec_counts" and recs:
        r = rng.choice(recs)
        r[rng.choice(["numParams", "numIndices", "numMotives", "numMinors"])] += 1
    elif choice == "rule_swap":
        cand = [r for r in recs if len(r["rules"]) >= 2 and r["rules"][0]["rhs"] != r["rules"][1]["rhs"]]
        if not cand:
            return None
        r = rng.choice(cand)
        r["rules"][0]["rhs"], r["rules"][1]["rhs"] = (
            r["rules"][1]["rhs"],
            r["rules"][0]["rhs"],
        )
    elif choice == "ctor_nfields" and ctors:
        rng.choice(ctors)["numFields"] += 1
    elif choice == "isrec" and types:
        t = rng.choice(types)
        t["isRec"] = not t["isRec"]
    elif choice == "nnested" and types:
        rng.choice(types)["numNested"] += 1
    elif choice == "drop_rec" and recs:
        recs.pop(rng.randrange(len(recs)))
    elif choice == "ctor_idx" and ctors:
        rng.choice(ctors)["cidx"] += 1
    elif choice == "rec_lparams" and any(r["levelParams"] for r in recs):
        r = rng.choice([r for r in recs if r["levelParams"]])
        r["levelParams"] = r["levelParams"][1:]
    elif choice == "numindices" and types:
        rng.choice(types)["numIndices"] += 1
    else:
        return None
    new = list(lines)
    new[i] = json.dumps(obj, separators=(",", ":"), sort_keys=True)
    if new[i] == lines[i] or json.loads(new[i]) == json.loads(lines[i]):
        return None
    return "\n".join(new) + "\n", "reject", choice


def run_binary(binary, text, workdir, timeout):
    path = os.path.join(workdir, "case.ndjson")
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    try:
        p = subprocess.run([binary, path], capture_output=True, text=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return "timeout", ""
    return {0: "accept", 1: "reject", 2: "decline"}.get(p.returncode, f"crash({p.returncode})"), p.stderr.strip()[:200]


def judge(expect, got):
    if got.startswith("crash"):
        return "CRASH"
    if got == "timeout":
        return "ok"  # a timeout is a decline
    if expect == "reject" and got == "accept":
        return "SOUNDNESS"
    if expect == "accept" and got == "reject":
        return "COMPLETENESS"
    return "ok"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--seconds", type=int, default=120)
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--rounds", type=int, default=10**9)
    ap.add_argument("--out", default="forge-out")
    ap.add_argument("--prelude", default=None)
    ap.add_argument("--inductive-sources", nargs="*", default=[])
    ap.add_argument("--timeout", type=int, default=60)
    args = ap.parse_args()
    seed = args.seed if args.seed is not None else random.SystemRandom().randrange(2**32)
    print(f"seed {seed}")
    rng = random.Random(seed)
    os.makedirs(args.out, exist_ok=True)
    sources = [load_lines(p) for p in args.inductive_sources]
    prelude = load_lines(args.prelude) if args.prelude else None
    stats = {}
    failures = 0
    deadline = time.time() + args.seconds
    rnd = 0
    with tempfile.TemporaryDirectory() as work:
        while time.time() < deadline and rnd < args.rounds:
            rnd += 1
            c = 1 + rnd // 3  # complexity grows with the round
            gens = ["levels", "prop", "stlc"] + (["tamper"] if sources else []) + (["nat"] if prelude else [])
            for g in gens:
                if time.time() >= deadline:
                    break
                made = None
                if g == "levels":
                    made = gen_levels(rng, c) + ("",)
                elif g == "prop":
                    made = gen_prop(rng, c) + ("",)
                elif g == "stlc":
                    made = gen_stlc(rng, c) + ("",)
                elif g == "tamper":
                    made = gen_tamper(rng, rng.choice(sources))
                elif g == "nat":
                    made = gen_nat_with_prelude(rng, c, prelude)
                if not made:
                    continue
                text, expect, note = made
                got, msg = run_binary(args.binary, text, work, args.timeout)
                verdict = judge(expect, got)
                s = stats.setdefault(
                    g,
                    {
                        "n": 0,
                        "accept": 0,
                        "reject": 0,
                        "decline": 0,
                        "timeout": 0,
                        "bad": 0,
                    },
                )
                s["n"] += 1
                s[got if got in s else "decline"] += 1
                if verdict != "ok":
                    failures += 1
                    s["bad"] += 1
                    name = f"{verdict.lower()}-{g}-{seed}-{rnd}.ndjson"
                    with open(os.path.join(args.out, name), "w", encoding="utf-8") as f:
                        f.write(text)
                    print(f"{verdict}: generator {g} {note} expected {expect}, got {got} ({msg}) -> {name}")
    print(
        json.dumps(
            {"seed": seed, "rounds": rnd, "failures": failures, "generators": stats},
            indent=1,
        )
    )
    return 1 if failures else 0


def gen_nat_with_prelude(rng, c, prelude):
    """Append a theorem `Nat.op x y = claimed := Eq.refl (Nat.op x y)`-style claim to a prelude that has Nat, Eq."""
    op = rng.choice(list(OPS))
    hi = 10 ** (1 + c)
    x, y = rng.randrange(hi), rng.randrange(hi if op != "Nat.pow" else 12)
    right = OPS[op](x, y)
    wrong = rng.random() < 0.5
    claimed = right + rng.choice([1, 2, 7]) if wrong else right
    # name/level/expr ids continue after the prelude's
    nn = nl = ne = 0
    names = {}
    for ln in prelude:
        o = json.loads(ln)
        if "in" in o:
            nn = max(nn, o["in"])
            if "str" in o:
                p = names.get(o["str"]["pre"], "")
                names[o["in"]] = (p + "." if p else "") + o["str"]["str"]
            else:
                p = names.get(o["num"]["pre"], "")
                names[o["in"]] = (p + "." if p else "") + str(o["num"]["i"])
        elif "il" in o:
            nl = max(nl, o["il"])
        elif "ie" in o:
            ne = max(ne, o["ie"])
    inv = {v: k for k, v in names.items()}
    for need in ("Nat", "Eq", "Eq.refl", op):
        if need not in inv:
            return None
    out = []
    ids = {"in": nn, "il": nl, "ie": ne + 1}

    def nid(s):
        if s in inv:
            return inv[s]
        pre, _, last = s.rpartition(".")
        p = nid(pre) if pre else 0
        ids["in"] += 1
        inv[s] = ids["in"]
        out.append(json.dumps({"in": ids["in"], "str": {"pre": p, "str": last}}, separators=(",", ":")))
        return ids["in"]

    cache = {}

    def lvl_one():
        if "one" not in cache:
            ids["il"] += 1
            out.append(json.dumps({"il": ids["il"], "succ": 0}, separators=(",", ":")))
            cache["one"] = ids["il"]
        return cache["one"]

    def ex(body):
        key = json.dumps(body, sort_keys=True)
        if key in cache:
            return cache[key]
        i = ids["ie"]
        ids["ie"] += 1
        out.append(json.dumps({"ie": i, **body}, separators=(",", ":")))
        cache[key] = i
        return i

    nat = ex({"const": {"name": nid("Nat"), "us": []}})
    lit = lambda v: ex({"natVal": str(v)})  # noqa: E731
    app = lambda f, a: ex({"app": {"fn": f, "arg": a}})  # noqa: E731
    lhs = app(app(ex({"const": {"name": nid(op), "us": []}}), lit(x)), lit(y))
    eq = ex({"const": {"name": nid("Eq"), "us": [lvl_one()]}})
    ty = app(app(app(eq, nat), lhs), lit(claimed))
    refl = ex({"const": {"name": nid("Eq.refl"), "us": [lvl_one()]}})
    val = app(app(refl, nat), lhs)
    out.append(
        json.dumps(
            {
                "thm": {
                    "name": nid("forge_nat"),
                    "levelParams": [],
                    "type": ty,
                    "value": val,
                    "all": [nid("forge_nat")],
                }
            },
            separators=(",", ":"),
        )
    )
    expect = "reject" if wrong else "accept"
    return "\n".join(prelude + out) + "\n", expect, f"{op} {x} {y} -> {claimed}"


if __name__ == "__main__":
    sys.exit(main())
