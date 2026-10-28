#!/usr/bin/env python3
"""Regenerates tests/regressions: one small file per unexpected behaviour found, each pinned to the check that must
fire (the manifest's `msg`). Every entry says what happened. Run from the repository root; the output is committed.
"""

import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "forge"))
from ndjson import Builder  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from slice import slice_lines  # noqa: E402

PRELUDE_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "tests", "arena", "good", "init-prelude.ndjson"
)


def base(*names):
    """A builder continuing the part of the Init prelude that [names] need: small files that still use real Nat, Eq, ..."""
    with open(PRELUDE_PATH, encoding="utf-8") as f:
        return Builder.extending(slice_lines(f, names))


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


# ---- found by mutation testing: each of these accepted what it must refuse when one line of the checker was flipped ----
ONE = ("succ", 0)
NAT = ("const", "Nat", [])
EQ_NAT = ("app", ("const", "Eq", [ONE]), NAT)


def _app(f, *args):
    for a in args:
        f = ("app", f, a)
    return f


def eq_nat(a, b):
    return ("app", ("app", EQ_NAT, a), b)


def refl_nat(a):
    return ("app", ("app", ("const", "Eq.refl", [ONE]), NAT), a)


def nat_succ(a):
    return ("app", ("const", "Nat.succ", []), a)


b = base("Nat", "Nat.succ", "Nat.zero", "Eq", "Eq.refl")
b.theorem(
    "t",
    [],
    ("pi", NAT, eq_nat(("bvar", 0), nat_succ(("const", "Nat.zero", [])))),
    ("lam", NAT, refl_nat(("bvar", 0))),
)
add(
    "eta-struct-non-structure.ndjson",
    b.text(),
    "reject",
    "claims every n : Nat equals Nat.succ Nat.zero. Structure eta must apply only to structure-like types (one constructor, no "
    "indices, not recursive): a mutation that skipped that test accepted this.",
    msg="the value does not have the declared type",
)

for name, lhs, rhs, why in [
    ("nat-offset-succ-succ", nat_succ(("nat", 1)), nat_succ(("nat", 2)), "Nat.succ 1 = Nat.succ 2"),
    ("nat-offset-succ-lit", nat_succ(("nat", 1)), ("nat", 5), "Nat.succ 1 = 5"),
]:
    b = base("Nat", "Nat.succ", "Eq", "Eq.refl")
    b.theorem("t", [], eq_nat(lhs, rhs), refl_nat(lhs))
    add(
        name + ".ndjson",
        b.text(),
        "reject",
        f"claims {why} by rfl. The successor/literal rule decides this one way or the other before anything is unfolded; its 'different' verdict "
        "must stay a refusal (a mutation turned it into 'equal' and nothing noticed).",
        msg="the value does not have the declared type",
    )

# two binders with different domains are different, whatever the bodies do
b = Builder()
b.axiom("f", [], ("pi", ("sort", ONE), ("sort", ONE)))
b.definition("d", [], ("pi", ("sort", 0), ("sort", ONE)), ("const", "f", []))
add(
    "binder-domain-mismatch.ndjson",
    b.text(),
    "reject",
    "f : Sort 1 -> Sort 1 is declared to have type Sort 0 -> Sort 1. Comparing two binders compares their domains first; a mutation "
    "that treated different domains as equal accepted this.",
    msg="the value does not have the declared type",
)

# structure eta in iota reduction applies to a constant that is not a constructor
ZERO = 0
b = base("Nat", "Prod", "Prod.mk", "Prod.rec", "Eq", "Eq.refl")
prod_nat = ("app", ("app", ("const", "Prod", [ZERO, ZERO]), NAT), NAT)
b.axiom("p0", [], prod_nat)
p0 = ("const", "p0", [])
rec_fst = (
    "app",
    (
        "app",
        ("app", ("app", ("app", ("const", "Prod.rec", [ONE, ZERO, ZERO]), NAT), NAT), ("lam", prod_nat, NAT)),
        ("lam", NAT, ("lam", NAT, ("bvar", 1))),
    ),
    p0,
)
b.theorem("t", [], eq_nat(rec_fst, ("proj", "Prod", 0, p0)), refl_nat(("proj", "Prod", 0, p0)))
add(
    "prod-rec-on-axiom-eta.ndjson",
    b.text(),
    "accept",
    "Prod.rec (fun a b => a) p0 = p0.1 for an axiom p0 : Nat x Nat holds by structure eta: the stuck major premise is replaced by "
    "Prod.mk p0.1 p0.2 before the rule fires. A mutation that skipped the expansion for every constant that is not a constructor "
    "refused it (completeness: nothing else noticed).",
)

# `outParam` only counts as a binder annotation when the file defines it as the identity-like function
T = ("const", "T", [])
MK = ("const", "T.mk", [])


def one_field_block(b, field_ty, claimed_field_ty):
    """inductive T : Type | mk : field_ty -> T, with a recursor whose minor premise is claimed to take claimed_field_ty."""
    u = ("param", "u")
    motive_t = ("pi", T, ("sort", u))

    def minor_t(fty):
        return ("pi", fty, ("app", ("bvar", 1), ("app", MK, ("bvar", 0))))

    b.inductive(
        [{"name": "T", "type": ("sort", ONE), "num_params": 0, "ctors": ["T.mk"]}],
        [
            {
                "name": "T.mk",
                "induct": "T",
                "type": ("pi", field_ty, T),
                "cidx": 0,
                "num_params": 0,
                "num_fields": 1,
            }
        ],
        [
            {
                "name": "T.rec",
                "lparams": ["u"],
                "type": (
                    "pi",
                    motive_t,
                    ("pi", minor_t(claimed_field_ty), ("pi", T, ("app", ("bvar", 2), ("bvar", 0)))),
                ),
                "num_params": 0,
                "num_motives": 1,
                "num_minors": 1,
                "rules": [
                    (
                        "T.mk",
                        1,
                        (
                            "lam",
                            motive_t,
                            (
                                "lam",
                                minor_t(claimed_field_ty),
                                ("lam", claimed_field_ty, ("app", ("bvar", 1), ("bvar", 0))),
                            ),
                        ),
                    )
                ],
            }
        ],
    )


b = base("Nat")
b.axiom("outParam", [], ("pi", ("sort", ONE), ("sort", ONE)))
one_field_block(b, ("app", ("const", "outParam", []), NAT), NAT)
add(
    "out-param-axiom-not-stripped.ndjson",
    b.text(),
    "reject",
    "outParam is an axiom here, so `outParam Nat` is an ordinary type and the recursor's minor premise must take `outParam Nat`, "
    "not `Nat`. The annotation is stripped only when the file's own definition is the identity-like one; a mutation that stripped it "
    "for any constant with another kind of declaration accepted the claimed recursor.",
    msg="the type differs from the derivation",
)
b = base("Nat", "Bool")
b.definition(
    "outParam",
    ["u"],
    ("pi", ("sort", ("param", "u")), ("sort", ONE)),
    ("lam", ("sort", ("param", "u")), ("const", "Bool", [])),
)
one_field_block(b, ("app", ("const", "outParam", [("succ", 0)]), NAT), NAT)
add(
    "out-param-not-identity.ndjson",
    b.text(),
    "reject",
    "outParam is defined as `fun a => Bool` here: `outParam Nat` is Bool, so the minor premise cannot be claimed to take Nat. Only a "
    "definition that returns its first argument makes outParam an annotation; a mutation that accepted any other shape stripped it.",
    msg="the type differs from the derivation",
)


# ---- a hand-written parametric nested inductive: T (a : Type) := mk (List (T a)) ----
def db(t, env):
    """Terms with named variables: ("var", n), ("pin", n, ty, body), ("lamn", n, ty, body) -> de Bruijn terms."""
    k = t[0]
    if k == "var":
        return ("bvar", len(env) - 1 - max(i for i, x in enumerate(env) if x == t[1]))
    if k in ("pin", "lamn"):
        return ("pi" if k == "pin" else "lam", db(t[2], env), db(t[3], env + [t[1]]))
    if k == "app":
        return ("app", db(t[1], env), db(t[2], env))
    return t


def tele(kind, binders, body):
    for n, ty in reversed(binders):
        body = (kind, n, ty, body)
    return body


def V(n):
    return ("var", n)


def build_nested_param_tree(b, rec_universe="u"):
    ty0 = ("sort", ONE)
    u = ("param", rec_universe)
    ListC = lambda *a: _app(("const", "List", [0]), *a)  # noqa: E731
    Tt = lambda a: _app(("const", "T", []), a)  # noqa: E731
    nil = _app(("const", "List.nil", [0]), Tt(V("a")))
    cons = lambda h, tl: _app(("const", "List.cons", [0]), Tt(V("a")), h, tl)  # noqa: E731
    mk = lambda lst: _app(("const", "T.mk", []), V("a"), lst)  # noqa: E731
    m1t = tele("pin", [("t", Tt(V("a")))], ("sort", u))
    m2t = tele("pin", [("l", ListC(Tt(V("a"))))], ("sort", u))
    mk_minor = tele("pin", [("x", ListC(Tt(V("a")))), ("ih", _app(V("m2"), V("x")))], _app(V("m1"), mk(V("x"))))
    nil_minor = _app(V("m2"), nil)
    cons_minor = tele(
        "pin",
        [("h", Tt(V("a"))), ("tl", ListC(Tt(V("a")))), ("ih1", _app(V("m1"), V("h"))), ("ih2", _app(V("m2"), V("tl")))],
        _app(V("m2"), cons(V("h"), V("tl"))),
    )
    head = [("a", ty0), ("m1", m1t), ("m2", m2t), ("mk", mk_minor), ("nil", nil_minor), ("cons", cons_minor)]
    rec_ty = tele("pin", head + [("t", Tt(V("a")))], _app(V("m1"), V("t")))
    rec1_ty = tele("pin", head + [("t", ListC(Tt(V("a"))))], _app(V("m2"), V("t")))
    args = [V(n) for n, _ in head]
    rec0 = lambda *x: _app(("const", "T.rec", [u]), *args, *x)  # noqa: E731
    rec1 = lambda *x: _app(("const", "T.rec_1", [u]), *args, *x)  # noqa: E731
    rule_mk = tele("lamn", head + [("x", ListC(Tt(V("a"))))], _app(V("mk"), V("x"), rec1(V("x"))))
    rule_nil = tele("lamn", head, V("nil"))
    rule_cons = tele(
        "lamn",
        head + [("h", Tt(V("a"))), ("tl", ListC(Tt(V("a"))))],
        _app(V("cons"), V("h"), V("tl"), rec0(V("h")), rec1(V("tl"))),
    )
    b.inductive(
        [
            {
                "name": "T",
                "type": db(tele("pin", [("a", ty0)], ty0), []),
                "num_params": 1,
                "ctors": ["T.mk"],
                "is_rec": True,
                "num_nested": 1,
            }
        ],
        [
            {
                "name": "T.mk",
                "induct": "T",
                "type": db(tele("pin", [("a", ty0), ("l", ListC(Tt(V("a"))))], Tt(V("a"))), []),
                "cidx": 0,
                "num_params": 1,
                "num_fields": 1,
            }
        ],
        [
            {
                "name": "T.rec",
                "lparams": [rec_universe],
                "type": db(rec_ty, []),
                "num_params": 1,
                "num_motives": 2,
                "num_minors": 3,
                "rules": [("T.mk", 1, db(rule_mk, []))],
            },
            {
                "name": "T.rec_1",
                "lparams": [rec_universe],
                "type": db(rec1_ty, []),
                "num_params": 1,
                "num_motives": 2,
                "num_minors": 3,
                "rules": [("List.nil", 0, db(rule_nil, [])), ("List.cons", 2, db(rule_cons, []))],
            },
        ],
    )


b = base("Nat", "List", "List.nil", "List.cons")
build_nested_param_tree(b)
add(
    "nested-parametric-tree.ndjson",
    b.text(),
    "accept",
    "T (a : Type) := mk (List (T a)): a nested inductive with a parameter, with its two recursors written by hand. The auxiliary "
    "type, its recursor and the rebuilding of the derived terms over the parameter are exercised only by a nested type that has "
    "one (Lean.Syntax has none): a mutation that rebuilt a lambda over the parameters as a Pi survived every other test.",
)


# a mutual block of propositions eliminates into Prop only
PROP = ("sort", 0)
A = ("const", "A", [])
B = ("const", "B", [])
b = Builder()
mt1 = ("pi", A, ("sort", ("param", "u")))
mt2 = ("pi", B, ("sort", ("param", "u")))
b.inductive(
    [{"name": "A", "type": PROP, "num_params": 0}, {"name": "B", "type": PROP, "num_params": 0}],
    [],
    [
        {
            "name": "A.rec",
            "lparams": ["u"],
            "type": ("pi", mt1, ("pi", mt2, ("pi", A, ("app", ("bvar", 2), ("bvar", 0))))),
            "num_params": 0,
            "num_motives": 2,
            "num_minors": 0,
            "rules": [],
        },
        {
            "name": "B.rec",
            "lparams": ["u"],
            "type": ("pi", mt1, ("pi", mt2, ("pi", B, ("app", ("bvar", 1), ("bvar", 0))))),
            "num_params": 0,
            "num_motives": 2,
            "num_minors": 0,
            "rules": [],
        },
    ],
)
add(
    "mutual-prop-large-elimination.ndjson",
    b.text(),
    "reject",
    "A and B are two empty propositions declared together, with recursors claimed to eliminate into every Sort. A single empty "
    "proposition may (False does); a mutual block of propositions eliminates into Prop only. A mutation that allowed large "
    "elimination for mutual blocks accepted the claim.",
    msg="universe parameters differ from the derivation",
)

# a string literal expands through String.ofList only if that has the type List Char -> String
b = base("String", "Char", "Nat", "List", "Eq", "Eq.refl")
b.axiom("String.ofList", [], ("pi", NAT, ("const", "String", [])))
b.theorem(
    "t",
    [],
    _app(
        ("const", "Eq", [ONE]), ("const", "String", []), ("str", "a"), _app(("const", "String.ofList", []), ("nat", 5))
    ),
    _app(("const", "Eq.refl", [ONE]), ("const", "String", []), ("str", "a")),
)
add(
    "string-of-list-wrong-type.ndjson",
    b.text(),
    "reject",
    'String.ofList is an axiom Nat -> String here and the file compares the literal "a" with String.ofList 5. A literal expands '
    "through the file's own String.ofList only when it has type List Char -> String (there is no String.mk here either), so the "
    "comparison has no meaning and is refused for that reason; a mutation that accepted the constant when either its universe "
    "parameters or its type fit expanded the literal anyway and failed later, for another reason.",
    msg="string literal: the environment has no String.ofList or String.mk of type List Char -> String",
)

# a mutual block whose types take different parameters
b = Builder()
b.inductive(
    [
        {"name": "A", "type": ("pi", ("sort", ONE), ("sort", ONE)), "num_params": 1},
        {"name": "B", "type": ("pi", ("sort", 0), ("sort", ONE)), "num_params": 1},
    ]
)
add(
    "mutual-different-parameters.ndjson",
    b.text(),
    "reject",
    "A and B are declared together but A takes a parameter of type Sort 1 and B one of type Sort 0. All types of a mutual block share "
    "their parameters; a mutation that inverted the comparison accepted exactly this.",
    msg="parameters of all inductive types must match",
)

# a universe parameter that is not declared, inside max / imax
for name, lv in [("max", ("max", ("param", "u"), ("param", "v"))), ("imax", ("imax", ("param", "v"), ("param", "u")))]:
    b = Builder()
    b.axiom("a", ["v"], ("sort", lv))
    add(
        f"undeclared-universe-in-{name}.ndjson",
        b.text(),
        "reject",
        f"a.{{v}} mentions the undeclared universe parameter u inside {name}. Every parameter must be declared: a mutation that "
        "accepted a {name} when only one side was in scope accepted this.".replace("{name}", name),
        msg="universe parameter out of scope",
    )

# files cut from an official export with tools/slice.py (kept compressed; arena.py feeds them on standard input)
SLICE = "tools/slice.py init.ndjson out.ndjson "
for path, decl, why in [
    (
        "init-int32-rxc-hassize.ndjson.gz",
        "_private.Init.Data.Range.Polymorphic.SInt.0.Int32.instRxcHasSize_eq",
        "Init (toolchain 4.34.0-rc2) never finished this: comparing `Nat.sub A B` with `inst.1 a b` unfolded Nat.sub, "
        "which forces whnf of B = a bit-vector value mod 2^32 and peels 2^31 successors. The kernel reduces the "
        "projection application first (type_checker.cpp try_unfold_proj_app).",
    ),
    (
        "init-char-ofordinal-proof3.ndjson.gz",
        "_private.Init.Data.Char.Ordinal.0.Char.ofOrdinal._proof_3",
        "Init (toolchain 4.34.0-rc2) never finished this: a `grind` certificate check compares `Bool.true` with "
        "`Nat.beq 4293853185 (natAbs (leadCoeff p) * 4294965248 - 1112063)` where p is a let-bound variable. The "
        "comparison peeled the literal one successor at a time because the term has a free variable; a variable whose "
        "value is closed now counts as closed for the arithmetic shortcut. Also: reduce_nat has no free-variable "
        "guard (the kernel has none).",
    ),
    (
        "init-lean-syntax-nested.ndjson.gz",
        "Lean.Syntax",
        "Lean.Syntax is the one nested inductive in Init (it contains Array Syntax, which contains List Syntax): the "
        "auxiliary types, their recursors and the restoring of the derived terms are exercised by nothing else in the "
        "quick tests (found by mutation testing: swapping the restore of a lambda for a Pi survived).",
    ),
]:
    files.append({"path": path, "expect": "accept", "why": why + " Cut with: " + SLICE + decl})

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
