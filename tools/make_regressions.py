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


def add(name, text, expect, why, msg=None, may_decline=False, env=None):
    with open(os.path.join(OUT, name), "w", encoding="utf-8") as f:
        f.write(text)
    e = {"path": name, "expect": expect, "why": why}
    if msg:
        e["msg"] = msg
    if may_decline:
        e["may_decline"] = True
    if env:
        e["env"] = env
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


def _refl_any(ty, name="x"):
    return _app(("const", "Eq.refl", [ONE]), ty, ("const", name, []))


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

# an ill-typed subterm whose type, inferred without looking inside it, is the expected one
BOOL = ("const", "Bool", [])
B_TRUE = ("const", "Bool.true", [])
N_ZERO = ("const", "Nat.zero", [])
T_OF = ("const", "T", [])
G_OF = ("const", "g", [])


def ill_typed_base():
    b = base("Nat", "Nat.succ", "Nat.zero", "Bool", "Bool.true")
    b.axiom("g", [], ("pi", NAT, NAT))
    b.definition("T", [], ("pi", BOOL, ("sort", ONE)), ("lam", BOOL, NAT), hints="regular")
    return b


b = ill_typed_base()
b.definition("bad", [], ("pi", NAT, NAT), ("lam", _app(T_OF, N_ZERO), ("bvar", 0)))
add(
    "ill-typed-lambda-domain.ndjson",
    b.text(),
    "reject",
    "fun (x : T Nat.zero) => x with T : Bool -> Type: the domain applies T to a Nat. Its type, inferred without looking inside "
    "the application, is a sort, and T Nat.zero unfolds to Nat so the lambda's type fits the declared Nat -> Nat. A binder domain "
    "must itself be checked; a mutation that only inferred its type accepted this.",
    msg="application type mismatch",
)
b = ill_typed_base()
b.definition("bad", [], NAT, nat_succ(_app(G_OF, B_TRUE)))
add(
    "ill-typed-application-argument.ndjson",
    b.text(),
    "reject",
    "Nat.succ (g Bool.true) with g : Nat -> Nat: the argument g Bool.true has type Nat when inferred without looking inside it, "
    "but applies g to a Bool. Arguments are checked, not just typed; a mutation that skipped that accepted this.",
    msg="application type mismatch",
)
b = ill_typed_base()
b.definition("bad", [], NAT, ("let", NAT, _app(G_OF, B_TRUE), ("bvar", 0)))
add(
    "ill-typed-let-value.ndjson",
    b.text(),
    "reject",
    "let x : Nat := g Bool.true; x: the value is ill-typed (g applied to a Bool) though its type is Nat. A let value is checked; a "
    "mutation that only inferred its type accepted this.",
    msg="application type mismatch",
)
b = ill_typed_base()
b.definition("bad", [], NAT, ("let", _app(T_OF, N_ZERO), N_ZERO, ("bvar", 0)))
add(
    "ill-typed-let-type.ndjson",
    b.text(),
    "reject",
    "let x : T Nat.zero := Nat.zero; x: the let's type applies T : Bool -> Type to a Nat. A let type is checked; a mutation that "
    "only inferred its sort accepted this.",
    msg="application type mismatch",
)

# `outParam` only counts as a binder annotation when the file defines it as the identity-like function
T = ("const", "T", [])
MK = ("const", "T.mk", [])


def one_field_block(b, field_ty, claimed_field_ty, tweak=None):
    """inductive T : Type | mk : field_ty -> T, with a recursor whose minor premise is claimed to take claimed_field_ty."""
    u = ("param", "u")
    motive_t = ("pi", T, ("sort", u))

    def minor_t(fty):
        return ("pi", fty, ("app", ("bvar", 1), ("app", MK, ("bvar", 0))))

    types = [{"name": "T", "type": ("sort", ONE), "num_params": 0, "ctors": ["T.mk"]}]
    ctors = [
        {
            "name": "T.mk",
            "induct": "T",
            "type": ("pi", field_ty, T),
            "cidx": 0,
            "num_params": 0,
            "num_fields": 1,
        }
    ]
    recs = [
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
    ]
    if tweak:
        tweak(types, ctors, recs)
    b.inductive(types, ctors, recs)


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


# ---- found by listing the checker's reject sites that no test file ever ended with ----
def refuse(name, text, why, msg):
    add(name + ".ndjson", text, "reject", why, msg=msg)


def claims(name, claim, tweak, msg):
    b = base("Nat")
    one_field_block(b, NAT, NAT, tweak=tweak)
    refuse(
        name,
        b.text(),
        f"inductive T := mk (n : Nat) with one claim about the block changed: {claim}. Every such claim is derived from the types "
        "and constructors and compared; none is trusted.",
        msg,
    )


claims(
    "claim-is-rec",
    "isRec true on a type that is not recursive",
    lambda t, c, r: t[0].update(is_rec=True),
    "claimed isRec of T differs from the derivation",
)
claims(
    "claim-is-reflexive",
    "isReflexive true",
    lambda t, c, r: t[0].update(is_reflexive=True),
    "claimed isReflexive of T differs from the derivation",
)
claims(
    "claim-num-nested",
    "numNested 1",
    lambda t, c, r: t[0].update(num_nested=1),
    "claimed numNested of T differs from the derivation",
)
claims(
    "claim-num-indices",
    "numIndices 1",
    lambda t, c, r: t[0].update(num_indices=1),
    "claimed numIndices of T differs from the derivation",
)
claims(
    "claim-rec-all",
    "the recursor's 'all' lists another type",
    lambda t, c, r: r[0].update(all=["T", "Nat"]),
    "T.rec: 'all' differs from the derivation",
)
claims(
    "claim-rec-minors",
    "two minor premises",
    lambda t, c, r: r[0].update(num_minors=2),
    "T.rec: parameter, index, motive or minor counts differ from the derivation",
)
claims(
    "claim-rec-rules",
    "no computation rule",
    lambda t, c, r: r[0].update(rules=[]),
    "T.rec: number of rules differs from the derivation",
)
claims(
    "claim-rec-k", "the K flag", lambda t, c, r: r[0].update(k=True), "T.rec: the K flag differs from the derivation"
)

b = Builder()
b.inductive([])
refuse("empty-inductive-block", b.text(), "an inductive block with no types.", "empty inductive block")

b = Builder()
b.inductive(
    [
        {"name": "A", "type": ("sort", ONE), "num_params": 0, "lparams": ["u"]},
        {"name": "B", "type": ("sort", ONE), "num_params": 0},
    ]
)
refuse(
    "block-universe-parameters",
    b.text(),
    "A takes a universe parameter and B none, in one block.",
    "inductive block: universe parameters differ between types",
)

b = Builder()
b.inductive(
    [
        {"name": "A", "type": ("pi", ("sort", ONE), ("sort", ONE)), "num_params": 1},
        {"name": "B", "type": ("sort", ONE), "num_params": 0},
    ]
)
refuse(
    "block-parameter-count",
    b.text(),
    "A has one parameter and B none, in one block.",
    "inductive block: number of parameters differs between types",
)

b = Builder()
b.inductive(
    [
        {"name": "A", "type": ("sort", ONE), "num_params": 0, "all": ["A"]},
        {"name": "B", "type": ("sort", ONE), "num_params": 0},
    ]
)
refuse(
    "block-all-not-the-block",
    b.text(),
    "A's 'all' lists only A although B is declared with it.",
    "inductive block: 'all' is not the block",
)

b = Builder()
b.inductive([{"name": "A", "type": ("sort", ONE), "num_params": 0}, {"name": "B", "type": PROP, "num_params": 0}])
refuse(
    "block-universes-differ",
    b.text(),
    "A : Type and B : Prop in one mutual block: the types must live in one universe.",
    "mutually inductive types must live in the same universe",
)

# the export's own references
head = json.dumps(META, separators=(",", ":"))
add(
    "dangling-reference.ndjson",
    head + '\n{"ie":0,"sort":5}\n',
    "reject",
    "an expression refers to level 5, which was never defined.",
    msg="dangling",
)
add(
    "index-defined-twice.ndjson",
    head + '\n{"in":1,"str":{"pre":0,"str":"x"}}\n{"in":1,"str":{"pre":0,"str":"y"}}\n',
    "reject",
    "name 1 is defined twice.",
    msg="defined twice",
)

# quotients
QU = ("param", "u")
QUOT_TY = ("pi", ("sort", QU), ("pi", ("pi", ("bvar", 0), ("pi", ("bvar", 1), PROP)), ("sort", QU)))
b = Builder()
b.quot("type", "Quot", ["u"], QUOT_TY)
refuse(
    "quot-without-eq",
    b.text(),
    "Quot declared in a file with no Eq: the quotient rules are stated through Eq.",
    "quotient: Eq is not declared",
)
b = base("Eq", "Nat")
b.quot("type", "Foo", ["u"], ("sort", ONE))
refuse(
    "quot-unexpected-name",
    b.text(),
    "a quotient declaration named Foo: only Quot, Quot.mk, Quot.lift and Quot.ind exist.",
    "quotient: unexpected name",
)
b = base("Eq", "Nat")
b.quot("type", "Quot", ["u", "v"], ("sort", ONE))
refuse(
    "quot-wrong-universes",
    b.text(),
    "Quot declared with two universe parameters instead of one.",
    "quotient: wrong universe parameters",
)
b = base("Eq", "Nat")
b.quot("type", "Quot", ["u"], ("sort", ONE))
refuse(
    "quot-wrong-type",
    b.text(),
    "Quot declared with type Type instead of {a : Sort u} -> (a -> a -> Prop) -> Sort u.",
    "quotient: the type of Quot is not the expected one",
)
# an Eq that is an inductive family but not the one the quotient rules need (PUnit under the names Eq and Eq.refl)
with open(PRELUDE_PATH, encoding="utf-8") as f:
    punit = slice_lines(f, ["PUnit", "PUnit.unit"])
renamed = []
for ln in punit:
    o = json.loads(ln)
    if "in" in o and "str" in o and o["str"]["str"] in ("PUnit", "unit"):
        o["str"]["str"] = {"PUnit": "Eq", "unit": "refl"}[o["str"]["str"]]
    renamed.append(json.dumps(o, separators=(",", ":"), sort_keys=True))
b = Builder.extending(renamed)
b.quot("type", "Quot", ["u"], QUOT_TY)
refuse(
    "quot-eq-wrong-shape",
    b.text(),
    "Eq is an inductive family with one constructor, but a one-universe PUnit in disguise: no parameters, no index. The quotient "
    "rules need the real Eq.",
    "quotient: Eq is not the expected inductive family",
)

# literals and levels and applications
b = Builder()
b.axiom("Nat", [], ("sort", ONE))
b.definition("d", [], ("const", "Nat", []), ("nat", 5))
refuse(
    "literal-without-genuine-nat",
    b.text(),
    "a natural number literal in a file whose Nat is an axiom, not the inductive type.",
    "natural number literal: the environment's Nat is not the genuine one",
)
b = Builder()
b.axiom("Nat", [], ("sort", ONE))
b.definition("d", [], ("sort", ONE), ("str", "a"))
refuse(
    "string-literal-without-string",
    b.text(),
    "a string literal in a file with no String.",
    "String literal without String",
)
b = Builder()
b.axiom("a", ["u"], ("sort", ("param", "u")))
b.definition("d", [], ("sort", ONE), ("const", "a", []))
refuse(
    "wrong-number-of-levels", b.text(), "a.{u} used with no universe level.", "wrong number of universe levels for a"
)
b = base("Nat", "Nat.zero")
b.definition("d", [], NAT, _app(N_ZERO, N_ZERO))
refuse("function-expected", b.text(), "Nat.zero applied to an argument: it is not a function.", "function expected")

# opaque
b = base("Nat", "Nat.zero", "Bool", "Bool.true")
b.opaque("o", [], NAT, B_TRUE)
refuse(
    "opaque-wrong-type",
    b.text(),
    "an opaque constant of type Nat whose value is Bool.true.",
    "the value does not have the declared type",
)

# a nested occurrence whose other parameters mention a field of the constructor
b = base("Nat", "PProd", "Eq")
eq_xx = _app(("const", "Eq", [ONE]), NAT, ("bvar", 0), ("bvar", 0))
b.inductive(
    [{"name": "T", "type": ("sort", ONE), "num_params": 0, "ctors": ["T.mk"]}],
    [
        {
            "name": "T.mk",
            "induct": "T",
            "type": ("pi", NAT, ("pi", _app(("const", "PProd", [ONE, 0]), T, eq_xx), T)),
            "cidx": 0,
            "num_params": 0,
            "num_fields": 2,
        }
    ],
)
refuse(
    "nested-parameter-with-local",
    b.text(),
    "T := mk (x : Nat) (PProd T (x = x)): T occurs inside PProd, whose other argument mentions the field x. A nested occurrence's "
    "parameters may not contain local variables.",
    "invalid nested inductive datatype",
)

claims(
    "claim-ctor-index",
    "constructor mk has index 1 though it is the first",
    lambda t, c, r: c[0].update(cidx=1),
    "constructor T.mk has the wrong index",
)
claims(
    "claim-ctor-undeclared",
    "the type lists mk but no constructor declaration is given",
    lambda t, c, r: c.clear(),
    "constructor T.mk is listed but not declared",
)
claims(
    "claim-recursor-missing",
    "no recursor is given",
    lambda t, c, r: r.clear(),
    "recursor T.rec is derived but missing from the file",
)

b = Builder()
b.inductive(
    [
        {"name": "A", "type": ("sort", ONE), "num_params": 0, "ctors": ["B.mk"]},
        {"name": "B", "type": ("sort", ONE), "num_params": 0},
    ],
    [{"name": "B.mk", "induct": "B", "type": B, "cidx": 0, "num_params": 0, "num_fields": 0}],
)
refuse(
    "claim-ctor-under-another-type",
    b.text(),
    "the type A lists B.mk as its constructor but B.mk is declared as a constructor of B.",
    "constructor B.mk is listed under another type",
)

b = Builder()
b.inductive(
    [{"name": "T", "type": ("pi", ("sort", ONE), ("sort", ONE)), "num_params": 1, "ctors": ["T.mk"]}],
    [{"name": "T.mk", "induct": "T", "type": ("const", "T", []), "cidx": 0, "num_params": 1, "num_fields": 0}],
)
refuse(
    "constructor-too-few-parameters",
    b.text(),
    "T takes one parameter but the type of T.mk has no binder for it.",
    "constructor T.mk: too few parameters",
)

# ---- found by the full mutation sweep ----
# annotations that are not the identity-like definitions are ordinary constants (optParam, autoParam, semiOutParam)
for ann, arity in [("optParam", 2), ("autoParam", 2), ("semiOutParam", 1)]:
    b = base("Nat", "Nat.zero")
    if arity == 2:
        b.axiom(ann, [], ("pi", ("sort", ONE), ("pi", ("bvar", 0), ("sort", ONE))))
        field = _app(("const", ann, []), NAT, N_ZERO)
    else:
        b.axiom(ann, [], ("pi", ("sort", ONE), ("sort", ONE)))
        field = _app(("const", ann, []), NAT)
    one_field_block(b, field, NAT)
    refuse(
        f"{ann.lower()}-axiom-not-stripped",
        b.text(),
        f"{ann} is an axiom here, so the field type `{ann} Nat ..` is an ordinary type and the recursor's minor premise must "
        "take it, not Nat. The annotation is stripped only when the file's definition returns its first argument; a mutation "
        "that stripped it by name alone accepted the claimed recursor.",
        "the type differs from the derivation",
    )

# a projection index equal to the number of fields is out of range
b = base("Nat", "Prod", "Prod.mk")
prod_nn = _app(("const", "Prod", [0, 0]), NAT, NAT)
b.axiom("p", [], prod_nn)
b.definition("d", [], NAT, ("proj", "Prod", 2, ("const", "p", [])))
refuse(
    "projection-index-boundary", b.text(), "the third projection (index 2) of a pair.", "projection index out of range"
)

# Nat.log2 on a literal is computed, not unfolded (the kernel's list of accelerated operations includes it here)
with open(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tests", "prims", "init-4.34.0-rc2.ndjson"),
    encoding="utf-8",
) as f:
    prims = f.read().splitlines()
for name, claimed, expect in [("nat-log2-literal", 9, "accept"), ("nat-log2-literal-wrong", 10, "reject")]:
    b = Builder.extending(prims)
    b.axiom("T", [], ("pi", NAT, ("sort", ONE)))
    b.axiom("t", [], _app(("const", "T", []), ("nat", claimed)))
    b.definition(
        "d",
        [],
        _app(("const", "T", []), _app(("const", "Nat.log2", []), ("nat", 1000))),
        ("const", "t", []),
    )
    add(
        name + ".ndjson",
        b.text(),
        expect,
        f"t : T {claimed} offered as a T (Nat.log2 1000); log2 1000 is 9. Nat.log2 is defined by well-founded recursion, so "
        "only the literal shortcut (gated, like the others, on the genuine definition) decides it; a mutation that turned the "
        "shortcut off left the true claim undecided.",
        msg="the value does not have the declared type" if expect == "reject" else None,
    )

# a constant's universe levels are compared as a list, every element
b = Builder()
b.axiom("a", ["u", "v"], ("sort", ("max", ("param", "u"), ("param", "v"))))
TWO = ("succ", ONE)
b.definition("y", [], ("sort", TWO), ("const", "a", [0, TWO]))
b.definition("x", [], ("sort", TWO), ("const", "a", [0, ONE]))
refuse(
    "constant-levels-differ-in-last",
    b.text(),
    "a.{0,2} and a.{0,1} agree in their first level and differ in the second; x : Sort 2 is given a.{0,1} : Sort 1. If terms were "
    "identified when only a prefix of the level lists agreed, the second would be read as the first (found by mutation testing).",
    msg="the value does not have the declared type",
)

# two terms of a structure with fields are not the same term
b = base("Nat", "Prod", "Prod.mk", "Eq", "Eq.refl")
b.axiom("x", [], prod_nn)
b.axiom("y", [], prod_nn)
b.theorem("t", [], _app(("const", "Eq", [ONE]), prod_nn, ("const", "x", []), ("const", "y", [])), _refl_any(prod_nn))
add(
    "two-pairs-not-equal.ndjson",
    b.text(),
    "reject",
    "x y : Nat x Nat are two unknown pairs. Only a structure with no fields has all its elements equal; a mutation that applied "
    "that rule to every structure accepted x = y.",
    msg="the value does not have the declared type",
)
b = base("PUnit", "PUnit.unit", "Eq", "Eq.refl")
punit = _app(("const", "PUnit", [ONE]))
b.axiom("x", [], punit)
b.axiom("y", [], punit)
b.theorem("t", [], _app(("const", "Eq", [ONE]), punit, ("const", "x", []), ("const", "y", [])), _refl_any(punit, "x"))
add(
    "two-units-equal.ndjson",
    b.text(),
    "accept",
    "x y : PUnit are equal: a structure with no fields has one element, whatever the terms look like.",
)

# Quot.lift computes only on Quot.mk
b = base("Nat", "Eq", "Eq.refl", "Quot", "Quot.mk", "Quot.lift")
rel = ("lam", NAT, ("lam", NAT, _app(("const", "Eq", [ONE]), NAT, ("bvar", 1), ("bvar", 0))))
quot_nat = _app(("const", "Quot", [ONE]), NAT, rel)
b.axiom("g", [], ("pi", NAT, ("pi", NAT, ("pi", NAT, quot_nat))))
f_id = ("lam", NAT, ("bvar", 0))
h_id = ("lam", NAT, ("lam", NAT, ("lam", _app(rel, ("bvar", 1), ("bvar", 0)), ("bvar", 0))))
g005 = _app(("const", "g", []), ("nat", 0), ("nat", 0), ("nat", 5))
lift = _app(("const", "Quot.lift", [ONE, ONE]), NAT, rel, NAT, f_id, h_id, g005)
b.theorem("t", [], eq_nat(lift, ("nat", 5)), refl_nat(("nat", 5)))
add(
    "quot-lift-on-non-mk.ndjson",
    b.text(),
    "reject",
    "Quot.lift id h (g 0 0 5) = 5 where g is an unknown function returning quotient elements. Quot.lift reduces only on a "
    "Quot.mk; a mutation that accepted any three-argument term as one computed f 5 and accepted the claim.",
    msg="the value does not have the declared type",
)

# two applications of one definition to different arguments are different when the definition keeps them apart
b = base("Nat", "Nat.succ", "Eq", "Eq.refl")
b.axiom("a", [], NAT)
b.axiom("b", [], NAT)
b.definition("f", [], ("pi", NAT, NAT), ("lam", NAT, nat_succ(("bvar", 0))), hints="regular")
fa, fb = _app(("const", "f", []), ("const", "a", [])), _app(("const", "f", []), ("const", "b", []))
b.theorem("t", [], eq_nat(fa, fb), refl_nat(fa))
add(
    "same-definition-different-arguments.ndjson",
    b.text(),
    "reject",
    "f a = f b for f := fun x => Nat.succ x and two unknown naturals a b. The lazy comparison first tries the arguments, and "
    "when they differ it unfolds both sides; a mutation that made the failed argument comparison count as success accepted this.",
    msg="the value does not have the declared type",
)

# a definition marked unsafe or partial is unusable by a safe declaration (the parser reads the safety field)
for safety in ("unsafe", "partial"):
    b = base("Nat", "Nat.zero")
    b.definition("u", [], NAT, N_ZERO, hints="regular", safety=safety)
    b.definition("d", [], NAT, ("const", "u", []), hints="regular")
    refuse(
        f"{safety}-definition-used-by-safe.ndjson".removesuffix(".ndjson"),
        b.text(),
        f'u is a definition with safety "{safety}" and a safe definition uses it. Only the exact word safe makes a definition '
        "safe; a mutation that read every other value as safe accepted this.",
        "unsafe or partial",
    )

# an unsafe declaration may mention other unsafe constants in its type
b = Builder()
b.axiom("U1", [], ("sort", ONE), unsafe=True)
b.axiom("U2", [], ("const", "U1", []), unsafe=True)
add(
    "unsafe-axiom-mentions-unsafe.ndjson",
    b.text(),
    "accept",
    "unsafe axioms U1 : Type and U2 : U1. The type of an unsafe declaration is checked with unsafe constants allowed.",
)
b = Builder()
b.axiom("U1", [], ("sort", ONE), unsafe=True)
b.axiom("u1", [], ("const", "U1", []), unsafe=True)
b.definition("D2", [], ("const", "U1", []), ("const", "u1", []), hints="regular", safety="unsafe")
add(
    "unsafe-definition-mentions-unsafe.ndjson",
    b.text(),
    "accept",
    "an unsafe definition whose type is an unsafe constant: its type is checked with unsafe constants allowed.",
)

# blank lines between records
head = json.dumps(META, separators=(",", ":"))
add(
    "blank-lines.ndjson",
    head + "\n\n" + '{"in":1,"str":{"pre":0,"str":"x"}}\n',
    "accept",
    "an empty line between records is skipped.",
)

# structure eta compares every field
for name, first, second in [("first", "bad", "ok"), ("second", "ok", "bad")]:
    b = base("Nat", "Nat.zero", "Prod", "Prod.mk", "Eq", "Eq.refl")
    b.axiom("p", [], prod_nn)
    p_ = ("const", "p", [])
    fst, snd = ("proj", "Prod", 0, p_), ("proj", "Prod", 1, p_)
    rebuilt = _app(
        ("const", "Prod.mk", [0, 0]), NAT, NAT, N_ZERO if first == "bad" else fst, N_ZERO if second == "bad" else snd
    )
    b.theorem("t", [], _app(("const", "Eq", [ONE]), prod_nn, p_, rebuilt), _refl_any(prod_nn, "p"))
    refuse(
        f"eta-struct-{name}-field-differs",
        b.text(),
        f"p = (Nat.zero, p.2) or (p.1, Nat.zero) for an unknown pair p: the {name} field of the rebuilt pair is not the projection. "
        "Structure eta compares every field; a mutation that skipped the first one accepted the first form.",
        "the value does not have the declared type",
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


# ---------------------------------------------------------------------------------------------------------------------
# What the coverage report and the second mutation round found no test for.

DEFEQ_MSG = "the value does not have the declared type"


def nat_def(name, term, claimed, expect, why, msg=None):
    """`d : T term := t` where `t : T claimed`: accepted exactly when term and claimed are definitionally equal."""
    b = Builder.extending(prims)
    b.axiom("T", [], ("pi", NAT, ("sort", ONE)))
    b.axiom("t", [], _app(("const", "T", []), ("nat", claimed)))
    b.definition("d", [], _app(("const", "T", []), term), ("const", "t", []))
    add(name + ".ndjson", b.text(), expect, why, msg=msg or (DEFEQ_MSG if expect == "reject" else None))


def N(op, *args):
    return _app(("const", op, []), *[("nat", x) for x in args])


for op, x, y, claimed, expect, how in [
    ("Nat.div", 7, 0, 0, "accept", "dividing by zero gives zero"),
    ("Nat.div", 7, 0, 7, "reject", "dividing by zero does not give the dividend"),
    ("Nat.mod", 7, 0, 7, "accept", "the remainder modulo zero is the number itself"),
    ("Nat.mod", 7, 0, 0, "reject", "the remainder modulo zero is not zero"),
    ("Nat.div", 7, 2, 3, "accept", "division rounds down"),
    ("Nat.div", 7, 2, 4, "reject", "division does not round up"),
    ("Nat.mod", 7, 2, 1, "accept", "7 mod 2"),
    ("Nat.mod", 7, 2, 0, "reject", "7 mod 2 is not 0"),
    ("Nat.gcd", 12, 18, 6, "accept", "greatest common divisor"),
    ("Nat.gcd", 12, 18, 12, "reject", "gcd is not the first argument"),
    ("Nat.land", 12, 10, 8, "accept", "bitwise and"),
    ("Nat.land", 12, 10, 14, "reject", "bitwise and is not or"),
    ("Nat.lor", 12, 10, 14, "accept", "bitwise or"),
    ("Nat.lor", 12, 10, 8, "reject", "bitwise or is not and"),
    ("Nat.xor", 12, 10, 6, "accept", "bitwise exclusive or"),
    ("Nat.xor", 12, 10, 14, "reject", "exclusive or is not or"),
    ("Nat.shiftLeft", 3, 4, 48, "accept", "3 shifted left by 4"),
    ("Nat.shiftLeft", 3, 4, 12, "reject", "a shift left is not a shift by the other amount"),
    ("Nat.shiftRight", 48, 4, 3, "accept", "48 shifted right by 4"),
    ("Nat.shiftRight", 48, 4, 768, "reject", "a shift right is not a shift left"),
    (
        "Nat.shiftRight",
        5,
        10**20,
        0,
        "accept",
        "shifting right by more than the number has bits leaves nothing, whatever the amount",
    ),
    ("Nat.shiftRight", 5, 10**20, 5, "reject", "the amount is not ignored"),
]:
    nat_def(
        f"nat-{op.split('.')[1].lower()}-{x}-{y}-{claimed}",
        N(op, x, y),
        claimed,
        expect,
        f"{op} {x} {y} is claimed to be {claimed} ({how}). The operation is decided by the literal shortcut, so a mutation of "
        "one of its cases (found by coverage: division by zero was never run) changes this verdict.",
    )

# the limits of the shortcuts: a result beyond them is declined, one at the limit is computed
LOG2 = "Nat.log2"
for name, term, claimed, expect, why in [
    (
        "pow-exponent-at-limit",
        N("Nat.pow", 1, 16777216),
        1,
        "accept",
        "1 to the power 2^24, the largest exponent the shortcut takes",
    ),
    (
        "pow-exponent-over-limit",
        N("Nat.pow", 1, 16777217),
        1,
        "decline",
        "1 to the power 2^24+1: one past the largest exponent, declined (the result would be 1, but the limit is on the "
        "exponent, not the result)",
    ),
    (
        "pow-size-at-limit",
        _app(("const", LOG2, []), N("Nat.pow", 32768, 16777216)),
        251658240,
        "accept",
        "32768^(2^24) has 15*2^24+1 bits: its size estimate, 16*2^24 = 2^28, is exactly the limit and is computed",
    ),
    (
        "pow-size-over-limit",
        _app(("const", LOG2, []), N("Nat.pow", 65536, 16777216)),
        268435456,
        "decline",
        "65536^(2^24): the size estimate is 17*2^24, over the limit 2^28",
    ),
    (
        "shiftleft-amount-at-limit",
        _app(("const", LOG2, []), N("Nat.shiftLeft", 1, 16777216)),
        16777216,
        "accept",
        "1 shifted left by 2^24, the largest amount the shortcut takes",
    ),
    (
        "shiftleft-amount-over-limit",
        _app(("const", LOG2, []), N("Nat.shiftLeft", 1, 16777217)),
        16777217,
        "decline",
        "one past the largest shift",
    ),
    (
        "shiftleft-amount-huge",
        _app(("const", LOG2, []), N("Nat.shiftLeft", 1, 10**30)),
        1,
        "decline",
        "a shift by 10^30 does not fit a machine integer: it must be declined before the amount is converted",
    ),
]:
    nat_def(
        "nat-" + name,
        term,
        claimed,
        expect,
        why + ". A decline is the checker saying it cannot decide, never a verdict.",
        msg="too large" if expect == "decline" else None,
    )

# string literals: the meaning of "ab" is String.ofList [Char.ofNat 97, Char.ofNat 98]
STRING = ("const", "String", [])
CHAR = ("const", "Char", [])


def chars(cps):
    lst = _app(("const", "List.nil", [0]), CHAR)
    for cp in reversed(cps):
        lst = _app(("const", "List.cons", [0]), CHAR, _app(("const", "Char.ofNat", []), ("nat", cp)), lst)
    return lst


def of_list(cps):
    return _app(("const", "String.ofList", []), chars(cps))


def string_base():
    return base(
        "String", "Char", "Nat", "List", "List.nil", "List.cons", "Eq", "Eq.refl", "String.ofList", "Char.ofNat",
        "String.toByteArray", "ByteArray",
    )  # fmt: skip


for name, s, cps, expect, why in [
    ("string-literal-expands", "ab", [97, 98], "accept", '"ab" is String.ofList [97, 98]'),
    ("string-literal-empty", "", [], "accept", '"" is String.ofList []'),
    ("string-literal-wrong-char", "ab", [97, 99], "reject", "the second character differs"),
    ("string-literal-too-short", "ab", [97], "reject", "the list is shorter than the string"),
    ("string-literal-too-long", "a", [97, 98], "reject", "the list is longer than the string"),
    ("string-literal-two-byte-char", "é", [233], "accept", "a character of two UTF-8 bytes is one list element"),
    ("string-literal-bytes-not-chars", "é", [195, 169], "reject", "the elements are characters, not bytes"),
    ("string-literal-three-byte-char", "€", [8364], "accept", "a character of three UTF-8 bytes"),
    ("string-literal-four-byte-char", "\U0001f600", [128512], "accept", "a character of four UTF-8 bytes"),
    ("string-literal-mixed-widths", "héllo", [104, 233, 108, 108, 111], "accept", "characters of different widths"),
    ("string-literal-mixed-widths-wrong", "héllo", [104, 233, 108, 111], "reject", "one character missing"),
]:
    b = string_base()
    b.theorem(
        "t",
        [],
        _app(("const", "Eq", [ONE]), STRING, ("str", s), of_list(cps)),
        _app(("const", "Eq.refl", [ONE]), STRING, ("str", s)),
    )
    add(
        name + ".ndjson",
        b.text(),
        expect,
        f"{why}. Found by coverage: the expansion of a string literal into the environment's String.ofList was reached by "
        "no quick test (only by the full Init check).",
        msg=DEFEQ_MSG if expect == "reject" else None,
    )

b = string_base()
b.theorem(
    "t",
    [],
    _app(("const", "Eq", [ONE]), STRING, ("str", "a"), ("str", "b")),
    _app(("const", "Eq.refl", [ONE]), STRING, ("str", "a")),
)
add(
    "string-literals-differ.ndjson",
    b.text(),
    "reject",
    '"a" and "b" are different literals; a mutation that made two string literals equal whatever their text accepted.',
    msg=DEFEQ_MSG,
)
for name, cps, expect in [
    ("string-literal-whnf", [97, 98], "accept"),
    ("string-literal-whnf-wrong", [97, 99], "reject"),
]:
    b = string_base()
    bytes_of = lambda x: _app(("const", "String.toByteArray", []), x)  # noqa: E731
    b.theorem(
        "t",
        [],
        _app(("const", "Eq", [ONE]), ("const", "ByteArray", []), bytes_of(("str", "ab")), bytes_of(of_list(cps))),
        _app(("const", "Eq.refl", [ONE]), ("const", "ByteArray", []), bytes_of(("str", "ab"))),
    )
    add(
        name + ".ndjson",
        b.text(),
        expect,
        'String.toByteArray of the literal "ab" against String.toByteArray of the expansion: the literal must be expanded '
        "when it is the major premise of a recursor or the argument of a projection (found by coverage).",
        msg=DEFEQ_MSG if expect == "reject" else None,
    )

# a primitive whose dependency is not the genuine definition loses the shortcut (the fingerprint holds the kind of every
# constant it depends on)
with open(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tests", "prims", "init-4.34.0-rc2.ndjson"),
    encoding="utf-8",
) as f:
    prim_lines = f.read().splitlines()
add_lines = slice_lines(prim_lines, ["Nat.add"])  # Nat.add and what it is built from, nothing else
prim_names = {0: ""}  # the ids of the cut, not of the whole file
for ln in add_lines:
    o = json.loads(ln)
    if "in" in o:
        sub = o.get("str") or o.get("num")
        pre = prim_names[sub["pre"]]
        last = sub["str"] if "str" in o else str(sub["i"])
        prim_names[o["in"]] = (pre + "." if pre else "") + last


def tamper_dependency(dep, to_kind):
    out = []
    for ln in add_lines:
        o = json.loads(ln)
        d = o.get("def")
        if d and prim_names[d["name"]] == dep:
            if to_kind == "opaque":
                o = {
                    "opaque": {
                        "name": d["name"], "levelParams": d["levelParams"], "type": d["type"], "value": d["value"],
                        "isUnsafe": False, "all": d["all"],
                    }
                }  # fmt: skip
            else:
                o = {
                    "axiom": {"name": d["name"], "levelParams": d["levelParams"], "type": d["type"], "isUnsafe": False}
                }
            ln = json.dumps(o, separators=(",", ":"), sort_keys=True)
        out.append(ln)
    return out


for kind in ("genuine", "opaque", "axiom"):
    b = Builder.extending(add_lines if kind == "genuine" else tamper_dependency("Nat.add._f", kind))
    b.axiom("T", [], ("pi", NAT, ("sort", ONE)))
    b.axiom("t", [], _app(("const", "T", []), ("nat", 200000000)))
    b.definition("d", [], _app(("const", "T", []), N("Nat.add", 100000000, 100000000)), ("const", "t", []))
    if kind == "genuine":
        add(
            "prim-dependency-genuine.ndjson",
            b.text(),
            "accept",
            "the control for the next two: Nat.add and what it is built from, as exported, and 10^8 + 10^8 = 2 * 10^8, which only the shortcut can decide (unfolding would take 10^8 steps).",
        )
        continue
    add(
        f"prim-dependency-{kind}.ndjson",
        b.text(),
        "reject",
        f"Nat.add._f, the helper Nat.add is built from, is {'an opaque constant with the genuine value' if kind == 'opaque' else 'an axiom of the genuine type'}. "
        "Nat.add no longer has the genuine fingerprint, so 10^8 + 10^8 is not computed, and unfolding stops at the helper: the claim "
        "T (10^8 + 10^8) from t : T (2 * 10^8) is refused. If the fingerprint did not hold the kind of a dependency (an opaque constant, an axiom), the "
        "shortcut would stay on and accept it (found by coverage: those branches of the fingerprint ran in no test).",
        msg=DEFEQ_MSG,
    )

# two universe levels that are equal and are compared by the decision procedure, which splits on the parameters
for n, expect in [(14, "accept"), (15, "decline")]:
    ps = [f"u{i}" for i in range(1, n + 1)]

    def mx(order):
        lvl = ("param", order[-1])
        for p_ in reversed(order[:-1]):
            lvl = ("max", ("param", p_), lvl)
        return lvl

    b = Builder()
    b.axiom("A", ps, ("sort", ("imax", ONE, mx(ps))))
    b.definition("d", ps, ("sort", ("imax", ONE, mx(list(reversed(ps))))), ("const", "A", [("param", p_) for p_ in ps]))
    add(
        f"level-{n}-parameters-in-imax.ndjson",
        b.text(),
        expect,
        f"Sort (imax 1 (max u1 .. u{n})) against the same with the parameters in the other order: equal levels that are not "
        f"the same term, decided by splitting on each of the {n} parameters. The procedure splits on at most 14 and declines "
        "beyond (the work doubles with each); a mutation of the bound moved the line.",
        msg="universe constraint" if expect == "decline" else None,
    )

# a universe parameter that occurs only in the body of a let (or only in its type and value) in a constant's type is still
# instantiated when the constant is used
U = ("param", "u")
for name, ty_c, expect, why in [
    (
        "let-body-universe-parameter",
        ("let", NAT, ("nat", 0), ("sort", U)),
        "accept",
        "c.{u} : let n : Nat := 0 in Sort u, and d : Prop := c.{0}: the type of c.{0} is the let with u replaced by 0, which "
        "reduces to Prop. A mutation of the cached 'mentions a universe parameter' flag of a let (ignoring the body) left u "
        "uninstantiated and the claim failed (found by mutation testing).",
    ),
    (
        "let-type-and-value-universe-parameter",
        ("let", ("sort", ("succ", U)), ("sort", U), ("bvar", 0)),
        "accept",
        "e.{u} : let X : Sort (u+1) := Sort u in X, and d : Prop := e.{0}: same, with the parameter in the type and the value.",
    ),
]:
    b = base("Nat")
    b.axiom("c", ["u"], ty_c)
    b.definition("d", [], ("sort", 0), ("const", "c", [0]))
    add(name + ".ndjson", b.text(), expect, why)
b = base("Nat")
b.axiom("c", ["u"], ("let", NAT, ("nat", 0), ("sort", U)))
b.definition("d", [], ("sort", ONE), ("const", "c", [0]))
add(
    "let-body-universe-parameter-wrong.ndjson",
    b.text(),
    "reject",
    "the same constant offered as a Type: c.{0} : Prop, not Type.",
    msg=DEFEQ_MSG,
)

# ---------------------------------------------------------------------------------------------------------------------
# Mutation round 3: what the AST-level mutants of the inductive and universe checks found no test for.

# A constructor field whose type has a non-positive occurrence is refused by the positivity check itself. The claims are the
# ones the checker would derive were the occurrence harmless (the field is not recursive: no induction hypothesis), so that
# nothing else about the file is wrong; a mutation that dropped the check then accepted the file, and the existing tests only
# refused such files because their claimed flags happened to differ.
b = base("Nat")
b.axiom("F", [], ("pi", ("sort", ONE), ("sort", ONE)))
for name, field_ty, why in [
    ("positivity-domain", ("pi", T, NAT), "mk : (T -> Nat) -> T: T occurs in the domain of the field's type"),
    (
        "positivity-domain-of-domain",
        ("pi", ("pi", T, NAT), NAT),
        "mk : ((T -> Nat) -> Nat) -> T: T occurs in the domain of a domain (strict positivity forbids it, as in Lean)",
    ),
    (
        "positivity-under-binder",
        ("pi", NAT, ("pi", T, NAT)),
        "mk : (Nat -> T -> Nat) -> T: the occurrence is in the second binder, below an innocent one",
    ),
]:
    b = base("Nat")
    # the flags are the derived ones, too: the type is recursive and reflexive by the syntactic definition
    one_field_block(b, field_ty, field_ty, lambda types, ctors, recs: types[0].update(is_rec=True, is_reflexive=True))
    add(
        name + ".ndjson",
        b.text(),
        "reject",
        why + ".",
        msg="non-positive occurrence",
    )
b = base("Nat")
b.axiom("F", [], ("pi", ("sort", ONE), ("sort", ONE)))
one_field_block(
    b,
    ("app", ("const", "F", []), T),
    ("app", ("const", "F", []), T),
    lambda types, ctors, recs: types[0].update(is_rec=True),
)
add(
    "positivity-argument-of-other-constant.ndjson",
    b.text(),
    "reject",
    "mk : F T -> T for an axiom F : Type -> Type: T occurs as an argument of something that is not an inductive type of the block "
    "(nor a nested one: F is not an inductive type), so the occurrence is invalid.",
    msg="invalid occurrence",
)

# a constant used at a universe level that is not declared
b = Builder()
b.axiom("A", ["v"], ("sort", ONE))
b.definition("d", [], ("sort", ONE), ("const", "A", [("param", "w")]))
add(
    "const-level-not-declared.ndjson",
    b.text(),
    "reject",
    "d : Type := A.{w}, where w is not a universe parameter of d (found by mutation testing: no test used a constant at an "
    "undeclared level; the Sort case had two).",
    msg="universe parameter out of scope in A",
)

# string literals compared the other way round, and against String.mk (older toolchains)
for name, cps, expect in [
    ("string-literal-reversed", [97, 98], "accept"),
    ("string-literal-reversed-wrong", [97, 99], "reject"),
]:
    b = string_base()
    b.theorem(
        "t",
        [],
        _app(("const", "Eq", [ONE]), STRING, of_list(cps), ("str", "ab")),
        _app(("const", "Eq.refl", [ONE]), STRING, of_list(cps)),
    )
    add(
        name + ".ndjson",
        b.text(),
        expect,
        'String.ofList [..] against the literal "ab": the expansion also happens when the application is on the left.',
        msg=DEFEQ_MSG if expect == "reject" else None,
    )
for name, cps, expect in [("string-mk-literal", [97, 98], "accept"), ("string-mk-literal-wrong", [97, 99], "reject")]:
    b = base("Char", "Nat", "List", "List.nil", "List.cons", "Eq", "Eq.refl", "Char.ofNat")
    b.axiom("String", [], ("sort", ONE))
    b.axiom("String.mk", [], ("pi", ("app", ("const", "List", [0]), CHAR), STRING))
    b.theorem(
        "t",
        [],
        _app(("const", "Eq", [ONE]), STRING, ("str", "ab"), _app(("const", "String.mk", []), chars(cps))),
        _app(("const", "Eq.refl", [ONE]), STRING, ("str", "ab")),
    )
    add(
        name + ".ndjson",
        b.text(),
        expect,
        'A toolchain whose String has the constructor String.mk (and no String.ofList): the literal "ab" is String.mk '
        "[a, b]. Found by mutation testing: nothing used the older name.",
        msg=DEFEQ_MSG if expect == "reject" else None,
    )

# the auxiliary type made for a nested occurrence takes a name no declaration has
b = base("Nat", "List", "List.nil", "List.cons")
b.axiom("_nested.List_1", [], ("sort", ONE))
build_nested_param_tree(b)
add(
    "nested-auxiliary-name-taken.ndjson",
    b.text(),
    "accept",
    "the nested tree of the previous file in an environment where `_nested.List_1`, the first name the checker would give the "
    "auxiliary type for List, already exists: it must take the next one. A mutation that skipped the check for an existing name "
    "collided with the declaration (found by mutation testing).",
)

# a recursor applied to fewer arguments than it takes is stuck, not an error
b = base("Nat", "Nat.rec", "Nat.zero", "Eq", "Eq.refl")
motive = ("lam", NAT, NAT)
partial = _app(("const", "Nat.rec", [ONE]), motive, ("nat", 0), ("lam", NAT, ("lam", NAT, ("bvar", 0))))
nat_to_nat = ("pi", NAT, NAT)
b.theorem(
    "t",
    [],
    _app(("const", "Eq", [ONE]), nat_to_nat, partial, ("lam", NAT, ("app", partial, ("bvar", 0)))),
    _app(("const", "Eq.refl", [ONE]), nat_to_nat, partial),
)
add(
    "recursor-partial-application-eta.ndjson",
    b.text(),
    "accept",
    "Nat.rec (fun _ => Nat) 0 (fun _ ih => ih) has its major premise missing: it is stuck, and equal to its eta-expansion. A "
    "mutation that read the major premise past the end of the arguments raised an internal error (a decline) here "
    "(found by mutation testing: nothing else compared a partly applied recursor).",
)

# an identity-like function that is not one of the four annotations is not stripped from a field type
b = base("Nat")
b.definition(
    "myIdentity",
    ["u"],
    ("pi", ("sort", ("param", "u")), ("sort", ("param", "u"))),
    ("lam", ("sort", ("param", "u")), ("bvar", 0)),
)
one_field_block(
    b,
    ("app", ("const", "myIdentity", [ONE]), NAT),
    ("app", ("const", "myIdentity", [ONE]), NAT),
)
add(
    "identity-function-not-an-annotation.ndjson",
    b.text(),
    "accept",
    "myIdentity.{u} (a : Sort u) : Sort u := a is a function that returns its first argument, like outParam, but it is not one of "
    "the four annotations the derivation strips (outParam, semiOutParam, optParam, autoParam): the field `myIdentity Nat` stays "
    "as it is, and the recursor's minor premise takes it. A mutation that stripped any such function refused the claimed "
    "recursor (found by mutation testing).",
)

# a computation rule that names the wrong constructor, with the right right-hand side
bool_lines = base("Bool", "Bool.rec").lines
swapped = []
for ln in bool_lines:
    o = json.loads(ln)
    if "inductive" in o and len(o["inductive"]["recs"]) == 1 and len(o["inductive"]["recs"][0]["rules"]) == 2:
        rules = o["inductive"]["recs"][0]["rules"]
        rules[0]["ctor"], rules[1]["ctor"] = rules[1]["ctor"], rules[0]["ctor"]
        ln = json.dumps(o, separators=(",", ":"), sort_keys=True)
    swapped.append(ln)
add(
    "rec-rule-names-the-wrong-constructor.ndjson",
    "\n".join(swapped) + "\n",
    "reject",
    "Bool.rec with the constructor names of its two computation rules exchanged and the right-hand sides left where they are: "
    "the rules differ from the derived ones in the constructor alone (found by mutation testing: every other test that changes a "
    "rule changes its right-hand side or the number of fields too).",
    msg="a computation rule differs from the derivation",
)

# Nat.log2 at the edges: log2 0 = 0 (the logarithm of zero is not an error), log2 1 = 0, log2 (2^k) = k, log2 (2^k - 1) = k - 1
for x, claimed, expect in [
    (0, 0, "accept"),
    (0, 1, "reject"),
    (1, 0, "accept"),
    (2, 1, "accept"),
    (3, 1, "accept"),
    (4, 2, "accept"),
    (4, 1, "reject"),
]:
    nat_def(
        f"nat-log2-{x}-{claimed}",
        _app(("const", "Nat.log2", []), ("nat", x)),
        claimed,
        expect,
        f"Nat.log2 {x} is claimed to be {claimed}. The machine logarithm is undefined at 0; the shortcut must answer 0 there, "
        "as the definition does (a mutation that did not special-case it raised an internal error: found by mutation testing).",
    )

# the type has fewer binders than the claimed number of parameters
b = base("Nat")
one_field_block(
    b,
    NAT,
    NAT,
    lambda types, ctors, recs: (
        types[0].update(num_params=1),
        ctors[0].update(num_params=1),
        recs[0].update(num_params=1),
    ),
)
add(
    "inductive-fewer-binders-than-parameters.ndjson",
    b.text(),
    "reject",
    "T : Type is claimed to have one parameter. A mutation that dropped the check read the missing parameter later and raised "
    "an internal error (a decline) instead of refusing the claim (found by mutation testing).",
    msg="number of parameters mismatch",
)


# each quotient declaration needs the ones it mentions: the declaration of the needed one is removed from a real cut
def without_quot(target, kind_removed):
    with open(PRELUDE_PATH, encoding="utf-8") as f:
        cut = slice_lines(f, [target, "Eq", "Eq.refl"])
    kept = [ln for ln in cut if not ('"quot"' in ln and json.loads(ln)["quot"]["kind"] == kind_removed)]
    assert len(kept) == len(cut) - 1, (target, kind_removed)
    return "\n".join(kept) + "\n"


for target, removed, needs, why in [
    ("Quot.mk", "type", "Quot.mk needs Quot", "Quot.mk declared without Quot"),
    ("Quot.ind", "ctor", "Quot.ind needs Quot.mk", "Quot.ind declared without Quot.mk"),
]:
    add(
        f"quot-{target.split('.')[1]}-without-{removed}.ndjson",
        without_quot(target, removed),
        "reject",
        why
        + ": each quotient declaration needs the ones its type mentions (found by mutation testing: the checks of the "
        "order were never reached).",
        msg=needs,
    )
with open(PRELUDE_PATH, encoding="utf-8") as f:
    lift_cut = slice_lines(f, ["Quot.lift"])
if not any('"quot"' in ln and json.loads(ln)["quot"]["kind"] == "ctor" for ln in lift_cut):
    add(
        "quot-lift-without-ctor.ndjson",
        "\n".join(lift_cut) + "\n",
        "reject",
        "Quot.lift declared with Quot but without Quot.mk (the cut of Quot.lift from a real export has no Quot.mk): the lift rule "
        "computes on Quot.mk, so it is needed first.",
        msg="Quot.lift needs Quot.mk",
    )

# the recursor's claimed counts must be the derived ones, one by one
for field, value, why in [
    ("num_params", 1, "one parameter more than the type has"),
    ("num_indices", 1, "one index more than the type has"),
    ("num_motives", 2, "two motives for a single type"),
    ("num_minors", 2, "two minor premises for a single constructor"),
]:
    b = base("Nat")
    one_field_block(b, NAT, NAT, lambda types, ctors, recs, f=field, v=value: recs[0].update({f: v}))
    add(
        f"rec-claims-wrong-{field.replace('_', '-')}.ndjson",
        b.text(),
        "reject",
        f"T.rec claimed with {why}: the counts are claims, compared with the derived ones one by one (found by mutation "
        "testing: a comparison of the motive count alone could be dropped unnoticed).",
        msg="counts differ",
    )

# a constructor whose result is not its type
b = base("Nat")
one_field_block(b, NAT, NAT, lambda types, ctors, recs: ctors[0].update(type=("pi", NAT, NAT)))
add(
    "constructor-wrong-return-type.ndjson",
    b.text(),
    "reject",
    "T.mk : Nat -> Nat, a constructor of T whose result is Nat. Found by mutation testing: nothing else reached the check.",
    msg="invalid return type",
)

# An Eq that the quotient rules do not accept although it is an inductive family of the right type: the check compares more
# than the type of Eq. Both are built with their recursors, as the checker derives them (so that nothing else about the file is
# wrong); the second part of the quotient package is declared after them.
SV = ("sort", ("param", "v"))
SU = ("sort", ("param", "u"))
EQ_V = lambda *a: _app(("const", "Eq", [("param", "v")]), *a)  # noqa: E731
EQ_REFL_V = lambda *a: _app(("const", "Eq.refl", [("param", "v")]), *a)  # noqa: E731
eq_type = db(tele("pin", [("A", SV), ("a", V("A")), ("b", V("A"))], PROP), [])

# (1) one parameter and two indices instead of two parameters and one index: Eq.refl : (a : A) -> Eq A a a with `a` a field
motive_1 = tele("pin", [("a", V("A")), ("b", V("A")), ("t", EQ_V(V("A"), V("a"), V("b")))], SU)
minor_1 = tele("pin", [("a", V("A"))], _app(V("m"), V("a"), V("a"), EQ_REFL_V(V("A"), V("a"))))
rec_1 = tele(
    "pin",
    [("A", SV), ("m", motive_1), ("r", minor_1), ("a", V("A")), ("b", V("A")), ("t", EQ_V(V("A"), V("a"), V("b")))],
    _app(V("m"), V("a"), V("b"), V("t")),
)
rule_1 = tele("lamn", [("A", SV), ("m", motive_1), ("r", minor_1), ("a", V("A"))], _app(V("r"), V("a")))
b = Builder()
b.inductive(
    [{"name": "Eq", "lparams": ["v"], "type": eq_type, "num_params": 1, "num_indices": 2, "ctors": ["Eq.refl"]}],
    [
        {
            "name": "Eq.refl",
            "induct": "Eq",
            "lparams": ["v"],
            "type": db(tele("pin", [("A", SV), ("a", V("A"))], EQ_V(V("A"), V("a"), V("a"))), []),
            "cidx": 0,
            "num_params": 1,
            "num_fields": 1,
        }
    ],
    [
        {
            "name": "Eq.rec",
            "lparams": ["u", "v"],
            "type": db(rec_1, []),
            "num_params": 1,
            "num_indices": 2,
            "num_motives": 1,
            "num_minors": 1,
            "rules": [("Eq.refl", 1, db(rule_1, []))],
        }
    ],
)
eq_variant_1 = b.text()
b.quot("type", "Quot", ["u"], QUOT_TY)
add(
    "quot-eq-other-split-of-arguments.ndjson",
    b.text(),
    "reject",
    "Eq with one parameter and two indices (Eq.refl has the field `a`): the same type and the same constructor type as the real Eq, "
    "another recursor. The quotient rules need the real Eq; the official kernel does not look at the split, WARRANT does (found by "
    "mutation testing: the two counts could be dropped unnoticed).",
    msg="quotient: Eq is not the expected inductive family",
)
add(
    "eq-other-split-of-arguments-alone.ndjson",
    eq_variant_1,
    "accept",
    "the control for the previous file: that Eq on its own is a valid inductive family (its recursor is the derived one).",
)

# (2) the real split, but the constructor's type has a redex in the index: Eq.refl : (A) (a : A) -> Eq A a ((fun x => x) a)
redex = _app(("lamn", "x", V("A"), V("x")), V("a"))
motive_2 = tele("pin", [("b", V("A")), ("t", EQ_V(V("A"), V("a"), V("b")))], SU)
minor_2 = _app(V("m"), redex, EQ_REFL_V(V("A"), V("a")))
rec_2 = tele(
    "pin",
    [("A", SV), ("a", V("A")), ("m", motive_2), ("r", minor_2), ("b", V("A")), ("t", EQ_V(V("A"), V("a"), V("b")))],
    _app(V("m"), V("b"), V("t")),
)
rule_2 = tele("lamn", [("A", SV), ("a", V("A")), ("m", motive_2), ("r", minor_2)], V("r"))
b = Builder()
b.inductive(
    [{"name": "Eq", "lparams": ["v"], "type": eq_type, "num_params": 2, "num_indices": 1, "ctors": ["Eq.refl"]}],
    [
        {
            "name": "Eq.refl",
            "induct": "Eq",
            "lparams": ["v"],
            "type": db(tele("pin", [("A", SV), ("a", V("A"))], EQ_V(V("A"), V("a"), redex)), []),
            "cidx": 0,
            "num_params": 2,
            "num_fields": 0,
        }
    ],
    [
        {
            "name": "Eq.rec",
            "lparams": ["u", "v"],
            "type": db(rec_2, []),
            "num_params": 2,
            "num_indices": 1,
            "num_motives": 1,
            "num_minors": 1,
            "k": True,
            "rules": [("Eq.refl", 0, db(rule_2, []))],
        }
    ],
)
eq_variant_2 = b.text()
b.quot("type", "Quot", ["u"], QUOT_TY)
add(
    "quot-eq-refl-type-not-the-expected-one.ndjson",
    b.text(),
    "reject",
    "Eq with the real split whose constructor has the type (A) (a : A) -> Eq A a ((fun x => x) a): the same up to reduction, not "
    "the type the quotient rules are stated for. A mutation that dropped the comparison of the constructor's type accepted it.",
    msg="quotient: Eq is not the expected inductive family",
)
add(
    "eq-refl-with-redex-alone.ndjson",
    eq_variant_2,
    "accept",
    "the control for the previous file: that Eq on its own is a valid inductive family.",
)

# A nested occurrence in a container that has an index: Vec (a : Type) : Nat -> Type, and T := mk (Vec T 0). The container's
# recursor and the nested type's two recursors are written as the checker derives them.
W = ("param", "w")
TYPE_W = ("sort", ("succ", W))
NZERO = ("const", "Nat.zero", [])
nsucc = lambda n: _app(("const", "Nat.succ", []), n)  # noqa: E731
vec_w = lambda *a: _app(("const", "Vec", [W]), *a)  # noqa: E731
vec_nil_w = lambda a: _app(("const", "Vec.nil", [W]), a)  # noqa: E731
vec_cons_w = lambda *a: _app(("const", "Vec.cons", [W]), *a)  # noqa: E731
vec_0 = lambda *a: _app(("const", "Vec", [0]), *a)  # noqa: E731
vec_nil_0 = lambda a: _app(("const", "Vec.nil", [0]), a)  # noqa: E731
vec_cons_0 = lambda *a: _app(("const", "Vec.cons", [0]), *a)  # noqa: E731


def build_vec_nested(b, break_rule=None):
    m_vec = tele("pin", [("n", NAT), ("v", vec_w(V("A"), V("n")))], SU)
    nil_minor = _app(V("m"), NZERO, vec_nil_w(V("A")))
    cons_minor = tele(
        "pin",
        [("n", NAT), ("a", V("A")), ("v", vec_w(V("A"), V("n"))), ("ih", _app(V("m"), V("n"), V("v")))],
        _app(V("m"), nsucc(V("n")), vec_cons_w(V("A"), V("n"), V("a"), V("v"))),
    )
    vec_head = [("A", TYPE_W), ("m", m_vec), ("nl", nil_minor), ("cn", cons_minor)]
    vec_rec_ty = tele("pin", vec_head + [("n", NAT), ("t", vec_w(V("A"), V("n")))], _app(V("m"), V("n"), V("t")))
    vrec = lambda *a: _app(("const", "Vec.rec", [("param", "u"), W]), V("A"), V("m"), V("nl"), V("cn"), *a)  # noqa: E731
    b.inductive(
        [
            {
                "name": "Vec",
                "lparams": ["w"],
                "type": db(tele("pin", [("A", TYPE_W), ("n", NAT)], TYPE_W), []),
                "num_params": 1,
                "num_indices": 1,
                "ctors": ["Vec.nil", "Vec.cons"],
                "is_rec": True,
            }
        ],
        [
            {
                "name": "Vec.nil",
                "induct": "Vec",
                "lparams": ["w"],
                "type": db(tele("pin", [("A", TYPE_W)], vec_w(V("A"), NZERO)), []),
                "cidx": 0,
                "num_params": 1,
                "num_fields": 0,
            },
            {
                "name": "Vec.cons",
                "induct": "Vec",
                "lparams": ["w"],
                "type": db(
                    tele(
                        "pin",
                        [("A", TYPE_W), ("n", NAT), ("a", V("A")), ("v", vec_w(V("A"), V("n")))],
                        vec_w(V("A"), nsucc(V("n"))),
                    ),
                    [],
                ),
                "cidx": 1,
                "num_params": 1,
                "num_fields": 3,
            },
        ],
        [
            {
                "name": "Vec.rec",
                "lparams": ["u", "w"],
                "type": db(vec_rec_ty, []),
                "num_params": 1,
                "num_indices": 1,
                "num_motives": 1,
                "num_minors": 2,
                "rules": [
                    ("Vec.nil", 0, db(tele("lamn", vec_head, V("nl")), [])),
                    (
                        "Vec.cons",
                        3,
                        db(
                            tele(
                                "lamn",
                                vec_head + [("n", NAT), ("a", V("A")), ("v", vec_w(V("A"), V("n")))],
                                _app(V("cn"), V("n"), V("a"), V("v"), vrec(V("n"), V("v"))),
                            ),
                            [],
                        ),
                    ),
                ],
            }
        ],
    )
    # the nested type T := mk (Vec T 0)
    T_ = ("const", "T", [])
    m1_t = tele("pin", [("t", T_)], SU)
    m2_t = tele("pin", [("n", NAT), ("v", vec_0(T_, V("n")))], SU)
    mk_minor = tele(
        "pin",
        [("a", vec_0(T_, NZERO)), ("ih", _app(V("m2"), NZERO, V("a")))],
        _app(V("m1"), _app(("const", "T.mk", []), V("a"))),
    )
    nl_minor = _app(V("m2"), NZERO, vec_nil_0(T_))
    cn_minor = tele(
        "pin",
        [
            ("n", NAT),
            ("a", T_),
            ("v", vec_0(T_, V("n"))),
            ("ih1", _app(V("m1"), V("a"))),
            ("ih2", _app(V("m2"), V("n"), V("v"))),
        ],
        _app(V("m2"), nsucc(V("n")), vec_cons_0(T_, V("n"), V("a"), V("v"))),
    )
    head = [("m1", m1_t), ("m2", m2_t), ("mk", mk_minor), ("nl", nl_minor), ("cn", cn_minor)]
    rec0_ty = tele("pin", head + [("t", T_)], _app(V("m1"), V("t")))
    rec1_ty = tele("pin", head + [("n", NAT), ("t", vec_0(T_, V("n")))], _app(V("m2"), V("n"), V("t")))
    hargs = [V(n) for n, _ in head]
    r0 = lambda *a: _app(("const", "T.rec", [("param", "u")]), *hargs, *a)  # noqa: E731
    r1 = lambda *a: _app(("const", "T.rec_1", [("param", "u")]), *hargs, *a)  # noqa: E731
    rule_mk = tele("lamn", head + [("a", vec_0(T_, NZERO))], _app(V("mk"), V("a"), r1(NZERO, V("a"))))
    rule_nil = tele("lamn", head, V("nl"))
    rule_cons = tele(
        "lamn",
        head + [("n", NAT), ("a", T_), ("v", vec_0(T_, V("n")))],
        _app(V("cn"), V("n"), V("a"), V("v"), r0(V("a")), r1(V("n"), V("v"))),
    )
    recs = [
        {
            "name": "T.rec",
            "lparams": ["u"],
            "type": db(rec0_ty, []),
            "num_params": 0,
            "num_indices": 0,
            "num_motives": 2,
            "num_minors": 3,
            "rules": [("T.mk", 1, db(rule_mk, []))],
        },
        {
            "name": "T.rec_1",
            "lparams": ["u"],
            "type": db(rec1_ty, []),
            "num_params": 0,
            "num_indices": 1,
            "num_motives": 2,
            "num_minors": 3,
            "rules": [("Vec.nil", 0, db(rule_nil, [])), ("Vec.cons", 3, db(rule_cons, []))],
        },
    ]
    if break_rule:
        break_rule(recs)
    b.inductive(
        [{"name": "T", "type": ("sort", ONE), "num_params": 0, "ctors": ["T.mk"], "is_rec": True, "num_nested": 1}],
        [
            {
                "name": "T.mk",
                "induct": "T",
                "type": db(tele("pin", [("a", vec_0(T_, NZERO))], T_), []),
                "cidx": 0,
                "num_params": 0,
                "num_fields": 1,
            }
        ],
        recs,
    )


b = base("Nat", "Nat.zero", "Nat.succ")
build_vec_nested(b)
add(
    "nested-in-indexed-container.ndjson",
    b.text(),
    "accept",
    "Vec (A : Type w) : Nat -> Type w with its recursor, and T := mk (Vec T 0): a nested occurrence in a container that has an "
    "index. The auxiliary type has the index, the nested recursor takes it, and the rules rebuild the container's constructors over "
    "T. Found by mutation testing: nothing else nested through a container with indices, so the split of the container's "
    "arguments into parameters and indices could be changed unnoticed.",
)

# a mutual block of two propositions, one with a constructor without fields and one empty: no K, small elimination
A_A = ("const", "A.a", [])
head_ab = [
    ("m1", ("pi", A, PROP)),
    ("m2", ("pi", B, PROP)),
    ("a", _app(V("m1"), A_A)),
]
b = Builder()
b.inductive(
    [
        {"name": "A", "type": PROP, "num_params": 0, "ctors": ["A.a"]},
        {"name": "B", "type": PROP, "num_params": 0},
    ],
    [{"name": "A.a", "induct": "A", "type": A, "cidx": 0, "num_params": 0, "num_fields": 0}],
    [
        {
            "name": "A.rec",
            "type": db(tele("pin", head_ab + [("t", A)], _app(V("m1"), V("t"))), []),
            "num_params": 0,
            "num_motives": 2,
            "num_minors": 1,
            "rules": [("A.a", 0, db(tele("lamn", head_ab, V("a")), []))],
        },
        {
            "name": "B.rec",
            "type": db(tele("pin", head_ab + [("t", B)], _app(V("m2"), V("t"))), []),
            "num_params": 0,
            "num_motives": 2,
            "num_minors": 1,
            "rules": [],
        },
    ],
)
add(
    "mutual-props-no-k.ndjson",
    b.text(),
    "accept",
    "A : Prop with a constructor without fields and B : Prop without constructors, declared together. K-like reduction (the "
    "recursor treats any proof as the constructor) is for a single proposition with a single constructor without fields; this block "
    "has one constructor without fields in all and two types. A mutation that dropped the test for a single type gave both "
    "recursors the K flag and the claim (no K) was refused (found by mutation testing).",
)

# a key repeated that is not the first key of the object
add(
    "duplicate-key-not-first.ndjson",
    head + '\n{"str":{"pre":0,"str":"x"},"in":1,"in":2}\n',
    "decline",
    "the repeated key is the second and third of the object: the check looked for repeats of the first key only (found by mutation "
    "testing).",
    msg="duplicate key",
)
add(
    "duplicate-key-nested.ndjson",
    head + '\n{"in":1,"str":{"pre":0,"str":"x","pre":1}}\n',
    "decline",
    "a repeated key inside a nested object.",
    msg="duplicate key",
)

# The failure of the same-arguments attempt of the lazy delta step is not a verdict about the pair. f 1 and f 2 (f := fun _ => 0)
# are tried once under a beta redex, found different in their arguments, and then agree after unfolding; asked directly later they
# must still agree. The attempt's failures were once recorded where is_def_eq looks for definite failures, and the later, direct
# question was answered "different": a valid file was refused (found by mutation testing: the role of that cache could not be
# pinned down by any test; a hand-made file then showed it).
b = base("Nat", "Eq", "Eq.refl")
b.definition("f", [], ("pi", NAT, NAT), ("lam", NAT, ("nat", 0)), hints="regular")
q = lambda x, y: _app(("const", "Eq", [ONE]), NAT, x, y)  # noqa: E731
r = lambda x: _app(("const", "Eq.refl", [ONE]), NAT, x)  # noqa: E731
redex = lambda n: _app(("lam", NAT, _app(("const", "f", []), ("bvar", 0))), ("nat", n))  # noqa: E731
f1, f2 = _app(("const", "f", []), ("nat", 1)), _app(("const", "f", []), ("nat", 2))
b.theorem("t1", [], q(redex(1), redex(2)), r(redex(1)))
b.theorem("t2", [], q(f1, f2), r(f1))
add(
    "failure-cache-is-not-a-verdict.ndjson",
    b.text(),
    "accept",
    "f := fun _ => 0: f 1 = f 2 holds. t1 asks it under a beta redex (the arguments differ, then the unfoldings agree), t2 asks "
    "it directly afterwards. The checker once refused t2.",
)

# Operands too large to be unfolded: only the shortcut can decide these, whatever the operation (a mutation that changed the name an
# operation is known by left small cases to the unfolding and went unnoticed)
BIG = 10**30 + 12345
BIG2 = 7**40 + 99
for op, x, y, res in [
    ("Nat.add", BIG, BIG2, BIG + BIG2),
    ("Nat.sub", BIG2, BIG, BIG2 - BIG),
    ("Nat.sub", BIG, BIG2, 0),
    ("Nat.mul", BIG, BIG2, BIG * BIG2),
    ("Nat.div", BIG, BIG2, BIG // BIG2),
    ("Nat.mod", BIG, BIG2, BIG % BIG2),
    ("Nat.mod", BIG, 7, BIG % 7),
    ("Nat.gcd", 2**90 * 3**20, 2**80 * 3**25 * 5, 2**80 * 3**20),
    ("Nat.land", BIG, BIG2, BIG & BIG2),
    ("Nat.lor", BIG, BIG2, BIG | BIG2),
    ("Nat.xor", BIG, BIG2, BIG ^ BIG2),
    ("Nat.shiftLeft", BIG, 70, BIG << 70),
    ("Nat.shiftRight", BIG, 70, BIG >> 70),
    ("Nat.pow", 3, 400, 3**400),
]:
    for claimed, expect in [(res, "accept"), (res + 1, "reject")]:
        nat_def(
            f"nat-big-{op.split('.')[1].lower()}-{x % 10000}-{claimed % 10000}",
            N(op, x, y),
            claimed,
            expect,
            f"{op} on operands of about {max(x, y).bit_length()} bits: unfolding the definition would take more steps than the "
            "checker's budget, so the shortcut for the operation must decide it"
            + ("." if expect == "accept" else ", and the claim is one more than the result."),
        )

# ---------------------------------------------------------------------------------------------------------------------
# Mutation round 3g

# Quot.lift with the same universe parameter twice
b = base("Eq", "Nat")
b.quot("lift", "Quot.lift", ["u", "u"], ("sort", ONE))
refuse(
    "quot-lift-same-universe-twice",
    b.text(),
    "Quot.lift.{u, u}: the two universe parameters must be different names (the quotient's and the target's).",
    "quotient: wrong universe parameters",
)

# a constructor whose universe parameters are not the type's
b = base("Nat")
one_field_block(b, NAT, NAT, lambda types, ctors, recs: ctors[0].update(lparams=["w"]))
add(
    "constructor-other-universe-parameters.ndjson",
    b.text(),
    "reject",
    "T : Type has no universe parameters and T.mk is declared with one (w). The constructor and its type share their parameters.",
    msg="universe parameters differ",
)

# an identity-like function of two arguments that is not optParam/autoParam is not stripped
b = base("Nat")
b.definition(
    "myConst2",
    ["u"],
    ("pi", ("sort", ("param", "u")), ("pi", ("bvar", 0), ("sort", ("param", "u")))),
    ("lam", ("sort", ("param", "u")), ("lam", ("bvar", 0), ("bvar", 1))),
)
one_field_block(
    b,
    _app(("const", "myConst2", [ONE]), NAT, ("nat", 0)),
    _app(("const", "myConst2", [ONE]), NAT, ("nat", 0)),
)
add(
    "two-argument-identity-not-an-annotation.ndjson",
    b.text(),
    "accept",
    "myConst2.{u} (a : Sort u) (x : a) : Sort u := a returns its first argument like optParam and autoParam, but it is neither: "
    "the field `myConst2 Nat 0` is kept as it is (found by mutation testing, as for the one-argument case).",
)

# structure eta is for structures that are not recursive
b = base("Eq", "Eq.refl")
TT = ("const", "T", [])
mk_c = ("const", "T.mk", [])
motive_r = ("pi", TT, SU)
minor_r = tele("pin", [("a", TT), ("ih", _app(V("m"), V("a")))], _app(V("m"), _app(mk_c, V("a"))))
head_r = [("m", motive_r), ("mk", minor_r)]
rec_r = lambda *a: _app(("const", "T.rec", [("param", "u")]), V("m"), V("mk"), *a)  # noqa: E731
b.inductive(
    [{"name": "T", "type": ("sort", ONE), "num_params": 0, "ctors": ["T.mk"], "is_rec": True}],
    [{"name": "T.mk", "induct": "T", "type": ("pi", TT, TT), "cidx": 0, "num_params": 0, "num_fields": 1}],
    [
        {
            "name": "T.rec",
            "lparams": ["u"],
            "type": db(tele("pin", head_r + [("t", TT)], _app(V("m"), V("t"))), []),
            "num_params": 0,
            "num_motives": 1,
            "num_minors": 1,
            "rules": [
                (
                    "T.mk",
                    1,
                    db(tele("lamn", head_r + [("a", TT)], _app(V("mk"), V("a"), rec_r(V("a")))), []),
                )
            ],
        }
    ],
)
b.axiom("x", [], TT)
b.theorem(
    "t",
    [],
    _app(("const", "Eq", [ONE]), TT, ("const", "x", []), _app(mk_c, ("proj", "T", 0, ("const", "x", [])))),
    _app(("const", "Eq.refl", [ONE]), TT, ("const", "x", [])),
)
add(
    "recursive-structure-no-eta.ndjson",
    b.text(),
    "reject",
    "T := mk (T) is a type with one constructor and no index but it is recursive; x = T.mk x.1 does not hold for an axiom x : T. "
    "Structure eta is for structures that are not recursive (found by mutation testing: nothing checked the condition).",
    msg="the value does not have the declared type",
)

# a metadata node is read through
add(
    "mdata-is-transparent.ndjson",
    head + '\n{"ie":0,"sort":0}\n{"ie":1,"mdata":{"expr":0,"data":{}}}\n{"in":1,"str":{"pre":0,"str":"d"}}\n'
    '{"axiom":{"name":1,"levelParams":[],"type":1,"isUnsafe":false}}\n',
    "accept",
    "an axiom d whose type is a metadata node around Prop (Sort 0): the node is read through. A mutation that read another key "
    "declined every file with metadata (found by mutation testing: no test file had a metadata node).",
)

# structure eta is not applied to structures that are propositions (as in the official kernel)
b = base("And", "And.rec", "Nat", "Eq", "Eq.refl")
b.axiom("P", [], PROP)
b.axiom("Q", [], PROP)
and_pq = _app(("const", "And", []), ("const", "P", []), ("const", "Q", []))
b.axiom("x", [], and_pq)
rec_and = _app(
    ("const", "And.rec", [ONE]),
    ("const", "P", []),
    ("const", "Q", []),
    ("lam", and_pq, NAT),
    ("lam", ("const", "P", []), ("lam", ("const", "Q", []), ("nat", 5))),
    ("const", "x", []),
)
b.theorem(
    "t",
    [],
    _app(("const", "Eq", [ONE]), NAT, rec_and, ("nat", 5)),
    _app(("const", "Eq.refl", [ONE]), NAT, ("nat", 5)),
)
add(
    "prop-structure-no-eta.ndjson",
    b.text(),
    "reject",
    "And.rec (fun _ _ => 5) x for an axiom x : P /\\ Q is stuck: the stuck major premise of a recursor is replaced by the "
    "constructor applied to its projections only for structures that are not propositions (the official kernel's rule). A "
    "mutation that did it for propositions too accepted the claim that this is 5 (found by mutation testing).",
    msg="the value does not have the declared type",
)

# a constructor of one type of a mutual block that returns another type of the block
b = Builder()
b.inductive(
    [
        {"name": "A", "type": ("sort", ONE), "num_params": 0, "ctors": ["A.mk"]},
        {"name": "B", "type": ("sort", ONE), "num_params": 0},
    ],
    [{"name": "A.mk", "induct": "A", "type": B, "cidx": 0, "num_params": 0, "num_fields": 0}],
    [],
)
add(
    "mutual-constructor-returns-the-other-type.ndjson",
    b.text(),
    "reject",
    "A.mk : B, a constructor of A that returns the other type of the block (found by mutation testing: the result must be the "
    "constructor's own type, not just a type of the block).",
    msg="invalid return type",
)

# String.mk with a universe parameter is not the constructor a literal expands through
b = base("Char", "Nat", "List", "List.nil", "List.cons", "Eq", "Eq.refl", "Char.ofNat")
b.axiom("String", [], ("sort", ONE))
b.axiom("String.mk", ["u"], ("pi", ("app", ("const", "List", [0]), CHAR), STRING))
b.theorem(
    "t",
    [],
    _app(("const", "Eq", [ONE]), STRING, ("str", "ab"), _app(("const", "String.mk", [0]), chars([97, 98]))),
    _app(("const", "Eq.refl", [ONE]), STRING, ("str", "ab")),
)
add(
    "string-mk-with-universe-parameter.ndjson",
    b.text(),
    "reject",
    "String.mk.{u} : List Char -> String, with a universe parameter it does not use: a literal would expand to String.mk without "
    "levels, which is not that constant, so the environment has no usable constructor for string literals (found by mutation testing).",
    msg="string literal: the environment has no String.ofList or String.mk",
)

# ---------------------------------------------------------------------------------------------------------------------
# Mutation round 3j

# a field of a constructor lives in a universe larger than the inductive type's, claims as derived
b = base("Nat")
one_field_block(b, ("sort", ONE), ("sort", ONE))
add(
    "constructor-field-universe-too-large.ndjson",
    b.text(),
    "reject",
    "T : Type with T.mk : Type -> T: the field has type Type : Type 1, larger than T's universe. The recursor is claimed as the "
    "checker would derive it, so only the universe check can refuse the file (found by mutation testing: the old tests refused "
    "such files for the wrong reason).",
    msg="a field lives in a universe larger",
)

# the type of an inductive type is itself checked
b = base("Nat", "List")
list_of_sort3 = _app(("const", "List", [0]), ("sort", ("succ", ("succ", ("succ", 0)))))
b.inductive([{"name": "T", "type": ("pi", list_of_sort3, ("sort", ONE)), "num_params": 0, "num_indices": 1}], [], [])
add(
    "inductive-type-ill-typed.ndjson",
    b.text(),
    "reject",
    "T : List.{0} (Sort 3) -> Type: List takes a Type 0, and Sort 3 is not one. Only checking the type of T as a type notices; "
    "peeling its binders does not (found by mutation testing).",
    msg="application type mismatch",
)

# an unsafe opaque constant is recorded by its type; its value is not looked at
b = base("Nat", "Bool", "Bool.true")
b.opaque("o", [], ("const", "Bool", []), ("const", "Nat.zero", []))
unsafe_lines = []
for ln in b.lines:
    o = json.loads(ln)
    if "opaque" in o:
        o["opaque"]["isUnsafe"] = True
        ln = json.dumps(o, separators=(",", ":"), sort_keys=True)
    unsafe_lines.append(ln)
add(
    "unsafe-opaque-value-not-checked.ndjson",
    "\n".join(unsafe_lines) + "\n",
    "accept",
    "unsafe opaque o : Bool := Nat.zero: the value has the wrong type, and it does not matter, because no safe declaration can use "
    "an unsafe constant and the kernel does not run unsafe code. A mutation that took an unsafe opaque for a safe one refused the "
    "file (found by mutation testing).",
)

# Quot.lift with its quotient argument missing is stuck, not an error
b = base("Nat", "Eq", "Eq.refl", "Quot", "Quot.mk", "Quot.lift")
rel_q = ("lam", NAT, ("lam", NAT, _app(("const", "Eq", [ONE]), NAT, ("bvar", 1), ("bvar", 0))))
quot_nat_q = _app(("const", "Quot", [ONE]), NAT, rel_q)
h_q = ("lam", NAT, ("lam", NAT, ("lam", _app(rel_q, ("bvar", 1), ("bvar", 0)), ("bvar", 0))))
partial_lift = _app(("const", "Quot.lift", [ONE, ONE]), NAT, rel_q, NAT, ("lam", NAT, ("bvar", 0)), h_q)
ty_q = ("pi", quot_nat_q, NAT)
b.theorem(
    "t",
    [],
    _app(("const", "Eq", [ONE]), ty_q, partial_lift, ("lam", quot_nat_q, ("app", partial_lift, ("bvar", 0)))),
    _app(("const", "Eq.refl", [ONE]), ty_q, partial_lift),
)
add(
    "quot-lift-partial-application-eta.ndjson",
    b.text(),
    "accept",
    "Quot.lift with five of its six arguments is stuck and equal to its eta-expansion. A mutation that read the sixth argument past "
    "the end raised an internal error (a decline) here (found by mutation testing).",
)

# an Eq with two constructors
rec_3_motive = tele("pin", [("b", V("A")), ("t", EQ_V(V("A"), V("a"), V("b")))], PROP)  # two constructors: Prop only
minor_3a = _app(V("m"), V("a"), EQ_REFL_V(V("A"), V("a")))
minor_3b = _app(V("m"), V("a"), _app(("const", "Eq.refl2", [("param", "v")]), V("A"), V("a")))
head_3 = [("A", SV), ("a", V("A")), ("m", rec_3_motive), ("r", minor_3a), ("r2", minor_3b)]
b = Builder()
b.inductive(
    [
        {
            "name": "Eq",
            "lparams": ["v"],
            "type": eq_type,
            "num_params": 2,
            "num_indices": 1,
            "ctors": ["Eq.refl", "Eq.refl2"],
        }
    ],
    [
        {
            "name": c,
            "induct": "Eq",
            "lparams": ["v"],
            "type": db(
                tele("pin", [("A", SV), ("a", V("A"))], EQ_V(V("A"), V("a"), V("a"))),
                [],
            ),
            "cidx": i,
            "num_params": 2,
            "num_fields": 0,
        }
        for i, c in enumerate(["Eq.refl", "Eq.refl2"])
    ],
    [
        {
            "name": "Eq.rec",
            "lparams": ["v"],
            "type": db(
                tele(
                    "pin", head_3 + [("b", V("A")), ("t", EQ_V(V("A"), V("a"), V("b")))], _app(V("m"), V("b"), V("t"))
                ),
                [],
            ),
            "num_params": 2,
            "num_indices": 1,
            "num_motives": 1,
            "num_minors": 2,
            "rules": [
                ("Eq.refl", 0, db(tele("lamn", head_3, V("r")), [])),
                ("Eq.refl2", 0, db(tele("lamn", head_3, V("r2")), [])),
            ],
        }
    ],
)
eq_variant_3 = b.text()
b.quot("type", "Quot", ["u"], QUOT_TY)
add(
    "quot-eq-two-constructors.ndjson",
    b.text(),
    "reject",
    "Eq with the real type and split and a second constructor with the type of Eq.refl: the quotient rules need the real Eq, which "
    "has one constructor (found by mutation testing).",
    msg="quotient: Eq is not the expected inductive family",
)
add(
    "eq-two-constructors-alone.ndjson",
    eq_variant_3,
    "accept",
    "the control for the previous file: that Eq on its own is a valid inductive family.",
)

# an Eq in Type: the real split and constructor, but a family of types, not of propositions
eq_type_4 = db(tele("pin", [("A", SV), ("a", V("A")), ("b", V("A"))], ("sort", ONE)), [])
motive_4 = tele("pin", [("b", V("A")), ("t", EQ_V(V("A"), V("a"), V("b")))], SU)
minor_4 = _app(V("m"), V("a"), EQ_REFL_V(V("A"), V("a")))
head_4 = [("A", SV), ("a", V("A")), ("m", motive_4), ("r", minor_4)]
b = Builder()
b.inductive(
    [{"name": "Eq", "lparams": ["v"], "type": eq_type_4, "num_params": 2, "num_indices": 1, "ctors": ["Eq.refl"]}],
    [
        {
            "name": "Eq.refl",
            "induct": "Eq",
            "lparams": ["v"],
            "type": db(tele("pin", [("A", SV), ("a", V("A"))], EQ_V(V("A"), V("a"), V("a"))), []),
            "cidx": 0,
            "num_params": 2,
            "num_fields": 0,
        }
    ],
    [
        {
            "name": "Eq.rec",
            "lparams": ["u", "v"],
            "type": db(
                tele(
                    "pin", head_4 + [("b", V("A")), ("t", EQ_V(V("A"), V("a"), V("b")))], _app(V("m"), V("b"), V("t"))
                ),
                [],
            ),
            "num_params": 2,
            "num_indices": 1,
            "num_motives": 1,
            "num_minors": 1,
            "rules": [("Eq.refl", 0, db(tele("lamn", head_4, V("r")), []))],
        }
    ],
)
eq_variant_4 = b.text()
b.quot("type", "Quot", ["u"], QUOT_TY)
add(
    "quot-eq-in-type.ndjson",
    b.text(),
    "reject",
    "Eq : (A : Sort v) -> A -> A -> Type, with the real constructor and split: a family of types, not of propositions. The "
    "quotient rules need the type of the real Eq (found by mutation testing: nothing compared it).",
    msg="quotient: Eq is not the expected inductive family",
)
add(
    "eq-in-type-alone.ndjson",
    eq_variant_4,
    "accept",
    "the control for the previous file: that Eq on its own is a valid inductive family.",
)

# reducibility hints must be a natural number; a line must be a JSON object, even a line of one character
m1 = json.dumps(Builder.META, separators=(",", ":"))
okname = '{"in":1,"str":{"pre":0,"str":"a"}}'
oksort = '{"il":1,"succ":0}\n{"ie":0,"sort":0}'
for fname, lines, msg_, why in [
    (
        "parse-negative-hints",
        [
            okname,
            oksort,
            '{"def":{"name":1,"levelParams":[],"type":0,"value":0,"hints":{"regular":-1},"safety":"safe","all":[1]}}',
        ],
        "unknown reducibility hints",
        "hints of regular height -1",
    ),
    ("parse-one-character-line", [okname, "5"], "expected an object", "a line that is the number 5"),
    ("parse-one-letter-line", [okname, "x"], "not valid JSON", "a line that is the letter x"),
]:
    add(
        f"{fname}.ndjson",
        "\n".join([m1] + lines) + "\n",
        "decline",
        f"{why}: declined with the reason (found by mutation testing: a line of one character, which can never be an object, was "
        "skipped silently; and a negative height was read).",
        msg=msg_,
    )

# a recursor in the file that is not the recursor of any type of the block
b = base("Nat")


def add_extra_recursor(types, ctors, recs):
    extra = dict(recs[0])
    extra["name"] = "T.extra"
    recs.append(extra)


one_field_block(b, NAT, NAT, add_extra_recursor)
add(
    "extra-recursor-in-block.ndjson",
    b.text(),
    "reject",
    "T with its recursor and a second recursor named T.extra that no type of the block has (found by mutation testing: the "
    "comparison went the other way only, every derived recursor must be in the file, but not every recursor of the file derived).",
    msg="is not the recursor of any type of its block",
)

# an occurrence of the type being defined with other parameters than its own
b = base("Nat")
PA = ("pi", ("sort", ONE), ("sort", ONE))
b.inductive(
    [{"name": "P", "type": PA, "num_params": 1, "ctors": ["P.mk"]}],
    [
        {
            "name": "P.mk",
            "induct": "P",
            "type": db(
                tele(
                    "pin",
                    [("A", ("sort", ONE)), ("x", _app(("const", "P", []), NAT))],
                    _app(("const", "P", []), V("A")),
                ),
                [],
            ),
            "cidx": 0,
            "num_params": 1,
            "num_fields": 1,
        }
    ],
    [],
)
add(
    "occurrence-with-other-parameters.ndjson",
    b.text(),
    "reject",
    "P (A : Type) : Type with P.mk : P Nat -> P A: the recursive occurrence has the parameter Nat, not the parameter A. Only the "
    "same parameters are allowed (found by mutation testing: a check that every parameter of an occurrence is the type's own "
    "could be dropped unnoticed).",
    msg="invalid occurrence",
)

# a type with two constructors has no structure eta: the recursor on a stuck major premise stays stuck
b = base("Bool", "Bool.rec", "Nat", "Eq", "Eq.refl")
b.axiom("bb", [], ("const", "Bool", []))
rec_bool = _app(
    ("const", "Bool.rec", [ONE]), ("lam", ("const", "Bool", []), NAT), ("nat", 5), ("nat", 6), ("const", "bb", [])
)
b.theorem(
    "t",
    [],
    _app(("const", "Eq", [ONE]), NAT, rec_bool, ("nat", 5)),
    _app(("const", "Eq.refl", [ONE]), NAT, ("nat", 5)),
)
add(
    "two-constructors-no-eta-in-recursor.ndjson",
    b.text(),
    "reject",
    "Bool.rec 5 6 b for an axiom b : Bool is stuck: Bool has two constructors, so b is not replaced by one of them (the official "
    "kernel's behaviour; a second check inside the expansion also refuses it, so this pins the behaviour, not one line).",
    msg="the value does not have the declared type",
)

# a constructor declared in the block that no type of the block lists
b = base("Nat")


def add_unlisted_ctor(types, ctors, recs):
    extra = dict(ctors[0])
    extra["name"] = "T.other"
    extra["cidx"] = 1
    ctors.append(extra)


one_field_block(b, NAT, NAT, add_unlisted_ctor)
add(
    "constructor-listed-by-no-type.ndjson",
    b.text(),
    "reject",
    "T lists the constructor T.mk, and the block declares a second constructor T.other that no type lists (found by mutation "
    "testing: every constructor the types list was checked, not the other way round).",
    msg="belongs to no type of its block",
)

# the checker's own work budget and its caches
b = Builder.extending(prims)
b.axiom("T", [], ("pi", NAT, ("sort", ONE)))
b.axiom("t", [], _app(("const", "T", []), ("nat", 9)))
b.definition("d", [], _app(("const", "T", []), _app(("const", "Nat.log2", []), ("nat", 1000))), ("const", "t", []))
add(
    "work-budget-exhausted.ndjson",
    b.text(),
    "decline",
    "the same file as nat-log2-literal, run with a work budget of 10 steps (WARRANT_FUEL): the checker declines and says why. "
    "With its normal budget (400 million steps) the file is accepted. A budget can turn an accept into a decline, never a decline "
    "into an accept.",
    msg="work budget exhausted",
    env={"WARRANT_FUEL": "10"},
)

# a term nested deeper than the stack allows is declined, not accepted and not a crash
deep = [json.dumps(Builder.META, separators=(",", ":"))]
for o in [
    {"in": 1, "str": {"pre": 0, "str": "N"}}, {"in": 2, "str": {"pre": 0, "str": "s"}},
    {"in": 3, "str": {"pre": 0, "str": "z"}}, {"in": 4, "str": {"pre": 0, "str": "d"}},
    {"il": 1, "succ": 0},
    {"ie": 0, "sort": 1}, {"ie": 1, "const": {"name": 1, "us": []}}, {"in": 5, "str": {"pre": 0, "str": "x"}}, {"ie": 2, "forallE": {"binderInfo": "default", "name": 5, "type": 1, "body": 1}},
    {"ie": 3, "const": {"name": 2, "us": []}}, {"ie": 4, "const": {"name": 3, "us": []}},
    {"axiom": {"name": 1, "levelParams": [], "type": 0, "isUnsafe": False}},
    {"axiom": {"name": 2, "levelParams": [], "type": 2, "isUnsafe": False}},
    {"axiom": {"name": 3, "levelParams": [], "type": 1, "isUnsafe": False}},
]:  # fmt: skip
    deep.append(json.dumps(o, separators=(",", ":")))
prev = 4
for k in range(3000):
    deep.append(json.dumps({"ie": 5 + k, "app": {"fn": 3, "arg": prev}}, separators=(",", ":")))
    prev = 5 + k
deep.append(
    json.dumps(
        {
            "def": {
                "name": 4,
                "levelParams": [],
                "type": 1,
                "value": prev,
                "hints": "abbrev",
                "safety": "safe",
                "all": [4],
            }
        },
        separators=(",", ":"),
    )
)
add(
    "deep-term-accepted.ndjson",
    "\n".join(deep) + "\n",
    "accept",
    "s (s (... z)) nested 3000 deep, with the stack the checker normally has: accepted. The control for the next file.",
)
add(
    "deep-term-stack-overflow.ndjson",
    "\n".join(deep) + "\n",
    "decline",
    "the same file with a stack of 1000 words (OCAMLRUNPARAM=l=1000): the checker declines with the reason instead of "
    "crashing or guessing (found by coverage: the handler had never run).",
    msg="stack overflow",
    env={"OCAMLRUNPARAM": "l=1000"},
)

# a file that is not valid JSON, a wrong shape of any value: the parser declines and names what it found
m1 = json.dumps(Builder.META, separators=(",", ":"))
okname = '{"in":1,"str":{"pre":0,"str":"a"}}'
oksort = '{"il":1,"succ":0}\n{"ie":0,"sort":0}'
for fname, lines, msg_, why in [
    ("missing-field", ['{"ie":1,"app":{"fn":0}}'], "missing field arg", "an application without its argument"),
    (
        "not-an-integer",
        ['{"in":"x","str":{"pre":0,"str":"a"}}'],
        "expected an integer",
        "a name index that is a string",
    ),
    (
        "not-a-boolean",
        [okname, oksort, '{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":"yes"}}'],
        "expected a boolean",
        "isUnsafe as a string",
    ),
    ("not-a-string", ['{"in":1,"str":{"pre":0,"str":5}}'], "expected a string", "a name component that is a number"),
    (
        "not-a-list",
        [okname, '{"ie":0,"const":{"name":1,"us":5}}'],
        "expected a list",
        "universe arguments that are a number",
    ),
    ("not-an-object", ['{"axiom":5}'], "expected an object", "a declaration that is a number"),
    (
        "unknown-hints",
        [
            okname,
            oksort,
            '{"def":{"name":1,"levelParams":[],"type":0,"value":0,"hints":"fast","safety":"safe","all":[1]}}',
        ],
        "unknown reducibility hints",
        "hints that are not opaque, abbrev or regular",
    ),
    (
        "unknown-quotient-kind",
        [okname, oksort, '{"quot":{"kind":"zzz","name":1,"levelParams":[],"type":0}}'],
        "unknown quotient kind",
        "a quotient declaration of no known kind",
    ),
    ("unknown-expression-kind", ['{"ie":0,"zzz":1}'], "unknown expression kind", "an expression node of no known kind"),
    ("level-operands", ['{"il":1,"max":[0]}'], "needs two operands", "a max with one operand"),
    ("unknown-level-kind", ['{"il":1,"zzz":0}'], "unknown level kind", "a level node of no known kind"),
    ("unknown-declaration-kind", ['{"zzz":{}}'], "unknown declaration kind", "a declaration of no known kind"),
    ("not-json", ["{not json"], "not valid JSON", "a line that is not JSON"),
    ("bad-name-entry", ['{"in":1,"zzz":{}}'], "bad name entry", "a name entry of neither shape"),
    ("bad-level-entry", ['{"il":1}'], "bad level entry", "a level entry with no node"),
    ("bad-expression-entry", ['{"ie":1}'], "bad expression entry", "an expression entry with no node"),
    ("bad-line", ['{"a":1,"b":2}'], "bad line", "a line that is not a table entry or one declaration"),
    ("second-meta-line", [m1], "second meta line", "two meta lines"),
]:
    add(
        f"parse-{fname}.ndjson",
        "\n".join([m1] + lines) + "\n",
        "decline",
        f"{why}: the parser declines with the reason (found by coverage: none of the parser's complaints was reached by a test).",
        msg=msg_,
    )
add(
    "parse-version-3-2.ndjson",
    json.dumps({"meta": {**Builder.META["meta"], "format": {"version": "3.2.0"}}}, separators=(",", ":")) + "\n",
    "decline",
    "format version 3.2.0: only 3.1.x is read.",
    msg="is not supported",
)
add(
    "parse-version-4.ndjson",
    json.dumps({"meta": {**Builder.META["meta"], "format": {"version": "4"}}}, separators=(",", ":")) + "\n",
    "decline",
    "format version 4: only 3.1.x is read.",
    msg="is not supported",
)

# unsafe inductive types, constructors and recursors are declined: no kernel check of them is made
b = base("PUnit")
punit_lines = b.lines[:]
for part in ("types", "ctors", "recs"):
    out = []
    for ln in punit_lines:
        o = json.loads(ln)
        if "inductive" in o:
            o["inductive"][part][0]["isUnsafe"] = True
            ln = json.dumps(o, separators=(",", ":"), sort_keys=True)
        out.append(ln)
    add(
        f"unsafe-inductive-{part}.ndjson",
        "\n".join(out) + "\n",
        "decline",
        f"PUnit with its {part[:-1] if part != 'ctors' else 'constructor'} marked unsafe: the checker does not check unsafe "
        "inductive declarations and says so, rather than accepting them unchecked (found by coverage).",
        msg={"types": "unsafe inductive types", "ctors": "unsafe constructors", "recs": "unsafe recursors"}[part],
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
# a file no entry names is a leftover of an earlier version of this script
listed = {e["path"] for e in files} | {"manifest.json"}
for leftover in sorted(set(os.listdir(OUT)) - listed):
    os.remove(os.path.join(OUT, leftover))
    print("removed leftover", leftover)
print(len(files), "regressions")
