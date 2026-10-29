"""A small writer for the lean4export NDJSON format (3.1.0): names, levels and expressions are interned and numbered
as they are first used, declarations are appended.

Expressions are nested tuples:
  ("sort", level) ("const", "Name", [levels]) ("app", f, a) ("lam", ty, body) ("pi", ty, body) ("bvar", i)
  ("let", ty, val, body) ("nat", n) ("str", s) ("proj", "StructName", idx, struct)
Levels: 0, ("succ", l), ("max", a, b), ("imax", a, b), ("param", "u").
"""

import json


def _decode_expr(o, name_of, level_of, expr_of):
    """The builder's tuple form of an exported expression node, or None for a form it does not write."""
    if "sort" in o:
        return ("sort", level_of[o["sort"]])
    if "const" in o:
        c = o["const"]
        return ("const", name_of[c["name"]], [level_of[u] for u in c["us"]])
    if "app" in o:
        return ("app", expr_of[o["app"]["fn"]], expr_of[o["app"]["arg"]])
    if "lam" in o:
        return ("lam", expr_of[o["lam"]["type"]], expr_of[o["lam"]["body"]])
    if "forallE" in o:
        return ("pi", expr_of[o["forallE"]["type"]], expr_of[o["forallE"]["body"]])
    if "bvar" in o:
        return ("bvar", o["bvar"])
    if "natVal" in o:
        return ("nat", int(o["natVal"]))
    if "strVal" in o:
        return ("str", o["strVal"])
    if "proj" in o:
        p = o["proj"]
        return ("proj", name_of[p["typeName"]], p["idx"], expr_of[p["struct"]])
    if "letE" in o:
        t = o["letE"]
        return ("let", expr_of[t["type"]], expr_of[t["value"]], expr_of[t["body"]])
    return None


class Builder:
    META = {
        "meta": {
            "exporter": {"name": "forge", "version": "0"},
            "format": {"version": "3.1.0"},
            "lean": {"githash": "0" * 40, "version": "4.29.1"},
        }
    }

    def __init__(self):
        self.lines = [json.dumps(self.META, separators=(",", ":"))]
        self.names = {"": 0}
        self.levels = {0: 0}
        self.exprs = {}
        self.n_names = 0
        self.n_levels = 0
        self.n_exprs = 0

    @classmethod
    def extending(cls, lines):
        """A builder that continues an existing export: new names, levels and expressions are numbered after the ones in
        [lines], a node already there is reused (an export with two identical nodes is malformed, and some checkers
        refuse it), and a name already defined keeps its id. Declarations of [lines] are kept as they are."""
        b = cls()
        b.lines = [ln.rstrip("\n") for ln in lines]
        name_of = {0: ""}
        level_of = {0: 0}
        expr_of = {}
        for ln in b.lines:
            o = json.loads(ln)
            if "in" in o:
                sub = o.get("str") or o.get("num")
                pre = name_of[sub["pre"]]
                last = sub["str"] if "str" in o else str(sub["i"])
                name_of[o["in"]] = (pre + "." if pre else "") + last
                b.n_names = max(b.n_names, o["in"])
            elif "il" in o:
                k = next(x for x in o if x != "il")
                v = o[k]
                lv = (
                    ("param", name_of[v])
                    if k == "param"
                    else ("succ", level_of[v])
                    if k == "succ"
                    else (k, level_of[v[0]], level_of[v[1]])
                )
                level_of[o["il"]] = lv
                b.levels[json.dumps(lv)] = o["il"]
                b.n_levels = max(b.n_levels, o["il"])
            elif "ie" in o:
                e = _decode_expr(o, name_of, level_of, expr_of)
                if e is not None:
                    expr_of[o["ie"]] = e
                    b.exprs.setdefault(json.dumps(e), o["ie"])
                b.n_exprs = max(b.n_exprs, o["ie"] + 1)
        b.names = {v: k for k, v in name_of.items()}
        return b

    def lparams(self, ps):
        """Name ids of declared universe parameters. A canonical export has a `param` level node for each, and some
        checkers insist on it, so one is interned here."""
        for p in ps:
            self.level(("param", p))
        return [self.name(p) for p in ps]

    def _emit(self, obj):
        self.lines.append(json.dumps(obj, separators=(",", ":"), sort_keys=True))

    def name(self, s):
        if s in self.names:
            return self.names[s]
        pre, _, last = s.rpartition(".")
        p = self.name(pre)
        self.n_names += 1
        i = self.n_names
        self._emit({"in": i, "str": {"pre": p, "str": last}})
        self.names[s] = i
        return i

    def level(self, lv):
        if lv == 0:
            return 0
        key = json.dumps(lv)
        if key in self.levels:
            return self.levels[key]
        kind = lv[0]
        if kind == "succ":
            body = {"succ": self.level(lv[1])}
        elif kind in ("max", "imax"):
            body = {kind: [self.level(lv[1]), self.level(lv[2])]}
        else:
            body = {"param": self.name(lv[1])}
        self.n_levels += 1
        i = self.n_levels
        self._emit({"il": i, **body})
        self.levels[key] = i
        return i

    def expr(self, e):
        key = json.dumps(e)
        if key in self.exprs:
            return self.exprs[key]
        k = e[0]
        if k == "sort":
            body = {"sort": self.level(e[1])}
        elif k == "const":
            body = {"const": {"name": self.name(e[1]), "us": [self.level(x) for x in e[2]]}}
        elif k == "app":
            body = {"app": {"fn": self.expr(e[1]), "arg": self.expr(e[2])}}
        elif k in ("lam", "pi"):
            nm = self.name("x")
            body = {
                ("lam" if k == "lam" else "forallE"): {
                    "binderInfo": "default",
                    "name": nm,
                    "type": self.expr(e[1]),
                    "body": self.expr(e[2]),
                }
            }
        elif k == "bvar":
            body = {"bvar": e[1]}
        elif k == "let":
            nm = self.name("x")
            body = {
                "letE": {
                    "name": nm,
                    "nondep": False,
                    "type": self.expr(e[1]),
                    "value": self.expr(e[2]),
                    "body": self.expr(e[3]),
                }
            }
        elif k == "proj":
            body = {"proj": {"typeName": self.name(e[1]), "idx": e[2], "struct": self.expr(e[3])}}
        elif k == "nat":
            body = {"natVal": str(e[1])}
        elif k == "str":
            body = {"strVal": e[1]}
        else:
            raise ValueError(k)
        i = self.n_exprs
        self.n_exprs += 1
        self._emit({"ie": i, **body})
        self.exprs[key] = i
        return i

    def axiom(self, name, lparams, ty, unsafe=False):
        self._emit(
            {
                "axiom": {
                    "name": self.name(name),
                    "levelParams": self.lparams(lparams),
                    "type": self.expr(ty),
                    "isUnsafe": unsafe,
                }
            }
        )

    def definition(self, name, lparams, ty, val, hints="abbrev"):
        self._emit(
            {
                "def": {
                    "name": self.name(name),
                    "levelParams": self.lparams(lparams),
                    "type": self.expr(ty),
                    "value": self.expr(val),
                    "hints": ({"regular": 1} if hints == "regular" else hints),
                    "safety": "safe",
                    "all": [self.name(name)],
                }
            }
        )

    def inductive(self, types, ctors=(), recs=()):
        """An inductive block. [types]: dicts with name, type, num_params, num_indices (optional: lparams, ctors, is_rec,
        num_nested); [ctors]: dicts with name, induct, type, num_params, num_fields, cidx; [recs] as in the export:
        dicts with name, type, rules (list of (ctor, nfields, rhs-expression)), k, num_params, num_indices,
        num_motives, num_minors. The recursors are claims: the checker derives its own and compares."""
        names = [t["name"] for t in types]
        self._emit(
            {
                "inductive": {
                    "types": [
                        {
                            "name": self.name(t["name"]),
                            "levelParams": self.lparams(t.get("lparams", [])),
                            "type": self.expr(t["type"]),
                            "all": [self.name(x) for x in names],
                            "ctors": [self.name(x) for x in t.get("ctors", [])],
                            "numParams": t["num_params"],
                            "numIndices": t.get("num_indices", 0),
                            "numNested": t.get("num_nested", 0),
                            "isRec": t.get("is_rec", False),
                            "isReflexive": t.get("is_reflexive", False),
                            "isUnsafe": False,
                        }
                        for t in types
                    ],
                    "ctors": [
                        {
                            "name": self.name(c["name"]),
                            "induct": self.name(c["induct"]),
                            "levelParams": self.lparams(c.get("lparams", [])),
                            "type": self.expr(c["type"]),
                            "cidx": c["cidx"],
                            "numParams": c["num_params"],
                            "numFields": c["num_fields"],
                            "isUnsafe": False,
                        }
                        for c in ctors
                    ],
                    "recs": [
                        {
                            "name": self.name(r["name"]),
                            "levelParams": self.lparams(r.get("lparams", [])),
                            "type": self.expr(r["type"]),
                            "all": [self.name(x) for x in names],
                            "numParams": r["num_params"],
                            "numIndices": r.get("num_indices", 0),
                            "numMotives": r["num_motives"],
                            "numMinors": r["num_minors"],
                            "k": r.get("k", False),
                            "isUnsafe": False,
                            "rules": [
                                {"ctor": self.name(c), "nfields": nf, "rhs": self.expr(rhs)}
                                for c, nf, rhs in r["rules"]
                            ],
                        }
                        for r in recs
                    ],
                }
            }
        )

    def theorem(self, name, lparams, ty, val):
        self._emit(
            {
                "thm": {
                    "name": self.name(name),
                    "levelParams": self.lparams(lparams),
                    "type": self.expr(ty),
                    "value": self.expr(val),
                    "all": [self.name(name)],
                }
            }
        )

    def text(self):
        return "\n".join(self.lines) + "\n"
