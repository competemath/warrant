"""A small writer for the lean4export NDJSON format (3.1.0): names, levels and expressions are interned and numbered
as they are first used, declarations are appended.

Expressions are nested tuples:
  ("sort", level) ("const", "Name", [levels]) ("app", f, a) ("lam", ty, body) ("pi", ty, body) ("bvar", i)
  ("let", ty, val, body) ("nat", n) ("str", s) ("proj", "StructName", idx, struct)
Levels: 0, ("succ", l), ("max", a, b), ("imax", a, b), ("param", "u").
"""

import json


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
        [lines], and a name already defined there keeps its id. Declarations of [lines] are kept as they are."""
        b = cls()
        b.lines = [ln.rstrip("\n") for ln in lines]
        by_id = {0: ""}
        for ln in b.lines:
            o = json.loads(ln)
            if "in" in o:
                sub = o.get("str") or o.get("num")
                pre = by_id[sub["pre"]]
                last = sub["str"] if "str" in o else str(sub["i"])
                by_id[o["in"]] = (pre + "." if pre else "") + last
                b.n_names = max(b.n_names, o["in"])
            elif "il" in o:
                b.n_levels = max(b.n_levels, o["il"])
            elif "ie" in o:
                b.n_exprs = max(b.n_exprs, o["ie"] + 1)
        b.names = {v: k for k, v in by_id.items()}
        return b

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
                    "levelParams": [self.name(p) for p in lparams],
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
                    "levelParams": [self.name(p) for p in lparams],
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
                            "levelParams": [self.name(x) for x in t.get("lparams", [])],
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
                            "levelParams": [self.name(x) for x in c.get("lparams", [])],
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
                            "levelParams": [self.name(x) for x in r.get("lparams", [])],
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
                    "levelParams": [self.name(p) for p in lparams],
                    "type": self.expr(ty),
                    "value": self.expr(val),
                    "all": [self.name(name)],
                }
            }
        )

    def text(self):
        return "\n".join(self.lines) + "\n"
