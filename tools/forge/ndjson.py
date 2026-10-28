"""A small writer for the lean4export NDJSON format (3.1.0): names, levels and expressions are interned and numbered
as they are first used, declarations are appended.

Expressions are nested tuples:
  ("sort", level) ("const", "Name", [levels]) ("app", f, a) ("lam", ty, body) ("pi", ty, body) ("bvar", i)
  ("let", ty, val, body) ("nat", n) ("str", s)
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
