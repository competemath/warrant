"""Cut the dependency closure of named declarations out of a lean4export NDJSON file.

    slice.py EXPORT.ndjson OUT.ndjson Name [Name ...]

The output keeps the meta line, the declarations the targets transitively mention (an inductive is kept whole
with its constructors and recursors) and exactly the name/level/expression lines those declarations reach.
Used to profile one slow declaration of a large export without re-checking the whole prefix.
"""

import json
import sys


def slice_lines(all_lines, targets):
    """The lines of an export that the declarations named in [targets] need (see the module docstring)."""
    targets = set(targets)
    names = {0: ""}
    expr_consts = {}  # ie -> set of const name ids used directly by that expression node
    expr_kids = {}  # ie -> child ie ids
    decls = []  # (line, kind, payload)
    by_name = {}  # name id -> decl index
    lines = []
    line_of = {}  # ("n"|"l"|"e", id) -> line number
    deps = {}  # same key -> keys it needs
    for line in all_lines:
        o = json.loads(line)
        lines.append(line)
        me = len(lines) - 1
        if "in" in o:
            line_of[("n", o["in"])] = me
            sub = o.get("str") or o.get("num")
            deps[("n", o["in"])] = [("n", sub["pre"])]
        elif "il" in o:
            line_of[("l", o["il"])] = me
            ks = [k for k in o if k != "il"][0]
            v = o[ks]
            deps[("l", o["il"])] = (
                [("n", v)] if ks == "param" else [("l", v)] if ks == "succ" else [("l", v[0]), ("l", v[1])]
            )
        elif "ie" in o:
            line_of[("e", o["ie"])] = me
            d = []
            for k, v in o.items():
                if k == "const":
                    d += [("n", v["name"])] + [("l", u) for u in v["us"]]
                elif k == "sort":
                    d.append(("l", v))
                elif k in ("app", "lam", "forallE", "letE"):
                    for kk, x in v.items():
                        if kk in ("fn", "arg", "type", "body", "value"):
                            d.append(("e", x))
                        elif kk == "name":
                            d.append(("n", x))
                elif k == "proj":
                    d += [("e", v["struct"]), ("n", v["typeName"])]
            deps[("e", o["ie"])] = d
        if "in" in o:
            if "str" in o:
                p = names[o["str"]["pre"]]
                names[o["in"]] = (p + "." if p else "") + o["str"]["str"]
            else:
                names[o["in"]] = names[o["num"]["pre"]] + "." + str(o["num"]["i"])
        elif "il" in o:
            pass
        elif "ie" in o:
            i = o["ie"]
            kids = []
            for k in ("app", "lam", "forallE", "letE", "proj"):
                if k in o:
                    v = o[k]
                    kids += [x for kk, x in v.items() if kk in ("fn", "arg", "type", "body", "value", "struct")]
            expr_kids[i] = kids
            if "const" in o:
                expr_consts[i] = {o["const"]["name"]}
            if "proj" in o:
                expr_consts.setdefault(i, set()).add(o["proj"]["typeName"])
        elif "meta" in o:
            continue
        else:
            k = list(o)[0]
            d = o[k]
            idx = len(decls)
            decls.append((len(lines) - 1, k, d))
            if k == "inductive":
                for t in d["types"]:
                    by_name[t["name"]] = idx
                for c in d["ctors"]:
                    by_name[c["name"]] = idx
                for r in d["recs"]:
                    by_name[r["name"]] = idx
            else:
                by_name[d["name"]] = idx

    memo = {}

    def consts_of(e):
        if e in memo:
            return memo[e]
        out, stack, seen = set(), [e], set()
        while stack:
            x = stack.pop()
            if x in seen or x in memo:
                if x in memo:
                    out |= memo[x]
                continue
            seen.add(x)
            out |= expr_consts.get(x, set())
            stack += expr_kids.get(x, [])
        memo[e] = out
        return out

    def roots(k, d):
        es = []
        if k == "inductive":
            for t in d["types"]:
                es.append(t["type"])
            for c in d["ctors"]:
                es.append(c["type"])
            for r in d["recs"]:
                es.append(r["type"])
                es += [x["rhs"] for x in r["rules"]]
        else:
            es.append(d["type"])
            if "value" in d:
                es.append(d["value"])
        return es

    def decl_ids(k, d):
        ns, ls = [], []
        if k == "inductive":
            for t in d["types"]:
                ns += [t["name"]] + t["all"] + t["ctors"]
                ls += t["levelParams"]
            for c in d["ctors"]:
                ns.append(c["name"])
                ls += c["levelParams"]
            for r in d["recs"]:
                ns.append(r["name"])
                ls += r["levelParams"]
                ns += [x["ctor"] for x in r["rules"]]
        else:
            ns.append(d["name"])
            ns += d.get("all", [])
            ls += d.get("levelParams", [])
        return [("n", x) for x in ns] + [("n", x) for x in ls]

    want = {i for i, n in names.items() if n in targets}
    todo = [by_name[i] for i in want if i in by_name]
    absent = sorted(targets - {names[i] for i in want if i in by_name})
    if absent:
        sys.exit("no such declaration: " + ", ".join(absent))
    keep = set()
    while todo:
        i = todo.pop()
        if i in keep:
            continue
        keep.add(i)
        _, k, d = decls[i]
        for e in roots(k, d):
            for c in consts_of(e):
                if c in by_name:
                    todo.append(by_name[c])
    need, stack = set(), []
    for i in keep:
        _, k, d = decls[i]
        for e in roots(k, d):
            stack.append(("e", e))
        stack += decl_ids(k, d)
    while stack:
        x = stack.pop()
        if x in need or x not in line_of:
            continue
        need.add(x)
        stack += deps[x]
    keep_lines = {line_of[x] for x in need} | {decls[i][0] for i in keep} | {0}
    print(f"kept {len(keep)} of {len(decls)} declarations", file=sys.stderr)
    return renumber([line for n, line in enumerate(lines) if n in keep_lines])


NAME_KEYS = {"name", "all", "levelParams", "ctors", "induct", "ctor", "typeName"}
EXPR_KEYS = {"type", "value", "rhs"}


def renumber(kept):
    """The same lines with names, levels and expressions numbered densely in order of appearance (1.., 1.., 0..).

    A slice keeps the original ids and so has holes; some checkers insist the numbering is continuous."""
    nm, lv, ex = {0: 0}, {0: 0}, {}

    def n(i):
        return nm[i]

    def lev(i):
        return lv[i]

    def e(i):
        return ex[i]

    def decl(o):
        if isinstance(o, dict):
            return {
                k: (
                    [n(x) for x in v]
                    if k in NAME_KEYS and isinstance(v, list) and all(isinstance(x, int) for x in v)
                    else n(v)
                    if k in NAME_KEYS and isinstance(v, int)
                    else e(v)
                    if k in EXPR_KEYS and isinstance(v, int)
                    else decl(v)
                )
                for k, v in o.items()
            }
        if isinstance(o, list):
            return [decl(x) for x in o]
        return o

    out = []
    for line in kept:
        o = json.loads(line)
        if "in" in o:
            sub = o.get("str") or o.get("num")
            nm[o["in"]] = len(nm)
            new = {"in": nm[o["in"]]}
            new["str" if "str" in o else "num"] = {**sub, "pre": n(sub["pre"])}
            o = new
        elif "il" in o:
            lv[o["il"]] = len(lv)
            k = next(x for x in o if x != "il")
            v = o[k]
            body = n(v) if k == "param" else lev(v) if k == "succ" else [lev(v[0]), lev(v[1])]
            o = {"il": lv[o["il"]], k: body}
        elif "ie" in o:
            ex[o["ie"]] = len(ex)
            new = {"ie": ex[o["ie"]]}
            for k, v in o.items():
                if k == "ie":
                    continue
                if k == "const":
                    new[k] = {"name": n(v["name"]), "us": [lev(u) for u in v["us"]]}
                elif k == "sort":
                    new[k] = lev(v)
                elif k == "app":
                    new[k] = {"fn": e(v["fn"]), "arg": e(v["arg"])}
                elif k in ("lam", "forallE"):
                    new[k] = {**v, "name": n(v["name"]), "type": e(v["type"]), "body": e(v["body"])}
                elif k == "letE":
                    new[k] = {
                        **v,
                        "name": n(v["name"]),
                        "type": e(v["type"]),
                        "value": e(v["value"]),
                        "body": e(v["body"]),
                    }
                elif k == "proj":
                    new[k] = {**v, "typeName": n(v["typeName"]), "struct": e(v["struct"])}
                else:
                    new[k] = v
            o = new
        elif "meta" not in o:
            o = decl(o)
        out.append(json.dumps(o, separators=(",", ":"), sort_keys=True) + "\n")
    return out


def main():
    src, dst = sys.argv[1], sys.argv[2]
    with open(src, encoding="utf-8") as f:
        kept = slice_lines(f, sys.argv[3:])
    with open(dst, "w", encoding="utf-8") as out:
        out.writelines(kept)


if __name__ == "__main__":
    main()
