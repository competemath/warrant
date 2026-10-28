# Contributing to WARRANT

Everything lands through a pull request into `main`; the `ci` check (build, unit and property tests, the arena
corpus, formatting, lint) must pass, a code owner must approve, every review conversation must be resolved, and the
merge queue squashes. Nobody pushes to `main`.

## Build and test

```
opam switch create . 5.3.0 --deps-only --with-test
dune build @all          # warnings are errors
dune test                # alcotest + qcheck
python3 tools/arena.py --binary _build/default/bin/main.exe tests/arena
dune build @fmt          # ocamlformat; `dune fmt` rewrites
```

## Adding a test

- A file WARRANT judged wrongly, or crashed on, goes into `tests/arena/<group>/<name>.ndjson` with its expected
  outcome in `tests/arena/<group>/manifest.json` (`accept`, `reject` or `either`), in the same pull request as the fix.
  **Every unexpected behaviour gets a test that targets exactly it.**
- A property of the theory (a law a minter must obey) goes into `test/` as a QCheck property.
- A new generator for the forge goes into `tools/forge/`; its outputs must have an outcome known by construction.

## The evidence discipline

The kernel's modules trade only in evidence values (`src/evidence/`). A fact's evidence is minted by exactly one
function, its type is abstract outside that module, and it carries the environment generation, universe substitution
and context it holds in. A pull request that adds a second way to produce a fact, or passes a bare `bool`/`int`/term
where evidence belongs, is declined whatever it fixes: put the fact into the minter.

## Commits

`git commit -s`: the Developer Certificate of Origin sign-off is required.
