# WARRANT

**W**itness-**A**uthenticated **R**e-derivation and **R**igid **A**ttestation **N**ucleus for **T**ypes: a checker for
[`lean4export`](https://github.com/leanprover/lean4export) files, in OCaml, whose only currency is provenance-indexed
evidence. Design and threat model: [docs/design.md](docs/design.md).

```
dune build
_build/default/bin/main.exe file.ndjson     # exit 0 accepted, 1 rejected, 2 declined
```

## Tests

| What | How | Gate |
|---|---|---|
| Lean Kernel Arena files (soundness bugs, tutorial, perf) | `python3 tools/arena.py --binary _build/default/bin/main.exe tests/arena` | CI |
| Universe levels against brute force, terms, primitives | `dune test` | CI |
| The evidence discipline | `python3 tools/lint_kernel.py`, `python3 tools/compile_fail.py` | CI |
| Random files with known verdicts, in rounds of growing size | `python3 tools/forge/forge.py --binary ...` | weekly, and short in CI |

Every unexpected behaviour (a wrong verdict, a crash, a reviewer's finding) gets a test that targets exactly it in
`tests/regressions` in the pull request that fixes it.

Licence: Apache-2.0.
