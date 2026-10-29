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
| Lean Kernel Arena files (soundness bugs, tutorial, perf) and the regressions | `python3 tools/arena.py --binary _build/default/bin/main.exe tests/arena tests/regressions` | CI |
| Every refusal the checker can make is reached by a test (or listed as unreachable, with the reason) | `python3 tools/reject_coverage.py --binary ... --allow tools/reject_unreachable.json tests/arena tests/regressions` | CI |
| Universe levels against brute force, terms, primitives (digest table against the official exports) | `dune test` | CI |
| The evidence discipline | `python3 tools/lint_kernel.py`, `python3 tools/compile_fail.py` | CI |
| Random files with known verdicts, in rounds of growing size | `python3 tools/forge/forge.py --binary ...` | weekly, and short in CI |
| The tests themselves: change one operator in the source, see whether anything fails | `python3 tools/mutate.py --work DIR ...` | weekly (`tools/mutation_equivalents.json` lists the changes that cannot matter, with the reason) |
| A second checker (nanoda, pinned) on the same files | `python3 tools/differential.py --binary ... --other 'CMD < {file}' ...` | weekly (`tools/differential_known.json` lists the understood differences) |

`tools/slice.py` cuts the closure of named declarations out of a large export (a 347 MB Init export becomes a 1 MB file
that still shows one slow declaration); the Init export itself is checked by hand, it is too large for the repository
(accepted, about fifteen minutes).

Every unexpected behaviour (a wrong verdict, a crash, a reviewer's finding) gets a test that targets exactly it in
`tests/regressions` in the pull request that fixes it.

Licence: Apache-2.0.
