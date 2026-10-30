# Design

WARRANT is a checker for `lean4export` files. It decides, for a file of Lean 4 declarations, whether every declaration
is admissible. It is written in OCaml, shares no code with Lean's kernel, and was designed from a study of every known
soundness bug of Lean 4 kernels (the official one, and the community and arena checkers): 53 bugs, five classes.

## The flaw it answers

Most of those bugs are one phenomenon: a fact was consumed where its justification was absent. The kernel acted on a
bare answer (a Boolean, a flag copied from the file, a cached result, a name) that nothing tied to the thing it was an
answer about. 44 of the 53 are of the form: (1) a second source of truth was trusted (the export's `k`, `numFields`,
recursor rules, `isRec`), (2) two internal computations of the same notion disagreed (is this type a proposition?
are these universe levels equal?), or (3) a boundary was crossed with a check missing (a closure compared without its
universe substitution, a term with loose bound variables, a recursor named after a temporary constant).

## The discipline

* **Evidence is the only currency** (`src/evidence.mli`). The facts the checker acts on are values of five abstract
  types: `Is_type`, `Typing`, `Conv`, `Is_prop`, `Ind_ok` (and `Quot_ok`). Each is stamped with the environment and the
  universe parameters it holds under. The types are private, and `tools/lint_kernel.py` fails CI unless each `Mint`
  function is called exactly once, from its designated minter (`tc.ml`, `ind.ml`, `quot.ml`).
* **The environment only grows through evidence** (`src/env.mli`). `Env.add_def` takes the evidence that the type is a
  type, that the value has a type, and that this type is convertible to the declared one, and checks that all three are
  about the same terms, in this environment, under these universe parameters. `tests/compile-fail/` holds the attempts
  to skip one of them or forge a value; CI requires each to fail to compile.
* **File metadata is a claim.** `numFields`, `isRec`, `isReflexive`, `numNested`, `k`, the recursor types, the rules,
  `all`, `numParams` of recursors: none is read as a fact. `src/ind.ml` derives all of them from the inductive types
  and constructor types, and the file is rejected if any claim differs. A recursor the file declares that the
  derivation does not produce is rejected. Nested inductives are eliminated to a derived mutual block and restored; the
  temporary names never reach the environment, so no later declaration can capture one.
* **One decision procedure per notion.** "Is this a proposition?" is `Tc.is_prop_type`, used by proof irrelevance,
  projections, structure eta and K; where a presentation matters (a type that is a proposition by declaration but
  normalises to something whose sort is stuck) every use asks both. Universe levels are compared by a semantic
  procedure over all valuations (`src/level.ml`), checked against brute force by `test/test_level.ml`; where it would
  be too expensive it raises, and the file is declined.
* **Substitution, not closures.** Terms are locally nameless and hash-consed with binder names erased, so alpha
  equivalence is pointer equality and the bug class that came from comparing closures with different universe
  substitutions or contexts cannot be written.
* **Shortcuts are optional.** The kernel's name-keyed accelerations (natural-number literals and their arithmetic) are
  enabled only when the environment's constant of that name has the fingerprint of the genuine definition
  (`src/fingerprint.ml`, `src/prim_digests.ml`). A file that defines its own `Nat.add` gets unfolding, never the
  shortcut. Unsafe and partial definitions and unsafe axioms are recorded as constants no safe declaration may mention;
  the values of the definitions are never read (an opaque constant is checked in full whether or not it is marked
  unsafe, as in the official kernel). What this leaves different from the official kernel is in
  [other-checkers.md](other-checkers.md).
* **Decline over trust.** Exit code 2 means "not covered": a resource limit, a format version, an unsupported feature.
  The checker never accepts to be helpful.

## What it does not claim

The evidence types make forging or skipping a check impossible to write, but the minters themselves (`Tc`, `Ind`,
`Quot`, `Level`) can still be wrong; they are covered by tests, the arena corpus, the forge (random files whose verdict
is known by construction) and review, not by the compiler. Specifically:

* A wrong *specification* (this kernel and Lean's agree on a theory that is itself wrong) is not detected.
* Definitional equality here is Lean's algorithm, which is not transitive (the `corner-cases` files); the files that
  exploit that are rejected by closing the gaps they use (both presentations of Prop-ness), not by changing the
  algorithm.
* Fingerprints trust the official exports they were generated from; `test/test_prim.ml` pins them to the corpus.
* OCaml's runtime, the compiler, Zarith/GMP and the hardware are trusted.
* Performance is not a goal. Substitution makes some inputs quadratic in time and memory, and a file that exhausts the
  work budget is declined.
