# What nine other checkers say about WARRANT's test files

On 2026-10-29 every file of `tests/arena` and `tests/regressions` was given to nine other checkers, each built from a
pinned commit (`competemath/tmp-kernel-panel`, workflow `warrant-corpus`, run 40967175259): con-ron, eink0rn, kefir,
kiota, lazylean, nanoda, official, sokonanoda and tenet. `official` is the Lean Kernel Arena's checker: it parses the
export and replays it through Lean 4.34.1's own kernel (`Lean.Kernel.Environment.replay`). A tenth, tenet-jvm, failed on
the undamaged baseline and is left out. Every disagreement was read checker by checker, against the kernel source
(`src/kernel/environment.cpp` and `type_checker.cpp` at Lean v4.29.1 and v4.34.1) and `src/Lean/Replay.lean`.

The question for each file is which side is right, not which side is the majority.

Two things about `official` explain most of what follows. Its replay **skips unsafe and partial constants**, and it
**rebuilds** each inductive type and the quotient package from part of what the file says, so what the file says about the
rest is never read.

## Three disagreements where WARRANT was the lenient one (changed)

| File | WARRANT before | Others | Official kernel source | Now |
|---|---|---|---|---|
| `unsafe-opaque-value-not-checked`, `unsafe-opaque-type-mentions-unsafe` | accepted | eink0rn, kefir, kiota, lazylean, sokonanoda, tenet refuse | `environment::add_opaque` has no unsafe case: it checks the type and the value with a **safe** type checker, so the value must have the type and neither may mention an unsafe constant. (`add_axiom` and `add_definition` do have an unsafe case, and WARRANT already followed it.) `official` accepted both only because the replay skips unsafe constants. | refused. `unsafe-opaque-well-typed` is the accepted control |
| `string-mk-literal` | accepted | kiota, lazylean, nanoda, official, sokonanoda, tenet refuse | `string_lit_to_constructor` expands a literal through `String.ofList` in v4.29.1 and in v4.34.1; `String.mk` is not accepted. | refused |
| `blank-lines` | skipped empty lines | nanoda, official, sokonanoda refuse | An empty line is not a JSON record. | refused (declined as malformed input) |

## Where WARRANT is stricter than another checker, on purpose

WARRANT's rule is that every statement in the file is either re-derived and compared, or the file is refused. A checker
that rebuilds the environment itself and ignores the statements it can rebuild accepts files WARRANT refuses. In each
list below the checkers after the dash accepted the file.

**Statements the kernel derives.** The replay builds `Declaration.inductDecl` from the universe parameters and parameter
count of the first type, the types' names and the constructors' names and types. It never reads the flags and counts of
the inductive records (`isRec`, `isReflexive`, `numNested`, `numIndices`), the universe parameters, parameter counts and
`all` of the other types of a block, or a recursor that the file leaves out. It does compare every constructor and
recursor the file does give with the generated one, so a wrong `all`, `rules` or `k` is refused by it.

* `claim-is-rec` — con-ron, kiota, lazylean, official
* `claim-is-reflexive` — con-ron, kiota, lazylean, nanoda, official, sokonanoda
* `claim-num-nested` — con-ron, kiota, lazylean, official
* `claim-num-indices` — con-ron, lazylean, official
* `claim-recursor-missing` — official, tenet
* `empty-inductive-block` — eink0rn, official, sokonanoda
* `block-universe-parameters`, `block-parameter-count`, `block-all-not-the-block` — official
* `claim-rec-all` — con-ron; `claim-rec-rules` — con-ron, kiota; `claim-rec-k` — kiota. Checkers that do not compare
  the recursor.
* `rec-rule-names-the-wrong-constructor` — con-ron, kiota. The two rules of `Bool.rec` have their constructor names
  exchanged, so `Bool.rec false true true` reduces to `false` and `true` is definitionally equal to `false`. A checker
  that accepts this file is not checking the rules.

**The quotient declarations.** `official` erases `Quot.mk`, `Quot.lift` and `Quot.ind` from the file and adds the
genuine package with `quotDecl` when it meets `Quot`, whatever the file says about their types. The rules of `Quot` are
stated through `Eq`, so WARRANT requires the file's `Eq` and the four constants to be the real ones.

* `quot-unexpected-name` — lazylean, official, tenet
* `quot-wrong-universes`, `quot-wrong-type` — lazylean, official
* `quot-lift-same-universe-twice` — official
* `quot-eq-other-split-of-arguments` — kefir, kiota, lazylean, official, tenet
* `quot-eq-refl-type-not-the-expected-one` — kiota, lazylean
* `quot-eq-wrong-shape`, `quot-eq-two-constructors`, `quot-eq-in-type` — kiota
* `quot-without-eq` — con-ron, kiota
* `quot-mk-without-type`, `quot-ind-without-ctor`, `quot-lift-without-quot-type`, `quot-ind-without-quot-type` — con-ron,
  kiota, lazylean
* `quot-lift-without-ctor` — con-ron, kiota, lazylean, tenet

**A name-table index defined twice** (a map overwrites; WARRANT will not pick one of two readings).
`index-defined-twice` — eink0rn, kiota, lazylean, official, sokonanoda.

**Machine arithmetic keyed on a name.** The official kernel takes `Nat.add` and the other operations from GMP by their
name. A file that defines its own `Nat.add` as `fun a b => a` and then proves `Nat.add 123456789 987654321 =
1111111110` by `rfl` is accepted: the sum comes from GMP, not from the file's definition. WARRANT turns a shortcut on
only when the definition and everything it depends on has the genuine fingerprint (`src/fingerprint.ml`).

* `fake-nat-add` — kiota, lazylean, official, sokonanoda
* `prim-dependency-opaque`, `prim-dependency-axiom` — kiota, lazylean, nanoda, official, sokonanoda
* `literal-without-genuine-nat` — eink0rn, kiota, lazylean, nanoda, official (the literal's meaning needs `Nat.zero` and
  `Nat.succ` of the real `Nat`)

**Checks the official kernel makes and the checker lacks** (the official kernel refuses all of these):
`undeclared-universe-in-max`, `undeclared-universe-in-imax`, `const-level-not-declared` — kiota;
`recursive-structure-no-eta` — eink0rn; `prop-structure-no-eta` — eink0rn, kefir, sokonanoda;
`closure-level-subst`, `pi-closure-context`, `unit-rec-rule` — sokonanoda; `forged-quot-ind` — kiota, nanoda;
`nested-name-capture` — nanoda, sokonanoda (the last five are the Arena's soundness-bug files).

## Where WARRANT accepts and another checker refuses

In all of these `official` accepts, except `string-mk-literal` (above).

| Files | Refused by | What the checker said |
|---|---|---|
| `unsafe-axiom-mentions-unsafe`, `unsafe-definition-mentions-unsafe` | kiota, sokonanoda | "unsafe axiom", "unsafe declarations are not supported". `add_axiom` and `add_definition` check unsafe declarations with unsafe constants allowed. |
| `nat-pow-size-at-limit`, `nat-shiftleft-amount-at-limit`, `nat-mul-chain-of-squarings-20` | nanoda, sokonanoda, lazylean (and eink0rn for the first) | Out of memory after 100 to 200 s (abort), or a type mismatch (eink0rn). |
| `init-int32-rxc-hassize`, `init-char-ofordinal-proof3` (cuts of the real Init) | eink0rn, lazylean, tenet | eink0rn: "the quotient package is incomplete" (the cut has `Quot`, `Quot.mk`, `Quot.lift` and no `Quot.ind`). lazylean and tenet fail on the `funext` proof that goes through `Quot.lift`; the cause was not examined. The other six accept. |
| `nested-auxiliary-name-taken` | tenet | Reserves the `_nested` namespace for itself. |
| `eq-other-split-of-arguments-alone`, `eq-refl-with-redex-alone`, `eq-two-constructors-alone`, `eq-in-type-alone` (valid `Eq`s, the controls of the files above) | con-ron | "reserved basis name" for `Eq`. |
| `mutual-props-no-k` | kiota | "duplicate recursor for type 1". |
| `mdata-is-transparent` | sokonanoda | "Expr.mdata is not supported". |
| `quot-lift-partial-application-eta` | eink0rn | "the quotient package is incomplete". |

## What is still different from the official kernel

* **Unsafe and partial definitions are recorded by their type; their values are not checked.** The official kernel
  checks them (an unsafe definition with unsafe constants allowed, after adding it, so that it may be recursive). WARRANT
  can therefore accept a file whose only fault is an ill-typed value of an unsafe or partial *definition*, which the
  official kernel refuses. Nothing safe can depend on such a constant (a safe declaration that mentions one is refused),
  so every safe declaration of an accepted file has been checked in full.
* **The type of a partial definition is checked with unsafe constants allowed.** The official kernel allows partial
  constants there but not unsafe ones.
