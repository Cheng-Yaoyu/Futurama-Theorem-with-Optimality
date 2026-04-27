# Optimality Theorem — Validation Summary

This document summarises the validation evidence for the optimality
side of the Futurama formalisation: paper Theorem 1 of
Evans–Huang–Nguyen 2014 ("Keeler's Theorem and Products of Distinct
Transpositions"), the surrounding Lemma 1 family (a parallel
paper-faithful track, not consumed by the Lean Theorem 1 lower-bound
chain — see §7 of `paper_correspondence.md`), and the Keeler-gap
remark.

---

## What is validated

### Theorem 1 — upper bound

`optimalScript` and `optimalScriptOfPerm` give an explicit `n + r + 2`
factor construction of paper Theorem 1's `λ`. The Lean development
proves correctness, exact length, helper inclusion, distinctness of
unordered pairs, and non-triviality of every step. These are bundled
on the explicit witness as `futuramaTheorem1OfPerm`, on the
`RepairSeq` witness as `optimalRepairSeqOfPerm`, and as a
single-declaration existence form as `futuramaTheorem1Full`.

### Theorem 1 — lower bound (best possible)

`futurama_optimal` is a `∀`-quantified statement over arbitrary
`RepairSeq (liftPerm σ)` saying no admissible repair sequence is
shorter than `n + r + 2`. The proof goes through the entry-counting
plus parity chain
(`repair_length_ge_entries_add_cycles` + `repair_length_parity` +
`repair_length_ne_entries_add_cycles`, closed by `omega`).

### Lemma 1 family (graph-theoretic / paper-faithful track)

* Lemma 1(a): `transposition_count_ge_cycle_length` (a `k`-cycle as
  a product of `t` transpositions has `t ≥ k − 1`).
* Lemma 1(b), trivial direction `V ⊆ W`:
  `minimal_factorization_covers_support`.
* Lemma 1(b), non-trivial direction `W ⊆ V`:
  `minimal_factorization_factorEndpoints_mem_support` and
  `minimal_factorization_factorEntries_mem_support`.
* Lemma 1(c): `minimal_factorization_has_adjacent` (a compatibility
  form) plus the paper-strong `minimal_factorization_has_adjacent_paper`,
  which exposes the `pre ++ [a, b] ++ suf` split and excludes the
  wrap-around edge exactly as the paper requires.

The Lemma 1 family is a parallel paper-faithful track. It is
**not** consumed by Theorem 1's own lower-bound proof; the entry-
counting plus parity chain stands on its own. Lemma 1 is preserved
because paper Theorems 2 and 3 (which the project does not formalise)
use it directly, and because it is a standard auxiliary tool worth
having available as a public Lean theorem.

### Keeler-gap remark

Paper p.138's "Keeler is optimal only for `r ≤ 2`" remark is
captured at theorem level for **all** `r`:

* `r = 1`: `keeler_optimal_single_cycle` —
  `(undoScript [c]).length = (optimalScript [c]).length`, both equal
  to `c.members.length + 3 = n + r + 2` (closed-form siblings
  `undoScript_length_single_cycle` /
  `optimalScript_length_single_cycle`).
* `r = 2`: `keeler_achieves_and_gap` evaluates to gap
  `(2 - 2) + 0 = 0`. Keeler matches the optimum.
* `r ≥ 3`: `keeler_achieves_and_gap` gives gap
  `(r - 2) + parity > 0`, matching paper's `2r - (r + 2) ± parity`
  formula.

---

## How it is validated

* **Kernel correctness** — `lake build Project.TestProject` succeeds
  with `exit 0`. Zero `sorry`, zero `admit`, zero user-defined axiom.
* **Definition correctness** — `RepairSeq` fields match paper
  Theorem 1's machine-side requirements (correctness, helper
  inclusion, nontriviality, distinct unordered pairs). The
  `optimalScript` block hierarchy is pinned by a nine-line
  `example := rfl` block inside `Optimality/UpperBound.lean` so
  any future drift on the paper-λ block structure breaks the
  build immediately.
* **Statement correctness** — the paper's six conjuncts
  (correctness, exact length, helper inclusion, distinct factors,
  non-trivial factors, "best possible") are all formalised; see
  [`paper_correspondence.md`](paper_correspondence.md) for the
  row-by-row mapping.
* **Executable sanity (`Validation6_Optimality`)** —
  boolean validators (`repairSeqValidator`, `optimalScriptValidator`,
  `keelerGapFormula`) plus 22 `native_decide` invocations across
  four representative cycle structures (3-cycle, 4-cycle, two
  2-cycles, three 2-cycles) and a uniform lower-bound theorem
  (`cutFamily_uniformLowerBound`) over the parameterised cut family.
* **Brute-force corroboration (`Validation7_BruteForceOptimality`,
  optional)** — exhaustive enumeration on `Fin 3` and `Fin 4`: no
  script of length `< n + r + 2` using only helper-containing
  distinct transpositions can undo any non-trivial `σ`. Discharged
  via `native_decide`, ~38 s wall-clock at `Fin 4`.
* **Negative controls (`Validation9_AntiTest`, optional)** — anti-
  tests confirming the boolean validators in
  `Validation6_Optimality.lean` correctly reject malformed inputs
  (identity script, length-(n+r+1) script, duplicate pair,
  helper-missing, self-swap, wrong target, length sensitivity).
  Discharges in well under one second.
* **Track-independence audit** — direct code inspection confirms
  zero references from the Theorem 1 lower-bound chain
  (`repair_length_ge_optimal` and friends) to any Lemma 1 family
  theorem. The two tracks are mathematically and structurally
  independent, mirroring paper's own proof structure.

All optimality validation is reproducible via:

```bash
lake build Project.validation.Optimality
```

The optional sub-files (`Validation7_BruteForceOptimality`,
`Validation8_Fin5Stress`, `Validation9_AntiTest`, `BruteForceAxioms`)
are not pulled in by the aggregate by default; uncomment the relevant
import lines at the top of `Project/validation/Optimality.lean` to
include them, or build them individually via
`lake build Project.validation.Optimality.X`.

---

## Axiom baseline

All theorem-level optimality endpoints
(`futuramaTheorem1OfPerm`, `futuramaTheorem1Full`, `futurama_optimal`,
`optimalScriptOfPerm_isOptimal`, `optimalScriptOfPerm_correct`,
`optimalScriptOfPerm_length`, `repair_length_ge_optimal`,
`repair_length_parity`, `repair_length_ge_entries`,
`repair_length_ge_entries_add_cycles`,
`repair_length_ne_entries_add_cycles`,
`transposition_count_ge_cycle_length`,
`minimal_factorization_covers_support`,
`minimal_factorization_factorEndpoints_mem_support`,
`minimal_factorization_factorEntries_mem_support`,
`minimal_factorization_has_adjacent`,
`minimal_factorization_has_adjacent_paper`,
`keeler_achieves_and_gap`, `keeler_optimal_single_cycle`,
`optimalScript_length_single_cycle`,
`optimalRepairSeqOfPerm`, `cutFamily_uniformLowerBound`) depend only
on the standard Lean / Mathlib axioms:

```
{propext, Classical.choice, Quot.sound}
```

with one good outlier: `undoScript_length_single_cycle` only
depends on `{propext, Quot.sound}` (no `Classical.choice` is
required by the proof, which routes through `undoScript_length`
plus `simp`).

The Class II axioms `{Lean.ofReduceBool, Lean.trustCompiler}` appear
**only** in the brute-force theorems
(`bruteForceOptimality_Fin3`, `bruteForceOptimality_Fin4`) where
`native_decide` is the discharge tactic. They are isolated to
`Validation7_BruteForceOptimality.lean` and do not leak into any
kernel theorem.

---

## Bottom line

Paper Theorem 1 of Evans–Huang–Nguyen 2014 is fully formalised:
upper bound (constructive), lower bound (universal over arbitrary
`RepairSeq`), and the Keeler-gap remark for all `r`. The
graph-theoretic Lemma 1 family is also fully formalised as a
parallel paper-faithful track. All endpoints are kernel-clean
(Class I axioms only). No remaining open issue.
