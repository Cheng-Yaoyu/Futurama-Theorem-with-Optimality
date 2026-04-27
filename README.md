# Formalising the Futurama Theorem (with optimality)

A complete Lean 4 + Mathlib formalisation of paper

> Ron Evans, Lihua Huang, Tuan Nguyen,
> *Keeler's Theorem and Products of Distinct Transpositions*,
> The American Mathematical Monthly **121** no. 2 (2014), 136–144.

A copy of the paper is included in this repository as
[`keeler2014.pdf`](keeler2014.pdf).

The theorem is the formal counterpart of the puzzle from the *Futurama*
episode "The Prisoner of Benda": a two-body mind-switching machine that
will not work twice on the same pair of bodies. The question — whether
**any** mind-scrambling permutation can be undone, and what the
**minimum** number of switches is — is answered constructively here.

## What is formalised

* **Constructive theorem** (a.k.a. Wikipedia / Futurama folk
  formulation): every finite permutation can be undone using two
  helper bodies, with every step a distinct helper-containing
  transposition. Both the default Keeler route and the parameterised
  cut family are proved.
* **Paper Theorem 1** (the refined Evans–Huang–Nguyen / Keeler
  result): every non-trivial permutation `P = C_1 · · · C_r` of
  disjoint cycles with `n = k_1 + · · · + k_r` can be undone by a
  product of **exactly `n + r + 2`** distinct helper-containing
  transpositions, and **no smaller number suffices**. The Lean
  formalisation provides both the explicit construction
  (`optimalScript`, `optimalScriptOfPerm`) and the matching
  `∀`-quantified lower bound (`futurama_optimal`), packaged together
  as `futuramaTheorem1OfPerm` (and as a single existence form,
  `futuramaTheorem1Full`).
* **Lemma 1 family** of the paper (a, b, c) — fully formalised,
  including the paper-strong form of Lemma 1(c) that exposes the
  `pre ++ [a, b] ++ suf` split and excludes the wrap-around edge.
* **Keeler-gap remark** for all `r ≥ 1`: `keeler_optimal_single_cycle`
  (`r = 1`) and `keeler_achieves_and_gap` (`r ≥ 2`).

The complete paper-to-Lean correspondence is in
[`Project/validation/paper_correspondence.md`](Project/validation/paper_correspondence.md).

## Build

This is a standard Lean 4 + Mathlib project. From the repo root:

```bash
# First-time setup (downloads Mathlib)
lake update

# Build everything
lake build

# Or build specific aggregates:
lake build Project.TestProject                  # main façade
lake build Project.validation.Constructive      # constructive validation
lake build Project.validation.Optimality        # optimality validation

# Optional: brute-force optimality at Fin 3 + Fin 4
# (~38 s wall-clock via native_decide; non-gating)
lake build Project.validation.Optimality.Validation7_BruteForceOptimality
lake build Project.validation.Optimality.BruteForceAxioms
```

The Mathlib version pinned in `lakefile.toml` is `v4.23.0`; Lean
toolchain is `leanprover/lean4:v4.23.0` (see `lean-toolchain`).

## Soundness

* **0** `sorry` / **0** `admit` / **0** user-defined `axiom` / **0**
  `opaque` / **0** `constant` in the default build path
  (`lake build Project`, `lake build Project.validation`,
  `lake build Project.validation.Constructive`,
  `lake build Project.validation.Optimality`).
* All public mathematical endpoints depend only on the standard Lean
  / Mathlib axioms `{propext, Classical.choice, Quot.sound}` (with
  one outlier: `undoScript_length_single_cycle` depends on only
  `{propext, Quot.sound}`).
* `{Lean.ofReduceBool, Lean.trustCompiler}` appear only in two
  `native_decide`-discharged validation theorems
  (`Validation5.exists_perm4_cross_checked` and
  `Validation7BruteForceOptimality.bruteForceOptimality_Fin{3,4}`)
  and are isolated to those validation files.
* The Plausible-driven randomised stress in
  `Validation11_PlausibleStress.lean` is **opt-in** (not imported by
  any aggregate). The `plausible` tactic in Mathlib v4.23.0 closes a
  passing randomised goal with `sorry`, so V11 is built only via
  `lake build Project.validation.Constructive.Validation11_PlausibleStress`;
  it is documented and reachable but does not enter any default
  build target, keeping the rest of the codebase `sorry`-clean.

## Reading order

1. [Project/README.md](Project/README.md) — code map.
2. [Project/PrisonerOfBenda.lean](Project/PrisonerOfBenda.lean) —
   one-page literate demonstration on an episode-inspired S6E10
   slice: 9 characters, 4-cycle + 3-cycle, restored by
   `optimalScript` in 11 swaps.
3. [Project/validation/optimality_summary.md](Project/validation/optimality_summary.md)
   — what the optimality side validates, in one page.
4. [Project/validation/paper_correspondence.md](Project/validation/paper_correspondence.md)
   — paper-to-Lean theorem-by-theorem mapping.
5. [Project/Futurama/Optimality/UpperBound.lean](Project/Futurama/Optimality/UpperBound.lean)
   — paper Theorem 1 construction λ + the central packaging
   (`futuramaTheorem1OfPerm` / `optimalRepairSeqOfPerm` /
   `futuramaTheorem1Full`).
6. [Project/Futurama/Optimality/LowerBound/Layer2.lean](Project/Futurama/Optimality/LowerBound/Layer2.lean)
   — the lower bound `t ≥ n + r + 2` and `futurama_optimal`.
7. [Project/Futurama/Optimality/Lemma1.lean](Project/Futurama/Optimality/Lemma1.lean)
   — Lemma 1(a)/(b)/(c).

## Out of scope

The following are **not** formalised here. They are paper-internal
extensions that build on the Lemma 1 family / parity theorem this
development already proves, and would be natural follow-ups:

* paper Theorem 2 (best possible algorithm for `P_1 := (12)(23)…(n−1,n)`,
  no helpers needed);
* paper Theorem 3 (best possible algorithm for `P_2 := (n,n−1)…(n,1)`,
  one helper needed);
* paper Theorem 4 (necessary and sufficient conditions for the
  identity to be expressible as a product of `m` distinct
  transpositions in `S_n`).

Single-helper / no-helper variants of the original Futurama Theorem
beyond the Keeler-gap remark are also out of scope.

## License

The repository is currently private for course submission. A
`LICENSE` file will be added (and a license selected — most likely
Apache-2.0 to match Mathlib) before the repository is made public.

The Lean formalisation in this repository is the author's original
work; the underlying mathematics is from Evans–Huang–Nguyen 2014
(cited above).
