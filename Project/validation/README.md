# Validation

This directory contains the validation evidence for the Futurama
formalisation. It is organised into two layers:

* **Constructive validation** (`Constructive/Validation2.lean` …
  `Constructive/Validation5.lean`, aggregated as `Constructive.lean`)
  — exercises the constructive Wikipedia-style theorem from
  `Project/Futurama/*.lean`.
* **Optimality validation** (`Optimality/Validation6_Optimality.lean`,
  `Optimality/Validation7_BruteForceOptimality.lean` (optional),
  `Optimality/Validation8_Fin5Stress.lean` (optional, documentation),
  `Optimality/Validation9_AntiTest.lean` (optional, anti-tests),
  plus three axiom-baseline harnesses, aggregated as `Optimality.lean`)
  — exercises paper Theorem 1, the Lemma 1 family, and the
  Keeler-gap remark.

A top-level `Project/validation.lean` aggregates both layers.

## Aggregate entry points

```bash
# Master: everything in both layers
lake build Project.validation

# Constructive only
lake build Project.validation.Constructive

# Optimality only
lake build Project.validation.Optimality
```

The optimality aggregate intentionally does **not** pull in the
optional sub-files by default; they are documented and reachable
via direct `lake build Project.validation.Optimality.X` regardless.
To include them in the aggregate, uncomment the relevant import
lines at the top of `Project/validation/Optimality.lean`.

```bash
# Optional: brute-force optimality on Fin 3 + Fin 4 (~38 s)
lake build Project.validation.Optimality.Validation7_BruteForceOptimality

# Optional: anti-tests for the validator suite (< 1 s)
lake build Project.validation.Optimality.Validation9_AntiTest

# Optional: Fin 5 exploration (theorem-level instantiation only,
# brute-force calls inside are commented out per file docstring)
lake build Project.validation.Optimality.Validation8_Fin5Stress

# Optional: brute-force axiom-baseline check
lake build Project.validation.Optimality.BruteForceAxioms
```

All aggregate commands return `exit 0`.

## Validation strategy (eight layers)

The validation is layered to give independent evidence at multiple
levels of abstraction:

1. **Kernel correctness** — every Lean source file in the default
   build path builds with `exit 0`. No `sorry`, no `admit`, no
   user-defined axiom anywhere reachable from `lake build Project`.
   The randomised optional file `Validation11_PlausibleStress.lean`
   is **not** part of the default build (Plausible's documented
   `sorry`-discharge convention is the reason); it lives outside
   every aggregate and is built only on direct request.

2. **Definition correctness** — every load-bearing definition has a
   documented mathematical role (see module docstrings in each
   `*.lean` file). The `optimalScript` block hierarchy is pinned by
   an embedded 9-line `example := rfl` harness inside
   `Optimality/UpperBound.lean` so any future drift on the
   paper-λ definitional shape breaks the build immediately.

3. **Statement correctness** — every public endpoint has a docstring
   matching the corresponding paper claim. The full row-by-row
   paper-to-Lean mapping for Theorem 1 + Lemma 1 is in
   [`paper_correspondence.md`](paper_correspondence.md).

4. **Executable boolean validators** —
   `Optimality/Validation6_Optimality.lean` defines
   `repairSeqValidator`, `optimalScriptValidator`, and
   `keelerGapFormula`, then runs 22 `native_decide` examples on
   four representative cycle structures (3-cycle, 4-cycle, two
   disjoint 2-cycles, three disjoint 2-cycles). These check
   correctness + distinctness + helper inclusion + non-triviality +
   exact length + Keeler-gap formula simultaneously.

5. **Cross-semantics agreement** —
   `Constructive/Validation5.lean` defines a second executable
   semantics (`runState` over `BodyState`) and verifies prefix-by-
   prefix agreement with `runScript` on every non-trivial
   `Perm (Fin 4)` × every cut schedule (24 × 44 combinations).

6. **Brute-force corroboration (optional)** —
   `Optimality/Validation7_BruteForceOptimality.lean` exhaustively
   enumerates every distinct-helper-containing script of length
   `< n + r + 2` over `Fin 3` and `Fin 4` and verifies that none
   undoes any non-trivial `σ`. This is an orthogonal
   `native_decide`-backed concordance check on the kernel proof's
   universal lower bound.

A seventh layer of **negative controls / anti-tests**
(`Optimality/Validation9_AntiTest.lean`) closes the
"validator might silently always return true" blind spot by feeding
the boolean validators from `Validation6_Optimality.lean` deliberately
bad inputs and confirming each returns `false`.

An eighth layer of **deterministic large-cycle stress**
(`Constructive/Validation10_LargeStress.lean`) instantiates the kernel
endpoints on inputs beyond the exhaustive `Fin 4` reach: single cycles
at `k = 5, 10, 20` and three disjoint 4-cycles on `Fin 12`. Discharged
by the closed-form length theorem and direct application of the
kernel correctness theorem; no `sorry` introduced.

An optional randomised companion `Validation11_PlausibleStress.lean`
re-verifies V10's length-formula examples through Mathlib's
`plausible` tactic. Plausible closes a passing randomised goal with
`sorry`, so V11 is **not** imported by the constructive aggregate;
build it directly via
`lake build Project.validation.Constructive.Validation11_PlausibleStress`
when randomised coverage is desired.

## Axiom baselines

The axiom-baseline harnesses produce `#print axioms` output for the
public endpoints to certify they depend only on standard Lean /
Mathlib axioms:

* `Optimality/AxiomBaseline.lean` — every kernel optimality endpoint
  depends on `{propext, Classical.choice, Quot.sound}` (with one
  good outlier: `undoScript_length_single_cycle` only depends on
  `{propext, Quot.sound}`).
* `Optimality/CutFamilyAxioms.lean` — the cut-family uniform lower
  bound `cutFamily_uniformLowerBound` is also clean (`{propext,
  Classical.choice, Quot.sound}`).
* `Optimality/BruteForceAxioms.lean` — the brute-force theorems pull
  in `{Lean.ofReduceBool, Lean.trustCompiler}` because of
  `native_decide`. These Class II axioms are **isolated** to
  `Validation7_BruteForceOptimality.lean`; they do **not** propagate
  to any kernel theorem.

## Files

### Constructive layer

| File | Purpose |
|------|---------|
| `Constructive.lean` | Aggregate entry point importing the four files below. |
| `Constructive/Validation2.lean` | Full external-spec closure plus exhaustive cut-family checks on representative cycles. |
| `Constructive/Validation3.lean` | Defensive checks, orientation checks, negative controls, deep `#print axioms` audits. |
| `Constructive/Validation4.lean` | Direct lower-level spec derivation, source traceability (`wikiSingleCycleBlock_eq_repairScriptAt`), and the 24-element `Fin 4` witness corpus. |
| `Constructive/Validation5.lean` | Exhaustive cross-semantics over the full `Fin 4` witness × cut surface. |
| `Constructive/Validation10_LargeStress.lean` | Deterministic single-cycle stress at `k = 5, 10, 20` and multi-cycle medium-size stress (three disjoint 4-cycles on `Fin 12`). Complementary to V5/V6 (which max out at `Fin 4` exhaustively) and V7 (which brute-forces at `Fin 3, 4`). Discharged by the closed-form length theorem + `decide` and direct application of `optimalScript_correct`; no `sorry`. |
| `Constructive/Validation11_PlausibleStress.lean` *(optional, not in aggregate)* | Randomised companion to V10 using Mathlib's `plausible` tactic on the same length-formula property. Plausible closes a passing randomised goal with `sorry` rather than synthesising a kernel proof, so V11 is **deliberately excluded** from `Constructive.lean` to keep the default build `sorry`-clean. Build directly via `lake build Project.validation.Constructive.Validation11_PlausibleStress`. |

### Optimality layer

| File | Purpose | In aggregate? |
|------|---------|---------------|
| `Optimality.lean` | Aggregate entry point. | (the aggregate itself) |
| `Optimality/AxiomBaseline.lean` | `#print axioms` for every kernel optimality endpoint. | ✓ |
| `Optimality/Validation6_Optimality.lean` | Boolean validators + 22 `native_decide` examples + the cut-family uniform lower-bound theorem `cutFamily_uniformLowerBound`. | ✓ |
| `Optimality/CutFamilyAxioms.lean` | `#print axioms` for `cutFamily_uniformLowerBound`. | ✓ |
| `Optimality/Validation7_BruteForceOptimality.lean` | Brute-force corroboration on `Fin 3` and `Fin 4`. ~38 s wall-clock. | optional |
| `Optimality/Validation8_Fin5Stress.lean` | `Fin 5` exploration. Theorem-level instantiation is active; brute-force `native_decide` calls are commented out (file docstring lists per-section time estimates). | optional |
| `Optimality/Validation9_AntiTest.lean` | Negative controls confirming the boolean validators in `Validation6_Optimality.lean` reject malformed inputs. < 1 s. | optional |
| `Optimality/BruteForceAxioms.lean` | `#print axioms` for the brute-force theorems in `Validation7_BruteForceOptimality.lean` (Class II). | optional |

### Summary documents

| File | Purpose |
|------|---------|
| [`constructive_summary.md`](constructive_summary.md) | One-page summary of the constructive theorem validation. |
| [`optimality_summary.md`](optimality_summary.md) | One-page summary of the optimality theorem validation. |
| [`paper_correspondence.md`](paper_correspondence.md) | Row-by-row paper-to-Lean correspondence for Theorem 1 + Lemma 1 + Keeler-gap. |
