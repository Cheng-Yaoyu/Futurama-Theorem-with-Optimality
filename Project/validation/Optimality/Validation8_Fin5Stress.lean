import Project.validation.Optimality.Validation7_BruteForceOptimality

/-!
# Validation 8 — Fin 5 exploration (experimental, non-gating)

This file is **experimental** and **non-gating**: nothing it does
contributes to the kernel proof of the Futurama theorem. The kernel
endpoints `futuramaTheoremOfPerm` / `futuramaTheorem1OfPerm` /
`futurama_optimal` are already universally quantified over arbitrary
finite `α`, so any `Fin 5` instantiation is corroboration only.

The expensive `native_decide` invocations in Sections 4-6 are
**commented out by default** to keep `lake build` fast. The
mathematical content (representative `Fin 5` cycle structures,
optimal-length sanity equations, brute-force scaffolding) remains
visible as documentation.

| Section | Activity | Estimated wall-clock |
|---------|----------|----------------------|
| 1 (active) | Theorem-level instantiations of every public endpoint at `Perm (Fin 5)` | < 1 s (elaboration only) |
| 2 (active) | `cycle5` and `cycle32` definitions plus structural `decide` sanity | < 1 s |
| 3 (active) | Optimal-length sanity equations | < 1 s |
| 4 (commented) | `bruteForceOptimalityCheck` on `cycle5` (single 5-cycle, ~2·10⁶ candidates) | minutes |
| 5 (commented) | `bruteForceOptimalityCheck` on `cycle32` (the `(3,2)` cycle structure, ~8.7·10⁶ candidates) | minutes |
| 6 (commented) | Full `∀ σ : Perm (Fin 5)` brute force (~5·10⁸ candidates) | hours; high RAM |

Section 6 in particular is intractable on commodity hardware
(observed OOM at ~16 GB RAM). To enable any commented section,
remove the surrounding `/- ... -/` braces; sections are
independent.
-/

open Equiv Equiv.Perm

namespace Project
namespace Futurama
namespace Validation8Fin5

open Validation7BruteForceOptimality

--------------------------------------------------------------------------------
-- Section 1: Main theorem Fin 5 theorem-level instantiation (active)
--
-- Pure type-checks: apply universally quantified main theorems
-- to `α := Fin 5` and confirm Lean accepts the type. No
-- `native_decide`. Elaboration-time only.
--------------------------------------------------------------------------------

example (σ : Perm (Fin 5)) :
    runScript (undoScriptOfPerm σ) * liftPerm σ = 1 :=
  futuramaTheoremOfPerm σ

example (σ : Perm (Fin 5)) :
    runScript (undoScriptOfPerm σ) * liftPerm σ = 1 ∧
      (undoScriptOfPerm σ).Nodup ∧
      ((undoScriptOfPerm σ).map stepPair).Nodup ∧
      ∀ step ∈ undoScriptOfPerm σ, UsesHelper step :=
  futuramaTheoremOfPermStrong σ

example (σ : Perm (Fin 5)) :
    runScript (undoScriptOfPerm σ) * liftPerm σ = 1 ∧
      (undoScriptOfPerm σ).Nodup ∧
      ((undoScriptOfPerm σ).map stepPair).Nodup ∧
      (∀ step ∈ undoScriptOfPerm σ, UsesHelper step) ∧
      (∀ step ∈ undoScriptOfPerm σ, step.1 ≠ step.2) :=
  futuramaTheoremOfPermStrongFullSpec σ

example (σ : Perm (Fin 5)) (hσ : 0 < σ.cycleFactorsFinset.card) :
    runScript (optimalScriptOfPerm σ) * liftPerm σ = 1 ∧
      (optimalScriptOfPerm σ).length =
        σ.support.card + σ.cycleFactorsFinset.card + 2 ∧
      ∀ seq : RepairSeq (liftPerm σ),
        (optimalScriptOfPerm σ).length ≤ seq.steps.length :=
  futuramaTheorem1OfPerm σ hσ

example (σ : Perm (Fin 5)) (hσ : 0 < σ.cycleFactorsFinset.card) :
    ∃ seq : RepairSeq (liftPerm σ),
      seq.steps.length = σ.support.card + σ.cycleFactorsFinset.card + 2 ∧
      ∀ seq' : RepairSeq (liftPerm σ), seq.steps.length ≤ seq'.steps.length :=
  futuramaTheorem1Full σ hσ

example (σ : Perm (Fin 5)) (hσ : 0 < σ.cycleFactorsFinset.card)
    (seq : RepairSeq (liftPerm σ)) :
    σ.support.card + σ.cycleFactorsFinset.card + 2 ≤ seq.steps.length :=
  futurama_optimal σ hσ seq

example (σ : Perm (Fin 5)) (hσ : σ.IsCycle)
    (ts : List (Perm (Fin 5))) (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = σ) :
    σ.support.card - 1 ≤ ts.length :=
  transposition_count_ge_cycle_length σ hσ ts hfactors hprod

example (c : Cycle (Fin 5)) :
    (undoScript [c]).length = (optimalScript [c]).length :=
  keeler_optimal_single_cycle c

noncomputable example (σ : Perm (Fin 5)) (hσ : 0 < σ.cycleFactorsFinset.card) :
    RepairSeq (liftPerm σ) :=
  optimalRepairSeqOfPerm σ hσ

--------------------------------------------------------------------------------
-- Section 2: Representative worst-case permutations on Fin 5
--
-- Two permutations are constructed (used by the commented-out
-- brute-force scaffolding in Sections 4-6):
--   (A) the single 5-cycle (0 1 2 3 4) -- worst-case r=1, n=5
--   (B) the (3,2) product (0 1 2)(3 4) -- worst-case r=2, n=5,
--       and the first cycle structure with two disjoint cycles of
--       different lengths (Fin 4 only had (2,2)).
--
-- Verification of the intended action is in the `decide` examples
-- immediately below each definition.
--------------------------------------------------------------------------------

/-- The 5-cycle `(0 1 2 3 4)`: `0 ↦ 1, 1 ↦ 2, 2 ↦ 3, 3 ↦ 4, 4 ↦ 0`. -/
def cycle5 : Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4

/-- The disjoint product `(0 1 2)(3 4)`: `0 ↦ 1, 1 ↦ 2, 2 ↦ 0, 3 ↦ 4, 4 ↦ 3`. -/
def cycle32 : Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 3 4

example : cycle5 0 = 1 := by decide
example : cycle5 1 = 2 := by decide
example : cycle5 2 = 3 := by decide
example : cycle5 3 = 4 := by decide
example : cycle5 4 = 0 := by decide

example : cycle32 0 = 1 := by decide
example : cycle32 1 = 2 := by decide
example : cycle32 2 = 0 := by decide
example : cycle32 3 = 4 := by decide
example : cycle32 4 = 3 := by decide

example : cycle5.support.card = 5 := by decide
example : cycle32.support.card = 5 := by decide

example : cycle5.cycleFactorsFinset.card = 1 := by decide
example : cycle32.cycleFactorsFinset.card = 2 := by decide

example : 0 < cycle5.cycleFactorsFinset.card := by decide
example : 0 < cycle32.cycleFactorsFinset.card := by decide

--------------------------------------------------------------------------------
-- Section 3: Optimal-length sanity (the values bruteForceOptimalityCheck
-- looks for as `target = n + r + 2`)
--
-- For cycle5  (n=5, r=1): target = 8
-- For cycle32 (n=5, r=2): target = 9
--------------------------------------------------------------------------------

example :
    cycle5.support.card + cycle5.cycleFactorsFinset.card + 2 = 8 := by decide

example :
    cycle32.support.card + cycle32.cycleFactorsFinset.card + 2 = 9 := by decide

--------------------------------------------------------------------------------
-- Section 4: Brute-force on cycle5  (DOCUMENTED, COMMENTED — ~2 min)
--
-- Worst case for r=1 at Fin 5. Per-perm enumeration ~2·10⁶ candidates.
-- Wall-clock ~2 min via `native_decide` on Apple Silicon M4 mini 16 GB.
-- Uncomment to re-run; keeping commented avoids per-build cost.
--------------------------------------------------------------------------------

/-
example :
    bruteForceOptimalityCheck (List.finRange 5) cycle5 = true := by
  native_decide
-/

--------------------------------------------------------------------------------
-- Section 5: Brute-force on cycle32  (DOCUMENTED, COMMENTED — ~4 min)
--
-- Worst case for r=2 at Fin 5; (3,2) is the first cycle structure
-- with disjoint cycles of different lengths. Per-perm enumeration
-- ~8.7·10⁶ candidates -- ~4× harder than Section 4.
-- Wall-clock ~4 min on the same machine.
-- Uncomment to re-run.
--------------------------------------------------------------------------------

/-
example :
    bruteForceOptimalityCheck (List.finRange 5) cycle32 = true := by
  native_decide
-/

--------------------------------------------------------------------------------
-- Section 6: Full ∀ σ : Perm (Fin 5) brute force
--            (DOCUMENTED, COMMENTED — 6+ hours, OOM-risk on 16 GB)
--
-- Aggregate enumeration ≈ 5·10⁸ candidate scripts. Naive single-quantifier
-- form is not feasible on 16 GB Apple Silicon (an attempted overnight run
-- was killed by the OS after ~31 min before any output was flushed; root
-- cause is that `native_decide` reduces the entire 119-σ verification as
-- one giant term whose peak memory exceeds available RAM). A split form
-- (one `example := by native_decide` per non-trivial σ) was also attempted
-- with the same outcome.
--
-- Engineering directions to make this feasible (none implemented; not
-- required for project correctness): support-restricted candidate
-- enumeration; parity / touch-count prefix pruning; a host machine with
-- ≥ 32 GB RAM. The kernel proof `futurama_optimal` already proves the
-- universal lower bound for arbitrary `n`, so this section's
-- corroboration is non-essential.
--
-- Do not uncomment on a 16 GB machine.
--------------------------------------------------------------------------------

/-
example :
    ∀ σ : Perm (Fin 5), 0 < σ.cycleFactorsFinset.card →
      bruteForceOptimalityCheck (List.finRange 5) σ = true := by
  native_decide
-/

end Validation8Fin5
end Futurama
end Project
