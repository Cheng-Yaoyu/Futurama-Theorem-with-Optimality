import Project.validation.Optimality.Validation6_Optimality

/-!
# Validation 7 -- Brute-force optimality check

**Status: optional / non-gating**. The abstract lower bound is already
proved at kernel level by `futurama_optimal` /
`repair_length_ge_optimal` with Class I axioms. This file provides an
orthogonal, concrete, `native_decide`-backed corroboration that no
sub-`(n + r + 2)`-length helper-containing script can undo a non-trivial
small `σ`.

This file is **Class II** (uses `native_decide`). It is intentionally
kept separate from the kernel endpoints so Class II axioms
(`Lean.ofReduceBool`, `Lean.trustCompiler`) do not propagate into
`Project/TestProject.lean`.

The `bruteForceOptimalityCheck` is a pure-`Bool` predicate, so the
`native_decide` tactic lands on a final boolean equation rather than
a compound proof-carrying proposition (the "Bool-layer discipline").

To keep the enumeration computable, `helperTranspositionCandidates`
takes an explicit `List α` of original elements rather than going
through `Finset.univ.toList` (which is `noncomputable` in the
Mathlib used by this project). For `Fin n`, callers pass
`List.finRange n`.
-/

open Equiv Equiv.Perm

namespace Project
namespace Futurama
namespace Validation7BruteForceOptimality

variable {α : Type*} [DecidableEq α]

--------------------------------------------------------------------------------
-- Section 1: Helper-containing transposition enumeration
--------------------------------------------------------------------------------

/-- Enumerate all unordered helper-containing transposition pairs whose
original component lies in `origs`, in canonical orientation
(helper on the left). The output has `2 * origs.length + 1` entries:
one `(x, y)` plus `(x, orig a)` and `(y, orig a)` for each `a ∈ origs`. -/
def helperTranspositionCandidates (origs : List α) : List (Body α × Body α) :=
  (Body.x, Body.y) ::
    origs.flatMap fun a => [(Body.x, Body.orig a), (Body.y, Body.orig a)]

/-- Recursive enumeration of all length-`k` sequences of distinct items
drawn from `cands`. -/
def distinctSequencesOfLength (cands : List (Body α × Body α)) :
    ℕ → List (List (Body α × Body α))
  | 0 => [[]]
  | k + 1 =>
      cands.flatMap fun c =>
        (distinctSequencesOfLength (cands.erase c) k).map (fun s => c :: s)

/-- All sequences of distinct items from `cands` with length strictly
less than `n`. -/
def scriptsOfLengthLT (cands : List (Body α × Body α)) (n : ℕ) :
    List (List (Body α × Body α)) :=
  (List.range n).flatMap (distinctSequencesOfLength cands)

variable [Fintype α]

/-- Brute-force optimality predicate: returns `true` iff every script
with strictly fewer than `(n + r + 2)` distinct helper-containing
transpositions fails the `repairSeqValidator` against `liftPerm σ`.
Equivalently: no sub-optimal-length helper-containing script undoes `σ`.

The `origs` parameter is the explicit list of original elements over
which the candidate set is built; for `Fin n` the canonical choice is
`List.finRange n`. -/
def bruteForceOptimalityCheck (origs : List α) (σ : Perm α) : Bool :=
  let target := σ.support.card + σ.cycleFactorsFinset.card + 2
  let cands := helperTranspositionCandidates origs
  (scriptsOfLengthLT cands target).all fun steps =>
    !(Validation6Optimality.repairSeqValidator steps (liftPerm σ))

end Validation7BruteForceOptimality
end Futurama
end Project

--------------------------------------------------------------------------------
-- Section 2: Fin 3 corroboration
--
-- Helper-containing pair count: 2 * 3 + 1 = 7
-- Max optimal length on Fin 3: 6 (single 3-cycle: n=3, r=1, n+r+2=6)
-- Sub-optimal sequences per σ: at most Σ_{k=0}^{5} P(7, k) ≈ 3000
-- 5 non-trivial perms total, aggregate enumeration ≈ 15000 candidates.
--------------------------------------------------------------------------------

namespace Project
namespace Futurama
namespace Validation7BruteForceOptimality

/-- Brute-force corroboration: at `Fin 3`, no non-trivial permutation can
be undone by fewer than `n + r + 2` distinct helper-containing
transpositions. -/
theorem bruteForceOptimality_Fin3 :
    ∀ σ : Perm (Fin 3), 0 < σ.cycleFactorsFinset.card →
      bruteForceOptimalityCheck (List.finRange 3) σ = true := by
  native_decide

end Validation7BruteForceOptimality
end Futurama
end Project

--------------------------------------------------------------------------------
-- Section 3: Fin 4 corroboration
--
-- Helper-containing pair count: 2 * 4 + 1 = 9
-- Max optimal length on Fin 4: 8 (two 2-cycles: n=4, r=2, n+r+2=8)
-- Sub-optimal sequences per σ: at most Σ_{k=0}^{7} P(9, k) ≈ 2.6 · 10^5
-- 23 non-trivial perms total, aggregate enumeration ≈ 6 · 10^6 candidates.
--
-- This example uses the same naive enumeration as Fin 3; no
-- "short-circuit on early-prefix permutation mismatch" optimisation
-- is applied. Wall-clock is in the minutes range.
--------------------------------------------------------------------------------

namespace Project
namespace Futurama
namespace Validation7BruteForceOptimality

/-- Brute-force corroboration: at `Fin 4`, no non-trivial permutation can
be undone by fewer than `n + r + 2` distinct helper-containing
transpositions. Wall-clock ≈ 38 seconds via naive `native_decide`. -/
theorem bruteForceOptimality_Fin4 :
    ∀ σ : Perm (Fin 4), 0 < σ.cycleFactorsFinset.card →
      bruteForceOptimalityCheck (List.finRange 4) σ = true := by
  native_decide

end Validation7BruteForceOptimality
end Futurama
end Project
