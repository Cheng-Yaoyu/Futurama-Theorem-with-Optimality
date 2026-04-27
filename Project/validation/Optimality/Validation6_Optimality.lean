import Project.TestProject

/-!
# Validation — Optimality

Boolean validators and concrete example checks for paper Theorem 1's
upper-bound construction (`optimalScript`) and the Keeler-gap formula.

This file is **Class II**: it discharges its example checks via
`native_decide`, which adds `Lean.ofReduceBool` and
`Lean.trustCompiler` to the axiom set. The kernel-level proof axioms
of `optimalScriptOfPerm_isOptimal` themselves remain Class I.

The file provides the boolean validators (`repairSeqValidator`,
`optimalScriptValidator`, `keelerGapFormula`), concrete example
checks on four representative cycle structures, cross-semantics
agreement examples, Keeler-gap sanity examples, and the cut-family
uniform-lower-bound theorem `cutFamily_uniformLowerBound`.
-/

open Equiv Equiv.Perm

namespace Project.Futurama.Validation6Optimality

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Section 1: Boolean validators -/

/-- Generic `RepairSeq`-shaped boolean validator. Returns `true` iff a
candidate `steps` list against a target `π : Perm (Body α)` simultaneously
satisfies all four `RepairSeq` machine-side properties:

* helper involvement (`stepsUseHelpers`),
* nontriviality (`stepsNontrivial`),
* distinctness of unordered pairs (`(steps.map stepPair).Nodup`),
* correctness (`runScript steps * π = 1`).

Re-uses `stepsUseHelpers` and `stepsNontrivial` from
`Project.Futurama.ValidationKit`. -/
def repairSeqValidator (steps : List (Body α × Body α)) (π : Perm (Body α)) : Bool :=
  stepsUseHelpers steps &&
  stepsNontrivial steps &&
  decide ((steps.map stepPair).Nodup) &&
  decide (runScript steps * π = 1)

/-- Specialisation of `repairSeqValidator` to `optimalScript`-on-`cycleProduct`,
plus an exact-length check `(optimalScript cs).length = n + r + 2`
where `n = (cs.map fun c => c.members.length).sum` and `r = cs.length`. -/
def optimalScriptValidator (cs : List (Cycle α)) : Bool :=
  repairSeqValidator (optimalScript cs) (cycleProduct cs) &&
  decide ((optimalScript cs).length =
    (cs.map fun c => c.members.length).sum + cs.length + 2)

/-- Keeler-gap formula for `cs.length ≥ 2`: returns the explicit
`(r - 2) + parity` gap predicted by `keeler_achieves_and_gap`. -/
def keelerGapFormula (cs : List (Cycle α)) : ℕ :=
  (cs.length - 2) + (if cs.length % 2 = 0 then 0 else 1)

/-! ## Section 2: Concrete example witnesses -/

/-- 3-cycle `(0 1 2)` in `S_3`. Paper indices: `n = 3`, `r = 1`, optimal length 6. -/
def cycle3 : Cycle (Fin 3) := ⟨0, 1, [2], by decide⟩

/-- 4-cycle `(0 1 2 3)` in `S_4`. Paper indices: `n = 4`, `r = 1`, optimal length 7. -/
def cycle4 : Cycle (Fin 4) := ⟨0, 1, [2, 3], by decide⟩

/-- Two disjoint 2-cycles `(0 1)(2 3)` in `S_4`. The paper's Stargate `P(2)`
example. `n = 4`, `r = 2`, optimal length 8. -/
def cycles2x2 : List (Cycle (Fin 4)) :=
  [⟨0, 1, [], by decide⟩, ⟨2, 3, [], by decide⟩]

/-- Three disjoint 2-cycles `(0 1)(2 3)(4 5)` in `S_6`. `n = 6`, `r = 3`,
optimal length 11. The paper's `P(3)` (a Stargate generalisation). -/
def cycles3x2 : List (Cycle (Fin 6)) :=
  [⟨0, 1, [], by decide⟩, ⟨2, 3, [], by decide⟩, ⟨4, 5, [], by decide⟩]

/-! ## Section 3: optimalScriptValidator passes on every example -/

example : optimalScriptValidator [cycle3] = true := by native_decide
example : optimalScriptValidator [cycle4] = true := by native_decide
example : optimalScriptValidator cycles2x2 = true := by native_decide
example : optimalScriptValidator cycles3x2 = true := by native_decide

/-! ## Section 4: repairSeqValidator (generic shape) on the optimal witnesses -/

example :
    repairSeqValidator (optimalScript [cycle3]) (cycleProduct [cycle3]) = true := by
  native_decide

example :
    repairSeqValidator (optimalScript [cycle4]) (cycleProduct [cycle4]) = true := by
  native_decide

example :
    repairSeqValidator (optimalScript cycles2x2) (cycleProduct cycles2x2) = true := by
  native_decide

example :
    repairSeqValidator (optimalScript cycles3x2) (cycleProduct cycles3x2) = true := by
  native_decide

/-! ## Section 5: Cross-semantics agreement (runState ↔ runScript) at every prefix -/

example :
    prefixSemanticsAgree (optimalScript [cycle3]) (cycleProduct [cycle3]) = true := by
  native_decide

example :
    prefixSemanticsAgree (optimalScript [cycle4]) (cycleProduct [cycle4]) = true := by
  native_decide

example :
    prefixSemanticsAgree (optimalScript cycles2x2) (cycleProduct cycles2x2) = true := by
  native_decide

example :
    prefixSemanticsAgree (optimalScript cycles3x2) (cycleProduct cycles3x2) = true := by
  native_decide

/-! ## Section 6: Keeler-gap sanity examples

For `r = 1` examples: `(undoScript [c]).length = (optimalScript [c]).length`.
These corroborate the theorem-level statement `keeler_optimal_single_cycle`.

For `r ≥ 2` examples: the gap matches `keelerGapFormula` (paper-equivalent
`(r - 2) + parity`). -/

-- r = 1 examples: equality
example : (undoScript [cycle3]).length = (optimalScript [cycle3]).length := by native_decide
example : (undoScript [cycle4]).length = (optimalScript [cycle4]).length := by native_decide

-- r = 2: gap formula (matches paper, gap = 0)
example :
    (undoScript cycles2x2).length =
      (optimalScript cycles2x2).length + keelerGapFormula cycles2x2 := by
  native_decide

-- r = 3: gap formula (matches paper, gap = 2)
example :
    (undoScript cycles3x2).length =
      (optimalScript cycles3x2).length + keelerGapFormula cycles3x2 := by
  native_decide

-- Sanity: at r = 2 the gap really is 0
example : keelerGapFormula cycles2x2 = 0 := by native_decide

-- Sanity: at r = 3 the gap really is 2
example : keelerGapFormula cycles3x2 = 2 := by native_decide

/-! ## Section 7: Per-example length sanity checks -/

-- 3-cycle: optimal length n + r + 2 = 3 + 1 + 2 = 6
example : (optimalScript [cycle3]).length = 6 := by native_decide

-- 4-cycle: optimal length 4 + 1 + 2 = 7
example : (optimalScript [cycle4]).length = 7 := by native_decide

-- (0 1)(2 3): optimal length 4 + 2 + 2 = 8
example : (optimalScript cycles2x2).length = 8 := by native_decide

-- (0 1)(2 3)(4 5): optimal length 6 + 3 + 2 = 11
example : (optimalScript cycles3x2).length = 11 := by native_decide

/-! ## Section 8: Cut-family uniform lower bound

For every non-trivial `σ` and every `cuts : CutSchedule (factorCycles σ)`,
the Keeler-family length `(undoScriptOfPermAt σ cuts).length` is at least
`n + r + 2`. This is a structurally-trivial wrapper: it packages
`undoScriptOfPermAt σ cuts` into a `RepairSeq (liftPerm σ)` using the
already-public machine-side lemmas, then invokes `futurama_optimal`.

Class breakdown: this theorem itself is Class I (no `native_decide`).
The file as a whole remains Class II because of Sections 3-7 examples. -/

/-- Cut-family uniform lower bound: every cut-schedule member of the
parameterised Keeler-family produces a script of length at least `n + r + 2`.

Structurally trivial: builds a `RepairSeq` from `undoScriptOfPermAt σ cuts`
using the already-public `mem_undoScriptAt_usesHelper`,
`mem_undoScriptAt_nontrivial`, `undoScriptAt_stepPairs_nodup`, and the
correctness side from `futuramaTheoremOfPermAt`; then feeds the result into
`futurama_optimal`. No new mathematical content; the role is to surface the
same lower bound at the `undoScriptOfPermAt`-indexed surface. -/
theorem cutFamily_uniformLowerBound
    (σ : Perm α) (hσ : 0 < σ.cycleFactorsFinset.card)
    (cuts : CutSchedule (factorCycles σ)) :
    σ.support.card + σ.cycleFactorsFinset.card + 2 ≤
      (undoScriptOfPermAt σ cuts).length := by
  let seq : RepairSeq (liftPerm σ) :=
    { steps := undoScriptOfPermAt σ cuts
      helper_constraint := by
        intro step hstep
        exact mem_undoScriptAt_usesHelper (by simpa [undoScriptOfPermAt] using hstep)
      nontrivial := by
        intro step hstep
        exact mem_undoScriptAt_nontrivial (by simpa [undoScriptOfPermAt] using hstep)
      distinct_pairs := by
        simpa [undoScriptOfPermAt] using
          undoScriptAt_stepPairs_nodup (cs := factorCycles σ) cuts
            (factorCycles_pairwise_disjoint σ)
      undoes := futuramaTheoremOfPermAt σ cuts }
  exact futurama_optimal σ hσ seq

end Project.Futurama.Validation6Optimality
