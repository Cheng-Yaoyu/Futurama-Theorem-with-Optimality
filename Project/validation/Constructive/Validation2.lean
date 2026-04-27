import Project.Futurama

open Equiv Equiv.Perm

namespace Project
namespace Futurama
namespace Validation2

/-!
# Validation 2 — Executable cross-checks for the constructive theorem

Machine-checked artifacts covering three areas:

1. package the endpoint theorem into a theorem that matches the external
   Futurama/Wikipedia-style specification more directly;
2. make the "each step is a genuine transposition" clause explicit by deriving
   nontriviality of every produced step;
3. stress-test the parameterised cut family by exhaustive checks on explicit
   finite examples, using direct computation rather than reusing the final
   correctness theorem.
-/

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem canonicalStep_nontrivial {step : Body α × Body α} (h : CanonicalStep step) :
    step.1 ≠ step.2 := by
  rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl <;> simp

omit [DecidableEq α] in
theorem mem_undoScript_nontrivial {cs : List (Cycle α)} {step : Body α × Body α}
    (h : step ∈ undoScript cs) : step.1 ≠ step.2 :=
  canonicalStep_nontrivial (mem_undoScript_canonical h)

section PermLevel

variable [Fintype α]

omit [DecidableEq α] [Fintype α] in
theorem mem_undoScriptAt_nontrivial
    {cs : List (Cycle α)} {cuts : CutSchedule cs} {step : Body α × Body α}
    (h : step ∈ undoScriptAt cuts) : step.1 ≠ step.2 :=
  canonicalStep_nontrivial (mem_undoScriptAt_canonical h)

theorem undoScriptOfPermAt_samePermutation
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    runScript (undoScriptOfPermAt σ cuts) = runScript (undoScriptOfPerm σ) := by
  simpa [undoScriptOfPermAt, undoScriptOfPerm] using
    runScript_undoScriptAt_eq_runScript_undoScript cuts

/-- Validation-level full-spec wrapper matching the main-file theorem name. -/
theorem futuramaTheoremOfPermStrongFullSpec (σ : Perm α) :
    runScript (undoScriptOfPerm σ) * liftPerm σ = 1 ∧
      (undoScriptOfPerm σ).Nodup ∧
      ((undoScriptOfPerm σ).map stepPair).Nodup ∧
      (∀ step ∈ undoScriptOfPerm σ, UsesHelper step) ∧
      (∀ step ∈ undoScriptOfPerm σ, step.1 ≠ step.2) := by
  simpa using RepairSpec.toFullSpecTheorem (Project.Futurama.externalRepairSpec σ)

/-- Validation-level full-spec wrapper for the parameterised permutation endpoint. -/
theorem futuramaTheoremOfPermStrongAtFullSpec
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    runScript (undoScriptOfPermAt σ cuts) * liftPerm σ = 1 ∧
      runScript (undoScriptOfPermAt σ cuts) = runScript (undoScriptOfPerm σ) ∧
      (undoScriptOfPermAt σ cuts).Nodup ∧
      ((undoScriptOfPermAt σ cuts).map stepPair).Nodup ∧
      (∀ step ∈ undoScriptOfPermAt σ cuts, UsesHelper step) ∧
      (∀ step ∈ undoScriptOfPermAt σ cuts, step.1 ≠ step.2) := by
  have hfull :
      runScript (undoScriptOfPermAt σ cuts) * liftPerm σ = 1 ∧
        (undoScriptOfPermAt σ cuts).Nodup ∧
        ((undoScriptOfPermAt σ cuts).map stepPair).Nodup ∧
        (∀ step ∈ undoScriptOfPermAt σ cuts, UsesHelper step) ∧
        (∀ step ∈ undoScriptOfPermAt σ cuts, step.1 ≠ step.2) := by
    simpa using
      RepairSpec.toFullSpecTheorem (Project.Futurama.externalRepairSpecAt σ cuts)
  rcases hfull with ⟨hcorrect, hnodup, hstepPairs, hhelpers, hproper⟩
  exact ⟨hcorrect, undoScriptOfPermAt_samePermutation σ cuts,
    hnodup, hstepPairs, hhelpers, hproper⟩

theorem wikipediaStyleWitness (σ : Perm α) :
    ∃ steps : List (Body α × Body α),
      runScript steps * liftPerm σ = 1 ∧
      ((steps.map stepPair).Nodup) ∧
      (∀ step ∈ steps, UsesHelper step) ∧
      (∀ step ∈ steps, step.1 ≠ step.2) := by
  exact Project.Futurama.externalRepairWitness σ

/-- Neutral alias for the existential external-spec witness theorem. -/
theorem externalStyleWitness (σ : Perm α) :
    ∃ steps : List (Body α × Body α),
      runScript steps * liftPerm σ = 1 ∧
      ((steps.map stepPair).Nodup) ∧
      (∀ step ∈ steps, UsesHelper step) ∧
      (∀ step ∈ steps, step.1 ≠ step.2) :=
  wikipediaStyleWitness σ

theorem no_orig_orig_step_of_perm
    (σ : Perm α) (a b : α) :
    (Body.orig a, Body.orig b) ∉ undoScriptOfPerm σ := by
  simpa [undoScriptOfPerm] using
    not_mem_undoScript_orig_orig (factorCycles σ) a b

end PermLevel

section ExhaustiveChecks

abbrev Cast := Fin 7
abbrev CCycle := Cycle Cast

def c01 : CCycle where
  first := 0
  second := 1
  rest := []
  nodup := by decide

def c012 : CCycle where
  first := 0
  second := 1
  rest := [2]
  nodup := by decide

def c0123 : CCycle where
  first := 0
  second := 1
  rest := [2, 3]
  nodup := by decide

def c01234 : CCycle where
  first := 0
  second := 1
  rest := [2, 3, 4]
  nodup := by decide

def c23 : CCycle where
  first := 2
  second := 3
  rest := []
  nodup := by decide

def c234 : CCycle where
  first := 2
  second := 3
  rest := [4]
  nodup := by decide

def c456 : CCycle where
  first := 4
  second := 5
  rest := [6]
  nodup := by decide

def c3456 : CCycle where
  first := 3
  second := 4
  rest := [5, 6]
  nodup := by decide

def singleCycleCutValidation (c : CCycle) : Bool :=
  (List.finRange c.tail.length).all fun cut =>
    decide (
      repairPermAt c cut * cyclePerm c = helperSwap ∧
      repairPermAt c cut = repairPerm c ∧
      (repairScriptAt c cut).Nodup
    )
    &&
    stepsNontrivial (repairScriptAt c cut)

example : singleCycleCutValidation c01 = true := by native_decide
example : singleCycleCutValidation c012 = true := by native_decide
example : singleCycleCutValidation c0123 = true := by native_decide
example : singleCycleCutValidation c01234 = true := by native_decide

example : allSchedulesValidate [c01] = true := by native_decide
example : allSchedulesValidate [c012] = true := by native_decide
example : allSchedulesValidate [c0123] = true := by native_decide
example : allSchedulesValidate [c01234] = true := by native_decide
example : allSchedulesValidate [c01, c23] = true := by native_decide
example : allSchedulesValidate [c01, c234] = true := by native_decide
example : allSchedulesValidate [c012, c3456] = true := by native_decide
example : allSchedulesValidate [c01, c23, c456] = true := by native_decide

end ExhaustiveChecks

#print axioms Project.Futurama.futuramaTheoremOfPermStrong
#print axioms Project.Futurama.futuramaTheoremOfPermStrongAt
#print axioms Project.Futurama.Validation2.futuramaTheoremOfPermStrongFullSpec
#print axioms Project.Futurama.Validation2.wikipediaStyleWitness

end Validation2
end Futurama
end Project
