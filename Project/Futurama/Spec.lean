import Project.Futurama.CoreCycle
import Project.Futurama.CoreSchedule
import Project.Futurama.FiniteBridge
import Project.Futurama.ParameterizedFamily

open Equiv Equiv.Perm

namespace Project
namespace Futurama

/-!
# Futurama Repair Specifications

This module defines the shared `RepairSpec` interface — a uniform
record packaging a repair script with all five machine-side
invariants (correctness, list-level Nodup, unordered-pair Nodup,
helper inclusion, every-step-non-trivial). Constructive theorems
elsewhere in the development produce `RepairSpec` instances via
`RepairSpec.ofCycles`, `RepairSpec.ofCyclesAt`, and the
`externalRepairSpec*` family.
-/

/-- A concrete repair script together with the correctness and machine-side
constraints expected from the constructive Futurama theorem. -/
structure RepairSpec {α : Type*} [DecidableEq α] (π : Perm (Body α)) where
  steps : List (Body α × Body α)
  correct : runScript steps * π = 1
  nodupSteps : steps.Nodup
  nodupPairs : (steps.map stepPair).Nodup
  helperIncluded : ∀ step ∈ steps, UsesHelper step
  properTransp : ∀ step ∈ steps, step.1 ≠ step.2

namespace RepairSpec

/-- `RepairSpec` packages are extensionally determined by their executable
script. All remaining fields live in proof-carrying propositions over that
script and are therefore proof-irrelevant once the scripts agree. -/
theorem ext_steps {α : Type*} [DecidableEq α] {π : Perm (Body α)}
    {lhs rhs : RepairSpec π} (hsteps : lhs.steps = rhs.steps) : lhs = rhs := by
  cases lhs with
  | mk steps correct nodupSteps nodupPairs helperIncluded properTransp =>
  cases rhs with
  | mk steps' correct' nodupSteps' nodupPairs' helperIncluded' properTransp' =>
      dsimp at hsteps
      subst steps'
      simp

/-- Transport a `RepairSpec` across an equality of target permutations without
changing its executable script or machine-side fields. -/
def castTarget {α : Type*} [DecidableEq α] {π ρ : Perm (Body α)}
    (h : π = ρ) (spec : RepairSpec π) : RepairSpec ρ where
  steps := spec.steps
  correct := by
    cases h
    exact spec.correct
  nodupSteps := spec.nodupSteps
  nodupPairs := spec.nodupPairs
  helperIncluded := spec.helperIncluded
  properTransp := spec.properTransp

@[simp] theorem castTarget_steps {α : Type*} [DecidableEq α]
    {π ρ : Perm (Body α)} (h : π = ρ) (spec : RepairSpec π) :
    (castTarget h spec).steps = spec.steps := rfl

/-- Project the correctness field from a `RepairSpec`. -/
theorem toCorrect {α : Type*} [DecidableEq α] {π : Perm (Body α)}
    (spec : RepairSpec π) :
    runScript spec.steps * π = 1 :=
  spec.correct

/-- Project the script-level `Nodup` field from a `RepairSpec`. -/
theorem toNodupSteps {α : Type*} [DecidableEq α] {π : Perm (Body α)}
    (spec : RepairSpec π) :
    spec.steps.Nodup :=
  spec.nodupSteps

/-- Project the unordered-pair `Nodup` field from a `RepairSpec`. -/
theorem toNodupPairs {α : Type*} [DecidableEq α] {π : Perm (Body α)}
    (spec : RepairSpec π) :
    (spec.steps.map stepPair).Nodup :=
  spec.nodupPairs

/-- Project the helper-inclusion field from a `RepairSpec`. -/
theorem toHelperIncluded {α : Type*} [DecidableEq α] {π : Perm (Body α)}
    (spec : RepairSpec π) :
    ∀ step ∈ spec.steps, UsesHelper step :=
  spec.helperIncluded

/-- Project the nontrivial-transposition field from a `RepairSpec`. -/
theorem toProperTransp {α : Type*} [DecidableEq α] {π : Perm (Body α)}
    (spec : RepairSpec π) :
    ∀ step ∈ spec.steps, step.1 ≠ step.2 :=
  spec.properTransp

/-- Extract the standard strong theorem bundle from any `RepairSpec`. -/
theorem toStrongTheorem {α : Type*} [DecidableEq α] {π : Perm (Body α)}
    (spec : RepairSpec π) :
    runScript spec.steps * π = 1 ∧
      spec.steps.Nodup ∧
      (spec.steps.map stepPair).Nodup ∧
      ∀ step ∈ spec.steps, UsesHelper step :=
  ⟨toCorrect spec, toNodupSteps spec, toNodupPairs spec,
    toHelperIncluded spec⟩

/-- Extract the full theorem bundle from any `RepairSpec`. -/
theorem toFullSpecTheorem {α : Type*} [DecidableEq α] {π : Perm (Body α)}
    (spec : RepairSpec π) :
    runScript spec.steps * π = 1 ∧
      spec.steps.Nodup ∧
      (spec.steps.map stepPair).Nodup ∧
      (∀ step ∈ spec.steps, UsesHelper step) ∧
      ∀ step ∈ spec.steps, step.1 ≠ step.2 :=
  ⟨toCorrect spec, toNodupSteps spec, toNodupPairs spec,
    toHelperIncluded spec, toProperTransp spec⟩

/-- Extract the external existential witness form used by the validation
harnesses from any `RepairSpec`. -/
theorem toExternalWitness {α : Type*} [DecidableEq α] {π : Perm (Body α)}
    (spec : RepairSpec π) :
    ∃ steps : List (Body α × Body α),
      runScript steps * π = 1 ∧
      (steps.map stepPair).Nodup ∧
      (∀ step ∈ steps, UsesHelper step) ∧
      ∀ step ∈ steps, step.1 ≠ step.2 :=
  ⟨spec.steps, toCorrect spec, toNodupPairs spec,
    toHelperIncluded spec, toProperTransp spec⟩

/-- Default cycle-list route, built directly from the existing default
construction. -/
def ofCycles {α : Type*} [DecidableEq α]
    (cs : List (Cycle α)) (hcs : cs.Pairwise Cycle.Disjoint) :
    RepairSpec (cycleProduct cs) where
  steps := undoScript cs
  correct := futuramaTheorem cs
  nodupSteps := undoScript_nodup hcs
  nodupPairs := undoScript_stepPairs_nodup hcs
  helperIncluded := by
    intro step hstep
    exact mem_undoScript_usesHelper hstep
  properTransp := by
    intro step hstep
    exact mem_undoScript_nontrivial hstep

@[simp] theorem ofCycles_steps {α : Type*} [DecidableEq α]
    (cs : List (Cycle α)) (hcs : cs.Pairwise Cycle.Disjoint) :
    (ofCycles cs hcs).steps = undoScript cs := rfl

/-- Parameterized cycle-list route, built directly from the existing
cut-schedule construction. -/
def ofCyclesAt {α : Type*} [DecidableEq α] [Fintype α]
    {cs : List (Cycle α)} (cuts : CutSchedule cs)
    (hcs : cs.Pairwise Cycle.Disjoint) :
    RepairSpec (cycleProduct cs) where
  steps := undoScriptAt cuts
  correct := futuramaTheoremAt cuts
  nodupSteps := undoScriptAt_nodup cuts hcs
  nodupPairs := undoScriptAt_stepPairs_nodup cuts hcs
  helperIncluded := by
    intro step hstep
    exact mem_undoScriptAt_usesHelper hstep
  properTransp := by
    intro step hstep
    exact mem_undoScriptAt_nontrivial hstep

@[simp] theorem ofCyclesAt_steps {α : Type*} [DecidableEq α] [Fintype α]
    {cs : List (Cycle α)} (cuts : CutSchedule cs)
    (hcs : cs.Pairwise Cycle.Disjoint) :
    (ofCyclesAt cuts hcs).steps = undoScriptAt cuts := rfl

theorem ofCycles_eq_ofCyclesAt_defaultSchedule
    {α : Type*} [DecidableEq α] [Fintype α]
    (cs : List (Cycle α)) (hcs : cs.Pairwise Cycle.Disjoint) :
    ofCycles cs hcs = ofCyclesAt (defaultSchedule cs) hcs := by
  apply ext_steps
  simp

/-- Permutation-level default route through the existing packaged endpoint. -/
noncomputable def ofPermEndpoint {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) : RepairSpec (liftPerm σ) := by
  rcases futuramaTheoremOfPermStrongFullSpec σ with
    ⟨hcorrect, hnodup, hstepPairs, hhelpers, hproper⟩
  exact
    { steps := undoScriptOfPerm σ
      correct := hcorrect
      nodupSteps := hnodup
      nodupPairs := hstepPairs
      helperIncluded := hhelpers
      properTransp := hproper }

@[simp] theorem ofPermEndpoint_steps
    {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    (ofPermEndpoint σ).steps = undoScriptOfPerm σ := by
  unfold ofPermEndpoint
  rcases futuramaTheoremOfPermStrongFullSpec σ with
    ⟨_, _, _, _, _⟩
  rfl

/-- Permutation-level default route rebuilt from lower-level lemmas rather
than by unpacking the strongest endpoint theorem. -/
noncomputable def ofPermDirect {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) : RepairSpec (liftPerm σ) := by
  let spec : RepairSpec (cycleProduct (factorCycles σ)) :=
    ofCycles (factorCycles σ) (factorCycles_pairwise_disjoint σ)
  exact castTarget (cycleProduct_factorCycles σ) spec

@[simp] theorem ofPermDirect_steps
    {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    (ofPermDirect σ).steps = undoScriptOfPerm σ := rfl

theorem ofPermEndpoint_eq_ofPermDirect
    {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    ofPermEndpoint σ = ofPermDirect σ := by
  apply ext_steps
  simp

/-- Parameterized permutation-level route through the existing packaged
endpoint. -/
noncomputable def ofPermAtEndpoint {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    RepairSpec (liftPerm σ) := by
  rcases futuramaTheoremOfPermStrongAtFullSpec σ cuts with
    ⟨hcorrect, hnodup, hstepPairs, hhelpers, hproper⟩
  exact
    { steps := undoScriptOfPermAt σ cuts
      correct := hcorrect
      nodupSteps := hnodup
      nodupPairs := hstepPairs
      helperIncluded := hhelpers
      properTransp := hproper }

@[simp] theorem ofPermAtEndpoint_steps
    {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    (ofPermAtEndpoint σ cuts).steps = undoScriptOfPermAt σ cuts := by
  unfold ofPermAtEndpoint
  rcases futuramaTheoremOfPermStrongAtFullSpec σ cuts with
    ⟨_, _, _, _, _⟩
  rfl

/-- Parameterized permutation-level route rebuilt from the lower-level
lemmas (rather than the packaged endpoint). -/
noncomputable def ofPermAtDirect {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    RepairSpec (liftPerm σ) := by
  let spec : RepairSpec (cycleProduct (factorCycles σ)) :=
    ofCyclesAt cuts (factorCycles_pairwise_disjoint σ)
  exact castTarget (cycleProduct_factorCycles σ) spec

@[simp] theorem ofPermAtDirect_steps
    {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    (ofPermAtDirect σ cuts).steps = undoScriptOfPermAt σ cuts := rfl

theorem ofPermAtEndpoint_eq_ofPermAtDirect
    {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    ofPermAtEndpoint σ cuts = ofPermAtDirect σ cuts := by
  apply ext_steps
  simp

theorem ofPermEndpoint_eq_ofPermAtEndpoint_defaultSchedule
    {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    ofPermEndpoint σ = ofPermAtEndpoint σ (defaultSchedule (factorCycles σ)) := by
  apply ext_steps
  simp

theorem ofPermDirect_eq_ofPermAtDirect_defaultSchedule
    {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    ofPermDirect σ = ofPermAtDirect σ (defaultSchedule (factorCycles σ)) := by
  apply ext_steps
  simp

end RepairSpec

/-- Neutral replacement for the old validation-level `WikipediaFuturama`
naming. This is a type-level label, not a distinct specification object. -/
abbrev ExternalRepairSpec {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) : Type _ :=
  RepairSpec (liftPerm σ)

/-- Type-level label for the direct lower-level construction path. -/
abbrev ExternalRepairSpecDirect {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) : Type _ :=
  RepairSpec (liftPerm σ)

/-- Type-level label for the parameterized endpoint construction path. -/
abbrev ExternalRepairSpecAt {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (_ : CutSchedule (factorCycles σ)) : Type _ :=
  RepairSpec (liftPerm σ)

/-- Type-level label for the parameterized direct construction path. -/
abbrev ExternalRepairSpecAtDirect {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (_ : CutSchedule (factorCycles σ)) : Type _ :=
  RepairSpec (liftPerm σ)

/-- Neutral endpoint-derived external repair package. -/
noncomputable def externalRepairSpec {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) : ExternalRepairSpec σ :=
  RepairSpec.ofPermEndpoint σ

/-- Neutral direct lower-level external repair package. -/
noncomputable def externalRepairSpecDirect {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) : ExternalRepairSpecDirect σ :=
  RepairSpec.ofPermDirect σ

/-- Neutral parameterized endpoint-derived external repair package. -/
noncomputable def externalRepairSpecAt {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    ExternalRepairSpecAt σ cuts :=
  RepairSpec.ofPermAtEndpoint σ cuts

/-- Neutral parameterized direct lower-level external repair package. -/
noncomputable def externalRepairSpecAtDirect
    {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    ExternalRepairSpecAtDirect σ cuts :=
  RepairSpec.ofPermAtDirect σ cuts

@[simp] theorem externalRepairSpec_steps
    {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    (externalRepairSpec σ).steps = undoScriptOfPerm σ :=
  RepairSpec.ofPermEndpoint_steps σ

@[simp] theorem externalRepairSpecDirect_steps
    {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    (externalRepairSpecDirect σ).steps = undoScriptOfPerm σ :=
  RepairSpec.ofPermDirect_steps σ

@[simp] theorem externalRepairSpecAt_steps
    {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    (externalRepairSpecAt σ cuts).steps = undoScriptOfPermAt σ cuts :=
  RepairSpec.ofPermAtEndpoint_steps σ cuts

@[simp] theorem externalRepairSpecAtDirect_steps
    {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    (externalRepairSpecAtDirect σ cuts).steps = undoScriptOfPermAt σ cuts :=
  RepairSpec.ofPermAtDirect_steps σ cuts

theorem externalRepairSpec_eq_direct
    {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    externalRepairSpec σ = externalRepairSpecDirect σ :=
  RepairSpec.ofPermEndpoint_eq_ofPermDirect σ

theorem externalRepairSpecAt_eq_direct
    {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    externalRepairSpecAt σ cuts = externalRepairSpecAtDirect σ cuts :=
  RepairSpec.ofPermAtEndpoint_eq_ofPermAtDirect σ cuts

theorem externalRepairSpec_eq_at_defaultSchedule
    {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    externalRepairSpec σ =
      externalRepairSpecAt σ (defaultSchedule (factorCycles σ)) :=
  RepairSpec.ofPermEndpoint_eq_ofPermAtEndpoint_defaultSchedule σ

theorem externalRepairSpecDirect_eq_atDirect_defaultSchedule
    {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    externalRepairSpecDirect σ =
      externalRepairSpecAtDirect σ (defaultSchedule (factorCycles σ)) :=
  RepairSpec.ofPermDirect_eq_ofPermAtDirect_defaultSchedule σ

/-- Existential external-style witness extracted from the neutral endpoint
repair package. -/
theorem externalRepairWitness {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) :
    ∃ steps : List (Body α × Body α),
      runScript steps * liftPerm σ = 1 ∧
      (steps.map stepPair).Nodup ∧
      (∀ step ∈ steps, UsesHelper step) ∧
      ∀ step ∈ steps, step.1 ≠ step.2 :=
  RepairSpec.toExternalWitness (externalRepairSpec σ)

/-- Existential external-style witness extracted from the neutral direct
repair package. -/
theorem externalRepairWitnessDirect {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) :
    ∃ steps : List (Body α × Body α),
      runScript steps * liftPerm σ = 1 ∧
      (steps.map stepPair).Nodup ∧
      (∀ step ∈ steps, UsesHelper step) ∧
      ∀ step ∈ steps, step.1 ≠ step.2 :=
  RepairSpec.toExternalWitness (externalRepairSpecDirect σ)

/-- Existential external-style witness extracted from the neutral parameterized
endpoint repair package. -/
theorem externalRepairWitnessAt {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    ∃ steps : List (Body α × Body α),
      runScript steps * liftPerm σ = 1 ∧
      (steps.map stepPair).Nodup ∧
      (∀ step ∈ steps, UsesHelper step) ∧
      ∀ step ∈ steps, step.1 ≠ step.2 :=
  RepairSpec.toExternalWitness (externalRepairSpecAt σ cuts)

/-- Existential external-style witness extracted from the neutral parameterized
direct repair package. -/
theorem externalRepairWitnessAtDirect
    {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    ∃ steps : List (Body α × Body α),
      runScript steps * liftPerm σ = 1 ∧
      (steps.map stepPair).Nodup ∧
      (∀ step ∈ steps, UsesHelper step) ∧
      ∀ step ∈ steps, step.1 ≠ step.2 :=
  RepairSpec.toExternalWitness (externalRepairSpecAtDirect σ cuts)

end Futurama
end Project
