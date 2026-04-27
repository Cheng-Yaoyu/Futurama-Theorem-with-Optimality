import Project.Futurama

open Equiv Equiv.Perm

namespace Project
namespace Futurama
namespace Validation3

/-!
# Validation V3 — executable harness

This file implements the V3 validation layers B through H:

* Layer B — formal `WikipediaFuturama` structure and its inhabitation
* Layer C — definition-level defensive lemmas
* Layer D — orientation cross-check on `Fin 4`
* Layer E — generic parameterized schedule enumeration (wider than V2)
* Layer F — concrete-witness enumeration over all permutations of `Fin 3`
* Layer G — negative controls (adversarial witnesses)
* Layer H — deep `#print axioms` audit
-/

--------------------------------------------------------------------------------
-- Layer B: Formal Wikipedia-style specification
--------------------------------------------------------------------------------

/-- Validation3 compatibility alias for the shared external repair
specification. -/
abbrev WikipediaFuturama {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) : Type _ :=
  ExternalRepairSpec σ

/-- Wikipedia-style derivation: the constructive theorem inhabits the
`WikipediaFuturama` structure for every finite permutation. -/
noncomputable def wikipedia_futurama {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) : WikipediaFuturama σ :=
  Project.Futurama.externalRepairSpec σ

/-- Neutral alias for the endpoint-derived external repair specification. -/
noncomputable abbrev externalRepairSpec {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) : ExternalRepairSpec σ :=
  Project.Futurama.externalRepairSpec σ

--------------------------------------------------------------------------------
-- Layer C: Definition-level defensive lemmas
--------------------------------------------------------------------------------

section DefensiveLemmas
variable {β : Type*} [DecidableEq β]

-- `liftPerm` fixes both helpers, for every scramble.
example (σ : Perm β) : liftPerm σ (Body.x : Body β) = Body.x := liftPerm_apply_x σ
example (σ : Perm β) : liftPerm σ (Body.y : Body β) = Body.y := liftPerm_apply_y σ

-- `liftPerm` is the identity on the identity, and commutes with composition.
example : liftPerm (1 : Perm β) = (1 : Perm (Body β)) := liftPerm_one
example (σ τ : Perm β) :
    liftPerm (σ * τ) = liftPerm σ * liftPerm τ := liftPerm_mul σ τ

-- `runScript` is contravariant under list concatenation.
example (s t : List (Body β × Body β)) :
    runScript (s ++ t) = runScript t * runScript s := runScript_append s t

-- `helperSwap` is its own inverse.
example : (helperSwap * helperSwap : Perm (Body β)) = 1 := helperSwap_mul_self

-- `cyclePermAux` agrees with the reverse `formPerm` — this is the semantic
-- bridge that justifies the project's non-standard cycle orientation.
example (first : β) (tail : List β) :
    cyclePermAux first tail =
      (List.map Body.orig (first :: tail)).reverse.formPerm :=
  cyclePermAux_eq_formPerm_reverse first tail

end DefensiveLemmas

section DefensiveDecidable

-- `UsesHelper` discriminates helper-involving pairs from original-only pairs.
example :
    UsesHelper ((Body.x, Body.orig (0 : Fin 3)) : Body (Fin 3) × Body (Fin 3)) := by
  left; rfl

example :
    UsesHelper ((Body.orig (0 : Fin 3), Body.y) : Body (Fin 3) × Body (Fin 3)) := by
  right; right; right; rfl

example : ¬ UsesHelper
    ((Body.orig (0 : Fin 3), Body.orig 1) : Body (Fin 3) × Body (Fin 3)) := by
  intro h
  rcases h with h | h | h | h <;> cases h

-- `stepPair` forgets orientation.
example : stepPair ((Body.x, Body.orig (0 : Fin 3)) : Body (Fin 3) × Body (Fin 3))
        = stepPair ((Body.orig 0, Body.x) : Body (Fin 3) × Body (Fin 3)) := by
  decide

end DefensiveDecidable

--------------------------------------------------------------------------------
-- Layer D: Orientation cross-check
--------------------------------------------------------------------------------

section OrientationCheck

/-- Test 3-cycle `⟨0, 1, [2]⟩` on `Fin 4`. -/
def c3 : Cycle (Fin 4) where
  first := 0
  second := 1
  rest := [2]
  nodup := by decide

/-- Test 4-cycle `⟨0, 1, [2, 3]⟩` on `Fin 4`. -/
def c4 : Cycle (Fin 4) where
  first := 0
  second := 1
  rest := [2, 3]
  nodup := by decide

-- Three-cycle orientation:
-- cycle data `⟨a₁, a₂, a₃⟩ = ⟨0, 1, 2⟩` induces
--   a₁ ↦ a₃  (0 ↦ 2),
--   a₂ ↦ a₁  (1 ↦ 0),
--   a₃ ↦ a₂  (2 ↦ 1).
example : cyclePerm c3 (Body.orig 0) = (Body.orig 2 : Body (Fin 4)) := by decide
example : cyclePerm c3 (Body.orig 1) = (Body.orig 0 : Body (Fin 4)) := by decide
example : cyclePerm c3 (Body.orig 2) = (Body.orig 1 : Body (Fin 4)) := by decide
example : cyclePerm c3 (Body.orig 3) = (Body.orig 3 : Body (Fin 4)) := by decide
example : cyclePerm c3 Body.x = (Body.x : Body (Fin 4)) := by decide
example : cyclePerm c3 Body.y = (Body.y : Body (Fin 4)) := by decide

-- Four-cycle orientation:
-- cycle data `⟨0, 1, 2, 3⟩` induces
--   0 ↦ 3, 1 ↦ 0, 2 ↦ 1, 3 ↦ 2.
example : cyclePerm c4 (Body.orig 0) = (Body.orig 3 : Body (Fin 4)) := by decide
example : cyclePerm c4 (Body.orig 1) = (Body.orig 0 : Body (Fin 4)) := by decide
example : cyclePerm c4 (Body.orig 2) = (Body.orig 1 : Body (Fin 4)) := by decide
example : cyclePerm c4 (Body.orig 3) = (Body.orig 2 : Body (Fin 4)) := by decide

-- Self-consistency: cyclePerm ∘ cyclePerm ∘ cyclePerm is the identity on the 3-cycle.
example : (cyclePerm c3 * cyclePerm c3 * cyclePerm c3 : Perm (Body (Fin 4))) = 1 := by
  decide

-- cyclePerm is its own inverse on the 2-cycle data (transpose).
def c2 : Cycle (Fin 4) where
  first := 0
  second := 1
  rest := []
  nodup := by decide

example : (cyclePerm c2 * cyclePerm c2 : Perm (Body (Fin 4))) = 1 := by decide
example : cyclePerm c2 = liftPerm (Equiv.swap (0 : Fin 4) 1) := by decide

end OrientationCheck

--------------------------------------------------------------------------------
-- Layer E: Generic parameterized schedule enumeration
--------------------------------------------------------------------------------

-- Layer E reuses the shared validation-kit enumeration helpers.

--------------------------------------------------------------------------------
-- Layer E — concrete enumeration on an 8-element cast (expands V2's coverage)
--------------------------------------------------------------------------------

section ConcreteEnumeration

abbrev Cast := Fin 8

def c01   : Cycle Cast := ⟨0, 1, [], by decide⟩
def c23   : Cycle Cast := ⟨2, 3, [], by decide⟩
def c45   : Cycle Cast := ⟨4, 5, [], by decide⟩
def c67   : Cycle Cast := ⟨6, 7, [], by decide⟩
def c012  : Cycle Cast := ⟨0, 1, [2], by decide⟩
def c234  : Cycle Cast := ⟨2, 3, [4], by decide⟩
def c456  : Cycle Cast := ⟨4, 5, [6], by decide⟩
def c0123 : Cycle Cast := ⟨0, 1, [2, 3], by decide⟩
def c3456 : Cycle Cast := ⟨3, 4, [5, 6], by decide⟩
def c56   : Cycle Cast := ⟨5, 6, [], by decide⟩
def c01234 : Cycle Cast := ⟨0, 1, [2, 3, 4], by decide⟩
def c012345 : Cycle Cast := ⟨0, 1, [2, 3, 4, 5], by decide⟩
def c0123456 : Cycle Cast := ⟨0, 1, [2, 3, 4, 5, 6], by decide⟩

-- Empty list (identity) — edge case V2 did not cover
example : allSchedulesValidate ([] : List (Cycle Cast)) = true := by native_decide

-- V2's baseline set — replayed under the generic predicate
example : allSchedulesValidate ([c01] : List (Cycle Cast)) = true := by native_decide
example : allSchedulesValidate ([c012] : List (Cycle Cast)) = true := by native_decide
example : allSchedulesValidate ([c0123] : List (Cycle Cast)) = true := by native_decide
example : allSchedulesValidate ([c01234] : List (Cycle Cast)) = true := by native_decide
example : allSchedulesValidate ([c01, c23] : List (Cycle Cast)) = true := by native_decide
example : allSchedulesValidate ([c01, c234] : List (Cycle Cast)) = true := by native_decide
example : allSchedulesValidate ([c012, c3456] : List (Cycle Cast)) = true := by native_decide
example : allSchedulesValidate ([c01, c23, c456] : List (Cycle Cast)) = true := by native_decide

-- V3 new additions: longer cycles, more cycles, and mixed shapes
example : allSchedulesValidate ([c012345] : List (Cycle Cast)) = true := by native_decide
example : allSchedulesValidate ([c0123456] : List (Cycle Cast)) = true := by native_decide
example : allSchedulesValidate ([c01, c23, c45] : List (Cycle Cast)) = true := by native_decide
example : allSchedulesValidate ([c01, c23, c45, c67] : List (Cycle Cast)) = true := by
  native_decide
example : allSchedulesValidate ([c0123, c456] : List (Cycle Cast)) = true := by
  native_decide
example : allSchedulesValidate ([c01, c234, c56] : List (Cycle Cast)) = true := by
  native_decide

end ConcreteEnumeration

--------------------------------------------------------------------------------
-- Layer F: Permutation-level enumeration over all of `Perm (Fin 3)`
--------------------------------------------------------------------------------

section PermEnumeration

abbrev PCast := Fin 3

-- We work over `Fin 3` here. Every permutation is realized as a specific cycle
-- list and the Wikipedia-style spec is validated by `native_decide` at the
-- cycle-list layer, which never reuses `futuramaTheorem*`.

def p_id  : List (Cycle PCast) := []
def p_01  : List (Cycle PCast) := [⟨0, 1, [], by decide⟩]
def p_02  : List (Cycle PCast) := [⟨0, 2, [], by decide⟩]
def p_12  : List (Cycle PCast) := [⟨1, 2, [], by decide⟩]
-- Standard 3-cycle (0 1 2) (i.e. 0↦1, 1↦2, 2↦0): cycle data `⟨0, 2, [1]⟩`
def p_012 : List (Cycle PCast) := [⟨0, 2, [1], by decide⟩]
-- Standard 3-cycle (0 2 1) (i.e. 0↦2, 2↦1, 1↦0): cycle data `⟨0, 1, [2]⟩`
def p_021 : List (Cycle PCast) := [⟨0, 1, [2], by decide⟩]

-- Cycle-list / Mathlib-permutation correspondence for each entry.
example : cycleProduct p_id  = (1 : Perm (Body PCast)) := by decide
example : cycleProduct p_01  = liftPerm (Equiv.swap (0 : PCast) 1) := by decide
example : cycleProduct p_02  = liftPerm (Equiv.swap (0 : PCast) 2) := by decide
example : cycleProduct p_12  = liftPerm (Equiv.swap (1 : PCast) 2) := by decide
example : cycleProduct p_012
        = liftPerm ((Equiv.swap (0 : PCast) 1) * (Equiv.swap 1 2)) := by decide
example : cycleProduct p_021
        = liftPerm ((Equiv.swap (0 : PCast) 2) * (Equiv.swap 1 2)) := by decide

-- Spec validation for every entry.
example : allSchedulesValidate p_id  = true := by native_decide
example : allSchedulesValidate p_01  = true := by native_decide
example : allSchedulesValidate p_02  = true := by native_decide
example : allSchedulesValidate p_12  = true := by native_decide
example : allSchedulesValidate p_012 = true := by native_decide
example : allSchedulesValidate p_021 = true := by native_decide

-- Cardinality check: `Perm (Fin 3)` has exactly 6 elements, so the six
-- entries above exhaust the permutation space.
example : Fintype.card (Perm PCast) = 6 := by decide

end PermEnumeration

--------------------------------------------------------------------------------
-- Layer G: Negative controls (adversarial witnesses)
--------------------------------------------------------------------------------

section NegativeControls

abbrev NCast := Fin 3

/-- A cycle that any correct repair must undo. -/
def c_NC : Cycle NCast where
  first  := 0
  second := 1
  rest   := [2]
  nodup  := by decide

/-- A deliberately truncated script — too short to undo the 3-cycle. -/
def brokenScript : List (Body NCast × Body NCast) :=
  [(Body.x, Body.orig 0)]

/-- The truncated script does not restore the identity. -/
example : runScript brokenScript * cyclePerm c_NC ≠ 1 := by decide

/-- A script with the same unordered helper swap twice. -/
def dupPairScript : List (Body NCast × Body NCast) :=
  [(Body.x, Body.orig 0), (Body.orig 0, Body.x)]

/-- That script's `stepPair` projection is not `Nodup`. -/
example : ¬ (dupPairScript.map stepPair).Nodup := by decide

/-- A script with a forbidden original-original step. -/
def origOrigScript : List (Body NCast × Body NCast) :=
  [(Body.orig 0, Body.orig 1)]

/-- That script fails the helper-involvement clause. -/
example : ¬ (∀ step ∈ origOrigScript, UsesHelper step) := by
  intro h
  have h01 := h (Body.orig 0, Body.orig 1) (by
    simp [origOrigScript])
  rcases h01 with h | h | h | h <;> cases h

/-- A script with a self-swap — fails the nontriviality clause. -/
def selfSwapScript : List (Body NCast × Body NCast) :=
  [(Body.x, Body.x)]

example : ¬ (∀ step ∈ selfSwapScript, step.1 ≠ step.2) := by
  intro h
  have := h (Body.x, Body.x) (by simp [selfSwapScript])
  exact this rfl

end NegativeControls

--------------------------------------------------------------------------------
-- Layer H: Deep axiom audit
--------------------------------------------------------------------------------

-- Intermediate support lemmas
#print axioms Project.Futurama.repairPerm_mul_cyclePerm
#print axioms Project.Futurama.repairProduct_mul_cycleProduct
#print axioms Project.Futurama.residualPerm_eq_parity
#print axioms Project.Futurama.runScript_undoScript

-- Cycle-list endpoints
#print axioms Project.Futurama.futuramaTheorem
#print axioms Project.Futurama.futuramaTheoremStrong
#print axioms Project.Futurama.futuramaTheoremStrongFullSpec

-- Finite-bridge plumbing
#print axioms Project.Futurama.cycleProduct_factorCycles
#print axioms Project.Futurama.factorCycles_pairwise_disjoint
#print axioms Project.Futurama.cyclePerm_cycleFromPerm

-- Permutation endpoints
#print axioms Project.Futurama.futuramaTheoremOfPerm
#print axioms Project.Futurama.futuramaTheoremOfPermStrong
#print axioms Project.Futurama.futuramaTheoremOfPermStrongFullSpec

-- Parameterized-family path
#print axioms Project.Futurama.repairPermAt_mul_cyclePerm
#print axioms Project.Futurama.repairPermAt_eq_repairPerm
#print axioms Project.Futurama.runScript_undoScriptAt_mul_cycleProduct
#print axioms Project.Futurama.futuramaTheoremAt
#print axioms Project.Futurama.futuramaTheoremStrongAt
#print axioms Project.Futurama.futuramaTheoremStrongAtFullSpec
#print axioms Project.Futurama.futuramaTheoremOfPermStrongAt
#print axioms Project.Futurama.futuramaTheoremOfPermStrongAtFullSpec

-- V3 derived result
#print axioms Project.Futurama.Validation3.wikipedia_futurama

end Validation3
end Futurama
end Project
