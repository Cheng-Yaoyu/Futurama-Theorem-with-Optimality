import Project.Futurama

open Equiv Equiv.Perm

namespace Project
namespace Futurama
namespace Validation4

/-!
# Validation V4 — executable strengthening harness

This file implements the strongest parts of the V4 layer:

* direct external-spec packaging from lower-level lemmas;
* explicit source-traceability for the parameterized single-cycle family;
* an alternate direct state simulator on finite casts;
* a `Fin 4` witness corpus covering the 24 cycle-shape representatives;
* stronger near-miss negative controls.
-/

--------------------------------------------------------------------------------
-- Layer A: Direct external-spec derivation from lower-level lemmas
--------------------------------------------------------------------------------

/-- Validation4 compatibility alias for the shared external repair
specification under the direct lower-level proof path. -/
abbrev WikipediaFuturamaDirect {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) : Type _ :=
  ExternalRepairSpecDirect σ

/-- Direct rebuild of the Wikipedia-style statement from the lower-level
constructive lemmas. The proof deliberately does not destructure
`futuramaTheoremOfPermStrongFullSpec`. -/
noncomputable def wikipedia_futurama_direct {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) : WikipediaFuturamaDirect σ :=
  Project.Futurama.externalRepairSpecDirect σ

/-- Neutral alias for the direct lower-level external repair specification. -/
noncomputable abbrev externalRepairSpecDirect {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) : ExternalRepairSpecDirect σ :=
  Project.Futurama.externalRepairSpecDirect σ

/-- Parameterized-family version of the same direct package. -/
abbrev WikipediaFuturamaDirectAt {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) : Type _ :=
  ExternalRepairSpecAtDirect σ cuts

noncomputable def wikipedia_futurama_direct_at
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    WikipediaFuturamaDirectAt σ cuts :=
  Project.Futurama.externalRepairSpecAtDirect σ cuts

/-- Neutral alias for the parameterized direct lower-level external repair
specification. -/
noncomputable abbrev externalRepairSpecAtDirect
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    ExternalRepairSpecAtDirect σ cuts :=
  Project.Futurama.externalRepairSpecAtDirect σ cuts

--------------------------------------------------------------------------------
-- Layer B: Blackboard / Wikipedia source-traceability
--------------------------------------------------------------------------------

section SourceTraceability

variable {α : Type*}

/-- The `(x 1) ... (x i)` segment in the translated Wikipedia / blackboard
single-cycle block. -/
def wikiPrefixBlock (c : Cycle α) (cut : Fin c.tail.length) :
    List (Body α × Body α) :=
  helperScript Body.x (prefixMembers c cut)

/-- The `(y (i+1)) ... (y k)` segment in the translated Wikipedia / blackboard
single-cycle block. -/
def wikiSuffixBlock (c : Cycle α) (cut : Fin c.tail.length) :
    List (Body α × Body α) :=
  helperScript Body.y (suffixMembers c cut)

/-- The trailing `(x (i+1))(y 1)` cleanup from the blackboard family. -/
def wikiCleanupBlock (c : Cycle α) (cut : Fin c.tail.length) :
    List (Body α × Body α) :=
  finishScript c.first (pivotOf c cut)

/-- Validation-only spelling of the Wikipedia / blackboard single-cycle family,
expressed in the project's left-to-right executable list convention. -/
def wikiSingleCycleBlock (c : Cycle α) (cut : Fin c.tail.length) :
    List (Body α × Body α) :=
  wikiPrefixBlock c cut ++ wikiSuffixBlock c cut ++ wikiCleanupBlock c cut

/-- Neutral long-term alias for the source-traceability prefix block. -/
abbrev blackboardPrefixBlock (c : Cycle α) (cut : Fin c.tail.length) :
    List (Body α × Body α) :=
  wikiPrefixBlock c cut

/-- Neutral long-term alias for the source-traceability suffix block. -/
abbrev blackboardSuffixBlock (c : Cycle α) (cut : Fin c.tail.length) :
    List (Body α × Body α) :=
  wikiSuffixBlock c cut

/-- Neutral long-term alias for the source-traceability cleanup block. -/
abbrev blackboardCleanupBlock (c : Cycle α) (cut : Fin c.tail.length) :
    List (Body α × Body α) :=
  wikiCleanupBlock c cut

/-- Neutral long-term alias for the source-traceability single-cycle block. -/
abbrev blackboardSingleCycleBlock (c : Cycle α) (cut : Fin c.tail.length) :
    List (Body α × Body α) :=
  wikiSingleCycleBlock c cut

@[simp] theorem wikiPrefixBlock_eq (c : Cycle α) (cut : Fin c.tail.length) :
    wikiPrefixBlock c cut = helperScript Body.x (prefixMembers c cut) := rfl

@[simp] theorem wikiSuffixBlock_eq (c : Cycle α) (cut : Fin c.tail.length) :
    wikiSuffixBlock c cut = helperScript Body.y (suffixMembers c cut) := rfl

@[simp] theorem wikiCleanupBlock_eq (c : Cycle α) (cut : Fin c.tail.length) :
    wikiCleanupBlock c cut = finishScript c.first (pivotOf c cut) := rfl

@[simp] theorem blackboardPrefixBlock_eq (c : Cycle α) (cut : Fin c.tail.length) :
    blackboardPrefixBlock c cut = helperScript Body.x (prefixMembers c cut) := rfl

@[simp] theorem blackboardSuffixBlock_eq (c : Cycle α) (cut : Fin c.tail.length) :
    blackboardSuffixBlock c cut = helperScript Body.y (suffixMembers c cut) := rfl

@[simp] theorem blackboardCleanupBlock_eq (c : Cycle α) (cut : Fin c.tail.length) :
    blackboardCleanupBlock c cut = finishScript c.first (pivotOf c cut) := rfl

/-- Source-traceability endpoint: the parameterized implementation is exactly
the translated Wikipedia / blackboard block. -/
@[simp] theorem wikiSingleCycleBlock_eq_repairScriptAt
    (c : Cycle α) (cut : Fin c.tail.length) :
    wikiSingleCycleBlock c cut = repairScriptAt c cut := rfl

/-- Neutral long-term alias of the same `rfl`-level source-traceability fact. -/
@[simp] theorem blackboardSingleCycleBlock_eq_repairScriptAt
    (c : Cycle α) (cut : Fin c.tail.length) :
    blackboardSingleCycleBlock c cut = repairScriptAt c cut := rfl

/-- Explicit blackboard-shape expansion using the cycle split at the chosen
cut. This is the theorem-level statement that the parameterized family really
has the advertised `(x ...)(y ...)(x pivot)(y first)` shape. -/
theorem wikiSingleCycleBlock_shape
    (c : Cycle α) (cut : Fin c.tail.length) :
    wikiSingleCycleBlock c cut =
      helperScript Body.x (c.members.take (cut.1 + 1)) ++
        helperScript Body.y (c.members.drop (cut.1 + 1)) ++
        [(Body.x, Body.orig (c.tail.get cut)), (Body.y, Body.orig c.first)] := by
  simp [wikiSingleCycleBlock, wikiPrefixBlock, wikiSuffixBlock, wikiCleanupBlock,
    pivotOf, finishScript]

theorem blackboardSingleCycleBlock_shape
    (c : Cycle α) (cut : Fin c.tail.length) :
    blackboardSingleCycleBlock c cut =
      helperScript Body.x (c.members.take (cut.1 + 1)) ++
        helperScript Body.y (c.members.drop (cut.1 + 1)) ++
        [(Body.x, Body.orig (c.tail.get cut)), (Body.y, Body.orig c.first)] := by
  simpa [blackboardSingleCycleBlock] using wikiSingleCycleBlock_shape c cut

@[simp] theorem wikiSingleCycleBlock_length
    (c : Cycle α) (cut : Fin c.tail.length) :
    (wikiSingleCycleBlock c cut).length = c.members.length + 2 := by
  simp [wikiSingleCycleBlock, wikiPrefixBlock, wikiSuffixBlock, wikiCleanupBlock,
    helperScript_length, finishScript_length, prefixMembers, suffixMembers,
    Cycle.members, Cycle.tail]
  omega

@[simp] theorem blackboardSingleCycleBlock_length
    (c : Cycle α) (cut : Fin c.tail.length) :
    (blackboardSingleCycleBlock c cut).length = c.members.length + 2 := by
  simpa [blackboardSingleCycleBlock] using wikiSingleCycleBlock_length c cut

end SourceTraceability

section SourceTraceabilityCorrectness

variable {α : Type*} [DecidableEq α]

theorem wikiSingleCycleBlock_correct
    (c : Cycle α) (cut : Fin c.tail.length) :
    runScript (wikiSingleCycleBlock c cut) * cyclePerm c = helperSwap := by
  change runScript (repairScriptAt c cut) * cyclePerm c = helperSwap
  simpa [repairPermAt] using repairPermAt_mul_cyclePerm c cut

theorem blackboardSingleCycleBlock_correct
    (c : Cycle α) (cut : Fin c.tail.length) :
    runScript (blackboardSingleCycleBlock c cut) * cyclePerm c = helperSwap := by
  simpa [blackboardSingleCycleBlock] using wikiSingleCycleBlock_correct c cut

theorem runScript_wikiSingleCycleBlock_eq_repairPermAt
    (c : Cycle α) (cut : Fin c.tail.length) :
    runScript (wikiSingleCycleBlock c cut) = repairPermAt c cut := by
  change runScript (repairScriptAt c cut) = repairPermAt c cut
  rfl

theorem runScript_blackboardSingleCycleBlock_eq_repairPermAt
    (c : Cycle α) (cut : Fin c.tail.length) :
    runScript (blackboardSingleCycleBlock c cut) = repairPermAt c cut := by
  simpa [blackboardSingleCycleBlock] using
    runScript_wikiSingleCycleBlock_eq_repairPermAt c cut

end SourceTraceabilityCorrectness

--------------------------------------------------------------------------------
-- Layer C / D support: generic schedule validation utilities
--------------------------------------------------------------------------------

-- Layer C and D reuse the shared ValidationKit enumeration helpers.

--------------------------------------------------------------------------------
-- Layer C: Alternate direct state simulator
--------------------------------------------------------------------------------

section DirectSimulatorExamples

abbrev SimCast := Fin 4

def simC01 : Cycle SimCast := ⟨0, 1, [], by decide⟩
def simC23 : Cycle SimCast := ⟨2, 3, [], by decide⟩
def simC012 : Cycle SimCast := ⟨0, 1, [2], by decide⟩
def simC0123 : Cycle SimCast := ⟨0, 1, [2, 3], by decide⟩

def simCut1 : Fin simC0123.tail.length := ⟨1, by decide⟩

example :
    runState (undoScript [simC012]) (cycleProduct [simC012]) =
      (fun z : Body SimCast => z) := by
  native_decide

example :
    runState (undoScript [simC0123]) (cycleProduct [simC0123]) =
      (fun z : Body SimCast => z) := by
  native_decide

example :
    runState (undoScript [simC01, simC23]) (cycleProduct [simC01, simC23]) =
      (fun z : Body SimCast => z) := by
  native_decide

example :
    runState (undoScriptAt (CutSchedule.cons simCut1 CutSchedule.nil))
        (cycleProduct [simC0123]) =
      (fun z : Body SimCast => z) := by
  native_decide

end DirectSimulatorExamples

--------------------------------------------------------------------------------
-- Layer D: Fin 4 witness corpus
--------------------------------------------------------------------------------

section Fin4WitnessCorpus

example : perm4Witnesses.length = 24 := by native_decide

example : Fintype.card (Perm Cast4) = 24 := by decide

example : perm4Witnesses.all allSchedulesValidate = true := by
  native_decide

example : (perm4Witnesses.map cycleProduct).Nodup := by
  native_decide

theorem perm4Images_nodup : perm4Images.Nodup := by
  native_decide

theorem exists_perm4_witness :
    ∀ σ : Perm Cast4, ∃ cs ∈ perm4Witnesses, cycleProduct cs = liftPerm σ := by
  native_decide

example :
    perm4Witnesses.all (fun cs =>
      decide (cycleProduct cs Body.x = (Body.x : Body Cast4) ∧
        cycleProduct cs Body.y = (Body.y : Body Cast4))) = true := by
  native_decide

end Fin4WitnessCorpus

--------------------------------------------------------------------------------
-- Layer E: Stronger near-miss negative controls
--------------------------------------------------------------------------------

section StrongerNegativeControls

abbrev NCast := Fin 4

def ncC012 : Cycle NCast := ⟨0, 1, [2], by decide⟩

def oddCleanupMissing : List (Body NCast × Body NCast) :=
  repairScripts [ncC012]

example : runScript oddCleanupMissing * cycleProduct [ncC012] ≠ 1 := by
  decide

def adjacentSwapNearMiss : List (Body NCast × Body NCast) :=
  [ (Body.x, Body.orig 0),
    (Body.y, Body.orig 1),
    (Body.x, Body.orig 2),
    (Body.x, Body.orig 1),
    (Body.y, Body.orig 0),
    (Body.x, Body.y) ]

example : runScript adjacentSwapNearMiss * cycleProduct [ncC012] ≠ 1 := by
  decide

def helperBrokenNearMiss : List (Body NCast × Body NCast) :=
  [ (Body.x, Body.orig 0),
    (Body.orig 3, Body.orig 1),
    (Body.y, Body.orig 2),
    (Body.x, Body.orig 1),
    (Body.y, Body.orig 0),
    (Body.x, Body.y) ]

example : ¬ (∀ step ∈ helperBrokenNearMiss, UsesHelper step) := by
  intro h
  have hbad := h (Body.orig 3, Body.orig 1) (by simp [helperBrokenNearMiss])
  rcases hbad with hbad | hbad | hbad | hbad <;> cases hbad

def dupPairNearMiss : List (Body NCast × Body NCast) :=
  undoScript [ncC012] ++ [(Body.orig 0, Body.x)]

example : ¬ (dupPairNearMiss.map stepPair).Nodup := by
  native_decide

def selfSwapNearMiss : List (Body NCast × Body NCast) :=
  undoScript [ncC012] ++ [(Body.x, Body.x)]

example : ¬ (∀ step ∈ selfSwapNearMiss, step.1 ≠ step.2) := by
  native_decide

end StrongerNegativeControls

--------------------------------------------------------------------------------
-- Layer F / audit snippets
--------------------------------------------------------------------------------

#print axioms Project.Futurama.Validation4.wikipedia_futurama_direct
#print axioms Project.Futurama.Validation4.wikipedia_futurama_direct_at

end Validation4
end Futurama
end Project
