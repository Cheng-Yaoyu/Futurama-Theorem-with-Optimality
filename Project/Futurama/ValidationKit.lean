import Project.Futurama.CoreCycle
import Project.Futurama.CoreSchedule
import Project.Futurama.FiniteBridge
import Project.Futurama.ParameterizedFamily

open Equiv Equiv.Perm

namespace Project
namespace Futurama

/-!
# Futurama Validation Kit

Shared executable validation utilities for the constructive Futurama
theorem and the optimality material.

## Sections

* **Generic schedule and script predicates** — boolean validators
  (`usesHelperBool`, `stepsUseHelpers`, `stepsNontrivial`,
  `scheduleValidation`, `allCutSchedules`, `allSchedulesValidate`).
* **Direct state simulator** — a second executable semantics
  (`BodyState`, `swapOccupants`, `stepState`, `runState`) used for
  cross-semantics agreement and the `prefixSemanticsAgree` checks.
* **Cross-semantics validators** — bridge between `runScript` and
  `runState` (`stateOfPerm`, `prefixSemanticsAgree`,
  `finalStateRestores`, `scheduleCrossSemanticsValidate`,
  `allSchedulesCrossSemanticsValidate`).
* **Fin 4 witness corpus** — the 24-element `perm4Witnesses`
  enumeration of all `Perm (Fin 4)` cycle structures, used as the
  exhaustive small-case ground for the validation suite.
-/

--------------------------------------------------------------------------------
-- Generic schedule and script predicates
--------------------------------------------------------------------------------

section GenericUtilities

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Boolean predicate: does `step` involve at least one helper body
(`Body.x` or `Body.y`)? Mirrors the proposition `UsesHelper step`
in decidable-`Bool` form so it can be evaluated by `decide` /
`native_decide`. -/
def usesHelperBool (step : Body α × Body α) : Bool :=
  match step with
  | (Body.x, _) => true
  | (Body.y, _) => true
  | (_, Body.x) => true
  | (_, Body.y) => true
  | _ => false

/-- Boolean predicate: does every step in `steps` use at least one
helper? Equivalent to `∀ step ∈ steps, UsesHelper step` after
`decide`-elaboration. -/
def stepsUseHelpers (steps : List (Body α × Body α)) : Bool :=
  steps.all usesHelperBool

/-- Boolean predicate: every step is a non-identity transposition
(`step.1 ≠ step.2`). Captures the "no trivial swap" requirement
of paper Theorem 1's machine-side conditions, in `Bool` form. -/
def stepsNontrivial (steps : List (Body α × Body α)) : Bool :=
  steps.all fun step => decide (step.1 ≠ step.2)

/-- All cut schedules indexed over the cycle list `cs`. The result is a
finite enumeration whose length equals `∏ c ∈ cs, c.tail.length`,
i.e. the size of the entire `CutSchedule cs` family. Used by the
`allSchedulesValidate` and `allSchedulesCrossSemanticsValidate`
exhaustive checks. -/
def allCutSchedules : {cs : List (Cycle α)} → List (CutSchedule cs)
  | [] => [.nil]
  | c :: cs =>
      List.flatMap
        (fun cut =>
          (allCutSchedules (cs := cs)).map fun rest =>
            CutSchedule.cons cut rest)
        (List.finRange c.tail.length)

/-- Boolean validator for a single cut schedule. Returns `true` iff
the resulting parameterised script:
1. correctly inverts `cycleProduct cs` (`runScript ... = 1`);
2. produces the same permutation as the default-route `undoScript cs`
   (cut-independence cross-check);
3. has `Nodup` step list;
4. has `Nodup` unordered-pair projection;
5. uses helpers in every step;
6. has every step non-trivial.

Bundles the six conditions of paper Theorem 1's strong endpoint
into a single `Bool`-valued check used to enumerate the cut family. -/
def scheduleValidation : {cs : List (Cycle α)} → CutSchedule cs → Bool
  | cs, cuts =>
      decide (runScript (undoScriptAt cuts) * cycleProduct cs = 1) &&
      decide (runScript (undoScriptAt cuts) = runScript (undoScript cs)) &&
      decide (undoScriptAt cuts).Nodup &&
      decide ((undoScriptAt cuts).map stepPair).Nodup &&
      stepsUseHelpers (undoScriptAt cuts) &&
      stepsNontrivial (undoScriptAt cuts)

/-- Run `scheduleValidation` over every cut schedule for `cs`. Returns
`true` iff every member of the parameterised cut family satisfies
the six-condition bundle. The cycle-list cut-family witness:
exhaustive correctness across the cut family on a fixed `cs`. -/
def allSchedulesValidate (cs : List (Cycle α)) : Bool :=
  (allCutSchedules (cs := cs)).all fun cuts => scheduleValidation cuts

end GenericUtilities

--------------------------------------------------------------------------------
-- Direct state simulator
--------------------------------------------------------------------------------

section DirectState

variable {α : Type*} [DecidableEq α]

/-- Direct-state semantics. A `BodyState α` is a pure function
`Body α → Body α` representing "where each label currently sits"
during a swap-by-swap simulation. Used as a parallel evaluator to
the Mathlib-`Perm`-based `runScript`; the two semantics agree at
every prefix (proved via `prefixSemanticsAgree`). -/
abbrev BodyState (α : Type*) := Body α → Body α

/-- The state-update under a single swap `(u, v)`: the occupant
currently equal to `u` becomes `v`, the occupant currently equal
to `v` becomes `u`, all other occupants are fixed. -/
def swapOccupants (u v current : Body α) : Body α :=
  if current = u then v else if current = v then u else current

/-- Apply one step of the direct-state semantics to a `BodyState`. -/
def stepState (st : BodyState α) (step : Body α × Body α) : BodyState α :=
  fun z => swapOccupants step.1 step.2 (st z)

/-- Run a list of swaps left-to-right under the direct-state semantics
(`foldl`-style). The cross-semantics theorem
`runState steps (stateOfPerm π) = stateOfPerm (runScript steps * π)`
links this back to `runScript` from `CoreCycle.lean`. -/
def runState (steps : List (Body α × Body α)) (st : BodyState α) : BodyState α :=
  steps.foldl stepState st

end DirectState

--------------------------------------------------------------------------------
-- Cross-semantics validators
--------------------------------------------------------------------------------

section CrossSemantics

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `BodyState` view of a permutation: `π` evaluated as a
function `Body α → Body α`. Bridges `Equiv.Perm (Body α)` into the
direct-state simulator. -/
def stateOfPerm (π : Perm (Body α)) : BodyState α :=
  fun z => π z

/-- The identity `BodyState`: every body holds its own label. -/
def identityState : BodyState α :=
  fun z => z

/-- Boolean: at every prefix length `n ∈ {0, 1, ..., steps.length}`,
the direct-state simulation `runState (steps.take n) (stateOfPerm π)`
agrees with the `Perm`-based answer
`stateOfPerm (runScript (steps.take n) * π)`. The cross-semantics
agreement test, evaluated by `decide` / `native_decide`. -/
def prefixSemanticsAgree
    (steps : List (Body α × Body α)) (π : Perm (Body α)) : Bool :=
  (List.range (steps.length + 1)).all fun n =>
    decide
      (runState (steps.take n) (stateOfPerm π) =
        stateOfPerm (runScript (steps.take n) * π))

/-- Boolean: after running all of `steps` under the direct-state
semantics starting from `stateOfPerm π`, every body holds its own
label (i.e. `runState steps (stateOfPerm π) = identityState`). -/
def finalStateRestores
    (steps : List (Body α × Body α)) (π : Perm (Body α)) : Bool :=
  decide (runState steps (stateOfPerm π) = identityState)

/-- Cross-semantics bundle: for a single cut schedule, both the
prefix-agreement and final-restore checks pass on the resulting
parameterised script. -/
def scheduleCrossSemanticsValidate : {cs : List (Cycle α)} → CutSchedule cs → Bool
  | cs, cuts =>
      let steps := undoScriptAt cuts
      let π := cycleProduct cs
      prefixSemanticsAgree steps π &&
        finalStateRestores steps π

/-- Run `scheduleCrossSemanticsValidate` over every cut schedule for
`cs`. The exhaustive cross-semantics witness on a fixed `cs`. -/
def allSchedulesCrossSemanticsValidate (cs : List (Cycle α)) : Bool :=
  (allCutSchedules (cs := cs)).all fun cuts =>
    scheduleCrossSemanticsValidate cuts

end CrossSemantics

--------------------------------------------------------------------------------
-- Fin 4 witness corpus
--------------------------------------------------------------------------------

section Fin4WitnessCorpus

/-- Notation alias for `Fin 4`, the universe of the witness corpus. -/
abbrev Cast4 := Fin 4

-- 6 transpositions on Fin 4 (cycle structure 2+1+1)

/-- Transposition `(0 1)` on `Fin 4`. -/
def c01 : Cycle Cast4 := ⟨0, 1, [], by decide⟩
/-- Transposition `(0 2)` on `Fin 4`. -/
def c02 : Cycle Cast4 := ⟨0, 2, [], by decide⟩
/-- Transposition `(0 3)` on `Fin 4`. -/
def c03 : Cycle Cast4 := ⟨0, 3, [], by decide⟩
/-- Transposition `(1 2)` on `Fin 4`. -/
def c12 : Cycle Cast4 := ⟨1, 2, [], by decide⟩
/-- Transposition `(1 3)` on `Fin 4`. -/
def c13 : Cycle Cast4 := ⟨1, 3, [], by decide⟩
/-- Transposition `(2 3)` on `Fin 4`. -/
def c23 : Cycle Cast4 := ⟨2, 3, [], by decide⟩

-- 8 three-cycles on Fin 4 (cycle structure 3+1; two orientations of each
-- triple, encoded as the (first, second, [third]) representation since
-- `cyclePerm` reads the inverse cycle, see `CoreCycle.lean`).

/-- 3-cycle on `{0, 1, 2}`, orientation `(0, 1, [2])`. -/
def c012a : Cycle Cast4 := ⟨0, 1, [2], by decide⟩
/-- 3-cycle on `{0, 1, 2}`, orientation `(0, 2, [1])`. -/
def c012b : Cycle Cast4 := ⟨0, 2, [1], by decide⟩
/-- 3-cycle on `{0, 1, 3}`, orientation `(0, 1, [3])`. -/
def c013a : Cycle Cast4 := ⟨0, 1, [3], by decide⟩
/-- 3-cycle on `{0, 1, 3}`, orientation `(0, 3, [1])`. -/
def c013b : Cycle Cast4 := ⟨0, 3, [1], by decide⟩
/-- 3-cycle on `{0, 2, 3}`, orientation `(0, 2, [3])`. -/
def c023a : Cycle Cast4 := ⟨0, 2, [3], by decide⟩
/-- 3-cycle on `{0, 2, 3}`, orientation `(0, 3, [2])`. -/
def c023b : Cycle Cast4 := ⟨0, 3, [2], by decide⟩
/-- 3-cycle on `{1, 2, 3}`, orientation `(1, 2, [3])`. -/
def c123a : Cycle Cast4 := ⟨1, 2, [3], by decide⟩
/-- 3-cycle on `{1, 2, 3}`, orientation `(1, 3, [2])`. -/
def c123b : Cycle Cast4 := ⟨1, 3, [2], by decide⟩

-- 6 four-cycles on Fin 4 (cycle structure 4); the six choices encode the
-- six distinct `(first, second, third, fourth)` orientations of a
-- 4-cycle (modulo cyclic shift but not modulo direction).

/-- 4-cycle on `Fin 4`, orientation `(0, 1, [2, 3])`. -/
def c0123a : Cycle Cast4 := ⟨0, 1, [2, 3], by decide⟩
/-- 4-cycle on `Fin 4`, orientation `(0, 1, [3, 2])`. -/
def c0123b : Cycle Cast4 := ⟨0, 1, [3, 2], by decide⟩
/-- 4-cycle on `Fin 4`, orientation `(0, 2, [1, 3])`. -/
def c0213a : Cycle Cast4 := ⟨0, 2, [1, 3], by decide⟩
/-- 4-cycle on `Fin 4`, orientation `(0, 2, [3, 1])`. -/
def c0231a : Cycle Cast4 := ⟨0, 2, [3, 1], by decide⟩
/-- 4-cycle on `Fin 4`, orientation `(0, 3, [1, 2])`. -/
def c0312a : Cycle Cast4 := ⟨0, 3, [1, 2], by decide⟩
/-- 4-cycle on `Fin 4`, orientation `(0, 3, [2, 1])`. -/
def c0321a : Cycle Cast4 := ⟨0, 3, [2, 1], by decide⟩

/-- The 24-element witness corpus: every `Perm (Fin 4)` is realised
(modulo `cycleProduct`) by exactly one entry of this list. The 24
entries cover:
* the empty list (identity, 1 entry),
* 6 transpositions,
* 3 disjoint 2-cycle pairs (`[c01, c23]`, `[c02, c13]`, `[c03, c12]`),
* 8 three-cycles,
* 6 four-cycles.

Used by the exhaustive `Perm (Fin 4)` checks. The cardinality `= 24`
is proved by `native_decide` immediately below. -/
def perm4Witnesses : List (List (Cycle Cast4)) :=
  [ [],
    [c01], [c02], [c03], [c12], [c13], [c23],
    [c01, c23], [c02, c13], [c03, c12],
    [c012a], [c012b], [c013a], [c013b], [c023a], [c023b], [c123a], [c123b],
    [c0123a], [c0123b], [c0213a], [c0231a], [c0312a], [c0321a] ]

/-- The image of `perm4Witnesses` under `cycleProduct`: 24 distinct
permutations of `Body Cast4` that together cover (via `liftPerm`)
every `Perm (Fin 4)`. -/
def perm4Images : List (Perm (Body Cast4)) :=
  perm4Witnesses.map cycleProduct

example : perm4Witnesses.length = 24 := by
  native_decide

example : (perm4Witnesses.map fun cs =>
    (allCutSchedules (cs := cs)).length).sum = 44 := by
  native_decide

example : perm4Images.Nodup := by
  native_decide

example : perm4Witnesses.all allSchedulesValidate = true := by
  native_decide

example : perm4Witnesses.all allSchedulesCrossSemanticsValidate = true := by
  native_decide

/-- Coverage theorem: every `σ : Perm (Fin 4)` is realised by some
witness in `perm4Witnesses` via `cycleProduct cs = liftPerm σ`. -/
theorem exists_perm4_witness :
    ∀ σ : Perm Cast4, ∃ cs ∈ perm4Witnesses, cycleProduct cs = liftPerm σ := by
  native_decide

/-- Cross-semantics-strengthened coverage: every `σ : Perm (Fin 4)`
is realised by a witness which additionally passes the cross-
semantics validator on its entire cut family. -/
theorem exists_perm4_cross_checked :
    ∀ σ : Perm Cast4,
      ∃ cs ∈ perm4Witnesses,
        cycleProduct cs = liftPerm σ ∧
          allSchedulesCrossSemanticsValidate cs = true := by
  native_decide

end Fin4WitnessCorpus

end Futurama
end Project
