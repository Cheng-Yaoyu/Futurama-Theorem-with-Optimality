import Project.Futurama.CoreCycle
import Project.Futurama.CoreSchedule
import Project.Futurama.FiniteBridge
import Project.Futurama.ParameterizedFamily
import Project.Futurama.Optimality.RepairSeq
import Project.Futurama.Optimality.UpperBound

/-!
# Optimality / Keeler — Keeler-gap remark

This file captures paper Section 1's "Keeler optimal only for `r ≤ 2`"
remark, formalised at theorem level for **all** `r`:

* `r = 1`: `keeler_optimal_single_cycle` — for any single cycle,
  Keeler's `undoScript` already achieves the optimum
  `n + r + 2 = c.members.length + 3`;
* `r ≥ 2`: `keeler_achieves_and_gap` — Keeler's `undoScript cs`
  has length `(n + r + 2) + (r - 2) + parity`. The gap is 0 at
  `r = 2` with an even cycle count (matching paper's "Keeler is
  optimal for `r = 2`"); the gap is `> 0` for `r ≥ 3`.

The closed-form siblings `undoScript_length_single_cycle` and
`optimalScript_length_single_cycle` provide the literal
`c.members.length + 3` form behind `keeler_optimal_single_cycle`'s
length equality.

**Axiom outlier**: `undoScript_length_single_cycle` depends on
`{Quot.sound, propext}` only — no `Classical.choice` — because its
proof routes through `undoScript_length` plus `simp`.
-/

open Equiv Equiv.Perm

namespace Project
namespace Futurama

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
/-- Closed-form length of Keeler's `undoScript` on a single cycle: `n + 3`.

    The explicit value behind `keeler_optimal_single_cycle`'s equality,
    useful when one needs the literal `c.members.length + 3` form rather
    than the equality with `optimalScript`. -/
theorem undoScript_length_single_cycle (c : Cycle α) :
    (undoScript [c]).length = c.members.length + 3 := by
  rw [undoScript_length]
  simp

/-- Closed-form length of `optimalScript` on a single cycle: `n + 3`. -/
theorem optimalScript_length_single_cycle (c : Cycle α) :
    (optimalScript [c]).length = c.members.length + 3 := by
  rw [optimalScript_length [c] (by simp)]
  simp

/-- For a single cycle (`r = 1`), Keeler's `undoScript` already achieves the
    optimal length: `(undoScript [c]).length = (optimalScript [c]).length`,
    both equal to `c.members.length + 3 = n + r + 2`.

    This closes the `r = 1` leg of paper p.138's remark "Keeler's algorithm
    is optimal only for r ≤ 2" -- which `keeler_achieves_and_gap`
    covers only for `r ≥ 2` (hypothesis `2 ≤ cs.length`). -/
theorem keeler_optimal_single_cycle (c : Cycle α) :
    (undoScript [c]).length = (optimalScript [c]).length := by
  rw [undoScript_length_single_cycle, optimalScript_length_single_cycle]

omit [Fintype α] in
/-- Keeler's `undoScript` is a valid `RepairSeq` and its gap to optimal is `(r-2) + parity`. -/
theorem keeler_achieves_and_gap
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hr : 2 ≤ cs.length) :
    ∃ (seq : RepairSeq (cycleProduct cs)),
      seq.steps = undoScript cs ∧
      seq.steps.length =
        ((cs.map fun c => c.members.length).sum + cs.length + 2) +
          (cs.length - 2) +
          (if cs.length % 2 = 0 then 0 else 1) := by
  rcases futuramaTheoremStrong cs hcs with ⟨hcorrect, _, hstepPairs, hhelpers⟩
  refine ⟨⟨undoScript cs, hhelpers, ?_, hstepPairs, hcorrect⟩, rfl,
    undoScript_length_eq_optimalBound_add_overhead cs hr⟩
  -- All Keeler steps are nontrivial: undoScript only produces canonical steps
  intro step hstep heq
  -- The step is in undoScript cs, which only produces CanonicalStep steps
  -- CanonicalStep has forms (x, orig a), (y, orig a), (x, y) — all nontrivial
  have hcan := mem_undoScript_canonical hstep
  rcases hcan with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact Body.noConfusion heq
  · exact Body.noConfusion heq
  · exact Body.noConfusion heq

end Futurama
end Project
