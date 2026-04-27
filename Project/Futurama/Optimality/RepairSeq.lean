import Project.Futurama.CoreCycle

/-!
# Optimality / RepairSeq — the adversary's object

This file hosts the `RepairSeq` structure and its entry-counting
projections. `RepairSeq (π : Perm (Body α))` is the abstract
"adversary's surface" used by the lower-bound proof: every valid
repair sequence — regardless of how it was built — fits this shape,
and the lower-bound chain in `Optimality/LowerBound/*.lean` shows
any such sequence has length ≥ `n + r + 2`.

The five fields mirror paper Theorem 1's machine-side requirements:
correctness (`undoes`), helper inclusion (`helper_constraint`),
distinct unordered pairs (`distinct_pairs`), and explicit
nontriviality (`nontrivial`). The `nontrivial` field is strictly
additional structure relative to the paper's implicit "transposition
is a 2-cycle on distinct elements"; we make this explicit because
Lean prefers explicit fields over implicit conventions, and the
resulting structures are equivalent in conclusion.
-/

open Equiv Equiv.Perm

namespace Project
namespace Futurama

variable {α : Type*} [DecidableEq α]

-- ═══════════════════════════════════════════════
-- Section 1: RepairSeq — the adversary's object
-- ═══════════════════════════════════════════════

/-- A valid repair sequence for a target permutation `π` on `Body α`.

This is the "adversary's object": any sequence of swaps that undoes `π`
while obeying the machine constraints (helper involvement, no repeated pairs). -/
structure RepairSeq (π : Perm (Body α)) where
  steps : List (Body α × Body α)
  helper_constraint : ∀ step ∈ steps, UsesHelper step
  nontrivial : ∀ step ∈ steps, step.1 ≠ step.2
  distinct_pairs : (steps.map stepPair).Nodup
  undoes : runScript steps * π = 1

variable {π : Perm (Body α)}

/-- The number of swaps in a repair sequence. -/
abbrev RepairSeq.len (seq : RepairSeq π) : ℕ :=
  seq.steps.length

/-- Extract original elements paired with helper `x`. -/
def RepairSeq.xEntries (seq : RepairSeq π) : List α :=
  seq.steps.filterMap fun
    | (Body.x, Body.orig a) => some a
    | (Body.orig a, Body.x) => some a
    | _ => none

/-- Extract original elements paired with helper `y`. -/
def RepairSeq.yEntries (seq : RepairSeq π) : List α :=
  seq.steps.filterMap fun
    | (Body.y, Body.orig a) => some a
    | (Body.orig a, Body.y) => some a
    | _ => none

/-- All original elements mentioned in the sequence. -/
def RepairSeq.origEntries (seq : RepairSeq π) : List α :=
  seq.steps.filterMap fun
    | (Body.orig a, _) => some a
    | (_, Body.orig a) => some a
    | _ => none

/-- Whether the sequence contains the helper-helper swap `(x, y)`. -/
def RepairSeq.hasHelperSwap (seq : RepairSeq π) : Prop :=
  (Body.x, Body.y) ∈ seq.steps ∨ (Body.y, Body.x) ∈ seq.steps

end Futurama
end Project
