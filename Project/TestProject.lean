import Project.Futurama
import Project.Futurama.Optimality

open Equiv Equiv.Perm

namespace Project
namespace Futurama

/-!
# The Futurama Theorem — top-level façade

This is the top-level entry point that re-exports the entire
formalisation:

* the constructive theorem development in `Project.Futurama.*`
  (single-cycle and multi-cycle repair, the `liftPerm` /
  `factorCycles` bridge from arbitrary finite permutations, the
  parameterised cut family, and the shared `RepairSpec` interface);
* the optimality material in `Project.Futurama.Optimality.*`
  (paper Theorem 1 upper-bound construction, the lower-bound chain,
  the Lemma 1 family, and the Keeler-gap remarks).

The file body itself contains only:

* a small `Crew` example demonstrating `cyclePerm` / `repairPerm`
  on a concrete 3-element scramble;
* `#check` diagnostics verifying every public endpoint resolves
  through the façade.
-/

variable {α : Type*} [DecidableEq α]

section Examples

inductive Crew
  | fry
  | leela
  | bender
  | zoidberg
  deriving DecidableEq, Repr

open Crew

def sampleCycle : Cycle Crew where
  first := fry
  second := leela
  rest := [bender]
  nodup := by simp

#eval cyclePerm sampleCycle (Body.orig fry)
#eval cyclePerm sampleCycle (Body.orig leela)
#eval cyclePerm sampleCycle (Body.orig bender)
#eval repairPerm sampleCycle Body.x
-- The theorem uses `repairPerm` on the left: `repairPerm * cyclePerm`.
#eval (repairPerm sampleCycle * cyclePerm sampleCycle) (Body.orig fry)
#eval (repairPerm sampleCycle * cyclePerm sampleCycle) (Body.orig leela)
#eval (repairPerm sampleCycle * cyclePerm sampleCycle) (Body.orig bender)
#eval (repairPerm sampleCycle * cyclePerm sampleCycle) Body.x
#eval (repairPerm sampleCycle * cyclePerm sampleCycle) Body.y

end Examples

-- Diagnostics: verify key theorem types resolve through the façade
#check @transposition_count_ge_cycle_length
#check @minimal_factorization_covers_support
#check @minimal_factorization_has_adjacent
#check @minimal_factorization_has_adjacent_paper
#check @repair_length_ge_optimal
#check @futurama_optimal
#check @optimalScriptOfPerm_correct
#check @optimalScriptOfPerm_length
#check @optimalScriptOfPerm_isOptimal
#check @futuramaTheorem1OfPerm
#check @futuramaTheorem1Full
#check @optimalRepairSeqOfPerm
#check @keeler_achieves_and_gap
#check @keeler_optimal_single_cycle

end Futurama
end Project
