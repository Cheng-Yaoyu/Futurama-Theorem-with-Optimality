import Project.Futurama

open Equiv Equiv.Perm

namespace Project
namespace Futurama
namespace Validation5

/-!
# Validation V5 — exhaustive cross-semantics harness

This file extends V4 by combining three ingredients into one executable check:

* the `Fin 4` witness corpus `perm4Witnesses`, which covers all 24
  permutations of the original cast;
* the exhaustive cut-schedule enumeration `allCutSchedules`;
* the alternate direct-state simulator `runState`.

The new ingredient over V4 is that the two executable semantics are compared
for **every prefix** of **every repair script** generated from every witness and
every cut schedule. We then separately ask the direct simulator to end at the
identity state, so the alternate semantics is not only compared against the
algebraic semantics but also checked directly on its own terms.
-/
--------------------------------------------------------------------------------
-- Exhaustive Fin 4 witness × schedule validation
--------------------------------------------------------------------------------

section Fin4CrossSemantics

/-- Total number of `(witness, cut schedule)` combinations covered by V5. -/
example :
    (perm4Witnesses.map fun cs =>
      (allCutSchedules (cs := cs)).length).sum = 44 := by
  native_decide

/-- Every `Fin 4` witness passes the new V5 cross-semantics check over all of
its cut schedules. -/
example :
    perm4Witnesses.all allSchedulesCrossSemanticsValidate = true := by
  native_decide

/-- Every permutation of `Fin 4` is represented by a witness whose entire cut
family passes the V5 cross-semantics check. -/
theorem exists_perm4_cross_checked :
    ∀ σ : Perm Cast4,
      ∃ cs ∈ perm4Witnesses,
        cycleProduct cs = liftPerm σ ∧
          allSchedulesCrossSemanticsValidate cs = true := by
  native_decide

end Fin4CrossSemantics

--------------------------------------------------------------------------------
-- Audit snippet
--------------------------------------------------------------------------------

#print axioms Project.Futurama.Validation5.exists_perm4_cross_checked

end Validation5
end Futurama
end Project
