import Project.Futurama.CoreCycle
import Project.Futurama.CoreSchedule
import Project.Futurama.FiniteBridge
import Project.Futurama.ParameterizedFamily
import Project.Futurama.Optimality.RepairSeq
import Project.Futurama.Optimality.LowerBound.Layer0
import Project.Futurama.Optimality.LowerBound.Layer1

/-!
# Optimality / LowerBound / Layer 2 — `t ≥ n + r + 2` (parity gap closure)

This file completes Theorem 1's lower-bound chain by combining
Layer 1's `t ≥ n + r` with the parity theorem and a strict-inequality
"gap obstruction" that rules out `t = n + r`, pushing the bound up
to `t ≥ n + r + 2`. It also hosts the `Perm α`-level corollary
`futurama_optimal`, which is paper Theorem 1's "best possible"
claim at the `Perm α` indexing surface.

The chain at the bottom of this file is the proof path actually used
by Theorem 1's lower bound:

```text
repair_length_ge_entries_add_cycles  -- from Layer 1 import
+ repair_length_parity                -- from this file
+ repair_length_ne_entries_add_cycles -- from this file
omega
⇒ repair_length_ge_optimal            -- from this file
⇒ futurama_optimal                    -- from this file
```

The graph-theoretic Lemma 1 family (in `Optimality/Lemma1.lean`)
is mathematically independent of this chain — paper Theorem 1's own
proof similarly avoids Lemma 1.
-/

open Equiv Equiv.Perm

namespace Project
namespace Futurama

variable {α : Type*} [DecidableEq α] [Fintype α]
variable {π : Perm (Body α)}

-- ═══════════════════════════════════════════════
-- Section 5: Layer 2 — t ≥ n + r + 2
-- ═══════════════════════════════════════════════

/-- `runScript` steps with non-trivial swaps produces sign `(-1)^(steps.length)`. -/
private theorem sign_runScript_of_ne (steps : List (Body α × Body α))
    (hne : ∀ step ∈ steps, step.1 ≠ step.2) :
    Equiv.Perm.sign (runScript steps) = (-1) ^ steps.length := by
  induction steps with
  | nil => simp [runScript]
  | cons step rest ih =>
      rw [runScript, map_mul, ih (fun s hs => hne s (.tail _ hs))]
      simp [Equiv.Perm.sign_swap (hne step (.head _)), List.length_cons, pow_succ, mul_comm]

/-- Sign of `runScript` in a `RepairSeq` is `(-1)^t`. -/
private theorem sign_runScript_eq (seq : RepairSeq π) :
    Equiv.Perm.sign (runScript seq.steps) = (-1) ^ seq.steps.length :=
  sign_runScript_of_ne _ seq.nontrivial

/-- Sign of `cyclePermAux` is `(-1)^(rest.length)`, assuming elements are distinct. -/
private theorem sign_cyclePermAux (first : α) (rest : List α)
    (hnd : (first :: rest).Nodup) :
    Equiv.Perm.sign (cyclePermAux first rest) = (-1) ^ rest.length := by
  induction rest generalizing first with
  | nil => simp [cyclePermAux]
  | cons a rest ih =>
      rw [cyclePermAux, map_mul]
      have hnd' : (a :: rest).Nodup := by
        exact (List.nodup_cons.mp hnd).2
      rw [ih a hnd']
      have ha_ne : a ≠ first := by
        intro heq; subst heq
        exact absurd (.head _) (List.nodup_cons.mp hnd).1
      have hne : (Body.orig a : Body α) ≠ Body.orig first := by
        intro h; exact ha_ne (Body.orig.inj h)
      rw [Equiv.Perm.sign_swap hne, List.length_cons, pow_succ]

/-- Sign of `cyclePerm c` is `(-1)^(c.members.length - 1)`. -/
private theorem sign_cyclePerm (c : Cycle α) :
    Equiv.Perm.sign (cyclePerm c) = (-1) ^ (c.members.length - 1) := by
  unfold cyclePerm
  have hnd : (c.first :: c.tail).Nodup := c.nodup
  rw [sign_cyclePermAux c.first c.tail hnd]
  congr 1

/-- Sign of `cycleProduct cs` is `(-1)^(n - r)` where n = total elements, r = |cs|. -/
private theorem sign_cycleProduct (cs : List (Cycle α)) :
    Equiv.Perm.sign (cycleProduct cs) =
      (-1) ^ ((cs.map fun c => c.members.length).sum - cs.length) := by
  induction cs with
  | nil => simp [cycleProduct]
  | cons c cs ih =>
      rw [cycleProduct, map_mul, ih, sign_cyclePerm]
      rw [← pow_add]
      congr 1
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hc : c.members.length ≥ 2 := by simp [Cycle.members]
      have hcs_ge : (cs.map fun c => c.members.length).sum ≥ cs.length := by
        clear ih hc c
        induction cs with
        | nil => simp
        | cons c' cs' ih' =>
            simp only [List.map_cons, List.sum_cons, List.length_cons]
            have : c'.members.length ≥ 2 := by simp [Cycle.members]
            linarith [ih']
      omega

/-- The parity constraint: t and n + r have the same parity. -/
theorem repair_length_parity
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs)) :
    seq.steps.length % 2 =
      ((cs.map fun c => c.members.length).sum + cs.length) % 2 := by
  -- From seq.undoes: runScript * cycleProduct = 1
  -- sign(runScript) * sign(cycleProduct) = sign(1) = 1
  have hsign : Equiv.Perm.sign (runScript seq.steps * cycleProduct cs) = 1 := by
    rw [seq.undoes]; simp
  rw [map_mul, sign_runScript_eq, sign_cycleProduct] at hsign
  -- (-1)^t * (-1)^(n-r) = (-1)^(t + (n-r)) = 1
  rw [← pow_add] at hsign
  -- (-1)^k = 1 iff k is even
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rw [neg_one_pow_eq_one_iff_even hne] at hsign
  -- n ≥ r (each cycle has ≥ 2 members, so sum ≥ 2r ≥ r)
  have hn_ge_r : (cs.map fun c => c.members.length).sum ≥ cs.length := by
    clear hsign seq
    induction cs with
    | nil => simp
    | cons c cs' ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have : c.members.length ≥ 2 := by simp [Cycle.members]
        have htail : cs'.Pairwise Cycle.Disjoint := (List.pairwise_cons.1 hcs).2
        have ih' := ih htail
        have hsum : c.members.length + (cs'.map fun c => c.members.length).sum ≥ 2 + cs'.length :=
          Nat.add_le_add this ih'
        omega
  -- From Even(t + (n-r)), deduce t % 2 = (n+r) % 2
  obtain ⟨k, hk⟩ := hsign
  omega

/-- Gap obstruction: for a nonempty cycle list, equality `t = n + r` is impossible.
    This is the remaining "rightmost element" argument from Evans–Huang–Nguyen.

    This pairs with
    `repair_length_ge_entries_add_cycles` and `repair_length_parity`, this is the third
    component of the Theorem 1 lower-bound chain consumed by `repair_length_ge_optimal`.
    The two siblings are public; this one is now public for symmetry. -/
theorem repair_length_ne_entries_add_cycles
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs)) :
    seq.steps.length ≠ (cs.map fun c => c.members.length).sum + cs.length := by
  intro heq
  have hnoXY : ¬ seq.hasHelperSwap :=
    not_hasHelperSwap_of_eq_case cs hcs seq heq
  have hdouble :
      seq.doubleEntrySet.card = cs.length :=
    doubleEntrySet_card_eq_cycles_of_eq_case cs hcs seq heq
  rcases exists_ordered_doubleStep_split_of_eq_case cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) with
    ⟨pre, mid, suf, hsplit_xy⟩ | ⟨pre, mid, suf, hsplit_yx⟩
  · exact rightmost_externalGapY_contradiction_of_minGap_xy cs hcs hcs_nonempty seq hnoXY heq
      hsplit_xy
  · let seqSwap := swapHelpersRepairSeq cs seq
    have heqSwap :
        seqSwap.steps.length = (cs.map fun c => c.members.length).sum + cs.length := by
      simpa [seqSwap, swapHelpersRepairSeq] using heq
    have hnoXYSwap : ¬ seqSwap.hasHelperSwap :=
      not_hasHelperSwap_of_eq_case cs hcs seqSwap heqSwap
    have hsplit_swap :
        seqSwap.steps =
          pre.map swapHelpersStep ++
            xDoubleStepOf_eq_case cs hcs seqSwap heqSwap
              (minGapCycleOf_eq_case cs hcs hcs_nonempty seqSwap heqSwap)
              (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seqSwap heqSwap) ::
            mid.map swapHelpersStep ++
            yDoubleStepOf_eq_case cs hcs seqSwap heqSwap
              (minGapCycleOf_eq_case cs hcs hcs_nonempty seqSwap heqSwap)
              (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seqSwap heqSwap) ::
            suf.map swapHelpersStep := by
      simpa [seqSwap] using
        swapHelpersRepairSeq_xy_split_of_yx_split cs hcs hcs_nonempty seq heq hsplit_yx
    exact rightmost_externalGapY_contradiction_of_minGap_xy cs hcs hcs_nonempty seqSwap
      hnoXYSwap heqSwap hsplit_swap

/-- Layer 2: for a nonempty cycle list, the main lower bound is `t ≥ n + r + 2`. -/
theorem repair_length_ge_optimal
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs)) :
    (cs.map fun c => c.members.length).sum + cs.length + 2 ≤ seq.steps.length := by
  let n := (cs.map fun c => c.members.length).sum
  let r := cs.length
  have h_lower : n + r ≤ seq.steps.length := by
    simpa [n, r] using repair_length_ge_entries_add_cycles cs hcs seq
  have h_parity : seq.steps.length % 2 = (n + r) % 2 := by
    simpa [n, r] using repair_length_parity cs hcs seq
  have hneq : seq.steps.length ≠ n + r := by
    simpa [n, r] using repair_length_ne_entries_add_cycles cs hcs hcs_nonempty seq
  omega

-- ═══════════════════════════════════════════════
-- Section 6: Corollaries
-- ═══════════════════════════════════════════════

/-- Optimality for arbitrary finite nontrivial permutations. -/
theorem futurama_optimal
    (σ : Perm α)
    (hσ : 0 < σ.cycleFactorsFinset.card)
    (seq : RepairSeq (liftPerm σ)) :
    σ.support.card + σ.cycleFactorsFinset.card + 2 ≤ seq.steps.length := by
  -- Bridge: liftPerm σ = cycleProduct (factorCycles σ)
  have hbridge : cycleProduct (factorCycles σ) = liftPerm σ :=
    cycleProduct_factorCycles σ
  have hnonempty : factorCycles σ ≠ [] := by
    intro hnil
    have hcard : σ.cycleFactorsFinset.card = 0 := by
      simpa [hnil] using (factorCycles_length (σ := σ)).symm
    omega
  -- Cast the seq to use cycleProduct
  let seq' : RepairSeq (cycleProduct (factorCycles σ)) :=
    { steps := seq.steps
      helper_constraint := seq.helper_constraint
      nontrivial := seq.nontrivial
      distinct_pairs := seq.distinct_pairs
      undoes := by rw [hbridge]; exact seq.undoes }
  calc σ.support.card + σ.cycleFactorsFinset.card + 2
      = ((factorCycles σ).map fun c => c.members.length).sum +
          (factorCycles σ).length + 2 := by
            rw [factorCycles_membersLengthSum, factorCycles_length]
    _ ≤ seq'.steps.length :=
          repair_length_ge_optimal _ (factorCycles_pairwise_disjoint σ) hnonempty seq'
    _ = seq.steps.length := rfl


end Futurama
end Project
