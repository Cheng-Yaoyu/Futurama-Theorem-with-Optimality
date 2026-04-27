import Project.Futurama.CoreCycle

open Equiv Equiv.Perm

namespace Project
namespace Futurama

/-!
# Futurama Core Schedule Layer

This module contains the default cycle-list composition layer: global
cycle products, concatenated repair scripts, the final helper cleanup,
and the default strong/full-spec theorem endpoints for cycle lists.

## Main definitions

* `cycleProduct` — the composed permutation of a cycle list.
* `repairScripts` — concatenated default per-cycle repair scripts.
* `repairProduct` — `runScript repairScripts` as a `Perm`.
* `residualPerm` — the residue after `repairProduct` is applied; used
  to derive the parity-cleanup conjunct.
* `finalCleanupScript` — appends the final `(x, y)` swap when needed.
* `undoScript` — the canonical full repair script
  `repairScripts ++ finalCleanupScript`.

## Main results

* `runScript_undoScript_mul_cycleProduct` — every default-route
  `undoScript cs` correctly inverts `cycleProduct cs`.
* `futuramaTheorem` — the most basic constructive endpoint at the
  cycle-list level (correctness only). Stronger packaged endpoints
  (`futuramaTheoremStrong*`) live in `ParameterizedFamily.lean` and
  are derived via `defaultSchedule`.
-/

variable {α : Type*} [DecidableEq α]

/-- Composition of `cyclePerm` over a list of disjoint cycles.

Models the "global scramble" obtained by composing per-cycle actions in
list order. Together with `liftPerm` and `factorCycles`, this is the
central bridge between the abstract `Equiv.Perm α` and the project's
`Cycle` / `Body` representation: every finite permutation factorises as
`cycleProduct (factorCycles σ) = liftPerm σ` (see
`cycleProduct_factorCycles` in `FiniteBridge.lean`). -/
def cycleProduct : List (Cycle α) → Perm (Body α)
  | [] => 1
  | c :: cs => cyclePerm c * cycleProduct cs

/-- Concatenate the canonical repair scripts cycle by cycle. -/
def repairScripts : List (Cycle α) → List (Body α × Body α)
  | [] => []
  | c :: cs => repairScript c ++ repairScripts cs

/-- The permutation induced by executing the cycle-by-cycle repair scripts. -/
def repairProduct : List (Cycle α) → Perm (Body α)
  | [] => 1
  | c :: cs => repairProduct cs * repairPerm c

/-- After each repaired cycle, the helpers toggle between `1` and `(x y)`. -/
def residualPerm : List (Cycle α) → Perm (Body α)
  | [] => 1
  | _ :: cs => residualPerm cs * helperSwap

/-- The final helper swap is needed exactly when the number of repaired cycles is odd. -/
def finalCleanupScript (cs : List (Cycle α)) : List (Body α × Body α) :=
  if cs.length % 2 = 0 then [] else [(Body.x, Body.y)]

/-- Keeler's complete repair script for a list of cycles.

This is the executable list form of the paper's global `τ`/`σ` construction
(equation (2)): concatenate the cyclewise repair blocks, then append the final
helper swap exactly in the odd-cycle case. -/
def undoScript (cs : List (Cycle α)) : List (Body α × Body α) :=
  repairScripts cs ++ finalCleanupScript cs

omit [DecidableEq α] in
@[simp] theorem finalCleanupScript_length (cs : List (Cycle α)) :
    (finalCleanupScript cs).length = if cs.length % 2 = 0 then 0 else 1 := by
  by_cases h : cs.length % 2 = 0 <;> simp [finalCleanupScript, h]

@[simp] theorem cycleProduct_nil :
    cycleProduct ([] : List (Cycle α)) = (1 : Perm (Body α)) :=
  rfl

@[simp] theorem cycleProduct_cons (c : Cycle α) (cs : List (Cycle α)) :
    cycleProduct (c :: cs) = cyclePerm c * cycleProduct cs :=
  rfl

omit [DecidableEq α] in
@[simp] theorem repairScripts_nil :
    repairScripts ([] : List (Cycle α)) = [] :=
  rfl

omit [DecidableEq α] in
@[simp] theorem repairScripts_cons (c : Cycle α) (cs : List (Cycle α)) :
    repairScripts (c :: cs) = repairScript c ++ repairScripts cs :=
  rfl

omit [DecidableEq α] in
theorem repairScripts_length (cs : List (Cycle α)) :
    (repairScripts cs).length = (cs.map fun c => c.members.length).sum + 2 * cs.length := by
  induction cs with
  | nil =>
      simp [repairScripts]
  | cons c cs ih =>
      simp [repairScripts, repairScript_length, ih, Nat.mul_add,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      rw [show (4 : Nat) = 2 + 2 by decide, Nat.add_assoc]

omit [DecidableEq α] in
theorem undoScript_length (cs : List (Cycle α)) :
    (undoScript cs).length =
      (cs.map fun c => c.members.length).sum + 2 * cs.length +
        (if cs.length % 2 = 0 then 0 else 1) := by
  simp [undoScript, repairScripts_length, Nat.add_left_comm, Nat.add_comm]

omit [DecidableEq α] in
theorem undoScript_length_le (cs : List (Cycle α)) :
    (undoScript cs).length ≤ (cs.map fun c => c.members.length).sum + 2 * cs.length + 1 := by
  rw [undoScript_length]
  by_cases h : cs.length % 2 = 0 <;> simp [h]

omit [DecidableEq α] in
/-- For at least two cycles, Keeler's script length is the paper's optimal target `n + r + 2`
plus an explicit overhead of `(r - 2) + parity`. -/
theorem undoScript_length_eq_optimalBound_add_overhead (cs : List (Cycle α))
    (hcs : 2 ≤ cs.length) :
    (undoScript cs).length =
      ((cs.map fun c => c.members.length).sum + cs.length + 2) +
        (cs.length - 2) +
        (if cs.length % 2 = 0 then 0 else 1) := by
  rw [undoScript_length]
  by_cases h : cs.length % 2 = 0
  · simp [h]
    omega
  · have h' : cs.length % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one cs.length with h0 | h1
      · contradiction
      · exact h1
    simp [h']
    omega

@[simp] theorem repairProduct_nil :
    repairProduct ([] : List (Cycle α)) = (1 : Perm (Body α)) :=
  rfl

@[simp] theorem repairProduct_cons (c : Cycle α) (cs : List (Cycle α)) :
    repairProduct (c :: cs) = repairProduct cs * repairPerm c :=
  rfl

@[simp] theorem residualPerm_nil :
    residualPerm ([] : List (Cycle α)) = (1 : Perm (Body α)) :=
  rfl

@[simp] theorem residualPerm_cons (c : Cycle α) (cs : List (Cycle α)) :
    residualPerm (c :: cs) = residualPerm cs * helperSwap :=
  rfl

@[simp] theorem cycleProduct_apply_x (cs : List (Cycle α)) :
    cycleProduct cs Body.x = Body.x := by
  induction cs with
  | nil =>
      simp [cycleProduct]
  | cons c cs ih =>
      simp [cycleProduct, cyclePerm, mul_apply, ih]

@[simp] theorem cycleProduct_apply_y (cs : List (Cycle α)) :
    cycleProduct cs Body.y = Body.y := by
  induction cs with
  | nil =>
      simp [cycleProduct]
  | cons c cs ih =>
      simp [cycleProduct, cyclePerm, mul_apply, ih]

@[simp] theorem helperSwap_mul_self :
    helperSwap * helperSwap = (1 : Perm (Body α)) := by
  ext z
  cases z <;> simp [helperSwap]

theorem runScript_repairScripts (cs : List (Cycle α)) :
    runScript (repairScripts cs) = repairProduct cs := by
  induction cs with
  | nil =>
      simp [repairScripts, repairProduct]
  | cons c cs ih =>
      simp [repairScripts, repairProduct, runScript_append, ih, repairPerm]

theorem helperSwap_disjoint_cycleProduct (cs : List (Cycle α)) :
    Equiv.Perm.Disjoint helperSwap (cycleProduct cs) := by
  intro z
  cases z with
  | x =>
      exact Or.inr (cycleProduct_apply_x cs)
  | y =>
      exact Or.inr (cycleProduct_apply_y cs)
  | orig a =>
      exact Or.inl (by simp [helperSwap, swap_apply_of_ne_of_ne])

theorem helperSwap_commute_cycleProduct (cs : List (Cycle α)) :
    Commute helperSwap (cycleProduct cs) :=
  (helperSwap_disjoint_cycleProduct cs).commute

/-- Paper correspondence: after repairing all cycles, only the parity-dependent
helper effect remains. This is the algebraic content of the paper's `τ P = (x y)^r`
step before the final cleanup. -/
theorem repairProduct_mul_cycleProduct (cs : List (Cycle α)) :
    repairProduct cs * cycleProduct cs = residualPerm cs := by
  induction cs with
  | nil =>
      simp [repairProduct, cycleProduct, residualPerm]
  | cons c cs ih =>
      calc
        repairProduct (c :: cs) * cycleProduct (c :: cs)
            = repairProduct cs * (repairPerm c * cyclePerm c) * cycleProduct cs := by
                simp [repairProduct, cycleProduct, mul_assoc]
        _ = repairProduct cs * helperSwap * cycleProduct cs := by
              rw [repairPerm_mul_cyclePerm]
        _ = repairProduct cs * cycleProduct cs * helperSwap := by
              calc
                repairProduct cs * helperSwap * cycleProduct cs
                    = repairProduct cs * (helperSwap * cycleProduct cs) := by
                        simp [mul_assoc]
                _ = repairProduct cs * (cycleProduct cs * helperSwap) := by
                      rw [(helperSwap_commute_cycleProduct cs).eq]
                _ = repairProduct cs * cycleProduct cs * helperSwap := by
                      simp [mul_assoc]
        _ = residualPerm cs * helperSwap := by
              rw [ih]
        _ = residualPerm (c :: cs) := by
              simp [residualPerm]

/-- The residual helper permutation is `1` for an even number of cycles and `(x y)` for an odd one. -/
theorem residualPerm_eq_parity (cs : List (Cycle α)) :
    residualPerm cs = if cs.length % 2 = 0 then 1 else helperSwap := by
  induction cs with
  | nil =>
      simp [residualPerm]
  | cons c cs ih =>
      rcases Nat.mod_two_eq_zero_or_one cs.length with h | h
      · have h' : (cs.length + 1) % 2 = 1 := (Nat.succ_mod_two_eq_one_iff).2 h
        simp [residualPerm, ih, h, h']
      · have h' : (cs.length + 1) % 2 = 0 := (Nat.succ_mod_two_eq_zero_iff).2 h
        simp [residualPerm, ih, h, h', helperSwap_mul_self]

theorem runScript_undoScript (cs : List (Cycle α)) :
    runScript (undoScript cs) =
      (if cs.length % 2 = 0 then 1 else helperSwap) * repairProduct cs := by
  rw [undoScript, runScript_append, runScript_repairScripts]
  by_cases h : cs.length % 2 = 0
  · simp [finalCleanupScript, h]
  · have h' : cs.length % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one cs.length with h0 | h1
      · contradiction
      · exact h1
    simp [finalCleanupScript, h', helperSwap, runScript]

/-- Full Futurama repair theorem for a cycle decomposition.

This matches the final restoration step in the paper's introductory argument:
compose the cyclewise repairs, then add the last helper swap exactly when the
number of cycles is odd. -/
theorem runScript_undoScript_mul_cycleProduct (cs : List (Cycle α)) :
    runScript (undoScript cs) * cycleProduct cs = 1 := by
  rw [runScript_undoScript, mul_assoc, repairProduct_mul_cycleProduct, residualPerm_eq_parity]
  by_cases h : cs.length % 2 = 0
  · simp [h]
  · have h' : cs.length % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one cs.length with h0 | h1
      · contradiction
      · exact h1
    simp [h', helperSwap_mul_self]

/-- A concise theorem name matching the statement in Keeler's proof. -/
theorem futuramaTheorem (cs : List (Cycle α)) :
    runScript (undoScript cs) * cycleProduct cs = 1 :=
  runScript_undoScript_mul_cycleProduct cs

omit [DecidableEq α] in
@[simp] theorem repairScripts_eq_flatMap (cs : List (Cycle α)) :
    repairScripts cs = cs.flatMap repairScript := by
  induction cs with
  | nil =>
      simp [repairScripts]
  | cons c cs ih =>
      simp [repairScripts, ih]

omit [DecidableEq α] in
theorem mem_repairScripts_iff {cs : List (Cycle α)} {step : Body α × Body α} :
    step ∈ repairScripts cs ↔ ∃ c ∈ cs, step ∈ repairScript c := by
  rw [repairScripts_eq_flatMap]
  simp [List.mem_flatMap]

omit [DecidableEq α] in
theorem mem_repairScripts_canonical {cs : List (Cycle α)} {step : Body α × Body α}
    (h : step ∈ repairScripts cs) : CanonicalStep step := by
  rcases (mem_repairScripts_iff).1 h with ⟨c, _, hc⟩
  exact mem_repairScript_canonical hc

omit [DecidableEq α] in
theorem mem_finalCleanupScript_canonical {cs : List (Cycle α)} {step : Body α × Body α}
    (h : step ∈ finalCleanupScript cs) : CanonicalStep step := by
  by_cases hparity : cs.length % 2 = 0
  · simp [finalCleanupScript, hparity] at h
  · have hstep : step = (Body.x, Body.y) := by
      simp [finalCleanupScript, hparity] at h
      exact h
    exact Or.inr <| Or.inr hstep

omit [DecidableEq α] in
theorem mem_undoScript_canonical {cs : List (Cycle α)} {step : Body α × Body α}
    (h : step ∈ undoScript cs) : CanonicalStep step := by
  rw [undoScript, List.mem_append] at h
  exact h.elim mem_repairScripts_canonical mem_finalCleanupScript_canonical

omit [DecidableEq α] in
theorem mem_undoScript_usesHelper {cs : List (Cycle α)} {step : Body α × Body α}
    (h : step ∈ undoScript cs) : UsesHelper step :=
  (mem_undoScript_canonical h).usesHelper

omit [DecidableEq α] in
theorem mem_undoScript_nontrivial {cs : List (Cycle α)} {step : Body α × Body α}
    (h : step ∈ undoScript cs) : step.1 ≠ step.2 :=
  (mem_undoScript_canonical h).nontrivial

omit [DecidableEq α] in
theorem repairScripts_nodup {cs : List (Cycle α)} (hcs : cs.Pairwise Cycle.Disjoint) :
    (repairScripts cs).Nodup := by
  rw [repairScripts_eq_flatMap, List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro c hc
    exact repairScript_nodup c
  · exact hcs.imp fun {_ _} h => repairScript_disjoint_of_cycle_disjoint h

omit [DecidableEq α] in
theorem not_mem_repairScripts_helperSwap {cs : List (Cycle α)} :
    (Body.x, Body.y) ∉ repairScripts cs := by
  intro h
  rcases (mem_repairScripts_iff).1 h with ⟨c, _, hc⟩
  exact not_mem_repairScript_helperSwap c hc

omit [DecidableEq α] in
theorem undoScript_nodup {cs : List (Cycle α)} (hcs : cs.Pairwise Cycle.Disjoint) :
    (undoScript cs).Nodup := by
  rw [undoScript]
  have hrepair : (repairScripts cs).Nodup := repairScripts_nodup hcs
  have hcleanup : (finalCleanupScript cs).Nodup := by
    by_cases hparity : cs.length % 2 = 0
    · simp [finalCleanupScript, hparity]
    · simp [finalCleanupScript, hparity]
  have hdisj : List.Disjoint (repairScripts cs) (finalCleanupScript cs) := by
    by_cases hparity : cs.length % 2 = 0
    · simp [finalCleanupScript, hparity]
    · rw [finalCleanupScript, if_neg hparity, List.disjoint_right]
      intro step hcleanup hrepair
      have hstep : step = (Body.x, Body.y) := by simpa using hcleanup
      subst step
      exact not_mem_repairScripts_helperSwap hrepair
  exact hrepair.append hcleanup hdisj

omit [DecidableEq α] in
/-- The repair script never repeats the same swap pair, even up to swapping its endpoints. -/
theorem undoScript_stepPairs_nodup {cs : List (Cycle α)} (hcs : cs.Pairwise Cycle.Disjoint) :
    ((undoScript cs).map stepPair).Nodup := by
  refine List.Nodup.map_on ?_ (undoScript_nodup hcs)
  intro step₁ h₁ step₂ h₂ hpair
  exact stepPair_injective_of_canonical
    (mem_undoScript_canonical h₁) (mem_undoScript_canonical h₂) hpair

omit [DecidableEq α] in
theorem not_mem_undoScript_orig_orig (cs : List (Cycle α)) (a b : α) :
    (Body.orig a, Body.orig b) ∉ undoScript cs := by
  intro h
  have hhelper := mem_undoScript_usesHelper h
  simp [UsesHelper] at hhelper

end Futurama
end Project
