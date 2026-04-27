import Project.Futurama.CoreCycle
import Project.Futurama.CoreSchedule
import Project.Futurama.FiniteBridge
import Project.Futurama.ParameterizedFamily
import Project.Futurama.Optimality.RepairSeq

/-!
# Optimality / LowerBound / Layer 0 — `t ≥ n` (entry counting) + helpers + gap-argument lemmas

Layer 0 establishes the first leg of Theorem 1's lower-bound chain:
`repair_length_ge_entries` says that every cycle-support entry must
appear (coupled with a helper) in some factor of the repair script,
so `t ≥ n`.

Sub-content:

* the entry-counting argument itself (`repair_length_ge_entries`);
* helper-fixing lemmas establishing that `runScript` and the
  `cyclePerm` / `cycleProduct` family all fix the helpers `x`/`y`
  outside the swap pairs that touch them;
* the `xStepFor` / `yStepFor` predicates, `xStepOf` / `yStepOf`
  extractors, and `exists_split_*` list-positioning lemmas which
  serve as the scaffolding for the Layer 1 doubling argument.
-/

open Equiv Equiv.Perm

namespace Project
namespace Futurama

variable {α : Type*} [DecidableEq α] [Fintype α]
variable {π : Perm (Body α)}

-- Section 3: Helpers & Layer 0 — t ≥ n
-- ═══════════════════════════════════════════════

omit [Fintype α] in
/-- If `z` does not appear in any step, `runScript` fixes `z`. -/
theorem runScript_apply_of_not_mem' (steps : List (Body α × Body α)) (z : Body α)
    (hz : ∀ step ∈ steps, z ≠ step.1 ∧ z ≠ step.2) :
    runScript steps z = z := by
  induction steps with
  | nil => simp
  | cons step rest ih =>
      obtain ⟨u, v⟩ := step
      simp only [runScript_cons, mul_apply]
      have h := hz (u, v) (.head _)
      rw [swap_apply_of_ne_of_ne h.1 h.2]
      exact ih fun s hs => hz s (List.mem_cons_of_mem _ hs)

omit [Fintype α] in
/-- `cyclePerm` fixes any `Body.orig a` where `a` is NOT a member of the cycle. -/
theorem cyclePerm_apply_orig_of_not_mem' (c : Cycle α) (a : α) (ha : a ∉ c.members) :
    cyclePerm c (Body.orig a) = Body.orig a := by
  rw [cyclePerm]
  apply cyclePermAux_orig_of_not_mem
  simp [Cycle.members, Cycle.tail] at ha ⊢; exact ha

omit [Fintype α] in
/-- Helper: `cyclePermAux first (a :: rest)` moves every element of `first :: a :: rest`
when the list is nodup. -/
private theorem cyclePermAux_ne_of_mem' (first a : α) (rest : List α)
    (hnodup : (first :: a :: rest).Nodup) (b : α) (hb : b ∈ first :: a :: rest) :
    cyclePermAux first (a :: rest) (Body.orig b) ≠ Body.orig b := by
  induction rest generalizing first a b with
  | nil =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      cases hb with
      | inl heq =>
          subst heq
          rw [cyclePermAux_first_step]; simp [cyclePermAux]
          intro h; exact (List.nodup_cons.mp hnodup).1 (by rw [h]; exact .head _)
      | inr heq =>
          subst heq
          have hne : first ≠ b := by
            intro h; exact (List.nodup_cons.mp hnodup).1 (by rw [h]; exact .head _)
          rw [cyclePermAux_head first b [] hne (by simp)]
          exact fun h => hne (Body.orig.inj h)
  | cons d rest ih =>
      cases List.mem_cons.mp hb with
      | inl heq =>
          subst heq
          rw [cyclePermAux_first_step]
          intro heq
          have hfirst_not_mem : b ∉ a :: d :: rest := (List.nodup_cons.mp hnodup).1
          have hfix := cyclePermAux_orig_of_not_mem hfirst_not_mem
          have := (cyclePermAux a (d :: rest)).injective (heq.trans hfix.symm)
          exact absurd (Body.orig.inj this) (fun h =>
            (List.nodup_cons.mp hnodup).1 (by rw [h]; exact .head _))
      | inr hb' =>
          cases List.mem_cons.mp hb' with
          | inl heq =>
              subst heq
              have hne : first ≠ b := by
                intro h; exact (List.nodup_cons.mp hnodup).1 (by rw [h]; exact .head _)
              have hfirst_not_rest : first ∉ d :: rest := by
                intro hm; exact (List.nodup_cons.mp hnodup).1 (.tail _ hm)
              rw [cyclePermAux_head first b (d :: rest) hne hfirst_not_rest]
              exact fun h => hne (Body.orig.inj h)
          | inr hb'' =>
              have hab : b ≠ a := by
                intro h; subst h
                exact (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1 hb''
              have hbf : b ≠ first := by
                intro h; subst h
                exact (List.nodup_cons.mp hnodup).1 (List.mem_cons_of_mem _ hb'')
              rw [cyclePermAux_skip_head hab hbf]
              exact ih a d ((List.nodup_cons.mp hnodup).2) b
                (List.mem_cons_of_mem _ hb'')

omit [Fintype α] in
/-- Every cycle moves its members. -/
theorem cyclePerm_ne_of_mem (c : Cycle α) (a : α) (ha : a ∈ c.members) :
    cyclePerm c (Body.orig a) ≠ Body.orig a := by
  rw [cyclePerm]
  apply cyclePermAux_ne_of_mem' c.first c.second c.rest c.nodup a
  have : a ∈ c.first :: c.second :: c.rest := by
    simp only [Cycle.members] at ha; exact ha
  exact this

private theorem cyclePerm_support (c : Cycle α) :
    (cyclePerm c).support = (c.members.map Body.orig).toFinset := by
  let l : List (Body α) := (c.members.map Body.orig).reverse
  have hl_nodup : l.Nodup := by
    refine List.nodup_reverse.mpr ?_
    simpa using
      (c.nodup.map (show Function.Injective Body.orig from fun _ _ h => Body.orig.inj h))
  have hl_not_singleton : ∀ z : Body α, l ≠ [z] := by
    intro z hz
    have hlen := congrArg List.length hz
    dsimp [l] at hlen
    simp at hlen
  calc
    (cyclePerm c).support = l.toFinset := by
      rw [cyclePerm, cyclePermAux_eq_formPerm_reverse]
      exact List.support_formPerm_of_nodup l hl_nodup hl_not_singleton
    _ = (c.members.map Body.orig).toFinset := by
      simpa [l] using (List.toFinset_reverse (l := c.members.map Body.orig))

omit [Fintype α] in
private theorem cyclePerm_preimage_member
    (c : Cycle α) (a : α) (ha : a ∈ c.members) :
    ∃ b ∈ c.members, b ≠ a ∧ cyclePerm c (Body.orig b) = Body.orig a := by
  let l : List (Body α) := (c.members.map Body.orig).reverse
  have hl_nodup : l.Nodup := by
    refine List.nodup_reverse.mpr ?_
    simpa using
      (c.nodup.map (show Function.Injective Body.orig from fun _ _ h => Body.orig.inj h))
  have hmem : Body.orig a ∈ l := by
    dsimp [l]
    exact List.mem_reverse.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)
  let z : Body α := l.prev (Body.orig a) hmem
  have hzmem : z ∈ l := by
    exact List.prev_mem (l := l) (x := Body.orig a) hmem
  have hnext : l.next z hzmem = Body.orig a := by
    simpa [z] using List.next_prev l hl_nodup (Body.orig a) hmem
  have hform : l.formPerm z = Body.orig a := by
    rw [List.formPerm_apply_mem_eq_next hl_nodup z hzmem, hnext]
  have hzmap : z ∈ c.members.map Body.orig := by
    exact List.mem_reverse.mp (by simpa [l] using hzmem)
  rcases List.mem_map.mp hzmap with ⟨b, hb, hbz⟩
  refine ⟨b, hb, ?_, ?_⟩
  · intro hba
    subst b
    have hfix : cyclePerm c (Body.orig a) = Body.orig a := by
      rw [cyclePerm, cyclePermAux_eq_formPerm_reverse]
      simpa [l, hbz] using hform
    exact cyclePerm_ne_of_mem c a ha hfix
  · rw [cyclePerm, cyclePermAux_eq_formPerm_reverse]
    simpa [l, hbz] using hform

omit [Fintype α] in
private theorem cyclePerm_image_member
    (c : Cycle α) (a : α) (ha : a ∈ c.members) :
    ∃ b ∈ c.members, b ≠ a ∧ cyclePerm c (Body.orig a) = Body.orig b := by
  let l : List (Body α) := c.members.map Body.orig
  have hl_nodup : l.Nodup := by
    dsimp [l]
    simpa using
      (c.nodup.map (show Function.Injective Body.orig from fun _ _ h => Body.orig.inj h))
  have hmem : Body.orig a ∈ l := by
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  let z : Body α := l.prev (Body.orig a) hmem
  have hzmem : z ∈ l := by
    exact List.prev_mem (l := l) (x := Body.orig a) hmem
  have hnext : l.reverse.next (Body.orig a) (List.mem_reverse.mpr hmem) = z := by
    simpa [z] using List.next_reverse_eq_prev l hl_nodup (Body.orig a) hmem
  have hform : l.reverse.formPerm (Body.orig a) = z := by
    rw [List.formPerm_apply_mem_eq_next (List.nodup_reverse.mpr hl_nodup) (Body.orig a)
      (List.mem_reverse.mpr hmem), hnext]
  rcases List.mem_map.mp hzmem with ⟨b, hb, hbz⟩
  refine ⟨b, hb, ?_, ?_⟩
  · intro hba
    subst b
    have hfix : cyclePerm c (Body.orig a) = Body.orig a := by
      rw [cyclePerm, cyclePermAux_eq_formPerm_reverse]
      simpa [l, hbz] using hform
    exact cyclePerm_ne_of_mem c a ha hfix
  · rw [cyclePerm, cyclePermAux_eq_formPerm_reverse]
    simpa [l, hbz] using hform

omit [Fintype α] in
theorem cyclePerm_eq_liftPerm_membersReverseFormPerm (c : Cycle α) :
    cyclePerm c = liftPerm c.members.reverse.formPerm := by
  rw [cyclePerm, cyclePermAux_eq_formPerm_reverse]
  simpa [List.map_reverse] using (formPerm_map_orig c.members.reverse)

omit [Fintype α] in
private theorem cyclePerm_apply_orig_mem_membersReverse_eq_next
    (c : Cycle α) {a : α} (ha : a ∈ c.members.reverse) :
    cyclePerm c (Body.orig a) = Body.orig (c.members.reverse.next a ha) := by
  rw [cyclePerm_eq_liftPerm_membersReverseFormPerm]
  rw [liftPerm_apply_orig]
  exact congrArg Body.orig
    (List.formPerm_apply_mem_eq_next (List.nodup_reverse.2 c.nodup) a ha)

omit [Fintype α] in
private theorem cyclePerm_apply_orig_mem_members_eq_prev
    (c : Cycle α) {a : α} (ha : a ∈ c.members) :
    cyclePerm c (Body.orig a) = Body.orig (c.members.prev a ha) := by
  have hrev : a ∈ c.members.reverse := by
    simpa using List.mem_reverse.mpr ha
  rw [cyclePerm_apply_orig_mem_membersReverse_eq_next c hrev]
  congr
  simpa using (List.next_reverse_eq_prev c.members c.nodup a ha)

omit [Fintype α] in
/-- If `a` is not in any cycle in `cs`, `cycleProduct cs` fixes `Body.orig a`. -/
theorem cycleProduct_fix_of_not_mem (cs : List (Cycle α))
    (ha : ∀ c ∈ cs, a ∉ c.members) :
    cycleProduct cs (Body.orig a) = Body.orig a := by
  induction cs with
  | nil => simp
  | cons d ds ih =>
      rw [cycleProduct_cons, mul_apply]
      rw [ih (fun c hc => ha c (.tail _ hc))]
      exact cyclePerm_apply_orig_of_not_mem' d a (ha d (.head _))

set_option linter.unusedSectionVars false in
/-- `cycleProduct` of pairwise-disjoint cycles moves every member of every cycle. -/
theorem cycleProduct_ne_orig_of_mem (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (c : Cycle α) (hc : c ∈ cs) (a : α) (ha : a ∈ c.members) :
    cycleProduct cs (Body.orig a) ≠ Body.orig a := by
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
      rw [cycleProduct_cons, mul_apply]
      rcases List.mem_cons.mp hc with rfl | hc'
      · -- c is the head; remaining cycles fix a by disjointness
        rw [cycleProduct_fix_of_not_mem ds (fun e he hae =>
          (List.pairwise_cons.mp hcs).1 e he ha hae)]
        exact cyclePerm_ne_of_mem c a ha
      · -- c is in the tail; d fixes a
        have hda : a ∉ d.members := fun hda =>
          (List.pairwise_cons.mp hcs).1 c hc' hda ha
        have hmoves := ih (List.pairwise_cons.mp hcs).2 hc'
        intro heq
        apply hmoves
        have hda_fix := cyclePerm_apply_orig_of_not_mem' d a hda
        have : (cyclePerm d) (cycleProduct ds (Body.orig a)) = (cyclePerm d) (Body.orig a) := by
          rw [hda_fix]; exact heq
        exact (cyclePerm d).injective this

omit [Fintype α] in
private theorem cycleProduct_preimage_member
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (c : Cycle α) (hc : c ∈ cs) (a : α) (ha : a ∈ c.members) :
    ∃ b ∈ c.members, b ≠ a ∧ cycleProduct cs (Body.orig b) = Body.orig a := by
  induction cs with
  | nil =>
      simp at hc
  | cons d ds ih =>
      rcases List.mem_cons.mp hc with rfl | hc'
      · rcases cyclePerm_preimage_member c a ha with ⟨b, hb, hba, hpre⟩
        refine ⟨b, hb, hba, ?_⟩
        rw [cycleProduct_cons, mul_apply]
        rw [cycleProduct_fix_of_not_mem (cs := ds) (a := b)]
        · exact hpre
        · intro e he hbe
          exact (List.pairwise_cons.mp hcs).1 e he hb hbe
      · rcases ih (List.pairwise_cons.mp hcs).2 hc' with ⟨b, hb, hba, hpre⟩
        refine ⟨b, hb, hba, ?_⟩
        rw [cycleProduct_cons, mul_apply, hpre]
        apply cyclePerm_apply_orig_of_not_mem'
        intro hda
        exact (List.pairwise_cons.mp hcs).1 c hc' hda ha

omit [Fintype α] in
theorem cycleProduct_image_member
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (c : Cycle α) (hc : c ∈ cs) (a : α) (ha : a ∈ c.members) :
    ∃ b ∈ c.members, b ≠ a ∧ cycleProduct cs (Body.orig a) = Body.orig b := by
  induction cs with
  | nil =>
      simp at hc
  | cons d ds ih =>
      rcases List.mem_cons.mp hc with rfl | hc'
      · rcases cyclePerm_image_member c a ha with ⟨b, hb, hba, himg⟩
        refine ⟨b, hb, hba, ?_⟩
        rw [cycleProduct_cons, mul_apply]
        rw [cycleProduct_fix_of_not_mem (cs := ds) (a := a)]
        · exact himg
        · intro e he hae
          exact (List.pairwise_cons.mp hcs).1 e he ha hae
      · rcases ih (List.pairwise_cons.mp hcs).2 hc' with ⟨b, hb, hba, himg⟩
        refine ⟨b, hb, hba, ?_⟩
        rw [cycleProduct_cons, mul_apply, himg]
        apply cyclePerm_apply_orig_of_not_mem'
        intro hdb
        exact (List.pairwise_cons.mp hcs).1 c hc' hdb hb

omit [Fintype α] in
private theorem cycleProduct_apply_orig_mem_membersReverse_eq_next
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (c : Cycle α) (hc : c ∈ cs) {a : α} (ha : a ∈ c.members.reverse) :
    cycleProduct cs (Body.orig a) = Body.orig (c.members.reverse.next a ha) := by
  have ha' : a ∈ c.members := by simpa using List.mem_reverse.mp ha
  induction cs with
  | nil =>
      simp at hc
  | cons d ds ih =>
      rcases List.mem_cons.mp hc with rfl | hc'
      · rw [cycleProduct_cons, mul_apply]
        rw [cycleProduct_fix_of_not_mem (cs := ds) (a := a)]
        · exact cyclePerm_apply_orig_mem_membersReverse_eq_next c ha
        · intro e he hae
          exact (List.pairwise_cons.mp hcs).1 e he ha' hae
      · rw [cycleProduct_cons, mul_apply]
        have hda : a ∉ d.members := by
          intro hda
          exact (List.pairwise_cons.mp hcs).1 c hc' hda ha'
        rw [ih (List.pairwise_cons.mp hcs).2 hc']
        apply cyclePerm_apply_orig_of_not_mem'
        intro hdb
        have hnextmem : c.members.reverse.next a ha ∈ c.members := by
          simpa using List.mem_reverse.mp
            (List.next_mem (l := c.members.reverse) (x := a) ha)
        exact (List.pairwise_cons.mp hcs).1 c hc' hdb hnextmem

/-- Every element in any cycle must appear in at least one swap step. -/
theorem elem_must_appear_in_seq
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (c : Cycle α) (hc : c ∈ cs) (a : α) (ha : a ∈ c.members) :
    ∃ step ∈ seq.steps, Body.orig a ∈ [step.1, step.2] := by
  by_contra h
  push_neg at h
  -- If Body.orig a doesn't appear in any step, runScript fixes it
  have hfix : runScript seq.steps (Body.orig a) = Body.orig a := by
    apply runScript_apply_of_not_mem'
    intro step hstep
    specialize h step hstep
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
    exact h
  -- runScript = (cycleProduct cs)⁻¹ since runScript * cycleProduct = 1
  have hmoves := cycleProduct_ne_orig_of_mem cs hcs c hc a ha
  apply hmoves
  -- From undoes: runScript * π = 1, so π⁻¹ = runScript
  -- hfix says runScript (orig a) = orig a, so π⁻¹ (orig a) = orig a, so π (orig a) = orig a
  have hu := seq.undoes
  have h1 : ∀ z, runScript seq.steps (cycleProduct cs z) = z := by
    intro z; exact congr_fun (congr_arg (↑·) hu) z
  -- runScript fixes orig a, and runScript ∘ cycleProduct = id
  -- If cycleProduct (orig a) = w, then runScript w = orig a
  -- Also runScript (orig a) = orig a (by hfix)
  -- If w ≠ orig a, then runScript maps both w and orig a to orig a
  -- But runScript is a permutation (injective), so w = orig a
  by_contra hne
  have h2 := h1 (Body.orig a)
  -- h2 : runScript (cycleProduct (orig a)) = orig a
  -- hfix : runScript (orig a) = orig a
  -- But cycleProduct (orig a) ≠ orig a (by hne), so these are different inputs
  -- mapping to the same output, contradicting injectivity
  exact hne ((runScript seq.steps).injective (h2.trans hfix.symm))

/-- Extract the unique original element from a step (if any). -/
private def origOfStep (step : Body α × Body α) : Option α :=
  match step.1, step.2 with
  | Body.orig a, _ => some a
  | _, Body.orig a => some a
  | _, _ => none

omit [DecidableEq α] [Fintype α] in
/-- If `Body.orig a` is in a step that uses a helper, then `origOfStep` returns `some a`. -/
private theorem origOfStep_eq_of_mem_and_helper {step : Body α × Body α}
    (hhelper : UsesHelper step) {a : α} (ha : Body.orig a ∈ [step.1, step.2]) :
    origOfStep step = some a := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
  have : ∀ (p q : Body α), p = Body.orig a ∨ q = Body.orig a →
      UsesHelper (p, q) →
      (match p, q with
        | Body.orig a, _ => some a
        | _, Body.orig a => some a
        | _, _ => none) = some a := by
    intro p q hpq hh
    rcases hpq with hp | hq
    · subst hp; simp
    · subst hq
      cases p with
      | orig b =>
          simp only [UsesHelper] at hh
          rcases hh with h | h | h | h <;> exact absurd h (by simp)
      | x => simp
      | y => simp
  exact this step.1 step.2 (by rcases ha with h | h <;> [left; right] <;> exact h.symm) hhelper

omit [DecidableEq α] [Fintype α] in
theorem flatten_members_length :
    ∀ (cs : List (Cycle α)),
    ((cs.map Cycle.members).flatten).length = (cs.map fun c => c.members.length).sum
  | [] => by simp
  | c :: cs => by
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons]
      rw [flatten_members_length cs]

omit [DecidableEq α] [Fintype α] in
theorem flatten_members_nodup :
    ∀ (cs : List (Cycle α)), cs.Pairwise Cycle.Disjoint →
    ((cs.map Cycle.members).flatten).Nodup
  | [], _ => List.nodup_nil
  | c :: cs, hcs => by
      simp only [List.map_cons, List.flatten_cons]
      apply List.Nodup.append c.nodup (flatten_members_nodup cs (List.Pairwise.of_cons hcs))
      -- Prove disjointness: no element in c.members is in (cs.map members).flatten
      intro a hac hmem
      rw [List.mem_flatten] at hmem
      obtain ⟨l, hl, hal⟩ := hmem
      rw [List.mem_map] at hl
      obtain ⟨c', hc', rfl⟩ := hl
      exact (List.pairwise_cons.mp hcs).1 c' hc' hac hal

omit [DecidableEq α] [Fintype α] in
theorem mem_flatten_members_iff {cs : List (Cycle α)} {a : α} :
    a ∈ (cs.map Cycle.members).flatten ↔ ∃ c ∈ cs, a ∈ c.members := by
  simp only [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨l, ⟨c, hc, rfl⟩, hal⟩; exact ⟨c, hc, hal⟩
  · rintro ⟨c, hc, hal⟩; exact ⟨c.members, ⟨c, hc, rfl⟩, hal⟩

/-- Layer 0: the number of swaps is at least the total number of elements. -/
theorem repair_length_ge_entries
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs)) :
    (cs.map fun c => c.members.length).sum ≤ seq.steps.length := by
  rw [← flatten_members_length cs]
  calc ((cs.map Cycle.members).flatten).length
      ≤ (seq.steps.filterMap origOfStep).length := by
        apply List.Subperm.length_le
        apply List.subperm_of_subset (flatten_members_nodup cs hcs)
        intro a ha
        rw [mem_flatten_members_iff] at ha
        obtain ⟨c, hc, hac⟩ := ha
        rw [List.mem_filterMap]
        obtain ⟨step, hstep, hmem⟩ := elem_must_appear_in_seq cs hcs seq c hc a hac
        exact ⟨step, hstep, origOfStep_eq_of_mem_and_helper
          (seq.helper_constraint step hstep) hmem⟩
    _ ≤ seq.steps.length := List.length_filterMap_le _ _

-- ═══════════════════════════════════════════════
-- Section 3b: Helper-fixing lemmas
-- ═══════════════════════════════════════════════

omit [Fintype α] in
private theorem cyclePermAux_fix_x (first : α) (rest : List α) :
    cyclePermAux first rest Body.x = Body.x := by
  induction rest generalizing first with
  | nil => simp [cyclePermAux]
  | cons a rest ih =>
    simp only [cyclePermAux, Perm.mul_apply]
    have : Equiv.swap (Body.orig a) (Body.orig first) (Body.x : Body α) = Body.x :=
      Equiv.swap_apply_of_ne_of_ne (fun h => Body.noConfusion h) (fun h => Body.noConfusion h)
    rw [this, ih]

omit [Fintype α] in
private theorem cyclePermAux_fix_y (first : α) (rest : List α) :
    cyclePermAux first rest Body.y = Body.y := by
  induction rest generalizing first with
  | nil => simp [cyclePermAux]
  | cons a rest ih =>
    simp only [cyclePermAux, Perm.mul_apply]
    have : Equiv.swap (Body.orig a) (Body.orig first) (Body.y : Body α) = Body.y :=
      Equiv.swap_apply_of_ne_of_ne (fun h => Body.noConfusion h) (fun h => Body.noConfusion h)
    rw [this, ih]

set_option linter.unusedSectionVars false in
theorem cyclePerm_fix_x (c : Cycle α) : cyclePerm c Body.x = Body.x :=
  cyclePermAux_fix_x c.first c.tail

set_option linter.unusedSectionVars false in
theorem cyclePerm_fix_y (c : Cycle α) : cyclePerm c Body.y = Body.y :=
  cyclePermAux_fix_y c.first c.tail

theorem cycleProduct_fix_x (cs : List (Cycle α)) : cycleProduct cs Body.x = Body.x := by
  induction cs with
  | nil => simp [cycleProduct]
  | cons c cs ih => simp [cycleProduct, Perm.mul_apply, cyclePerm_fix_x, ih]

theorem cycleProduct_fix_y (cs : List (Cycle α)) : cycleProduct cs Body.y = Body.y := by
  induction cs with
  | nil => simp [cycleProduct]
  | cons c cs ih => simp [cycleProduct, Perm.mul_apply, cyclePerm_fix_y, ih]

theorem runScript_fix_x (cs : List (Cycle α)) (seq : RepairSeq (cycleProduct cs)) :
    runScript seq.steps Body.x = Body.x := by
  have h := seq.undoes
  rw [mul_eq_one_iff_eq_inv] at h
  rw [h]
  calc (cycleProduct cs)⁻¹ Body.x
      = (cycleProduct cs)⁻¹ (cycleProduct cs Body.x) := by rw [cycleProduct_fix_x]
    _ = Body.x := Perm.inv_apply_self _ _

theorem runScript_fix_y (cs : List (Cycle α)) (seq : RepairSeq (cycleProduct cs)) :
    runScript seq.steps Body.y = Body.y := by
  have h := seq.undoes
  rw [mul_eq_one_iff_eq_inv] at h
  rw [h]
  calc (cycleProduct cs)⁻¹ Body.y
      = (cycleProduct cs)⁻¹ (cycleProduct cs Body.y) := by rw [cycleProduct_fix_y]
    _ = Body.y := Perm.inv_apply_self _ _

-- ═══════════════════════════════════════════════
-- Section 3c: Star transposition (gap argument lemmas)
-- ═══════════════════════════════════════════════

omit [Fintype α] in
/-- runScript of x-orig swaps fixes Body.orig b if b is not an element of any step. -/
private theorem runScript_x_fixes_non_member (steps : List (Body α × Body α))
    (b : α)
    (hform : ∀ s ∈ steps, ∃ a, (s = (Body.x, Body.orig a) ∨ s = (Body.orig a, Body.x)) ∧ a ≠ b) :
    runScript steps (Body.orig b : Body α) = Body.orig b := by
  induction steps with
  | nil => simp [runScript]
  | cons s rest ih =>
    simp only [runScript, Perm.mul_apply]
    have ⟨a, ha, hab⟩ := hform s (List.mem_cons.mpr (Or.inl rfl))
    have ih' := ih (fun s' hs' => hform s' (List.mem_cons.mpr (Or.inr hs')))
    -- After simp: goal is runScript rest (swap s.1 s.2 (Body.orig b)) = Body.orig b
    -- swap(s.1, s.2)(Body.orig b) = Body.orig b when a ≠ b
    have hswap_fix : Equiv.swap s.1 s.2 (Body.orig b : Body α) = Body.orig b := by
      rcases ha with rfl | rfl
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => Body.noConfusion h
        · exact fun h => Body.noConfusion h (fun h => (hab h.symm).elim)
      · rw [Equiv.swap_comm, Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => Body.noConfusion h
        · exact fun h => Body.noConfusion h (fun h => (hab h.symm).elim)
    rw [hswap_fix, ih']

omit [DecidableEq α] [Fintype α] in
/-- Head element ≠ rest elements when stepPairs are nodup. -/
private theorem head_ne_rest_elem (b : α) (rest : List (Body α × Body α))
    (s : Body α × Body α)
    (hs : s = (Body.x, Body.orig b) ∨ s = (Body.orig b, Body.x))
    (hnodup : (List.map stepPair (s :: rest)).Nodup)
    (s' : Body α × Body α) (hs' : s' ∈ rest)
    (c : α) (hc : s' = (Body.x, Body.orig c) ∨ s' = (Body.orig c, Body.x)) :
    b ≠ c := by
  intro heq; subst heq
  have h1 : stepPair s = stepPair s' := by
    rcases hs with rfl | rfl <;> rcases hc with rfl | rfl <;> simp [stepPair]
  have hmem : stepPair s ∈ (List.map stepPair rest) := by
    rw [h1]; exact List.mem_map.mpr ⟨s', hs', rfl⟩
  exact (List.nodup_cons.mp hnodup).1 hmem

set_option linter.unusedSectionVars false in
/-- A nonempty list of x-orig swaps (with distinct pairs) does NOT fix Body.x.
    (Star transposition identity: the first swap sends x to orig(b), and all
    subsequent swaps fix orig(b) since they involve different elements.) -/
theorem x_only_swaps_ne_x (steps : List (Body α × Body α))
    (hne : steps ≠ [])
    (hform : ∀ s ∈ steps, ∃ a, s = (Body.x, Body.orig a) ∨ s = (Body.orig a, Body.x))
    (hnodup : (steps.map stepPair).Nodup) :
    runScript steps (Body.x : Body α) ≠ Body.x := by
  match steps, hne with
  | s :: rest, _ =>
    obtain ⟨b, hb⟩ := hform s (List.mem_cons.mpr (Or.inl rfl))
    simp only [runScript, Perm.mul_apply]
    have hswap : Equiv.swap s.1 s.2 Body.x = Body.orig b := by
      rcases hb with rfl | rfl
      · exact Equiv.swap_apply_left _ _
      · rw [Equiv.swap_comm]; exact Equiv.swap_apply_left _ _
    rw [hswap]
    have hfix : runScript rest (Body.orig b : Body α) = Body.orig b := by
      apply runScript_x_fixes_non_member
      intro s' hs'
      obtain ⟨c, hc⟩ := hform s' (List.mem_cons.mpr (Or.inr hs'))
      exact ⟨c, hc, (head_ne_rest_elem b rest s hb hnodup s' hs' c hc).symm⟩
    rw [hfix]
    exact fun h => Body.noConfusion h

omit [Fintype α] in
private theorem runScript_y_fixes_non_member (steps : List (Body α × Body α))
    (b : α)
    (hform : ∀ s ∈ steps, ∃ a, (s = (Body.y, Body.orig a) ∨ s = (Body.orig a, Body.y)) ∧ a ≠ b) :
    runScript steps (Body.orig b : Body α) = Body.orig b := by
  induction steps with
  | nil => simp [runScript]
  | cons s rest ih =>
    simp only [runScript, Perm.mul_apply]
    have ⟨a, ha, hab⟩ := hform s (List.mem_cons.mpr (Or.inl rfl))
    have ih' := ih (fun s' hs' => hform s' (List.mem_cons.mpr (Or.inr hs')))
    have hswap_fix : Equiv.swap s.1 s.2 (Body.orig b : Body α) = Body.orig b := by
      rcases ha with rfl | rfl
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => Body.noConfusion h
        · exact fun h => Body.noConfusion h (fun h => (hab h.symm).elim)
      · rw [Equiv.swap_comm, Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => Body.noConfusion h
        · exact fun h => Body.noConfusion h (fun h => (hab h.symm).elim)
    rw [hswap_fix, ih']

omit [DecidableEq α] [Fintype α] in
private theorem head_ne_rest_elem_y (b : α) (rest : List (Body α × Body α))
    (s : Body α × Body α)
    (hs : s = (Body.y, Body.orig b) ∨ s = (Body.orig b, Body.y))
    (hnodup : (List.map stepPair (s :: rest)).Nodup)
    (s' : Body α × Body α) (hs' : s' ∈ rest)
    (c : α) (hc : s' = (Body.y, Body.orig c) ∨ s' = (Body.orig c, Body.y)) :
    b ≠ c := by
  intro heq; subst heq
  have h1 : stepPair s = stepPair s' := by
    rcases hs with rfl | rfl <;> rcases hc with rfl | rfl <;> simp [stepPair]
  have hmem : stepPair s ∈ (List.map stepPair rest) := by
    rw [h1]
    exact List.mem_map.mpr ⟨s', hs', rfl⟩
  exact (List.nodup_cons.mp hnodup).1 hmem

set_option linter.unusedSectionVars false in
/-- A nonempty list of y-orig swaps (with distinct pairs) does NOT fix Body.y. -/
theorem y_only_swaps_ne_y (steps : List (Body α × Body α))
    (hne : steps ≠ [])
    (hform : ∀ s ∈ steps, ∃ a, s = (Body.y, Body.orig a) ∨ s = (Body.orig a, Body.y))
    (hnodup : (steps.map stepPair).Nodup) :
    runScript steps (Body.y : Body α) ≠ Body.y := by
  match steps, hne with
  | s :: rest, _ =>
    obtain ⟨b, hb⟩ := hform s (List.mem_cons.mpr (Or.inl rfl))
    simp only [runScript, Perm.mul_apply]
    have hswap : Equiv.swap s.1 s.2 Body.y = Body.orig b := by
      rcases hb with rfl | rfl
      · exact Equiv.swap_apply_left _ _
      · rw [Equiv.swap_comm]
        exact Equiv.swap_apply_left _ _
    rw [hswap]
    have hfix : runScript rest (Body.orig b : Body α) = Body.orig b := by
      apply runScript_y_fixes_non_member
      intro s' hs'
      obtain ⟨c, hc⟩ := hform s' (List.mem_cons.mpr (Or.inr hs'))
      exact ⟨c, hc, (head_ne_rest_elem_y b rest s hb hnodup s' hs' c hc).symm⟩
    rw [hfix]
    exact fun h => Body.noConfusion h

omit [Fintype α] in
theorem mem_xEntries_iff {seq : RepairSeq π} {a : α} :
    a ∈ seq.xEntries ↔
      ∃ step ∈ seq.steps, step = (Body.x, Body.orig a) ∨ step = (Body.orig a, Body.x) := by
  constructor
  · intro ha
    rw [RepairSeq.xEntries, List.mem_filterMap] at ha
    rcases ha with ⟨step, hstep, hsome⟩
    rcases step with ⟨u, v⟩
    cases u with
    | orig b =>
        cases v with
        | orig c => cases hsome
        | x =>
            cases hsome
            exact ⟨(Body.orig a, Body.x), hstep, Or.inr rfl⟩
        | y => cases hsome
    | x =>
        cases v with
        | orig b =>
            cases hsome
            exact ⟨(Body.x, Body.orig a), hstep, Or.inl rfl⟩
        | x => cases hsome
        | y => cases hsome
    | y =>
        cases v with
        | orig b => cases hsome
        | x => cases hsome
        | y => cases hsome
  · rintro ⟨step, hstep, hform⟩
    rw [RepairSeq.xEntries, List.mem_filterMap]
    exact ⟨step, hstep, by rcases hform with rfl | rfl <;> rfl⟩

omit [Fintype α] in
theorem mem_yEntries_iff {seq : RepairSeq π} {a : α} :
    a ∈ seq.yEntries ↔
      ∃ step ∈ seq.steps, step = (Body.y, Body.orig a) ∨ step = (Body.orig a, Body.y) := by
  constructor
  · intro ha
    rw [RepairSeq.yEntries, List.mem_filterMap] at ha
    rcases ha with ⟨step, hstep, hsome⟩
    rcases step with ⟨u, v⟩
    cases u with
    | orig b =>
        cases v with
        | orig c => cases hsome
        | x => cases hsome
        | y =>
            cases hsome
            exact ⟨(Body.orig a, Body.y), hstep, Or.inr rfl⟩
    | x =>
        cases v with
        | orig b => cases hsome
        | x => cases hsome
        | y => cases hsome
    | y =>
        cases v with
        | orig b =>
            cases hsome
            exact ⟨(Body.y, Body.orig a), hstep, Or.inl rfl⟩
        | x => cases hsome
        | y => cases hsome
  · rintro ⟨step, hstep, hform⟩
    rw [RepairSeq.yEntries, List.mem_filterMap]
    exact ⟨step, hstep, by rcases hform with rfl | rfl <;> rfl⟩

def XStepFor (a : α) (step : Body α × Body α) : Prop :=
  step = (Body.x, Body.orig a) ∨ step = (Body.orig a, Body.x)

def YStepFor (a : α) (step : Body α × Body α) : Prop :=
  step = (Body.y, Body.orig a) ∨ step = (Body.orig a, Body.y)

omit [DecidableEq α] [Fintype α] in
private theorem step_eq_of_mem_of_stepPair_eq
    {steps : List (Body α × Body α)}
    (hnd : (steps.map stepPair).Nodup)
    {s t : Body α × Body α}
    (hs : s ∈ steps) (ht : t ∈ steps)
    (hpair : stepPair s = stepPair t) :
    s = t := by
  revert s t
  induction steps with
  | nil =>
      intro s t hs
      cases hs
  | cons u us ih =>
      intro s t hs ht hpair
      rcases List.mem_cons.mp hs with hs | hs
      · subst s
        rcases List.mem_cons.mp ht with ht | ht
        · subst t
          rfl
        · have hmemt : stepPair t ∈ us.map stepPair := by
            exact List.mem_map.mpr ⟨t, ht, rfl⟩
          have hmem : stepPair u ∈ us.map stepPair := by
            simpa [hpair] using hmemt
          exact False.elim ((List.nodup_cons.mp hnd).1 hmem)
      · rcases List.mem_cons.mp ht with ht | ht
        · subst t
          have hmems : stepPair s ∈ us.map stepPair := by
            exact List.mem_map.mpr ⟨s, hs, rfl⟩
          have hmem : stepPair u ∈ us.map stepPair := by
            simpa [hpair] using hmems
          exact False.elim ((List.nodup_cons.mp hnd).1 hmem)
        · exact ih (List.nodup_cons.mp hnd).2 hs ht hpair

omit [Fintype α] in
theorem unique_xStepFor
    (seq : RepairSeq π)
    {a : α} {s t : Body α × Body α}
    (hs : s ∈ seq.steps) (ht : t ∈ seq.steps)
    (hsa : XStepFor a s) (hta : XStepFor a t) :
    s = t := by
  have hpair : stepPair s = stepPair t := by
    rcases hsa with rfl | rfl <;> rcases hta with rfl | rfl <;> simp [stepPair]
  exact step_eq_of_mem_of_stepPair_eq seq.distinct_pairs hs ht hpair

omit [Fintype α] in
theorem unique_yStepFor
    (seq : RepairSeq π)
    {a : α} {s t : Body α × Body α}
    (hs : s ∈ seq.steps) (ht : t ∈ seq.steps)
    (hsa : YStepFor a s) (hta : YStepFor a t) :
    s = t := by
  have hpair : stepPair s = stepPair t := by
    rcases hsa with rfl | rfl <;> rcases hta with rfl | rfl <;> simp [stepPair]
  exact step_eq_of_mem_of_stepPair_eq seq.distinct_pairs hs ht hpair

omit [Fintype α] in
private theorem existsUnique_xStep_of_mem_xEntries
    (seq : RepairSeq π) {a : α} (ha : a ∈ seq.xEntries) :
    ∃! step, step ∈ seq.steps ∧ XStepFor a step := by
  rcases (mem_xEntries_iff).1 ha with ⟨step, hstep, hform⟩
  refine ⟨step, ⟨hstep, hform⟩, ?_⟩
  intro t ht
  exact unique_xStepFor seq ht.1 hstep ht.2 hform

omit [Fintype α] in
private theorem existsUnique_yStep_of_mem_yEntries
    (seq : RepairSeq π) {a : α} (ha : a ∈ seq.yEntries) :
    ∃! step, step ∈ seq.steps ∧ YStepFor a step := by
  rcases (mem_yEntries_iff).1 ha with ⟨step, hstep, hform⟩
  refine ⟨step, ⟨hstep, hform⟩, ?_⟩
  intro t ht
  exact unique_yStepFor seq ht.1 hstep ht.2 hform

noncomputable def xStepOf (seq : RepairSeq π) (a : α) (ha : a ∈ seq.xEntries) :
    Body α × Body α :=
  Classical.choose (existsUnique_xStep_of_mem_xEntries seq ha)

omit [Fintype α] in
theorem xStepOf_mem (seq : RepairSeq π) (a : α) (ha : a ∈ seq.xEntries) :
    xStepOf seq a ha ∈ seq.steps := by
  exact (Classical.choose_spec (existsUnique_xStep_of_mem_xEntries seq ha)).1.1

omit [Fintype α] in
theorem xStepOf_spec (seq : RepairSeq π) (a : α) (ha : a ∈ seq.xEntries) :
    XStepFor a (xStepOf seq a ha) := by
  exact (Classical.choose_spec (existsUnique_xStep_of_mem_xEntries seq ha)).1.2

noncomputable def yStepOf (seq : RepairSeq π) (a : α) (ha : a ∈ seq.yEntries) :
    Body α × Body α :=
  Classical.choose (existsUnique_yStep_of_mem_yEntries seq ha)

omit [Fintype α] in
theorem yStepOf_mem (seq : RepairSeq π) (a : α) (ha : a ∈ seq.yEntries) :
    yStepOf seq a ha ∈ seq.steps := by
  exact (Classical.choose_spec (existsUnique_yStep_of_mem_yEntries seq ha)).1.1

omit [Fintype α] in
theorem yStepOf_spec (seq : RepairSeq π) (a : α) (ha : a ∈ seq.yEntries) :
    YStepFor a (yStepOf seq a ha) := by
  exact (Classical.choose_spec (existsUnique_yStep_of_mem_yEntries seq ha)).1.2

omit [DecidableEq α] [Fintype α] in
theorem step_form_of_helper_and_orig_mem {step : Body α × Body α}
    (hhelper : UsesHelper step) {a : α} (ha : Body.orig a ∈ [step.1, step.2]) :
    step = (Body.x, Body.orig a) ∨ step = (Body.orig a, Body.x) ∨
      step = (Body.y, Body.orig a) ∨ step = (Body.orig a, Body.y) := by
  rcases step with ⟨u, v⟩
  simp only [UsesHelper] at hhelper
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
  cases u <;> cases v <;> simp at hhelper ha ⊢
  all_goals simp [ha]

omit [Fintype α] in
theorem step_is_xStep_or_yStep_of_no_helperSwap
    (seq : RepairSeq π)
    (hnoXY : ¬ seq.hasHelperSwap)
    {step : Body α × Body α}
    (hstep : step ∈ seq.steps) :
    (∃ a, XStepFor a step) ∨ (∃ a, YStepFor a step) := by
  rcases step with ⟨u, v⟩
  have hhelper := seq.helper_constraint (u, v) hstep
  have hne := seq.nontrivial (u, v) hstep
  cases u with
  | orig a =>
      cases v with
      | orig b =>
          simp [UsesHelper] at hhelper
      | x =>
          exact Or.inl ⟨a, Or.inr rfl⟩
      | y =>
          exact Or.inr ⟨a, Or.inr rfl⟩
  | x =>
      cases v with
      | orig a =>
          exact Or.inl ⟨a, Or.inl rfl⟩
      | x =>
          exact False.elim (hne rfl)
      | y =>
          have : (Body.x, Body.y) ∉ seq.steps := by
            intro h
            exact hnoXY (Or.inl h)
          exact False.elim (this hstep)
  | y =>
      cases v with
      | orig a =>
          exact Or.inr ⟨a, Or.inl rfl⟩
      | x =>
          have : (Body.y, Body.x) ∉ seq.steps := by
            intro h
            exact hnoXY (Or.inr h)
          exact False.elim (this hstep)
      | y =>
          exact False.elim (hne rfl)

omit [Fintype α] in
theorem step_avoids_y_of_no_helperSwap_of_not_yStep
    (seq : RepairSeq π)
    (hnoXY : ¬ seq.hasHelperSwap)
    {step : Body α × Body α}
    (hstep : step ∈ seq.steps)
    (hnot : ∀ a, ¬ YStepFor a step) :
    Body.y ≠ step.1 ∧ Body.y ≠ step.2 := by
  rcases step_is_xStep_or_yStep_of_no_helperSwap seq hnoXY hstep with
    ⟨a, hx⟩ | ⟨a, hy⟩
  · rcases hx with rfl | rfl <;> simp
  · exact False.elim (hnot a hy)

omit [DecidableEq α] [Fintype α] in
theorem helper_step_mentions_eq {step : Body α × Body α}
    (hhelper : UsesHelper step)
    {a b : α}
    (ha : Body.orig a ∈ [step.1, step.2])
    (hb : Body.orig b ∈ [step.1, step.2]) :
    a = b := by
  have hform := step_form_of_helper_and_orig_mem hhelper ha
  rcases hform with rfl | rfl | rfl | rfl
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with hbx | hba
    · cases hbx
    · exact (Body.orig.inj hba).symm
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with hba | hbx
    · exact (Body.orig.inj hba).symm
    · cases hbx
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with hby | hba
    · cases hby
    · exact (Body.orig.inj hba).symm
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with hba | hby
    · exact (Body.orig.inj hba).symm
    · cases hby

omit [Fintype α] in
private theorem step_mentions_unique_of_not_double
    (seq : RepairSeq π) {a : α}
    (hnot : ¬ (a ∈ seq.xEntries ∧ a ∈ seq.yEntries))
    {s t : Body α × Body α}
    (hs : s ∈ seq.steps) (ht : t ∈ seq.steps)
    (hsa : Body.orig a ∈ [s.1, s.2]) (hta : Body.orig a ∈ [t.1, t.2]) :
    s = t := by
  have hsform := step_form_of_helper_and_orig_mem (seq.helper_constraint s hs) hsa
  have htform := step_form_of_helper_and_orig_mem (seq.helper_constraint t ht) hta
  have hsxy : XStepFor a s ∨ YStepFor a s := by
    rcases hsform with hsx | hsx | hsy | hsy
    · exact Or.inl (Or.inl hsx)
    · exact Or.inl (Or.inr hsx)
    · exact Or.inr (Or.inl hsy)
    · exact Or.inr (Or.inr hsy)
  have htxy : XStepFor a t ∨ YStepFor a t := by
    rcases htform with htx | htx | hty | hty
    · exact Or.inl (Or.inl htx)
    · exact Or.inl (Or.inr htx)
    · exact Or.inr (Or.inl hty)
    · exact Or.inr (Or.inr hty)
  rcases hsxy with hsx | hsy <;> rcases htxy with htx | hty
  · exact unique_xStepFor seq hs ht hsx htx
  · exfalso
    exact hnot ⟨(mem_xEntries_iff).2 ⟨s, hs, hsx⟩, (mem_yEntries_iff).2 ⟨t, ht, hty⟩⟩
  · exfalso
    exact hnot ⟨(mem_xEntries_iff).2 ⟨t, ht, htx⟩, (mem_yEntries_iff).2 ⟨s, hs, hsy⟩⟩
  · exact unique_yStepFor seq hs ht hsy hty

omit [DecidableEq α] [Fintype α] in
theorem step_not_mem_prefix_of_split
    {steps pre suf : List (Body α × Body α)} {step : Body α × Body α}
    (hsplit : steps = pre ++ step :: suf)
    (hnd : (steps.map stepPair).Nodup) :
    step ∉ pre := by
  intro hmem
  have hnd' : (pre.map stepPair ++ stepPair step :: suf.map stepPair).Nodup := by
    simpa [hsplit, List.map_append]
      using hnd
  have hdisj : List.Disjoint (pre.map stepPair) (stepPair step :: suf.map stepPair) :=
    (List.nodup_append'.1 hnd').2.2
  have hpairmem : stepPair step ∈ pre.map stepPair := by
    exact List.mem_map.mpr ⟨step, hmem, rfl⟩
  exact hdisj hpairmem (by simp)

omit [DecidableEq α] [Fintype α] in
theorem step_not_mem_suffix_of_split
    {steps pre suf : List (Body α × Body α)} {step : Body α × Body α}
    (hsplit : steps = pre ++ step :: suf)
    (hnd : (steps.map stepPair).Nodup) :
    step ∉ suf := by
  intro hmem
  have hnd' : (pre.map stepPair ++ stepPair step :: suf.map stepPair).Nodup := by
    simpa [hsplit, List.map_append]
      using hnd
  have htailnd : (stepPair step :: suf.map stepPair).Nodup :=
    (List.nodup_append'.1 hnd').2.1
  have hpairmem : stepPair step ∈ suf.map stepPair := by
    exact List.mem_map.mpr ⟨step, hmem, rfl⟩
  exact (List.nodup_cons.mp htailnd).1 hpairmem

abbrev stepIdx (step : Body α × Body α) (steps : List (Body α × Body α)) : Nat :=
  @List.idxOf (Body α × Body α) instBEqOfDecidableEq step steps

omit [Fintype α] in
theorem idxOf_eq_length_pre_of_split
    {steps pre suf : List (Body α × Body α)} {step : Body α × Body α}
    (hsplit : steps = pre ++ step :: suf)
    (hnot : step ∉ pre) :
    stepIdx step steps = pre.length := by
  calc
    stepIdx step steps = pre.length + stepIdx step (step :: suf) := by
      simpa [hsplit] using
        (List.idxOf_append_of_notMem (l₁ := pre) (l₂ := step :: suf) hnot)
    _ = pre.length := by simp

omit [Fintype α] in
theorem idxOf_eq_idxOf_pre_of_mem_pre_split
    {steps pre suf : List (Body α × Body α)} {step target : Body α × Body α}
    (hsplit : steps = pre ++ step :: suf)
    (htarget : target ∈ pre) :
    stepIdx target steps = stepIdx target pre := by
  simpa [hsplit] using
    (List.idxOf_append_of_mem (l₁ := pre) (l₂ := step :: suf) htarget)

omit [Fintype α] in
theorem idxOf_eq_length_pre_succ_add_idxOf_of_mem_suf_split
    {steps pre suf : List (Body α × Body α)} {step target : Body α × Body α}
    (hsplit : steps = pre ++ step :: suf)
    (_htarget : target ∈ suf)
    (hnotpre : target ∉ pre)
    (hne : target ≠ step) :
    stepIdx target steps = pre.length + 1 + stepIdx target suf := by
  have hnot : target ∉ pre ++ [step] := by
    simp [hnotpre, hne]
  calc
    stepIdx target steps = (pre ++ [step]).length + stepIdx target suf := by
      simpa [hsplit, List.append_assoc] using
        (List.idxOf_append_of_notMem (l₁ := pre ++ [step]) (l₂ := suf) hnot)
    _ = pre.length + 1 + stepIdx target suf := by
      simp

omit [Fintype α] in
theorem stepIdx_lt_length_of_mem
    {steps : List (Body α × Body α)} {step : Body α × Body α}
    (h : step ∈ steps) :
    stepIdx step steps < steps.length := by
  unfold stepIdx
  induction steps with
  | nil =>
      cases h
  | cons x xs ih =>
      by_cases hx : x = step
      · subst hx
        simp
      · rw [List.idxOf_cons_ne _ hx]
        have htail : step ∈ xs := by
          rcases List.mem_cons.mp h with hEq | htail
          · exact False.elim (hx hEq.symm)
          · exact htail
        exact Nat.succ_lt_succ (ih htail)

omit [DecidableEq α] [Fintype α] in
theorem xEntries_yEntries_length_le_steps_length :
    ∀ steps : List (Body α × Body α),
      (steps.filterMap fun
          | (Body.x, Body.orig a) => some a
          | (Body.orig a, Body.x) => some a
          | _ => none).length +
        (steps.filterMap fun
          | (Body.y, Body.orig a) => some a
          | (Body.orig a, Body.y) => some a
          | _ => none).length ≤ steps.length
  | [] => by simp
  | step :: steps => by
      have ih := xEntries_yEntries_length_le_steps_length steps
      rcases step with ⟨u, v⟩
      cases u <;> cases v <;> simp
      all_goals omega

omit [DecidableEq α] [Fintype α] in
theorem xEntries_yEntries_length_lt_steps_length_of_helperSwap :
    ∀ steps : List (Body α × Body α),
      ((Body.x, Body.y) ∈ steps ∨ (Body.y, Body.x) ∈ steps) →
        (steps.filterMap fun
            | (Body.x, Body.orig a) => some a
            | (Body.orig a, Body.x) => some a
            | _ => none).length +
          (steps.filterMap fun
            | (Body.y, Body.orig a) => some a
            | (Body.orig a, Body.y) => some a
            | _ => none).length < steps.length
  | [], h => by
      simp at h
  | step :: steps, h => by
      rcases step with ⟨u, v⟩
      rcases h with hxy | hyx
      · rcases List.mem_cons.mp hxy with hhead | htail
        · cases hhead
          exact Nat.lt_succ_of_le (xEntries_yEntries_length_le_steps_length steps)
        · have hlt := xEntries_yEntries_length_lt_steps_length_of_helperSwap steps (Or.inl htail)
          cases u <;> cases v <;> simp at hlt ⊢ <;> omega
      · rcases List.mem_cons.mp hyx with hhead | htail
        · cases hhead
          exact Nat.lt_succ_of_le (xEntries_yEntries_length_le_steps_length steps)
        · have hlt := xEntries_yEntries_length_lt_steps_length_of_helperSwap steps (Or.inr htail)
          cases u <;> cases v <;> simp at hlt ⊢ <;> omega

omit [Fintype α] in
theorem cycle_count_le_inter_card
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (X Y : Finset α)
    (hxy : ∀ c ∈ cs, ∃ a ∈ c.members, a ∈ X ∧ a ∈ Y) :
    cs.length ≤ (X ∩ Y).card := by
  induction cs generalizing X Y with
  | nil => simp
  | cons c cs ih =>
      rcases List.pairwise_cons.mp hcs with ⟨hhead, htail⟩
      rcases hxy c (.head _) with ⟨a, ha_mem, haX, haY⟩
      have htailXY : ∀ c' ∈ cs, ∃ b ∈ c'.members, b ∈ X.erase a ∧ b ∈ Y.erase a := by
        intro c' hc'
        rcases hxy c' (.tail _ hc') with ⟨b, hb_mem, hbX, hbY⟩
        have hba : b ≠ a := by
          intro hba
          subst hba
          exact hhead c' hc' ha_mem hb_mem
        exact ⟨b, hb_mem, by simp [hbX, hba], by simp [hbY, hba]⟩
      have ih' := ih htail (X.erase a) (Y.erase a) htailXY
      have haXY : a ∈ X ∩ Y := by simp [haX, haY]
      have herase :
          X.erase a ∩ Y.erase a = (X ∩ Y).erase a := by
        ext z
        simp [and_left_comm, eq_comm]
      calc
        (c :: cs).length = cs.length + 1 := by simp
        _ ≤ (X.erase a ∩ Y.erase a).card + 1 := by omega
        _ = ((X ∩ Y).erase a).card + 1 := by rw [herase]
        _ = (X ∩ Y).card := by
              simpa [Nat.add_comm] using (Finset.card_erase_add_one haXY)

abbrev RepairSeq.xEntrySet (seq : RepairSeq π) : Finset α := seq.xEntries.toFinset

abbrev RepairSeq.yEntrySet (seq : RepairSeq π) : Finset α := seq.yEntries.toFinset

abbrev RepairSeq.entrySet (seq : RepairSeq π) : Finset α := seq.xEntrySet ∪ seq.yEntrySet

abbrev RepairSeq.doubleEntrySet (seq : RepairSeq π) : Finset α := seq.xEntrySet ∩ seq.yEntrySet

omit [Fintype α] in
theorem mem_doubleEntrySet_iff {seq : RepairSeq π} {a : α} :
    a ∈ seq.doubleEntrySet ↔ a ∈ seq.xEntries ∧ a ∈ seq.yEntries := by
  simp [RepairSeq.doubleEntrySet, RepairSeq.xEntrySet, RepairSeq.yEntrySet]

omit [DecidableEq α] [Fintype α] in
theorem cycle_member_ne_of_pairwise
    {cs : List (Cycle α)} (hcs : cs.Pairwise Cycle.Disjoint)
    {c d : Cycle α} (hc : c ∈ cs) (hd : d ∈ cs) (hcd : c ≠ d)
    {a b : α} (ha : a ∈ c.members) (hb : b ∈ d.members) :
    a ≠ b := by
  intro hab
  induction cs generalizing c d a b with
  | nil =>
      cases hc
  | cons e es ih =>
      rcases List.mem_cons.mp hc with rfl | hc'
      · rcases List.mem_cons.mp hd with hde | hd'
        · exact hcd hde.symm
        · exact (List.pairwise_cons.mp hcs).1 d hd' ha (hab ▸ hb)
      · rcases List.mem_cons.mp hd with hde | hd'
        · subst d
          exact (List.pairwise_cons.mp hcs).1 c hc' (hab ▸ hb) ha
        · exact ih (List.pairwise_cons.mp hcs).2 hc' hd' hcd ha hb hab

theorem exists_split_rightmost {β : Type*} (p : β → Prop) [DecidablePred p] :
    ∀ l : List β, (∃ x ∈ l, p x) →
      ∃ pre x suf, l = pre ++ x :: suf ∧ p x ∧ ∀ y ∈ suf, ¬ p y
  | [], h => by
      rcases h with ⟨x, hx, _⟩
      cases hx
  | x :: xs, h => by
      by_cases htail : ∃ y ∈ xs, p y
      · rcases exists_split_rightmost (p := p) xs htail with
          ⟨pre, y, suf, hsplit, hy, hsuf⟩
        exact ⟨x :: pre, y, suf, by simp [hsplit], hy, hsuf⟩
      · have hx : p x := by
          rcases h with ⟨y, hy, hpy⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hpy
          · exact False.elim (htail ⟨y, hy, hpy⟩)
        exact ⟨[], x, xs, by simp, hx, by
          intro y hy hpy
          exact htail ⟨y, hy, hpy⟩⟩

theorem exists_split_leftmost {β : Type*} (p : β → Prop) [DecidablePred p] :
    ∀ l : List β, (∃ x ∈ l, p x) →
      ∃ pre x suf, l = pre ++ x :: suf ∧ p x ∧ ∀ y ∈ pre, ¬ p y
  | [], h => by
      rcases h with ⟨x, hx, _⟩
      cases hx
  | x :: xs, h => by
      by_cases hx : p x
      · exact ⟨[], x, xs, by simp, hx, by
          intro y hy
          cases hy⟩
      · rcases exists_split_leftmost (p := p) xs (by
          rcases h with ⟨y, hy, hpy⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact False.elim (hx hpy)
          · exact ⟨y, hy, hpy⟩) with ⟨pre, y, suf, hsplit, hy, hpre⟩
        exact ⟨x :: pre, y, suf, by simp [hsplit], hy, by
          intro z hz hpz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hx hpz
          · exact hpre z hz hpz⟩

theorem exists_split_of_mem {β : Type*} :
    ∀ (l : List β) {x : β}, x ∈ l → ∃ pre suf, l = pre ++ x :: suf
  | [], _, h => by cases h
  | y :: ys, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨[], ys, by simp⟩
      · rcases exists_split_of_mem ys h' with ⟨pre, suf, hsplit⟩
        exact ⟨y :: pre, suf, by simp [hsplit]⟩

omit [Fintype α] in
theorem exists_split_two_of_lt_idx
    {steps : List (Body α × Body α)} {step₁ step₂ : Body α × Body α}
    (hnd : (steps.map stepPair).Nodup)
    (h₁ : step₁ ∈ steps) (h₂ : step₂ ∈ steps)
    (hneq : step₁ ≠ step₂)
    (hlt : stepIdx step₁ steps < stepIdx step₂ steps) :
    ∃ pre mid suf, steps = pre ++ step₁ :: mid ++ step₂ :: suf := by
  rcases exists_split_of_mem steps h₁ with ⟨pre, suf, hsplit⟩
  have h₂_not_pre : step₂ ∉ pre := by
    intro hmem
    have hidx₂_pre :
        stepIdx step₂ steps = stepIdx step₂ pre := by
      simpa using idxOf_eq_idxOf_pre_of_mem_pre_split hsplit hmem
    have hidx₂_lt :
        stepIdx step₂ steps < pre.length := by
      rw [hidx₂_pre]
      exact stepIdx_lt_length_of_mem hmem
    have hidx₁ :
        stepIdx step₁ steps = pre.length := by
      simpa using idxOf_eq_length_pre_of_split hsplit
        (step_not_mem_prefix_of_split hsplit hnd)
    omega
  have h₂_in_suf : step₂ ∈ suf := by
    rw [hsplit] at h₂
    rcases List.mem_append.mp h₂ with hmem | hmem
    · exact False.elim (h₂_not_pre hmem)
    · rcases List.mem_cons.mp hmem with hEq | hsuf
      · exact False.elim (hneq hEq.symm)
      · exact hsuf
  rcases exists_split_of_mem suf h₂_in_suf with ⟨mid, suf', hsuf⟩
  exact ⟨pre, mid, suf', by simp [hsplit, hsuf]⟩

private def StepMentionsCycle (c : Cycle α) (step : Body α × Body α) : Prop :=
  ∃ a ∈ c.members, Body.orig a ∈ [step.1, step.2]

theorem exists_rightmost_cycle_step
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (c : Cycle α) (hc : c ∈ cs) :
    ∃ pre step suf a,
      seq.steps = pre ++ step :: suf ∧
      a ∈ c.members ∧ Body.orig a ∈ [step.1, step.2] ∧
      ∀ s ∈ suf, ∀ b ∈ c.members, Body.orig b ∉ [s.1, s.2] := by
  classical
  obtain ⟨step, hstep, horig⟩ :=
    elem_must_appear_in_seq cs hcs seq c hc c.first (by simp [Cycle.members])
  have hex : ∃ s ∈ seq.steps, StepMentionsCycle c s := by
    exact ⟨step, hstep, c.first, by simp [Cycle.members], horig⟩
  rcases exists_split_rightmost (p := StepMentionsCycle c) seq.steps hex with
    ⟨pre, step, suf, hsplit, hmention, hsuf⟩
  rcases hmention with ⟨a, ha_mem, ha_step⟩
  exact ⟨pre, step, suf, a, hsplit, ha_mem, ha_step, by
    intro s hs b hb hmem
    exact hsuf s hs ⟨b, hb, hmem⟩⟩

theorem exists_leftmost_cycle_step
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (c : Cycle α) (hc : c ∈ cs) :
    ∃ pre step suf a,
      seq.steps = pre ++ step :: suf ∧
      a ∈ c.members ∧ Body.orig a ∈ [step.1, step.2] ∧
      ∀ s ∈ pre, ∀ b ∈ c.members, Body.orig b ∉ [s.1, s.2] := by
  classical
  obtain ⟨step, hstep, horig⟩ :=
    elem_must_appear_in_seq cs hcs seq c hc c.first (by simp [Cycle.members])
  have hex : ∃ s ∈ seq.steps, StepMentionsCycle c s := by
    exact ⟨step, hstep, c.first, by simp [Cycle.members], horig⟩
  rcases exists_split_leftmost (p := StepMentionsCycle c) seq.steps hex with
    ⟨pre, step, suf, hsplit, hmention, hpre⟩
  rcases hmention with ⟨a, ha_mem, ha_step⟩
  exact ⟨pre, step, suf, a, hsplit, ha_mem, ha_step, by
    intro s hs b hb hmem
    exact hpre s hs ⟨b, hb, hmem⟩⟩

omit [Fintype α] in
private theorem runScript_fixes_cycle_of_no_mentions
    (steps : List (Body α × Body α))
    (c : Cycle α)
    (hsteps : ∀ step ∈ steps, ∀ b ∈ c.members, Body.orig b ∉ [step.1, step.2]) :
    ∀ b ∈ c.members, runScript steps (Body.orig b) = Body.orig b := by
  intro b hb
  apply runScript_apply_of_not_mem'
  intro step hstep
  have h := hsteps step hstep b hb
  simpa [eq_comm] using h

omit [Fintype α] in
private theorem runScript_apply_not_mem_cycle_of_fixes
    (steps : List (Body α × Body α))
    (c : Cycle α)
    (hfix : ∀ b ∈ c.members, runScript steps (Body.orig b) = Body.orig b)
    {z : Body α}
    (hz : ∀ b ∈ c.members, z ≠ Body.orig b) :
    ∀ b ∈ c.members, runScript steps z ≠ Body.orig b := by
  intro b hb hEq
  have hfixb := hfix b hb
  have : z = Body.orig b := by
    apply (runScript steps).injective
    rw [hEq, hfixb]
  exact hz b hb this

omit [Fintype α] in
theorem leftmost_cycle_step_double
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (c : Cycle α) (hc : c ∈ cs)
    {pre suf : List (Body α × Body α)} {step : Body α × Body α} {a : α}
    (hsplit : seq.steps = pre ++ step :: suf)
    (ha_mem : a ∈ c.members)
    (ha_step : Body.orig a ∈ [step.1, step.2])
    (hpre : ∀ s ∈ pre, ∀ b ∈ c.members, Body.orig b ∉ [s.1, s.2]) :
    a ∈ seq.xEntries ∧ a ∈ seq.yEntries := by
  by_contra hnot
  obtain ⟨b, hb, hba, himg⟩ := cycleProduct_image_member cs hcs c hc a ha_mem
  have hstep_mem : step ∈ seq.steps := by
    rw [hsplit]
    simp
  have hstep_not_mem_suf : step ∉ suf :=
    step_not_mem_suffix_of_split hsplit seq.distinct_pairs
  have hsuf_no_a : ∀ s ∈ suf, Body.orig a ∉ [s.1, s.2] := by
    intro s hs hsMention
    have hs_seq : s ∈ seq.steps := by
      rw [hsplit]
      exact List.mem_append.mpr <| Or.inr <| List.mem_cons_of_mem _ hs
    have hEq : s = step :=
      step_mentions_unique_of_not_double seq hnot hs_seq hstep_mem hsMention ha_step
    exact hstep_not_mem_suf (by simpa [hEq] using hs)
  have hpre_fix_b : runScript pre (Body.orig b) = Body.orig b := by
    exact runScript_fixes_cycle_of_no_mentions pre c hpre b hb
  have hsuf_fix_a : runScript suf (Body.orig a) = Body.orig a := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hsuf_no_a s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hundo : ∀ z, runScript seq.steps (cycleProduct cs z) = z := by
    intro z
    exact congr_fun (congr_arg (↑·) seq.undoes) z
  have hrun : runScript seq.steps (Body.orig b) = Body.orig a := by
    simpa [himg] using hundo (Body.orig a)
  have hswap : Equiv.swap step.1 step.2 (Body.orig b) = Body.orig a := by
    rw [hsplit, runScript_append_apply, runScript_cons, mul_apply, hpre_fix_b] at hrun
    apply (runScript suf).injective
    rw [hsuf_fix_a]
    exact hrun
  have hstep_form :=
    step_form_of_helper_and_orig_mem (seq.helper_constraint step hstep_mem) ha_step
  rcases hstep_form with rfl | rfl | rfl | rfl
  · have hfix : Equiv.swap Body.x (Body.orig a) (Body.orig b) = Body.orig b := by
      apply Equiv.swap_apply_of_ne_of_ne <;> simp [hba]
    rw [hfix] at hswap
    exact hba (Body.orig.inj hswap)
  · have hfix : Equiv.swap (Body.orig a) Body.x (Body.orig b) = Body.orig b := by
      apply Equiv.swap_apply_of_ne_of_ne <;> simp [hba]
    rw [hfix] at hswap
    exact hba (Body.orig.inj hswap)
  · have hfix : Equiv.swap Body.y (Body.orig a) (Body.orig b) = Body.orig b := by
      apply Equiv.swap_apply_of_ne_of_ne <;> simp [hba]
    rw [hfix] at hswap
    exact hba (Body.orig.inj hswap)
  · have hfix : Equiv.swap (Body.orig a) Body.y (Body.orig b) = Body.orig b := by
      apply Equiv.swap_apply_of_ne_of_ne <;> simp [hba]
    rw [hfix] at hswap
    exact hba (Body.orig.inj hswap)

omit [Fintype α] in
theorem rightmost_cycle_step_double
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (c : Cycle α) (hc : c ∈ cs)
    {pre suf : List (Body α × Body α)} {step : Body α × Body α} {a : α}
    (hsplit : seq.steps = pre ++ step :: suf)
    (ha_mem : a ∈ c.members)
    (ha_step : Body.orig a ∈ [step.1, step.2])
    (hsuf : ∀ s ∈ suf, ∀ b ∈ c.members, Body.orig b ∉ [s.1, s.2]) :
    a ∈ seq.xEntries ∧ a ∈ seq.yEntries := by
  by_contra hnot
  obtain ⟨b, hb, hba, hpreimage⟩ := cycleProduct_preimage_member cs hcs c hc a ha_mem
  have hstep_mem : step ∈ seq.steps := by
    rw [hsplit]
    simp
  have hstep_not_mem_pre : step ∉ pre :=
    step_not_mem_prefix_of_split hsplit seq.distinct_pairs
  have hpre_no_a : ∀ s ∈ pre, Body.orig a ∉ [s.1, s.2] := by
    intro s hs hsMention
    have hs_seq : s ∈ seq.steps := by
      rw [hsplit]
      exact List.mem_append.mpr <| Or.inl hs
    have hEq : s = step :=
      step_mentions_unique_of_not_double seq hnot hs_seq hstep_mem hsMention ha_step
    exact hstep_not_mem_pre (by simpa [hEq] using hs)
  have hpre_fix_a : runScript pre (Body.orig a) = Body.orig a := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hpre_no_a s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hsuf_fix : ∀ d ∈ c.members, runScript suf (Body.orig d) = Body.orig d := by
    apply runScript_fixes_cycle_of_no_mentions suf c
    intro s hs d hd
    exact hsuf s hs d hd
  have hundo : ∀ z, runScript seq.steps (cycleProduct cs z) = z := by
    intro z
    exact congr_fun (congr_arg (↑·) seq.undoes) z
  have hrun : runScript seq.steps (Body.orig a) = Body.orig b := by
    simpa [hpreimage] using hundo (Body.orig b)
  have hswap : Equiv.swap step.1 step.2 (Body.orig a) = Body.orig b := by
    rw [hsplit, runScript_append_apply, runScript_cons, mul_apply, hpre_fix_a] at hrun
    apply (runScript suf).injective
    rw [hsuf_fix b hb]
    exact hrun
  have hstep_form :=
    step_form_of_helper_and_orig_mem (seq.helper_constraint step hstep_mem) ha_step
  rcases hstep_form with rfl | rfl | rfl | rfl <;> simp at hswap


end Futurama
end Project
