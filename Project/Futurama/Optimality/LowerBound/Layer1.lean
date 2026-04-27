import Project.Futurama.CoreCycle
import Project.Futurama.CoreSchedule
import Project.Futurama.FiniteBridge
import Project.Futurama.ParameterizedFamily
import Project.Futurama.Optimality.RepairSeq
import Project.Futurama.Optimality.LowerBound.Layer0

/-!
# Optimality / LowerBound / Layer 1 — `t ≥ n + r` (cycle-double-counting)

Layer 1 strengthens Layer 0's `t ≥ n` to `t ≥ n + r` by showing every
cycle in the disjoint-cycle decomposition contributes at least one
"double entry" — an element appearing twice in the helper-containing
transposition list (once paired with `x`, once paired with `y`).
This is Evans–Huang–Nguyen's "doubling argument" plus the
`xy_split` / `minGapCycle` machinery used to handle the case where
the script intersperses both helpers.

This is the largest module of the development (~5000 LOC). The
internal lemma chain (`*_of_eq_case` / `*_of_xy_split` /
`*_of_minGap_xy`) is densely interconnected; the file is kept as a
single unit so the inductive arguments can refer freely to each
other without forward-declaration gymnastics.
-/

open Equiv Equiv.Perm

namespace Project
namespace Futurama

variable {α : Type*} [DecidableEq α] [Fintype α]
variable {π : Perm (Body α)}

-- Section 4: Layer 1 — t ≥ n + r
-- ═══════════════════════════════════════════════

/-- Each cycle must have at least one element appearing with both helpers.
    Proof (Evans–Huang–Nguyen, Theorem 1): Let A = c.members. Consider the
    rightmost (= last in seq.steps) element a ∈ A appearing in any step.
    The permutation cycleProduct maps orig(a) to orig(b) for some b ∈ A with
    b ≠ a. So runScript must send orig(b) to orig(a), meaning σ has a factor
    involving orig(a). Since a is rightmost in A, all subsequent steps involve
    only elements outside A. For σ to correctly route b → a, element a must
    appear with BOTH helpers x and y. (If a appeared with only one helper,
    say x, then σ could not simultaneously fix x and route all cycle members
    correctly, by the star-transposition cycle structure.) -/
theorem cycle_has_double_entry
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (c : Cycle α) (hc : c ∈ cs) :
    ∃ a ∈ c.members, a ∈ seq.xEntries ∧ a ∈ seq.yEntries := by
  classical
  rcases exists_rightmost_cycle_step cs hcs seq c hc with
    ⟨pre, step, suf, a, hsplit, ha_mem, ha_step, hsuf⟩
  have hdouble :=
    rightmost_cycle_step_double cs hcs seq c hc hsplit ha_mem ha_step hsuf
  exact ⟨a, ha_mem, hdouble.1, hdouble.2⟩

private theorem cycle_members_subset_entrySet
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs)) :
    ((cs.map Cycle.members).flatten).toFinset ⊆ seq.entrySet := by
  intro a ha
  have ha' : a ∈ (cs.map Cycle.members).flatten := by simpa using ha
  rw [mem_flatten_members_iff] at ha'
  rcases ha' with ⟨c, hc, hac⟩
  obtain ⟨step, hstep, hmem⟩ := elem_must_appear_in_seq cs hcs seq c hc a hac
  have hform := step_form_of_helper_and_orig_mem (seq.helper_constraint step hstep) hmem
  rcases hform with h | h | h | h
  · exact Finset.mem_union.mpr <| Or.inl <| by
      simpa [RepairSeq.xEntrySet] using ((mem_xEntries_iff).2 ⟨step, hstep, Or.inl h⟩)
  · exact Finset.mem_union.mpr <| Or.inl <| by
      simpa [RepairSeq.xEntrySet] using ((mem_xEntries_iff).2 ⟨step, hstep, Or.inr h⟩)
  · exact Finset.mem_union.mpr <| Or.inr <| by
      simpa [RepairSeq.yEntrySet] using ((mem_yEntries_iff).2 ⟨step, hstep, Or.inl h⟩)
  · exact Finset.mem_union.mpr <| Or.inr <| by
      simpa [RepairSeq.yEntrySet] using ((mem_yEntries_iff).2 ⟨step, hstep, Or.inr h⟩)

private theorem entrySet_card_ge_entries
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs)) :
    (cs.map fun c => c.members.length).sum ≤ seq.entrySet.card := by
  calc
    (cs.map fun c => c.members.length).sum = (((cs.map Cycle.members).flatten).toFinset).card := by
      rw [← flatten_members_length cs]
      exact (List.toFinset_card_of_nodup (flatten_members_nodup cs hcs)).symm
    _ ≤ seq.entrySet.card := Finset.card_le_card (cycle_members_subset_entrySet cs hcs seq)

private theorem doubleEntrySet_card_ge_cycles
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs)) :
    cs.length ≤ seq.doubleEntrySet.card := by
  apply cycle_count_le_inter_card cs hcs seq.xEntrySet seq.yEntrySet
  intro c hc
  rcases cycle_has_double_entry cs hcs seq c hc with ⟨a, ha_mem, hax, hay⟩
  exact ⟨a, ha_mem, by simpa [RepairSeq.xEntrySet] using hax,
    by simpa [RepairSeq.yEntrySet] using hay⟩

private theorem entries_length_ge_entries_add_cycles
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs)) :
    (cs.map fun c => c.members.length).sum + cs.length ≤
      seq.xEntries.length + seq.yEntries.length := by
  let X : Finset α := seq.xEntrySet
  let Y : Finset α := seq.yEntrySet
  have hunion :
      (cs.map fun c => c.members.length).sum ≤ (X ∪ Y).card := by
    simpa [X, Y, RepairSeq.entrySet] using entrySet_card_ge_entries cs hcs seq
  have hinter :
      cs.length ≤ (X ∩ Y).card := by
    simpa [X, Y, RepairSeq.doubleEntrySet] using doubleEntrySet_card_ge_cycles cs hcs seq
  calc
    (cs.map fun c => c.members.length).sum + cs.length
      ≤ (X ∪ Y).card + (X ∩ Y).card := by omega
    _ = X.card + Y.card := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (Finset.card_union_add_card_inter X Y)
    _ ≤ seq.xEntries.length + seq.yEntries.length := by
          exact Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)

/-- Layer 1: the number of swaps is at least n + r. -/
theorem repair_length_ge_entries_add_cycles
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs)) :
    (cs.map fun c => c.members.length).sum + cs.length ≤ seq.steps.length := by
  calc
    (cs.map fun c => c.members.length).sum + cs.length
      ≤ seq.xEntries.length + seq.yEntries.length :=
        entries_length_ge_entries_add_cycles cs hcs seq
    _ ≤ seq.steps.length := by
          simpa [RepairSeq.xEntries, RepairSeq.yEntries] using
            xEntries_yEntries_length_le_steps_length seq.steps

theorem not_hasHelperSwap_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length) :
    ¬ seq.hasHelperSwap := by
  intro hswap
  have hlt : seq.xEntries.length + seq.yEntries.length < seq.steps.length := by
    simpa [RepairSeq.hasHelperSwap, RepairSeq.xEntries, RepairSeq.yEntries] using
      xEntries_yEntries_length_lt_steps_length_of_helperSwap seq.steps hswap
  have hge : (cs.map fun c => c.members.length).sum + cs.length ≤
      seq.xEntries.length + seq.yEntries.length := by
    exact entries_length_ge_entries_add_cycles cs hcs seq
  omega

theorem doubleEntrySet_card_eq_cycles_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length) :
    seq.doubleEntrySet.card = cs.length := by
  let n := (cs.map fun c => c.members.length).sum
  let r := cs.length
  have hxy_eq : seq.xEntries.length + seq.yEntries.length = seq.steps.length := by
    have hge : n + r ≤ seq.xEntries.length + seq.yEntries.length := by
      simpa [n, r] using entries_length_ge_entries_add_cycles cs hcs seq
    have hle : seq.xEntries.length + seq.yEntries.length ≤ seq.steps.length := by
      simpa [RepairSeq.xEntries, RepairSeq.yEntries] using
        xEntries_yEntries_length_le_steps_length seq.steps
    omega
  have hunion_ge : n ≤ seq.entrySet.card := by
    simpa [n, RepairSeq.entrySet] using entrySet_card_ge_entries cs hcs seq
  have hinter_ge : r ≤ seq.doubleEntrySet.card := by
    simpa [r, RepairSeq.doubleEntrySet] using doubleEntrySet_card_ge_cycles cs hcs seq
  have hsum_le : seq.entrySet.card + seq.doubleEntrySet.card ≤ n + r := by
    calc
      seq.entrySet.card + seq.doubleEntrySet.card
        = seq.xEntrySet.card + seq.yEntrySet.card := by
            simpa [RepairSeq.entrySet, RepairSeq.doubleEntrySet, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using
              (Finset.card_union_add_card_inter seq.xEntrySet seq.yEntrySet)
      _ ≤ seq.xEntries.length + seq.yEntries.length := by
            exact Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
      _ = n + r := by omega
  have hentry_eq : seq.entrySet.card = n := by omega
  omega

private theorem entrySet_card_eq_entries_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length) :
    seq.entrySet.card = (cs.map fun c => c.members.length).sum := by
  let n := (cs.map fun c => c.members.length).sum
  let r := cs.length
  have hxy_eq : seq.xEntries.length + seq.yEntries.length = seq.steps.length := by
    have hge : n + r ≤ seq.xEntries.length + seq.yEntries.length := by
      simpa [n, r] using entries_length_ge_entries_add_cycles cs hcs seq
    have hle : seq.xEntries.length + seq.yEntries.length ≤ seq.steps.length := by
      simpa [RepairSeq.xEntries, RepairSeq.yEntries] using
        xEntries_yEntries_length_le_steps_length seq.steps
    omega
  have hinter_eq : seq.doubleEntrySet.card = r := by
    simpa [r] using doubleEntrySet_card_eq_cycles_of_eq_case cs hcs seq heq
  have hunion_ge : n ≤ seq.entrySet.card := by
    simpa [n, RepairSeq.entrySet] using entrySet_card_ge_entries cs hcs seq
  have hsum_le : seq.entrySet.card + seq.doubleEntrySet.card ≤ n + r := by
    calc
      seq.entrySet.card + seq.doubleEntrySet.card
        = seq.xEntrySet.card + seq.yEntrySet.card := by
            simpa [RepairSeq.entrySet, RepairSeq.doubleEntrySet, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using
              (Finset.card_union_add_card_inter seq.xEntrySet seq.yEntrySet)
      _ ≤ seq.xEntries.length + seq.yEntries.length := by
            exact Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
      _ = n + r := by omega
  omega

private theorem entrySet_eq_members_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length) :
    seq.entrySet = ((cs.map Cycle.members).flatten).toFinset := by
  have hsubset : ((cs.map Cycle.members).flatten).toFinset ⊆ seq.entrySet :=
    cycle_members_subset_entrySet cs hcs seq
  have hcard_members :
      (((cs.map Cycle.members).flatten).toFinset).card =
        (cs.map fun c => c.members.length).sum := by
    rw [← flatten_members_length cs]
    exact List.toFinset_card_of_nodup (flatten_members_nodup cs hcs)
  have hcard_entry :
      seq.entrySet.card = (cs.map fun c => c.members.length).sum :=
    entrySet_card_eq_entries_of_eq_case cs hcs seq heq
  apply Finset.Subset.antisymm
  · intro a ha
    by_contra hnot
    have hssub :
        ((cs.map Cycle.members).flatten).toFinset ⊂ seq.entrySet := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
      intro hEq
      exact hnot (hEq ▸ ha)
    have hlt := Finset.card_lt_card hssub
    rw [hcard_members, hcard_entry] at hlt
    exact Nat.lt_irrefl _ hlt
  · exact hsubset

private theorem orig_step_mem_members_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    {step : Body α × Body α} (hstep : step ∈ seq.steps) {a : α}
    (ha : YStepFor a step ∨ XStepFor a step) :
    a ∈ ((cs.map Cycle.members).flatten).toFinset := by
  have ha_entry : a ∈ seq.entrySet := by
    rcases ha with hy | hx
    · exact Finset.mem_union.mpr <| Or.inr <| by
        simpa [RepairSeq.yEntrySet] using ((mem_yEntries_iff).2 ⟨step, hstep, hy⟩)
    · exact Finset.mem_union.mpr <| Or.inl <| by
        simpa [RepairSeq.xEntrySet] using ((mem_xEntries_iff).2 ⟨step, hstep, hx⟩)
  rw [entrySet_eq_members_of_eq_case cs hcs seq heq] at ha_entry
  exact ha_entry

private theorem existsUnique_doubleEntry_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    ∃! a, a ∈ c.members ∧ a ∈ seq.xEntries ∧ a ∈ seq.yEntries := by
  obtain ⟨a, ha_mem, hax, hay⟩ := cycle_has_double_entry cs hcs seq c hc
  refine ⟨a, ⟨ha_mem, hax, hay⟩, ?_⟩
  intro b hb
  by_cases hab : b = a
  · exact hab
  · exfalso
    have ha_double : a ∈ seq.doubleEntrySet := by
      exact (mem_doubleEntrySet_iff).2 ⟨hax, hay⟩
    have hcountInter : cs.length ≤
        ((seq.doubleEntrySet.erase a) ∩ (seq.doubleEntrySet.erase a)).card := by
      apply cycle_count_le_inter_card cs hcs (seq.doubleEntrySet.erase a) (seq.doubleEntrySet.erase a)
      intro c' hc'
      by_cases hcc' : c' = c
      · subst hcc'
        have hb_double : b ∈ seq.doubleEntrySet := by
          exact (mem_doubleEntrySet_iff).2 ⟨hb.2.1, hb.2.2⟩
        exact ⟨b, hb.1, by simp [hb_double, hab], by simp [hb_double, hab]⟩
      · obtain ⟨d, hd_mem, hdx, hdy⟩ := cycle_has_double_entry cs hcs seq c' hc'
        have hda : d ≠ a := by
          exact cycle_member_ne_of_pairwise hcs hc' hc hcc' hd_mem ha_mem
        have hd_double : d ∈ seq.doubleEntrySet := by
          exact (mem_doubleEntrySet_iff).2 ⟨hdx, hdy⟩
        exact ⟨d, hd_mem, by simp [hd_double, hda], by simp [hd_double, hda]⟩
    have hcard : seq.doubleEntrySet.card = cs.length :=
      doubleEntrySet_card_eq_cycles_of_eq_case cs hcs seq heq
    have herase : (seq.doubleEntrySet.erase a).card = cs.length - 1 := by
      have hcardErase : (seq.doubleEntrySet.erase a).card + 1 = cs.length := by
        calc
          (seq.doubleEntrySet.erase a).card + 1 = seq.doubleEntrySet.card := by
            simpa [Nat.add_comm] using (Finset.card_erase_add_one ha_double)
          _ = cs.length := hcard
      omega
    have hlt : cs.length ≤ cs.length - 1 := by
      simpa [Finset.inter_self, herase] using hcountInter
    have hlenpos : 1 ≤ cs.length := List.length_pos_of_mem hc
    have hsucc : cs.length + 1 ≤ cs.length := by
      calc
        cs.length + 1 ≤ (cs.length - 1) + 1 := Nat.succ_le_succ hlt
        _ = cs.length := Nat.sub_add_cancel hlenpos
    exact Nat.not_succ_le_self _ hsucc

private noncomputable def doubleEntryOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) : α :=
  Classical.choose (existsUnique_doubleEntry_of_eq_case cs hcs seq heq c hc)

private theorem doubleEntryOf_eq_case_mem
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    doubleEntryOf_eq_case cs hcs seq heq c hc ∈ c.members := by
  exact (Classical.choose_spec (existsUnique_doubleEntry_of_eq_case cs hcs seq heq c hc)).1.1

private theorem doubleEntryOf_eq_case_mem_x
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    doubleEntryOf_eq_case cs hcs seq heq c hc ∈ seq.xEntries := by
  exact (Classical.choose_spec (existsUnique_doubleEntry_of_eq_case cs hcs seq heq c hc)).1.2.1

private theorem doubleEntryOf_eq_case_mem_y
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    doubleEntryOf_eq_case cs hcs seq heq c hc ∈ seq.yEntries := by
  exact (Classical.choose_spec (existsUnique_doubleEntry_of_eq_case cs hcs seq heq c hc)).1.2.2

private theorem eq_case_other_member_not_double
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {b : α} (hb_mem : b ∈ c.members)
    (hb_ne : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc) :
    ¬ (b ∈ seq.xEntries ∧ b ∈ seq.yEntries) := by
  intro hb_double
  have huniq := Classical.choose_spec (existsUnique_doubleEntry_of_eq_case cs hcs seq heq c hc)
  exact hb_ne (huniq.2 b ⟨hb_mem, hb_double.1, hb_double.2⟩)

private theorem leftmost_cycle_step_eq_doubleEntry_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre suf : List (Body α × Body α)} {step : Body α × Body α} {a : α}
    (hsplit : seq.steps = pre ++ step :: suf)
    (ha_mem : a ∈ c.members)
    (ha_step : Body.orig a ∈ [step.1, step.2])
    (hpre : ∀ s ∈ pre, ∀ b ∈ c.members, Body.orig b ∉ [s.1, s.2]) :
    a = doubleEntryOf_eq_case cs hcs seq heq c hc := by
  have hdouble :=
    leftmost_cycle_step_double cs hcs seq c hc hsplit ha_mem ha_step hpre
  exact (Classical.choose_spec
    (existsUnique_doubleEntry_of_eq_case cs hcs seq heq c hc)).2 a
      ⟨ha_mem, hdouble.1, hdouble.2⟩

private theorem rightmost_cycle_step_eq_doubleEntry_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre suf : List (Body α × Body α)} {step : Body α × Body α} {a : α}
    (hsplit : seq.steps = pre ++ step :: suf)
    (ha_mem : a ∈ c.members)
    (ha_step : Body.orig a ∈ [step.1, step.2])
    (hsuf : ∀ s ∈ suf, ∀ b ∈ c.members, Body.orig b ∉ [s.1, s.2]) :
    a = doubleEntryOf_eq_case cs hcs seq heq c hc := by
  have hdouble :=
    rightmost_cycle_step_double cs hcs seq c hc hsplit ha_mem ha_step hsuf
  exact (Classical.choose_spec
    (existsUnique_doubleEntry_of_eq_case cs hcs seq heq c hc)).2 a
      ⟨ha_mem, hdouble.1, hdouble.2⟩

private theorem exists_leftmost_doubleEntry_step_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    ∃ pre step suf,
      seq.steps = pre ++ step :: suf ∧
      Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∈ [step.1, step.2] ∧
      ∀ s ∈ pre, ∀ b ∈ c.members, Body.orig b ∉ [s.1, s.2] := by
  rcases exists_leftmost_cycle_step cs hcs seq c hc with
    ⟨pre, step, suf, a, hsplit, ha_mem, ha_step, hpre⟩
  have ha_eq :
      a = doubleEntryOf_eq_case cs hcs seq heq c hc :=
    leftmost_cycle_step_eq_doubleEntry_of_eq_case cs hcs seq heq c hc hsplit ha_mem ha_step hpre
  subst a
  exact ⟨pre, step, suf, hsplit, ha_step, hpre⟩

private theorem exists_rightmost_doubleEntry_step_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    ∃ pre step suf,
      seq.steps = pre ++ step :: suf ∧
      Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∈ [step.1, step.2] ∧
      ∀ s ∈ suf, ∀ b ∈ c.members, Body.orig b ∉ [s.1, s.2] := by
  rcases exists_rightmost_cycle_step cs hcs seq c hc with
    ⟨pre, step, suf, a, hsplit, ha_mem, ha_step, hsuf⟩
  have ha_eq :
      a = doubleEntryOf_eq_case cs hcs seq heq c hc :=
    rightmost_cycle_step_eq_doubleEntry_of_eq_case cs hcs seq heq c hc hsplit ha_mem ha_step hsuf
  subst a
  exact ⟨pre, step, suf, hsplit, ha_step, hsuf⟩

private theorem other_member_has_step_after_leftmost_doubleEntry_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {b : α} (hb_mem : b ∈ c.members)
    (hb_ne : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc) :
    ∃ pre step suf stepb,
      seq.steps = pre ++ step :: suf ∧
      Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∈ [step.1, step.2] ∧
      stepb ∈ suf ∧
      Body.orig b ∈ [stepb.1, stepb.2] := by
  rcases exists_leftmost_doubleEntry_step_of_eq_case cs hcs seq heq c hc with
    ⟨pre, step, suf, hsplit, hstep_mem, hpre⟩
  obtain ⟨stepb, hstepb_mem, hb_step⟩ := elem_must_appear_in_seq cs hcs seq c hc b hb_mem
  have hstep_not_pre : stepb ∉ pre := by
    intro hs
    exact hpre stepb hs b hb_mem hb_step
  have hstep_ne : stepb ≠ step := by
    intro hEq
    subst stepb
    have hstep_mem' : step ∈ seq.steps := by
      rw [hsplit]
      simp
    have hdouble_eq : b = doubleEntryOf_eq_case cs hcs seq heq c hc := by
      exact helper_step_mentions_eq (seq.helper_constraint step hstep_mem') hb_step hstep_mem
    exact hb_ne hdouble_eq
  have hstep_in_suf : stepb ∈ suf := by
    rw [hsplit] at hstepb_mem
    rcases List.mem_append.mp hstepb_mem with hs | hs
    · exact False.elim (hstep_not_pre hs)
    · rcases List.mem_cons.mp hs with hEq | hsuf
      · exact False.elim (hstep_ne hEq)
      · exact hsuf
  exact ⟨pre, step, suf, stepb, hsplit, hstep_mem, hstep_in_suf, hb_step⟩

private theorem other_member_has_step_before_rightmost_doubleEntry_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {b : α} (hb_mem : b ∈ c.members)
    (hb_ne : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc) :
    ∃ pre step suf stepb,
      seq.steps = pre ++ step :: suf ∧
      Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∈ [step.1, step.2] ∧
      stepb ∈ pre ∧
      Body.orig b ∈ [stepb.1, stepb.2] := by
  rcases exists_rightmost_doubleEntry_step_of_eq_case cs hcs seq heq c hc with
    ⟨pre, step, suf, hsplit, hstep_mem, hsuf⟩
  obtain ⟨stepb, hstepb_mem, hb_step⟩ := elem_must_appear_in_seq cs hcs seq c hc b hb_mem
  have hstep_not_suf : stepb ∉ suf := by
    intro hs
    exact hsuf stepb hs b hb_mem hb_step
  have hstep_ne : stepb ≠ step := by
    intro hEq
    subst stepb
    have hstep_mem' : step ∈ seq.steps := by
      rw [hsplit]
      simp
    have hdouble_eq : b = doubleEntryOf_eq_case cs hcs seq heq c hc := by
      exact helper_step_mentions_eq (seq.helper_constraint step hstep_mem') hb_step hstep_mem
    exact hb_ne hdouble_eq
  have hstep_in_pre : stepb ∈ pre := by
    rw [hsplit] at hstepb_mem
    rcases List.mem_append.mp hstepb_mem with hs | hs
    · exact hs
    · rcases List.mem_cons.mp hs with hEq | hsuf'
      · exact False.elim (hstep_ne hEq)
      · exact False.elim (hstep_not_suf hsuf')
  exact ⟨pre, step, suf, stepb, hsplit, hstep_mem, hstep_in_pre, hb_step⟩

noncomputable def xDoubleStepOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) : Body α × Body α :=
  xStepOf seq
    (doubleEntryOf_eq_case cs hcs seq heq c hc)
    (doubleEntryOf_eq_case_mem_x cs hcs seq heq c hc)

private theorem xDoubleStepOf_eq_case_mem
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    xDoubleStepOf_eq_case cs hcs seq heq c hc ∈ seq.steps := by
  exact xStepOf_mem seq
    (doubleEntryOf_eq_case cs hcs seq heq c hc)
    (doubleEntryOf_eq_case_mem_x cs hcs seq heq c hc)

private theorem xDoubleStepOf_eq_case_spec
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    XStepFor (doubleEntryOf_eq_case cs hcs seq heq c hc)
      (xDoubleStepOf_eq_case cs hcs seq heq c hc) := by
  exact xStepOf_spec seq
    (doubleEntryOf_eq_case cs hcs seq heq c hc)
    (doubleEntryOf_eq_case_mem_x cs hcs seq heq c hc)

noncomputable def yDoubleStepOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) : Body α × Body α :=
  yStepOf seq
    (doubleEntryOf_eq_case cs hcs seq heq c hc)
    (doubleEntryOf_eq_case_mem_y cs hcs seq heq c hc)

private theorem yDoubleStepOf_eq_case_mem
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    yDoubleStepOf_eq_case cs hcs seq heq c hc ∈ seq.steps := by
  exact yStepOf_mem seq
    (doubleEntryOf_eq_case cs hcs seq heq c hc)
    (doubleEntryOf_eq_case_mem_y cs hcs seq heq c hc)

private theorem yDoubleStepOf_eq_case_spec
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    YStepFor (doubleEntryOf_eq_case cs hcs seq heq c hc)
      (yDoubleStepOf_eq_case cs hcs seq heq c hc) := by
  exact yStepOf_spec seq
    (doubleEntryOf_eq_case cs hcs seq heq c hc)
    (doubleEntryOf_eq_case_mem_y cs hcs seq heq c hc)

private theorem swap_xDoubleStepOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    Equiv.swap (xDoubleStepOf_eq_case cs hcs seq heq c hc).1
        (xDoubleStepOf_eq_case cs hcs seq heq c hc).2 =
      Equiv.swap Body.x (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) := by
  rcases xDoubleStepOf_eq_case_spec cs hcs seq heq c hc with h | h
  · simp [h]
  · simpa [h] using
      (Equiv.swap_comm Body.x (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))).symm

private theorem swap_yDoubleStepOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    Equiv.swap (yDoubleStepOf_eq_case cs hcs seq heq c hc).1
        (yDoubleStepOf_eq_case cs hcs seq heq c hc).2 =
      Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) := by
  rcases yDoubleStepOf_eq_case_spec cs hcs seq heq c hc with h | h
  · simp [h]
  · simpa [h] using
      (Equiv.swap_comm Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))).symm

private theorem xDoubleStepOf_eq_case_mentions
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∈
      [(xDoubleStepOf_eq_case cs hcs seq heq c hc).1,
        (xDoubleStepOf_eq_case cs hcs seq heq c hc).2] := by
  rcases xDoubleStepOf_eq_case_spec cs hcs seq heq c hc with h | h <;> simp [h]

private theorem yDoubleStepOf_eq_case_mentions
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∈
      [(yDoubleStepOf_eq_case cs hcs seq heq c hc).1,
        (yDoubleStepOf_eq_case cs hcs seq heq c hc).2] := by
  rcases yDoubleStepOf_eq_case_spec cs hcs seq heq c hc with h | h <;> simp [h]

private theorem doubleEntryStep_eq_xDouble_or_yDouble_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {step : Body α × Body α}
    (hstep_mem : step ∈ seq.steps)
    (hstep_mentions :
      Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∈ [step.1, step.2]) :
    step = xDoubleStepOf_eq_case cs hcs seq heq c hc ∨
      step = yDoubleStepOf_eq_case cs hcs seq heq c hc := by
  have hform :=
    step_form_of_helper_and_orig_mem (seq.helper_constraint step hstep_mem) hstep_mentions
  rcases hform with hx | hx | hy | hy
  · left
    exact unique_xStepFor seq hstep_mem (xDoubleStepOf_eq_case_mem cs hcs seq heq c hc)
      (Or.inl hx) (xDoubleStepOf_eq_case_spec cs hcs seq heq c hc)
  · left
    exact unique_xStepFor seq hstep_mem (xDoubleStepOf_eq_case_mem cs hcs seq heq c hc)
      (Or.inr hx) (xDoubleStepOf_eq_case_spec cs hcs seq heq c hc)
  · right
    exact unique_yStepFor seq hstep_mem (yDoubleStepOf_eq_case_mem cs hcs seq heq c hc)
      (Or.inl hy) (yDoubleStepOf_eq_case_spec cs hcs seq heq c hc)
  · right
    exact unique_yStepFor seq hstep_mem (yDoubleStepOf_eq_case_mem cs hcs seq heq c hc)
      (Or.inr hy) (yDoubleStepOf_eq_case_spec cs hcs seq heq c hc)

private theorem xDoubleStep_ne_yDoubleStep_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    xDoubleStepOf_eq_case cs hcs seq heq c hc ≠
      yDoubleStepOf_eq_case cs hcs seq heq c hc := by
  intro h
  have hx := xDoubleStepOf_eq_case_spec cs hcs seq heq c hc
  have hy := yDoubleStepOf_eq_case_spec cs hcs seq heq c hc
  rcases hx with hx | hx <;> rcases hy with hy | hy
  all_goals
    rw [hx] at h
    rw [hy] at h
    simp at h

private noncomputable def xDoubleStepIdxOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) : Nat :=
  stepIdx (xDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps

private noncomputable def yDoubleStepIdxOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) : Nat :=
  stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps

theorem exists_ordered_doubleStep_split_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    (∃ pre mid suf,
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) ∨
    (∃ pre mid suf,
      seq.steps =
        pre ++ yDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) := by
  classical
  have hx_mem : xDoubleStepOf_eq_case cs hcs seq heq c hc ∈ seq.steps :=
    xDoubleStepOf_eq_case_mem cs hcs seq heq c hc
  have hy_mem : yDoubleStepOf_eq_case cs hcs seq heq c hc ∈ seq.steps :=
    yDoubleStepOf_eq_case_mem cs hcs seq heq c hc
  have hxy_ne :
      xDoubleStepOf_eq_case cs hcs seq heq c hc ≠
        yDoubleStepOf_eq_case cs hcs seq heq c hc :=
    xDoubleStep_ne_yDoubleStep_of_eq_case cs hcs seq heq c hc
  by_cases hlt :
      stepIdx (xDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps <
        stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps
  · rcases exists_split_two_of_lt_idx seq.distinct_pairs hx_mem hy_mem hxy_ne hlt with
      ⟨pre, mid, suf, hsplit⟩
    exact Or.inl ⟨pre, mid, suf, hsplit⟩
  · have hlt' :
        stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps <
          stepIdx (xDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps := by
      have hne :
          stepIdx (xDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps ≠
            stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps := by
        intro hEq
        exact hxy_ne ((List.idxOf_inj hx_mem hy_mem).1 hEq)
      omega
    rcases exists_split_two_of_lt_idx seq.distinct_pairs hy_mem hx_mem hxy_ne.symm hlt' with
      ⟨pre, mid, suf, hsplit⟩
    exact Or.inr ⟨pre, mid, suf, hsplit⟩

private noncomputable def gapOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) : Nat :=
  max
      (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
      (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) -
    min
      (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
      (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) - 1

private theorem leftmostDoubleStepIdx_eq_min_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre suf : List (Body α × Body α)} {step : Body α × Body α}
    (hsplit : seq.steps = pre ++ step :: suf)
    (hstep_mentions :
      Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∈ [step.1, step.2])
    (hpre : ∀ s ∈ pre, ∀ b ∈ c.members, Body.orig b ∉ [s.1, s.2]) :
    stepIdx step seq.steps =
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
        (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
  have hstep_mem : step ∈ seq.steps := by
    rw [hsplit]
    simp
  have hstep_not_pre := step_not_mem_prefix_of_split hsplit seq.distinct_pairs
  have hstep_eq :=
    doubleEntryStep_eq_xDouble_or_yDouble_of_eq_case cs hcs seq heq c hc hstep_mem hstep_mentions
  rcases hstep_eq with hstepx | hstepy
  · subst hstepx
    have hy_not_pre :
        yDoubleStepOf_eq_case cs hcs seq heq c hc ∉ pre := by
      intro hy
      exact hpre (yDoubleStepOf_eq_case cs hcs seq heq c hc) hy
        (doubleEntryOf_eq_case cs hcs seq heq c hc)
        (doubleEntryOf_eq_case_mem cs hcs seq heq c hc)
        (yDoubleStepOf_eq_case_mentions cs hcs seq heq c hc)
    have hy_in_suf :
        yDoubleStepOf_eq_case cs hcs seq heq c hc ∈ suf := by
      have hy_mem := yDoubleStepOf_eq_case_mem cs hcs seq heq c hc
      rw [hsplit] at hy_mem
      rcases List.mem_append.mp hy_mem with hy | hy
      · exact False.elim (hy_not_pre hy)
      · rcases List.mem_cons.mp hy with hyEq | hySuf
        · exact False.elim
            (xDoubleStep_ne_yDoubleStep_of_eq_case cs hcs seq heq c hc (by simpa using hyEq.symm))
        · exact hySuf
    have hidx_x :
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length := by
      unfold xDoubleStepIdxOf_eq_case
      simpa using idxOf_eq_length_pre_of_split hsplit hstep_not_pre
    have hidx_y :
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc =
          pre.length + 1 + stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) suf := by
      unfold yDoubleStepIdxOf_eq_case
      simpa using idxOf_eq_length_pre_succ_add_idxOf_of_mem_suf_split hsplit hy_in_suf hy_not_pre
        (xDoubleStep_ne_yDoubleStep_of_eq_case cs hcs seq heq c hc).symm
    have hlt :
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
          yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
      rw [hidx_x, hidx_y]
      omega
    calc
      stepIdx (xDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps = pre.length := by
        simpa [xDoubleStepIdxOf_eq_case] using hidx_x
      _ = min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
        rw [hidx_x, hidx_y]
        omega
  · subst hstepy
    have hx_not_pre :
        xDoubleStepOf_eq_case cs hcs seq heq c hc ∉ pre := by
      intro hx
      exact hpre (xDoubleStepOf_eq_case cs hcs seq heq c hc) hx
        (doubleEntryOf_eq_case cs hcs seq heq c hc)
        (doubleEntryOf_eq_case_mem cs hcs seq heq c hc)
        (xDoubleStepOf_eq_case_mentions cs hcs seq heq c hc)
    have hx_in_suf :
        xDoubleStepOf_eq_case cs hcs seq heq c hc ∈ suf := by
      have hx_mem := xDoubleStepOf_eq_case_mem cs hcs seq heq c hc
      rw [hsplit] at hx_mem
      rcases List.mem_append.mp hx_mem with hx | hx
      · exact False.elim (hx_not_pre hx)
      · rcases List.mem_cons.mp hx with hxEq | hxSuf
        · exact False.elim
            (xDoubleStep_ne_yDoubleStep_of_eq_case cs hcs seq heq c hc (by simpa using hxEq))
        · exact hxSuf
    have hidx_y :
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length := by
      unfold yDoubleStepIdxOf_eq_case
      simpa using idxOf_eq_length_pre_of_split hsplit hstep_not_pre
    have hidx_x :
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc =
          pre.length + 1 + stepIdx (xDoubleStepOf_eq_case cs hcs seq heq c hc) suf := by
      unfold xDoubleStepIdxOf_eq_case
      simpa using idxOf_eq_length_pre_succ_add_idxOf_of_mem_suf_split hsplit hx_in_suf hx_not_pre
        (xDoubleStep_ne_yDoubleStep_of_eq_case cs hcs seq heq c hc)
    have hlt :
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
          xDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
      rw [hidx_x, hidx_y]
      omega
    calc
      stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps = pre.length := by
        simpa [yDoubleStepIdxOf_eq_case] using hidx_y
      _ = min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
        rw [hidx_x, hidx_y]
        omega

private theorem rightmostDoubleStepIdx_eq_max_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre suf : List (Body α × Body α)} {step : Body α × Body α}
    (hsplit : seq.steps = pre ++ step :: suf)
    (hstep_mentions :
      Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∈ [step.1, step.2])
    (hsuf : ∀ s ∈ suf, ∀ b ∈ c.members, Body.orig b ∉ [s.1, s.2]) :
    stepIdx step seq.steps =
      max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
        (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
  have hstep_mem : step ∈ seq.steps := by
    rw [hsplit]
    simp
  have hstep_not_pre := step_not_mem_prefix_of_split hsplit seq.distinct_pairs
  have hstep_not_suf := step_not_mem_suffix_of_split hsplit seq.distinct_pairs
  have hstep_eq :=
    doubleEntryStep_eq_xDouble_or_yDouble_of_eq_case cs hcs seq heq c hc hstep_mem hstep_mentions
  rcases hstep_eq with hstepx | hstepy
  · subst hstepx
    have hy_not_suf :
        yDoubleStepOf_eq_case cs hcs seq heq c hc ∉ suf := by
      intro hy
      exact hsuf (yDoubleStepOf_eq_case cs hcs seq heq c hc) hy
        (doubleEntryOf_eq_case cs hcs seq heq c hc)
        (doubleEntryOf_eq_case_mem cs hcs seq heq c hc)
        (yDoubleStepOf_eq_case_mentions cs hcs seq heq c hc)
    have hy_in_pre :
        yDoubleStepOf_eq_case cs hcs seq heq c hc ∈ pre := by
      have hy_mem := yDoubleStepOf_eq_case_mem cs hcs seq heq c hc
      rw [hsplit] at hy_mem
      rcases List.mem_append.mp hy_mem with hy | hy
      · exact hy
      · rcases List.mem_cons.mp hy with hyEq | hySuf
        · exact False.elim
            (xDoubleStep_ne_yDoubleStep_of_eq_case cs hcs seq heq c hc (by simpa using hyEq.symm))
        · exact False.elim (hy_not_suf hySuf)
    have hidx_x :
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length := by
      unfold xDoubleStepIdxOf_eq_case
      simpa using idxOf_eq_length_pre_of_split hsplit hstep_not_pre
    have hidx_y :
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc =
          stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) pre := by
      unfold yDoubleStepIdxOf_eq_case
      simpa using idxOf_eq_idxOf_pre_of_mem_pre_split hsplit hy_in_pre
    have : stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) pre < pre.length := by
      exact stepIdx_lt_length_of_mem hy_in_pre
    have hlt :
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
          xDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
      rw [hidx_x, hidx_y]
      exact this
    calc
      stepIdx (xDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps = pre.length := by
        simpa [xDoubleStepIdxOf_eq_case] using hidx_x
      _ = max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
        rw [hidx_x, hidx_y]
        omega
  · subst hstepy
    have hx_not_suf :
        xDoubleStepOf_eq_case cs hcs seq heq c hc ∉ suf := by
      intro hx
      exact hsuf (xDoubleStepOf_eq_case cs hcs seq heq c hc) hx
        (doubleEntryOf_eq_case cs hcs seq heq c hc)
        (doubleEntryOf_eq_case_mem cs hcs seq heq c hc)
        (xDoubleStepOf_eq_case_mentions cs hcs seq heq c hc)
    have hx_in_pre :
        xDoubleStepOf_eq_case cs hcs seq heq c hc ∈ pre := by
      have hx_mem := xDoubleStepOf_eq_case_mem cs hcs seq heq c hc
      rw [hsplit] at hx_mem
      rcases List.mem_append.mp hx_mem with hx | hx
      · exact hx
      · rcases List.mem_cons.mp hx with hxEq | hxSuf
        · exact False.elim
            (xDoubleStep_ne_yDoubleStep_of_eq_case cs hcs seq heq c hc (by simpa using hxEq))
        · exact False.elim (hx_not_suf hxSuf)
    have hidx_y :
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length := by
      unfold yDoubleStepIdxOf_eq_case
      simpa using idxOf_eq_length_pre_of_split hsplit hstep_not_pre
    have hidx_x :
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc =
          stepIdx (xDoubleStepOf_eq_case cs hcs seq heq c hc) pre := by
      unfold xDoubleStepIdxOf_eq_case
      simpa using idxOf_eq_idxOf_pre_of_mem_pre_split hsplit hx_in_pre
    have : stepIdx (xDoubleStepOf_eq_case cs hcs seq heq c hc) pre < pre.length := by
      exact stepIdx_lt_length_of_mem hx_in_pre
    have hlt :
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
          yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
      rw [hidx_x, hidx_y]
      exact this
    calc
      stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps = pre.length := by
        simpa [yDoubleStepIdxOf_eq_case] using hidx_y
      _ = max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
        rw [hidx_x, hidx_y]
        omega

private theorem other_member_has_step_between_doubleSteps_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {b : α} (hb_mem : b ∈ c.members)
    (hb_ne : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc) :
    ∃ stepb ∈ seq.steps,
      Body.orig b ∈ [stepb.1, stepb.2] ∧
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) <
        stepIdx stepb seq.steps ∧
      stepIdx stepb seq.steps <
        max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
  obtain ⟨stepb, hstepb_mem, hb_step⟩ := elem_must_appear_in_seq cs hcs seq c hc b hb_mem
  rcases exists_leftmost_doubleEntry_step_of_eq_case cs hcs seq heq c hc with
    ⟨preL, stepL, sufL, hsplitL, hstepL_mentions, hpreL⟩
  have hstepb_not_preL : stepb ∉ preL := by
    intro hs
    exact hpreL stepb hs b hb_mem hb_step
  have hstepb_ne_stepL : stepb ≠ stepL := by
    intro hEq
    subst stepb
    have hstepL_mem : stepL ∈ seq.steps := by
      rw [hsplitL]
      simp
    have hb_eq : b = doubleEntryOf_eq_case cs hcs seq heq c hc := by
      exact helper_step_mentions_eq (seq.helper_constraint stepL hstepL_mem) hb_step hstepL_mentions
    exact hb_ne hb_eq
  have hstepb_in_sufL : stepb ∈ sufL := by
    rw [hsplitL] at hstepb_mem
    rcases List.mem_append.mp hstepb_mem with hs | hs
    · exact False.elim (hstepb_not_preL hs)
    · rcases List.mem_cons.mp hs with hEq | hsuf
      · exact False.elim (hstepb_ne_stepL hEq)
      · exact hsuf
  have hidx_left :
      stepIdx stepb seq.steps = preL.length + 1 + stepIdx stepb sufL := by
    simpa using
      idxOf_eq_length_pre_succ_add_idxOf_of_mem_suf_split hsplitL hstepb_in_sufL
        hstepb_not_preL hstepb_ne_stepL
  have hmin_left :
      stepIdx stepL seq.steps =
        min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
    exact leftmostDoubleStepIdx_eq_min_of_eq_case cs hcs seq heq c hc hsplitL hstepL_mentions hpreL
  have hgt :
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) <
        stepIdx stepb seq.steps := by
    rw [← hmin_left, hidx_left]
    have hidx_stepL : stepIdx stepL seq.steps = preL.length := by
      simpa using idxOf_eq_length_pre_of_split hsplitL (step_not_mem_prefix_of_split hsplitL seq.distinct_pairs)
    rw [hidx_stepL]
    omega
  rcases exists_rightmost_doubleEntry_step_of_eq_case cs hcs seq heq c hc with
    ⟨preR, stepR, sufR, hsplitR, hstepR_mentions, hsufR⟩
  have hstepb_not_sufR : stepb ∉ sufR := by
    intro hs
    exact hsufR stepb hs b hb_mem hb_step
  have hstepb_ne_stepR : stepb ≠ stepR := by
    intro hEq
    subst stepb
    have hstepR_mem : stepR ∈ seq.steps := by
      rw [hsplitR]
      simp
    have hb_eq : b = doubleEntryOf_eq_case cs hcs seq heq c hc := by
      exact helper_step_mentions_eq (seq.helper_constraint stepR hstepR_mem) hb_step hstepR_mentions
    exact hb_ne hb_eq
  have hstepb_in_preR : stepb ∈ preR := by
    rw [hsplitR] at hstepb_mem
    rcases List.mem_append.mp hstepb_mem with hs | hs
    · exact hs
    · rcases List.mem_cons.mp hs with hEq | hsuf
      · exact False.elim (hstepb_ne_stepR hEq)
      · exact False.elim (hstepb_not_sufR hsuf)
  have hidx_right :
      stepIdx stepb seq.steps = stepIdx stepb preR := by
    simpa using idxOf_eq_idxOf_pre_of_mem_pre_split hsplitR hstepb_in_preR
  have hmax_right :
      stepIdx stepR seq.steps =
        max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
    exact rightmostDoubleStepIdx_eq_max_of_eq_case cs hcs seq heq c hc hsplitR hstepR_mentions hsufR
  have hlt :
      stepIdx stepb seq.steps <
        max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
    rw [← hmax_right, hidx_right]
    have hidx_stepR : stepIdx stepR seq.steps = preR.length := by
      simpa using idxOf_eq_length_pre_of_split hsplitR (step_not_mem_prefix_of_split hsplitR seq.distinct_pairs)
    rw [hidx_stepR]
    exact stepIdx_lt_length_of_mem hstepb_in_preR
  exact ⟨stepb, hstepb_mem, hb_step, hgt, hlt⟩

private theorem gapOf_eq_case_pos
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    0 < gapOf_eq_case cs hcs seq heq c hc := by
  let a := doubleEntryOf_eq_case cs hcs seq heq c hc
  have ha_mem : a ∈ c.members := doubleEntryOf_eq_case_mem cs hcs seq heq c hc
  obtain ⟨b, hb_mem, hba, _⟩ := cycleProduct_image_member cs hcs c hc a ha_mem
  obtain ⟨stepb, hstepb_mem, hb_step, hgt, hlt⟩ :=
    other_member_has_step_between_doubleSteps_of_eq_case cs hcs seq heq c hc hb_mem hba
  have hspan :
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) + 2 ≤
        max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
    omega
  unfold gapOf_eq_case
  omega

private theorem exists_min_gap_cycle_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length) :
    ∃ c : { c // c ∈ cs }, ∀ d : { d // d ∈ cs },
      gapOf_eq_case cs hcs seq heq c.1 c.2 ≤ gapOf_eq_case cs hcs seq heq d.1 d.2 := by
  let f : { c // c ∈ cs } → ℕ := fun c => gapOf_eq_case cs hcs seq heq c.1 c.2
  let oc := cs.attach.argmin f
  have hocne : oc ≠ none := by
    intro hoc
    have hnil : cs.attach = [] := by
      simpa [oc, f] using (List.argmin_eq_none (l := cs.attach) (f := f)).mp hoc
    exact hcs_nonempty (by simpa using hnil)
  rcases Option.ne_none_iff_exists'.mp hocne with ⟨c, hcoc⟩
  refine ⟨c, ?_⟩
  intro d
  have hc_mem : c ∈ cs.attach := List.argmin_mem hcoc
  have hd_mem : d ∈ cs.attach := by simp
  exact List.le_of_mem_argmin hd_mem hcoc

private noncomputable def minGapCycleMemberOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length) :
    { c // c ∈ cs } := by
  classical
  let f : { c // c ∈ cs } → ℕ := fun c => gapOf_eq_case cs hcs seq heq c.1 c.2
  let oc := cs.attach.argmin f
  have hocne : oc ≠ none := by
    intro hoc
    have hnil : cs.attach = [] := by
      simpa [oc, f] using (List.argmin_eq_none (l := cs.attach) (f := f)).mp hoc
    exact hcs_nonempty (by simpa using hnil)
  have hoc : oc.isSome := by
    rw [Option.isSome_iff_exists]
    exact Option.ne_none_iff_exists'.mp hocne
  exact oc.get hoc

noncomputable def minGapCycleOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length) :
    Cycle α :=
  (minGapCycleMemberOf_eq_case cs hcs hcs_nonempty seq heq).1

theorem minGapCycleOf_eq_case_mem
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    :
    minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq ∈ cs :=
  (minGapCycleMemberOf_eq_case cs hcs hcs_nonempty seq heq).2

private theorem minGapCycleOf_eq_case_min
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (d : Cycle α) (hd : d ∈ cs) :
    gapOf_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ≤
      gapOf_eq_case cs hcs seq heq d hd := by
  classical
  let f : { c // c ∈ cs } → ℕ := fun c => gapOf_eq_case cs hcs seq heq c.1 c.2
  let oc := cs.attach.argmin f
  have hocne : oc ≠ none := by
    intro hoc
    have hnil : cs.attach = [] := by
      simpa [oc, f] using (List.argmin_eq_none (l := cs.attach) (f := f)).mp hoc
    exact hcs_nonempty (by simpa using hnil)
  have hoc : oc.isSome := by
    rw [Option.isSome_iff_exists]
    exact Option.ne_none_iff_exists'.mp hocne
  have hchosen :
      minGapCycleMemberOf_eq_case cs hcs hcs_nonempty seq heq ∈ cs.attach.argmin f := by
    unfold minGapCycleMemberOf_eq_case
    simp [f]
  have hd_mem : (⟨d, hd⟩ : { c // c ∈ cs }) ∈ cs.attach := by
    simp
  have hle := List.le_of_mem_argmin hd_mem hchosen
  simpa [f, minGapCycleOf_eq_case] using hle

private theorem minGapCycleOf_eq_case_pos
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length) :
    0 <
      gapOf_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) := by
  exact gapOf_eq_case_pos cs hcs seq heq
    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)

private theorem runScript_middle_maps_cycle_image_of_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {u v : α}
    (_hu_mem : u ∈ c.members) (_hv_mem : v ∈ c.members)
    (hu_ne : u ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hv_ne : v ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hpre_v : ∀ s ∈ pre, Body.orig v ∉ [s.1, s.2])
    (hsuf_u : ∀ s ∈ suf, Body.orig u ∉ [s.1, s.2])
    (himg : cycleProduct cs (Body.orig u) = Body.orig v) :
    runScript mid (Body.orig v) = Body.orig u := by
  have hundo : runScript seq.steps (Body.orig v) = Body.orig u := by
    have h := congr_fun (congr_arg (↑·) seq.undoes) (Body.orig u)
    simpa [himg] using h
  have hpre_fix_v : runScript pre (Body.orig v) = Body.orig v := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hpre_v s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hsuf_fix_u : runScript suf (Body.orig u) = Body.orig u := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hsuf_u s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hv_orig_ne_x : (Body.orig v : Body α) ≠ Body.x := by simp
  have hv_orig_ne_a :
      (Body.orig v : Body α) ≠ Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    intro hEq
    exact hv_ne (Body.orig.inj hEq)
  have hfix_x_v :
      Equiv.swap Body.x (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (Body.orig v) = Body.orig v := by
    exact Equiv.swap_apply_of_ne_of_ne hv_orig_ne_x hv_orig_ne_a
  rw [hsplit, runScript_append_apply, runScript_cons, mul_apply,
    runScript_append_apply, runScript_cons, mul_apply] at hundo
  rw [swap_xDoubleStepOf_eq_case cs hcs seq heq c hc,
    swap_yDoubleStepOf_eq_case cs hcs seq heq c hc, hpre_fix_v, hfix_x_v] at hundo
  have hmid :
      Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (runScript mid (Body.orig v)) = Body.orig u := by
    exact (runScript suf).injective (hundo.trans hsuf_fix_u.symm)
  have hu_orig_ne_y : (Body.orig u : Body α) ≠ Body.y := by simp
  have hu_orig_ne_a :
      (Body.orig u : Body α) ≠ Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    intro hEq
    exact hu_ne (Body.orig.inj hEq)
  have hfix_y_u :
      Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (Body.orig u) = Body.orig u := by
    exact Equiv.swap_apply_of_ne_of_ne hu_orig_ne_y hu_orig_ne_a
  exact (Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))).injective
    (hmid.trans hfix_y_u.symm)

private theorem runScript_middle_maps_image_doubleEntry_to_y_of_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {b : α}
    (_hb_mem : b ∈ c.members)
    (hba : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hpre_b : ∀ s ∈ pre, Body.orig b ∉ [s.1, s.2])
    (hsuf_a :
      ∀ s ∈ suf, Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∉ [s.1, s.2])
    (himg :
      cycleProduct cs (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) = Body.orig b) :
    runScript mid (Body.orig b) = Body.y := by
  have hundo :
      runScript seq.steps (Body.orig b) =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    have h := congr_fun (congr_arg (↑·) seq.undoes)
      (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
    simpa [himg] using h
  have hpre_fix_b : runScript pre (Body.orig b) = Body.orig b := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hpre_b s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hsuf_fix_a :
      runScript suf (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hsuf_a s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hb_orig_ne_x : (Body.orig b : Body α) ≠ Body.x := by simp
  have hb_orig_ne_a :
      (Body.orig b : Body α) ≠ Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    intro hEq
    exact hba (Body.orig.inj hEq)
  have hfix_x_b :
      Equiv.swap Body.x (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (Body.orig b) = Body.orig b := by
    exact Equiv.swap_apply_of_ne_of_ne hb_orig_ne_x hb_orig_ne_a
  rw [hsplit, runScript_append_apply, runScript_cons, mul_apply,
    runScript_append_apply, runScript_cons, mul_apply] at hundo
  rw [swap_xDoubleStepOf_eq_case cs hcs seq heq c hc,
    swap_yDoubleStepOf_eq_case cs hcs seq heq c hc, hpre_fix_b, hfix_x_b] at hundo
  have hmid :
      Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (runScript mid (Body.orig b)) =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    exact (runScript suf).injective (hundo.trans hsuf_fix_a.symm)
  have hswap_y :
      Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) Body.y =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    exact Equiv.swap_apply_left _ _
  exact (Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))).injective
    (hmid.trans hswap_y.symm)

private theorem runScript_middle_maps_x_to_preimage_doubleEntry_of_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {u : α}
    (_hu_mem : u ∈ c.members)
    (hu_ne : u ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hpre_a :
      ∀ s ∈ pre, Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∉ [s.1, s.2])
    (hsuf_u : ∀ s ∈ suf, Body.orig u ∉ [s.1, s.2])
    (himg :
      cycleProduct cs (Body.orig u) =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) :
    runScript mid Body.x = Body.orig u := by
  have hundo :
      runScript seq.steps
        (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) = Body.orig u := by
    have h := congr_fun (congr_arg (↑·) seq.undoes) (Body.orig u)
    simpa [himg] using h
  have hpre_fix_a :
      runScript pre (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hpre_a s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hsuf_fix_u : runScript suf (Body.orig u) = Body.orig u := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hsuf_u s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  rw [hsplit, runScript_append_apply, runScript_cons, mul_apply,
    runScript_append_apply, runScript_cons, mul_apply] at hundo
  rw [swap_xDoubleStepOf_eq_case cs hcs seq heq c hc,
    swap_yDoubleStepOf_eq_case cs hcs seq heq c hc, hpre_fix_a,
    Equiv.swap_apply_right] at hundo
  have hmid :
      Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (runScript mid Body.x) = Body.orig u := by
    exact (runScript suf).injective (hundo.trans hsuf_fix_u.symm)
  have hu_orig_ne_y : (Body.orig u : Body α) ≠ Body.y := by simp
  have hu_orig_ne_a :
      (Body.orig u : Body α) ≠ Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    intro hEq
    exact hu_ne (Body.orig.inj hEq)
  have hfix_y_u :
      Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (Body.orig u) = Body.orig u := by
    exact Equiv.swap_apply_of_ne_of_ne hu_orig_ne_y hu_orig_ne_a
  exact (Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))).injective
    (hmid.trans hfix_y_u.symm)

private theorem runScript_middle_maps_cycle_image_of_split_rev
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ yDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {u v : α}
    (_hu_mem : u ∈ c.members) (_hv_mem : v ∈ c.members)
    (hu_ne : u ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hv_ne : v ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hpre_v : ∀ s ∈ pre, Body.orig v ∉ [s.1, s.2])
    (hsuf_u : ∀ s ∈ suf, Body.orig u ∉ [s.1, s.2])
    (himg : cycleProduct cs (Body.orig u) = Body.orig v) :
    runScript mid (Body.orig v) = Body.orig u := by
  have hundo : runScript seq.steps (Body.orig v) = Body.orig u := by
    have h := congr_fun (congr_arg (↑·) seq.undoes) (Body.orig u)
    simpa [himg] using h
  have hpre_fix_v : runScript pre (Body.orig v) = Body.orig v := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hpre_v s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hsuf_fix_u : runScript suf (Body.orig u) = Body.orig u := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hsuf_u s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hv_orig_ne_y : (Body.orig v : Body α) ≠ Body.y := by simp
  have hv_orig_ne_a :
      (Body.orig v : Body α) ≠ Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    intro hEq
    exact hv_ne (Body.orig.inj hEq)
  have hfix_y_v :
      Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (Body.orig v) = Body.orig v := by
    exact Equiv.swap_apply_of_ne_of_ne hv_orig_ne_y hv_orig_ne_a
  rw [hsplit, runScript_append_apply, runScript_cons, mul_apply,
    runScript_append_apply, runScript_cons, mul_apply] at hundo
  rw [swap_yDoubleStepOf_eq_case cs hcs seq heq c hc,
    swap_xDoubleStepOf_eq_case cs hcs seq heq c hc, hpre_fix_v, hfix_y_v] at hundo
  have hmid :
      Equiv.swap Body.x (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (runScript mid (Body.orig v)) = Body.orig u := by
    exact (runScript suf).injective (hundo.trans hsuf_fix_u.symm)
  have hu_orig_ne_x : (Body.orig u : Body α) ≠ Body.x := by simp
  have hu_orig_ne_a :
      (Body.orig u : Body α) ≠ Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    intro hEq
    exact hu_ne (Body.orig.inj hEq)
  have hfix_x_u :
      Equiv.swap Body.x (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (Body.orig u) = Body.orig u := by
    exact Equiv.swap_apply_of_ne_of_ne hu_orig_ne_x hu_orig_ne_a
  exact (Equiv.swap Body.x (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))).injective
    (hmid.trans hfix_x_u.symm)

private theorem runScript_middle_maps_image_doubleEntry_to_x_of_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ yDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {b : α}
    (_hb_mem : b ∈ c.members)
    (hba : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hpre_b : ∀ s ∈ pre, Body.orig b ∉ [s.1, s.2])
    (hsuf_a :
      ∀ s ∈ suf, Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∉ [s.1, s.2])
    (himg :
      cycleProduct cs (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) = Body.orig b) :
    runScript mid (Body.orig b) = Body.x := by
  have hundo :
      runScript seq.steps (Body.orig b) =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    have h := congr_fun (congr_arg (↑·) seq.undoes)
      (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
    simpa [himg] using h
  have hpre_fix_b : runScript pre (Body.orig b) = Body.orig b := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hpre_b s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hsuf_fix_a :
      runScript suf (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    apply runScript_apply_of_not_mem'
    intro s hs
    have hno := hsuf_a s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hno
    exact hno
  have hb_orig_ne_y : (Body.orig b : Body α) ≠ Body.y := by simp
  have hb_orig_ne_a :
      (Body.orig b : Body α) ≠ Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    intro hEq
    exact hba (Body.orig.inj hEq)
  have hfix_y_b :
      Equiv.swap Body.y (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (Body.orig b) = Body.orig b := by
    exact Equiv.swap_apply_of_ne_of_ne hb_orig_ne_y hb_orig_ne_a
  rw [hsplit, runScript_append_apply, runScript_cons, mul_apply,
    runScript_append_apply, runScript_cons, mul_apply] at hundo
  rw [swap_yDoubleStepOf_eq_case cs hcs seq heq c hc,
    swap_xDoubleStepOf_eq_case cs hcs seq heq c hc, hpre_fix_b, hfix_y_b] at hundo
  have hmid :
      Equiv.swap Body.x (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))
        (runScript mid (Body.orig b)) =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    exact (runScript suf).injective (hundo.trans hsuf_fix_a.symm)
  have hswap_x :
      Equiv.swap Body.x (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) Body.x =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) := by
    exact Equiv.swap_apply_left _ _
  exact (Equiv.swap Body.x (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc))).injective
    (hmid.trans hswap_x.symm)

private theorem runScript_middle_maps_cycle_image_of_ordered_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {u v : α}
    (hu_mem : u ∈ c.members) (hv_mem : v ∈ c.members)
    (hu_ne : u ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hv_ne : v ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (himg : cycleProduct cs (Body.orig u) = Body.orig v) :
    (((∃ pre mid suf,
        seq.steps =
          pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
            mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf ∧
        (∀ s ∈ pre, Body.orig v ∉ [s.1, s.2]) ∧
        (∀ s ∈ suf, Body.orig u ∉ [s.1, s.2])) →
        ∃ pre mid suf,
          seq.steps =
            pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
              mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf ∧
          (∀ s ∈ pre, Body.orig v ∉ [s.1, s.2]) ∧
          (∀ s ∈ suf, Body.orig u ∉ [s.1, s.2]) ∧
          runScript mid (Body.orig v) = Body.orig u) ∧
      ((∃ pre mid suf,
        seq.steps =
          pre ++ yDoubleStepOf_eq_case cs hcs seq heq c hc ::
            mid ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: suf ∧
        (∀ s ∈ pre, Body.orig v ∉ [s.1, s.2]) ∧
        (∀ s ∈ suf, Body.orig u ∉ [s.1, s.2])) →
        ∃ pre mid suf,
          seq.steps =
            pre ++ yDoubleStepOf_eq_case cs hcs seq heq c hc ::
              mid ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: suf ∧
          (∀ s ∈ pre, Body.orig v ∉ [s.1, s.2]) ∧
          (∀ s ∈ suf, Body.orig u ∉ [s.1, s.2]) ∧
          runScript mid (Body.orig v) = Body.orig u)) := by
  constructor
  · intro hsplit
    rcases hsplit with ⟨pre, mid, suf, hsplit, hpre_v, hsuf_u⟩
    refine ⟨pre, mid, suf, hsplit, hpre_v, hsuf_u, ?_⟩
    exact runScript_middle_maps_cycle_image_of_split cs hcs seq heq c hc hsplit
      hu_mem hv_mem hu_ne hv_ne hpre_v hsuf_u himg
  · intro hsplit
    rcases hsplit with ⟨pre, mid, suf, hsplit, hpre_v, hsuf_u⟩
    refine ⟨pre, mid, suf, hsplit, hpre_v, hsuf_u, ?_⟩
    exact runScript_middle_maps_cycle_image_of_split_rev cs hcs seq heq c hc hsplit
      hu_mem hv_mem hu_ne hv_ne hpre_v hsuf_u himg

private theorem runScript_middle_maps_doubleEntry_endpoint_of_ordered_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {b : α}
    (hb_mem : b ∈ c.members)
    (hba : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (himg :
      cycleProduct cs (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) = Body.orig b) :
    (((∃ pre mid suf,
        seq.steps =
          pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
            mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf ∧
        (∀ s ∈ pre, Body.orig b ∉ [s.1, s.2]) ∧
        (∀ s ∈ suf, Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∉ [s.1, s.2])) →
        ∃ pre mid suf,
          seq.steps =
            pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
              mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf ∧
          (∀ s ∈ pre, Body.orig b ∉ [s.1, s.2]) ∧
          (∀ s ∈ suf, Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∉ [s.1, s.2]) ∧
          runScript mid (Body.orig b) = Body.y) ∧
      ((∃ pre mid suf,
        seq.steps =
          pre ++ yDoubleStepOf_eq_case cs hcs seq heq c hc ::
            mid ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: suf ∧
        (∀ s ∈ pre, Body.orig b ∉ [s.1, s.2]) ∧
        (∀ s ∈ suf, Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∉ [s.1, s.2])) →
        ∃ pre mid suf,
          seq.steps =
            pre ++ yDoubleStepOf_eq_case cs hcs seq heq c hc ::
              mid ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: suf ∧
          (∀ s ∈ pre, Body.orig b ∉ [s.1, s.2]) ∧
          (∀ s ∈ suf, Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∉ [s.1, s.2]) ∧
          runScript mid (Body.orig b) = Body.x)) := by
  constructor
  · intro hsplit
    rcases hsplit with ⟨pre, mid, suf, hsplit, hpre_b, hsuf_a⟩
    refine ⟨pre, mid, suf, hsplit, hpre_b, hsuf_a, ?_⟩
    exact runScript_middle_maps_image_doubleEntry_to_y_of_split cs hcs seq heq c hc hsplit
      hb_mem hba hpre_b hsuf_a himg
  · intro hsplit
    rcases hsplit with ⟨pre, mid, suf, hsplit, hpre_b, hsuf_a⟩
    refine ⟨pre, mid, suf, hsplit, hpre_b, hsuf_a, ?_⟩
    exact runScript_middle_maps_image_doubleEntry_to_x_of_split cs hcs seq heq c hc hsplit
      hb_mem hba hpre_b hsuf_a himg

private def GapYStepOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    (step : Body α × Body α) : Prop :=
  (∃ a, YStepFor a step) ∧
    min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
        (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) ≤
      stepIdx step seq.steps ∧
    stepIdx step seq.steps ≤
      max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
        (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc)

private theorem yDoubleStep_gapY_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    GapYStepOf_eq_case cs hcs seq heq c hc
      (yDoubleStepOf_eq_case cs hcs seq heq c hc) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨doubleEntryOf_eq_case cs hcs seq heq c hc,
      yDoubleStepOf_eq_case_spec cs hcs seq heq c hc⟩
  · unfold yDoubleStepIdxOf_eq_case
    exact Nat.min_le_right _ _
  · unfold yDoubleStepIdxOf_eq_case
    exact Nat.le_max_right _ _

private theorem exists_rightmost_gapY_step_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    ∃ pre step suf,
      seq.steps = pre ++ step :: suf ∧
      GapYStepOf_eq_case cs hcs seq heq c hc step ∧
      ∀ s ∈ suf, ¬ GapYStepOf_eq_case cs hcs seq heq c hc s := by
  classical
  have hex :
      ∃ step ∈ seq.steps, GapYStepOf_eq_case cs hcs seq heq c hc step := by
    exact ⟨yDoubleStepOf_eq_case cs hcs seq heq c hc,
      yDoubleStepOf_eq_case_mem cs hcs seq heq c hc,
      yDoubleStep_gapY_of_eq_case cs hcs seq heq c hc⟩
  rcases exists_split_rightmost (p := GapYStepOf_eq_case cs hcs seq heq c hc) seq.steps hex with
    ⟨pre, step, suf, hsplit, hgap, hsuf⟩
  exact ⟨pre, step, suf, hsplit, hgap, hsuf⟩

private def ExternalGapYStepOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    (step : Body α × Body α) : Prop :=
  ∃ h, YStepFor h step ∧ h ∉ c.members ∧ GapYStepOf_eq_case cs hcs seq heq c hc step

private def InternalGapYStepOf_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    (step : Body α × Body α) : Prop :=
  ∃ a, YStepFor a step ∧ a ∈ c.members ∧ GapYStepOf_eq_case cs hcs seq heq c hc step

private theorem yDoubleStep_internalGapY_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    InternalGapYStepOf_eq_case cs hcs seq heq c hc
      (yDoubleStepOf_eq_case cs hcs seq heq c hc) := by
  refine ⟨doubleEntryOf_eq_case cs hcs seq heq c hc,
    yDoubleStepOf_eq_case_spec cs hcs seq heq c hc,
    doubleEntryOf_eq_case_mem cs hcs seq heq c hc,
    yDoubleStep_gapY_of_eq_case cs hcs seq heq c hc⟩

private theorem xDoubleStepIdx_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) :
    xDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length := by
  have hsplit' :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq c hc ::
            (mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) := by
    simpa [List.append_assoc] using hsplit
  unfold xDoubleStepIdxOf_eq_case
  simpa using idxOf_eq_length_pre_of_split hsplit'
    (step_not_mem_prefix_of_split hsplit' seq.distinct_pairs)

private theorem yDoubleStepIdx_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) :
    yDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length + 1 + mid.length := by
  have hsplit' :
      seq.steps =
        (pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: mid) ++
          yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf := by
    simpa [List.append_assoc] using hsplit
  have hnot :
      yDoubleStepOf_eq_case cs hcs seq heq c hc ∉
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: mid := by
    exact step_not_mem_prefix_of_split hsplit' seq.distinct_pairs
  unfold yDoubleStepIdxOf_eq_case
  have hy_idx := idxOf_eq_length_pre_of_split hsplit' hnot
  simp only [List.length_append, List.length_cons] at hy_idx
  calc
    yDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length + (mid.length + 1) := hy_idx
    _ = pre.length + 1 + mid.length := by omega

private theorem xDouble_lt_yDoubleIdx_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) :
    xDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
      yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
  rw [xDoubleStepIdx_of_xy_split cs hcs seq heq c hc hsplit,
    yDoubleStepIdx_of_xy_split cs hcs seq heq c hc hsplit]
  omega

private theorem externalGapYStep_ne_yDoubleStep_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {step : Body α × Body α}
    (hstep : step ∈ seq.steps)
    (hExt : ExternalGapYStepOf_eq_case cs hcs seq heq c hc step) :
    step ≠ yDoubleStepOf_eq_case cs hcs seq heq c hc := by
  intro hEq
  subst step
  rcases hExt with ⟨h, hy, hnot_mem, _⟩
  have hh_step :
      Body.orig h ∈
        [(yDoubleStepOf_eq_case cs hcs seq heq c hc).1,
          (yDoubleStepOf_eq_case cs hcs seq heq c hc).2] := by
    rcases hy with hy | hy <;> simp [hy]
  have ha_step := yDoubleStepOf_eq_case_mentions cs hcs seq heq c hc
  have hhelper :=
    seq.helper_constraint (yDoubleStepOf_eq_case cs hcs seq heq c hc)
      (yDoubleStepOf_eq_case_mem cs hcs seq heq c hc)
  have hh_eq :
      h = doubleEntryOf_eq_case cs hcs seq heq c hc := by
    exact helper_step_mentions_eq hhelper hh_step ha_step
  exact hnot_mem (hh_eq ▸ doubleEntryOf_eq_case_mem cs hcs seq heq c hc)

private theorem externalGapYStep_lt_yDoubleIdx_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {step : Body α × Body α}
    (hstep : step ∈ seq.steps)
    (hExt : ExternalGapYStepOf_eq_case cs hcs seq heq c hc step) :
    stepIdx step seq.steps <
      yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
  rcases hExt with ⟨h, hy, hnot_mem, hgap⟩
  have hmax :
      max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) =
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
    have hlt := xDouble_lt_yDoubleIdx_of_xy_split cs hcs seq heq c hc hsplit
    omega
  have hle :
      stepIdx step seq.steps ≤
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
    rw [← hmax]
    exact hgap.2.2
  have hne_idx :
      stepIdx step seq.steps ≠
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
    intro hEqIdx
    have hy_mem := yDoubleStepOf_eq_case_mem cs hcs seq heq c hc
    have hEqStep :
        step = yDoubleStepOf_eq_case cs hcs seq heq c hc := by
      exact (List.idxOf_inj hstep hy_mem).1 hEqIdx
    exact externalGapYStep_ne_yDoubleStep_of_eq_case cs hcs seq heq c hc hstep
      ⟨h, hy, hnot_mem, hgap⟩ hEqStep
  omega

private theorem externalGapYStep_ne_xDoubleStep_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {step : Body α × Body α}
    (hstep : step ∈ seq.steps)
    (hExt : ExternalGapYStepOf_eq_case cs hcs seq heq c hc step) :
    step ≠ xDoubleStepOf_eq_case cs hcs seq heq c hc := by
  intro hEq
  subst step
  rcases hExt with ⟨h, hy, hnot_mem, _⟩
  have hh_step :
      Body.orig h ∈
        [(xDoubleStepOf_eq_case cs hcs seq heq c hc).1,
          (xDoubleStepOf_eq_case cs hcs seq heq c hc).2] := by
    rcases hy with hy | hy <;> simp [hy]
  have ha_step := xDoubleStepOf_eq_case_mentions cs hcs seq heq c hc
  have hhelper :=
    seq.helper_constraint (xDoubleStepOf_eq_case cs hcs seq heq c hc)
      (xDoubleStepOf_eq_case_mem cs hcs seq heq c hc)
  have hh_eq :
      h = doubleEntryOf_eq_case cs hcs seq heq c hc := by
    exact helper_step_mentions_eq hhelper hh_step ha_step
  exact hnot_mem (hh_eq ▸ doubleEntryOf_eq_case_mem cs hcs seq heq c hc)

private theorem externalGapYStep_strict_between_doubleIdx_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {step : Body α × Body α}
    (hstep : step ∈ seq.steps)
    (hExt : ExternalGapYStepOf_eq_case cs hcs seq heq c hc step) :
    xDoubleStepIdxOf_eq_case cs hcs seq heq c hc < stepIdx step seq.steps ∧
      stepIdx step seq.steps <
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
  rcases hExt with ⟨h, hy, hnot_mem, hgap⟩
  have hlt_xy := xDouble_lt_yDoubleIdx_of_xy_split cs hcs seq heq c hc hsplit
  have hmin :
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) =
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
    omega
  have hge :
      xDoubleStepIdxOf_eq_case cs hcs seq heq c hc ≤ stepIdx step seq.steps := by
    rw [← hmin]
    exact hgap.2.1
  have hne_idx :
      stepIdx step seq.steps ≠
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
    intro hEqIdx
    have hx_mem := xDoubleStepOf_eq_case_mem cs hcs seq heq c hc
    have hEqStep :
        step = xDoubleStepOf_eq_case cs hcs seq heq c hc := by
      exact (List.idxOf_inj hstep hx_mem).1 hEqIdx
    exact externalGapYStep_ne_xDoubleStep_of_eq_case cs hcs seq heq c hc hstep
      ⟨h, hy, hnot_mem, hgap⟩ hEqStep
  refine ⟨?_, externalGapYStep_lt_yDoubleIdx_of_xy_split cs hcs seq heq c hc hsplit hstep
    ⟨h, hy, hnot_mem, hgap⟩⟩
  omega

private theorem externalGapYStep_mem_mid_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {step : Body α × Body α}
    (hstep : step ∈ seq.steps)
    (hExt : ExternalGapYStepOf_eq_case cs hcs seq heq c hc step) :
    step ∈ mid := by
  have hbetween :=
    externalGapYStep_strict_between_doubleIdx_of_xy_split cs hcs seq heq c hc hsplit hstep hExt
  have hstepSeq : step ∈ seq.steps := hstep
  have hsplit_pre :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq c hc ::
            (mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) := by
    simpa [List.append_assoc] using hsplit
  have hsplit_right :
      seq.steps =
        (pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: mid) ++
          yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf := by
    simpa [List.append_assoc] using hsplit
  rw [hsplit_pre] at hstep
  rcases List.mem_append.mp hstep with hpre | htail
  · rcases exists_split_of_mem pre hpre with ⟨preL, preR, hpre_split⟩
    have hsplit_step :
        seq.steps =
          preL ++ step :: (preR ++
            xDoubleStepOf_eq_case cs hcs seq heq c hc ::
            mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) := by
      simp [hsplit, hpre_split, List.append_assoc]
    have hidx_step : stepIdx step seq.steps = preL.length := by
      simpa using idxOf_eq_length_pre_of_split hsplit_step
        (step_not_mem_prefix_of_split hsplit_step seq.distinct_pairs)
    have hidx_x :
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length := by
      simpa using xDoubleStepIdx_of_xy_split cs hcs seq heq c hc hsplit
    rw [hidx_step, hidx_x] at hbetween
    have : preL.length < pre.length := by
      rw [hpre_split, List.length_append, List.length_cons]
      omega
    exfalso
    omega
  · rcases List.mem_cons.mp htail with hEqX | htail
    · exact False.elim
        (externalGapYStep_ne_xDoubleStep_of_eq_case cs hcs seq heq c hc hstepSeq hExt hEqX)
    · rcases List.mem_append.mp htail with hmid | htail'
      · exact hmid
      · rcases List.mem_cons.mp htail' with hEqY | hsuf
        · exact False.elim
            (externalGapYStep_ne_yDoubleStep_of_eq_case cs hcs seq heq c hc hstepSeq hExt hEqY)
        · rcases exists_split_of_mem suf hsuf with ⟨sufL, sufR, hsuf_split⟩
          have hsplit_step :
              seq.steps =
                (pre ++
                  xDoubleStepOf_eq_case cs hcs seq heq c hc ::
                  mid ++
                  yDoubleStepOf_eq_case cs hcs seq heq c hc ::
                  sufL) ++ step :: sufR := by
            simp [hsplit, hsuf_split, List.append_assoc]
          have hidx_step :
              stepIdx step seq.steps =
                (pre ++
                  xDoubleStepOf_eq_case cs hcs seq heq c hc ::
                  mid ++
                  yDoubleStepOf_eq_case cs hcs seq heq c hc ::
                  sufL).length := by
            simpa using idxOf_eq_length_pre_of_split hsplit_step
              (step_not_mem_prefix_of_split hsplit_step seq.distinct_pairs)
          have hidx_y :
              yDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length + 1 + mid.length := by
            simpa using yDoubleStepIdx_of_xy_split cs hcs seq heq c hc hsplit
          rw [hidx_step, hidx_y] at hbetween
          simp only [List.length_append, List.length_cons] at hbetween
          omega

private theorem exists_mid_split_at_externalGapY_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {step : Body α × Body α}
    (hstep : step ∈ seq.steps)
    (hExt : ExternalGapYStepOf_eq_case cs hcs seq heq c hc step) :
    ∃ midL midR, mid = midL ++ step :: midR := by
  have hmid :
      step ∈ mid :=
    externalGapYStep_mem_mid_of_xy_split cs hcs seq heq c hc hsplit hstep hExt
  rcases exists_split_of_mem mid hmid with ⟨midL, midR, hmid_split⟩
  exact ⟨midL, midR, hmid_split⟩

private theorem yDoubleStep_mem_suffix_of_externalGapY_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {preE sufE : List (Body α × Body α)} {stepE : Body α × Body α}
    (hsplit_ext : seq.steps = preE ++ stepE :: sufE)
    (hExt : ExternalGapYStepOf_eq_case cs hcs seq heq c hc stepE) :
    yDoubleStepOf_eq_case cs hcs seq heq c hc ∈ sufE := by
  have hstep_mem : stepE ∈ seq.steps := by
    rw [hsplit_ext]
    simp
  have hy_mem : yDoubleStepOf_eq_case cs hcs seq heq c hc ∈ seq.steps :=
    yDoubleStepOf_eq_case_mem cs hcs seq heq c hc
  have hlt :
      stepIdx stepE seq.steps <
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc :=
    externalGapYStep_lt_yDoubleIdx_of_xy_split cs hcs seq heq c hc hsplit_xy hstep_mem hExt
  have hlt' :
      stepIdx stepE seq.steps <
        stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps := by
    simpa [yDoubleStepIdxOf_eq_case] using hlt
  have hidx_stepE : stepIdx stepE seq.steps = preE.length := by
    simpa using idxOf_eq_length_pre_of_split hsplit_ext
      (step_not_mem_prefix_of_split hsplit_ext seq.distinct_pairs)
  rw [hsplit_ext] at hy_mem
  rcases List.mem_append.mp hy_mem with hy_pre | hy_tail
  · have hy_idx_pre :
        stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps =
          stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) preE := by
      simpa using idxOf_eq_idxOf_pre_of_mem_pre_split hsplit_ext hy_pre
    have hy_lt : stepIdx (yDoubleStepOf_eq_case cs hcs seq heq c hc) seq.steps < preE.length := by
      rw [hy_idx_pre]
      exact stepIdx_lt_length_of_mem hy_pre
    rw [hidx_stepE] at hlt'
    omega
  · rcases List.mem_cons.mp hy_tail with hy_eq | hy_suf
    · exact False.elim
        (externalGapYStep_ne_yDoubleStep_of_eq_case cs hcs seq heq c hc hstep_mem hExt hy_eq.symm)
    · exact hy_suf

private theorem exists_leftmost_internalGapY_step_right_of_external_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {preE sufE : List (Body α × Body α)} {stepE : Body α × Body α}
    (hsplit_ext : seq.steps = preE ++ stepE :: sufE)
    (hExt : ExternalGapYStepOf_eq_case cs hcs seq heq c hc stepE) :
    ∃ preI stepI sufI,
      sufE = preI ++ stepI :: sufI ∧
      InternalGapYStepOf_eq_case cs hcs seq heq c hc stepI ∧
      ∀ s ∈ preI, ¬ InternalGapYStepOf_eq_case cs hcs seq heq c hc s := by
  classical
  have hy_in_suf :
      yDoubleStepOf_eq_case cs hcs seq heq c hc ∈ sufE :=
    yDoubleStep_mem_suffix_of_externalGapY_of_xy_split cs hcs seq heq c hc
      hsplit_xy hsplit_ext hExt
  have hex :
      ∃ step ∈ sufE, InternalGapYStepOf_eq_case cs hcs seq heq c hc step := by
    exact ⟨yDoubleStepOf_eq_case cs hcs seq heq c hc, hy_in_suf,
      yDoubleStep_internalGapY_of_eq_case cs hcs seq heq c hc⟩
  rcases exists_split_leftmost
      (p := InternalGapYStepOf_eq_case cs hcs seq heq c hc) sufE hex with
    ⟨preI, stepI, sufI, hsplitI, hInt, hpreI⟩
  exact ⟨preI, stepI, sufI, hsplitI, hInt, hpreI⟩

omit [Fintype α] in
private theorem stepIdx_between_middle_of_split_two
    {steps pre mid suf : List (Body α × Body α)}
    {left right step : Body α × Body α}
    (hnd : (steps.map stepPair).Nodup)
    (hsplit : steps = pre ++ left :: mid ++ right :: suf)
    (hstep_mid : step ∈ mid) :
    stepIdx left steps < stepIdx step steps ∧
      stepIdx step steps < stepIdx right steps := by
  rcases exists_split_of_mem mid hstep_mid with ⟨midL, midR, hmid⟩
  have hsplit_step :
      steps = (pre ++ left :: midL) ++ step :: (midR ++ right :: suf) := by
    simp [hsplit, hmid, List.append_assoc]
  have hleft_idx : stepIdx left steps = pre.length := by
    have hsplit_left :
        steps = pre ++ left :: (midL ++ step :: (midR ++ right :: suf)) := by
      simp [hsplit_step, List.append_assoc]
    simpa using idxOf_eq_length_pre_of_split hsplit_left
      (step_not_mem_prefix_of_split hsplit_left hnd)
  have hstep_idx : stepIdx step steps = pre.length + 1 + midL.length := by
    have hidx :=
      idxOf_eq_length_pre_of_split hsplit_step
        (step_not_mem_prefix_of_split hsplit_step hnd)
    simp only [List.length_append, List.length_cons] at hidx
    calc
      stepIdx step steps = pre.length + (midL.length + 1) := hidx
      _ = pre.length + 1 + midL.length := by omega
  have hright_idx : stepIdx right steps = pre.length + 1 + mid.length := by
    have hsplit_right :
        steps = (pre ++ left :: mid) ++ right :: suf := by
      simp [hsplit, List.append_assoc]
    have hnot :
        right ∉ pre ++ left :: mid := by
      exact step_not_mem_prefix_of_split hsplit_right hnd
    have hidx := idxOf_eq_length_pre_of_split hsplit_right hnot
    simp only [List.length_append, List.length_cons] at hidx
    calc
      stepIdx right steps = pre.length + (mid.length + 1) := hidx
      _ = pre.length + 1 + mid.length := by omega
  constructor
  · rw [hleft_idx, hstep_idx]
    omega
  · rw [hstep_idx, hright_idx]
    have hmid_len : midL.length < mid.length := by
      rw [hmid, List.length_append, List.length_cons]
      omega
    omega

private theorem gap_strict_of_mid_member_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {step : Body α × Body α}
    (hstep_mid : step ∈ mid) :
    min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
        (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) <
      stepIdx step seq.steps ∧
    stepIdx step seq.steps <
      max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
        (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
  have hbetween :=
    stepIdx_between_middle_of_split_two seq.distinct_pairs hsplit_xy hstep_mid
  have hxy :
      xDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
    exact xDouble_lt_yDoubleIdx_of_xy_split cs hcs seq heq c hc hsplit_xy
  have hmin :
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) =
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
    exact Nat.min_eq_left (Nat.le_of_lt hxy)
  have hmax :
      max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) =
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
    exact Nat.max_eq_right (Nat.le_of_lt hxy)
  rw [hmin, hmax]
  exact hbetween

private theorem no_yStep_between_rightmost_external_and_next_internal
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    (_hnoXY : ¬ seq.hasHelperSwap)
    {preE sufE : List (Body α × Body α)} {stepE : Body α × Body α}
    (hsplit_ext : seq.steps = preE ++ stepE :: sufE)
    (hExt : ExternalGapYStepOf_eq_case cs hcs seq heq c hc stepE)
    (hsuf_ext : ∀ s ∈ sufE, ¬ ExternalGapYStepOf_eq_case cs hcs seq heq c hc s)
    {preI sufI : List (Body α × Body α)} {stepI : Body α × Body α}
    (hsplit_int : sufE = preI ++ stepI :: sufI)
    (hInt : InternalGapYStepOf_eq_case cs hcs seq heq c hc stepI)
    (hpre_int : ∀ s ∈ preI, ¬ InternalGapYStepOf_eq_case cs hcs seq heq c hc s) :
    ∀ s ∈ preI, ∀ a, ¬ YStepFor a s := by
  intro s hs a hys
  rcases hExt with ⟨h, hy, hnot_mem, hgapE⟩
  rcases hInt with ⟨aI, hyI, haI_mem, hgapI⟩
  have hsplit_global :
      seq.steps = preE ++ stepE :: preI ++ stepI :: sufI := by
    simp [hsplit_ext, hsplit_int, List.append_assoc]
  have hbetween :=
    stepIdx_between_middle_of_split_two seq.distinct_pairs hsplit_global hs
  have hs_gap :
      GapYStepOf_eq_case cs hcs seq heq c hc s := by
    refine ⟨⟨a, hys⟩, ?_, ?_⟩
    · exact le_trans hgapE.2.1 (Nat.le_of_lt hbetween.1)
    · exact le_trans (Nat.le_of_lt hbetween.2) hgapI.2.2
  by_cases ha_mem : a ∈ c.members
  · exact hpre_int s hs ⟨a, hys, ha_mem, hs_gap⟩
  · have hs_suf : s ∈ sufE := by
      rw [hsplit_int]
      exact List.mem_append.mpr (Or.inl hs)
    exact hsuf_ext s hs_suf ⟨a, hys, ha_mem, hs_gap⟩

omit [Fintype α] in
private theorem runScript_fix_y_of_sublist_no_ySteps
    (seq : RepairSeq π)
    (hnoXY : ¬ seq.hasHelperSwap)
    (steps : List (Body α × Body α))
    (hsub : ∀ s ∈ steps, s ∈ seq.steps)
    (hnotY : ∀ s ∈ steps, ∀ a, ¬ YStepFor a s) :
    runScript steps Body.y = Body.y := by
  apply runScript_apply_of_not_mem'
  intro s hs
  have hsSeq := hsub s hs
  have havoid := step_avoids_y_of_no_helperSwap_of_not_yStep seq hnoXY hsSeq (hnotY s hs)
  simpa [eq_comm] using havoid

omit [Fintype α] in
private theorem runScript_avoids_y_of_sublist_no_ySteps
    (seq : RepairSeq π)
    (hnoXY : ¬ seq.hasHelperSwap)
    (steps : List (Body α × Body α))
    (hsub : ∀ s ∈ steps, s ∈ seq.steps)
    (hnotY : ∀ s ∈ steps, ∀ a, ¬ YStepFor a s)
    {z : Body α} (hz : z ≠ Body.y) :
    runScript steps z ≠ Body.y := by
  induction steps generalizing z with
  | nil =>
      simpa [runScript] using hz
  | cons step rest ih =>
      have hstep_mem : step ∈ seq.steps := hsub step (by simp)
      have hstep_avoid :
          Body.y ≠ step.1 ∧ Body.y ≠ step.2 :=
        step_avoids_y_of_no_helperSwap_of_not_yStep seq hnoXY hstep_mem
          (hnotY step (by simp))
      have hy_fix :
          Equiv.swap step.1 step.2 Body.y = Body.y := by
        exact Equiv.swap_apply_of_ne_of_ne hstep_avoid.1 hstep_avoid.2
      have hz' : Equiv.swap step.1 step.2 z ≠ Body.y := by
        intro hEq
        exact hz <|
          (Equiv.swap step.1 step.2).injective (hEq.trans hy_fix.symm)
      have hsub_rest : ∀ s ∈ rest, s ∈ seq.steps := by
        intro s hs
        exact hsub s (by simp [hs])
      have hnotY_rest : ∀ s ∈ rest, ∀ a, ¬ YStepFor a s := by
        intro s hs a
        exact hnotY s (by simp [hs]) a
      simpa [runScript] using ih hsub_rest hnotY_rest hz'

omit [Fintype α] in
private theorem runScript_fix_orig_of_sublist_no_hStep
    (seq : RepairSeq π)
    (hnoXY : ¬ seq.hasHelperSwap)
    (steps : List (Body α × Body α))
    (hsub : ∀ s ∈ steps, s ∈ seq.steps)
    {h : α}
    (hnotX : ∀ s ∈ steps, ¬ XStepFor h s)
    (hnotY : ∀ s ∈ steps, ¬ YStepFor h s) :
    runScript steps (Body.orig h : Body α) = Body.orig h := by
  apply runScript_apply_of_not_mem'
  intro s hs
  have hsSeq := hsub s hs
  rcases step_is_xStep_or_yStep_of_no_helperSwap seq hnoXY hsSeq with
    ⟨a, hx⟩ | ⟨a, hy⟩
  · have hneq : a ≠ h := by
      intro hEq
      subst hEq
      exact hnotX s hs hx
    rcases hx with rfl | rfl <;> simpa [eq_comm] using hneq
  · have hneq : a ≠ h := by
      intro hEq
      subst hEq
      exact hnotY s hs hy
    rcases hy with rfl | rfl <;> simpa [eq_comm] using hneq

omit [Fintype α] in
private theorem runScript_avoids_orig_of_sublist_no_hStep
    (seq : RepairSeq π)
    (hnoXY : ¬ seq.hasHelperSwap)
    (steps : List (Body α × Body α))
    (hsub : ∀ s ∈ steps, s ∈ seq.steps)
    {h : α}
    (hnotX : ∀ s ∈ steps, ¬ XStepFor h s)
    (hnotY : ∀ s ∈ steps, ¬ YStepFor h s)
    {z : Body α} (hz : z ≠ Body.orig h) :
    runScript steps z ≠ Body.orig h := by
  intro hEq
  have hfix :
      runScript steps (Body.orig h : Body α) = Body.orig h :=
    runScript_fix_orig_of_sublist_no_hStep seq hnoXY steps hsub hnotX hnotY
  exact hz <| (runScript steps).injective (hEq.trans hfix.symm)

omit [Fintype α] in
private theorem runScript_external_internal_segment_maps_external_to_internal
    (seq : RepairSeq π)
    (hnoXY : ¬ seq.hasHelperSwap)
    {midL preI sufI : List (Body α × Body α)}
    {stepE stepI : Body α × Body α}
    {h a : α}
    (hsub_midL : ∀ s ∈ midL, s ∈ seq.steps)
    (hsub_preI : ∀ s ∈ preI, s ∈ seq.steps)
    (hsub_sufI : ∀ s ∈ sufI, s ∈ seq.steps)
    (hE : YStepFor h stepE)
    (hI : YStepFor a stepI)
    (_ha_ne_h : a ≠ h)
    (hnot_h_midL_x : ∀ s ∈ midL, ¬ XStepFor h s)
    (hnot_h_midL_y : ∀ s ∈ midL, ¬ YStepFor h s)
    (hnot_preI_y : ∀ s ∈ preI, ∀ b, ¬ YStepFor b s)
    (hnot_a_sufI_x : ∀ s ∈ sufI, ¬ XStepFor a s)
    (hnot_a_sufI_y : ∀ s ∈ sufI, ¬ YStepFor a s) :
    runScript (midL ++ stepE :: preI ++ stepI :: sufI) (Body.orig h) = Body.orig a := by
  have hmidL_fix_h :
      runScript midL (Body.orig h : Body α) = Body.orig h :=
    runScript_fix_orig_of_sublist_no_hStep seq hnoXY midL hsub_midL hnot_h_midL_x hnot_h_midL_y
  have hpre_fix_y :
      runScript preI Body.y = Body.y :=
    runScript_fix_y_of_sublist_no_ySteps seq hnoXY preI hsub_preI hnot_preI_y
  have hsuf_fix_a :
      runScript sufI (Body.orig a : Body α) = Body.orig a :=
    runScript_fix_orig_of_sublist_no_hStep seq hnoXY sufI hsub_sufI hnot_a_sufI_x hnot_a_sufI_y
  have hdecomp :
      midL ++ stepE :: preI ++ stepI :: sufI =
        midL ++ stepE :: (preI ++ stepI :: sufI) := by
    simp [List.append_assoc]
  rw [hdecomp, runScript_append_apply, runScript_cons, Perm.mul_apply,
    runScript_append_apply, runScript_cons, Perm.mul_apply, hmidL_fix_h]
  rcases hE with rfl | rfl
  · simp
    rw [hpre_fix_y]
    rcases hI with rfl | rfl
    · simpa using hsuf_fix_a
    · simpa [Equiv.swap_comm] using hsuf_fix_a
  · simp
    rw [hpre_fix_y]
    rcases hI with rfl | rfl
    · simpa using hsuf_fix_a
    · simpa [Equiv.swap_comm] using hsuf_fix_a

private theorem runScript_mid_maps_external_to_internal_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {midL preI midR : List (Body α × Body α)}
    {stepE stepI : Body α × Body α}
    {h a : α}
    (hmid :
      mid = midL ++ stepE :: preI ++ stepI :: midR)
    (hyE : YStepFor h stepE)
    (hI : YStepFor a stepI)
    (ha_ne_h : a ≠ h)
    (hnot_h_midL_x : ∀ s ∈ midL, ¬ XStepFor h s)
    (hnot_h_midL_y : ∀ s ∈ midL, ¬ YStepFor h s)
    (hnot_preI_y : ∀ s ∈ preI, ∀ b, ¬ YStepFor b s)
    (hnot_a_midR_x : ∀ s ∈ midR, ¬ XStepFor a s)
    (hnot_a_midR_y : ∀ s ∈ midR, ¬ YStepFor a s) :
    runScript mid (Body.orig h : Body α) = Body.orig a := by
  rw [hmid]
  apply runScript_external_internal_segment_maps_external_to_internal seq hnoXY
  · intro s hs
    rw [hsplit_xy]
    simp [hmid, hs, List.append_assoc]
  · intro s hs
    rw [hsplit_xy]
    simp [hmid, hs, List.append_assoc]
  · intro s hs
    rw [hsplit_xy]
    simp [hmid, hs, List.append_assoc]
  · exact hyE
  · exact hI
  · exact ha_ne_h
  · exact hnot_h_midL_x
  · exact hnot_h_midL_y
  · exact hnot_preI_y
  · exact hnot_a_midR_x
  · exact hnot_a_midR_y

private theorem internalGapYStep_no_y_mentions_in_suffix_of_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {preE sufE : List (Body α × Body α)} {stepE : Body α × Body α}
    (hsplit_ext : seq.steps = preE ++ stepE :: sufE)
    {preI sufI : List (Body α × Body α)} {stepI : Body α × Body α}
    (hsplit_int : sufE = preI ++ stepI :: sufI)
    (hInt : InternalGapYStepOf_eq_case cs hcs seq heq c hc stepI) :
    ∃ a, YStepFor a stepI ∧ a ∈ c.members ∧ ∀ s ∈ sufI, ¬ YStepFor a s := by
  rcases hInt with ⟨a, hyI, ha_mem, _⟩
  refine ⟨a, hyI, ha_mem, ?_⟩
  intro s hs hyS
  have hsplit_global :
      seq.steps = preE ++ stepE :: preI ++ stepI :: sufI := by
    simp [hsplit_ext, hsplit_int, List.append_assoc]
  have hstepI_mem : stepI ∈ seq.steps := by
    rw [hsplit_global]
    simp
  have hs_mem : s ∈ seq.steps := by
    rw [hsplit_global]
    simp [hs, List.append_assoc]
  have hs_eq : s = stepI :=
    unique_yStepFor seq hs_mem hstepI_mem hyS hyI
  have hs_not :
      stepI ∉ sufI :=
    step_not_mem_suffix_of_split hsplit_global seq.distinct_pairs
  exact hs_not (hs_eq ▸ hs)

private theorem internalGapYStep_nonDouble_no_x_anywhere
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {stepI : Body α × Body α}
    (hstepI : stepI ∈ seq.steps)
    {a : α}
    (hyI : YStepFor a stepI)
    (ha_mem : a ∈ c.members)
    (ha_ne :
      a ≠ doubleEntryOf_eq_case cs hcs seq heq c hc) :
    ∀ s ∈ seq.steps, ¬ XStepFor a s := by
  intro s hs hxS
  have ha_y : a ∈ seq.yEntries := by
    exact (mem_yEntries_iff).2 ⟨stepI, hstepI, hyI⟩
  have ha_x : a ∈ seq.xEntries := by
    exact (mem_xEntries_iff).2 ⟨s, hs, hxS⟩
  exact eq_case_other_member_not_double cs hcs seq heq c hc ha_mem ha_ne
    ⟨ha_x, ha_y⟩

private theorem nonDouble_member_step_strict_between_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {b : α}
    (hb_mem : b ∈ c.members)
    (hb_ne : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    {step : Body α × Body α}
    (hstep : step ∈ seq.steps)
    (hb_step : Body.orig b ∈ [step.1, step.2]) :
    xDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
        stepIdx step seq.steps ∧
      stepIdx step seq.steps <
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
  obtain ⟨stepb, hstepb_mem, hb_stepb, hlo, hhi⟩ :=
    other_member_has_step_between_doubleSteps_of_eq_case cs hcs seq heq c hc hb_mem hb_ne
  have hform_step :=
    step_form_of_helper_and_orig_mem (seq.helper_constraint step hstep) hb_step
  have hform_stepb :=
    step_form_of_helper_and_orig_mem (seq.helper_constraint stepb hstepb_mem) hb_stepb
  have hEq : step = stepb := by
    rcases hform_step with hx | hx | hy | hy
    · rcases hform_stepb with hxb | hxb | hyb | hyb
      · exact unique_xStepFor seq hstep hstepb_mem (Or.inl hx) (Or.inl hxb)
      · exact unique_xStepFor seq hstep hstepb_mem (Or.inl hx) (Or.inr hxb)
      · exfalso
        have hb_x : b ∈ seq.xEntries := by
          exact (mem_xEntries_iff).2 ⟨step, hstep, Or.inl hx⟩
        have hb_y : b ∈ seq.yEntries := by
          exact (mem_yEntries_iff).2 ⟨stepb, hstepb_mem, Or.inl hyb⟩
        exact eq_case_other_member_not_double cs hcs seq heq c hc hb_mem hb_ne
          ⟨hb_x, hb_y⟩
      · exfalso
        have hb_x : b ∈ seq.xEntries := by
          exact (mem_xEntries_iff).2 ⟨step, hstep, Or.inl hx⟩
        have hb_y : b ∈ seq.yEntries := by
          exact (mem_yEntries_iff).2 ⟨stepb, hstepb_mem, Or.inr hyb⟩
        exact eq_case_other_member_not_double cs hcs seq heq c hc hb_mem hb_ne
          ⟨hb_x, hb_y⟩
    · rcases hform_stepb with hxb | hxb | hyb | hyb
      · exact unique_xStepFor seq hstep hstepb_mem (Or.inr hx) (Or.inl hxb)
      · exact unique_xStepFor seq hstep hstepb_mem (Or.inr hx) (Or.inr hxb)
      · exfalso
        have hb_x : b ∈ seq.xEntries := by
          exact (mem_xEntries_iff).2 ⟨step, hstep, Or.inr hx⟩
        have hb_y : b ∈ seq.yEntries := by
          exact (mem_yEntries_iff).2 ⟨stepb, hstepb_mem, Or.inl hyb⟩
        exact eq_case_other_member_not_double cs hcs seq heq c hc hb_mem hb_ne
          ⟨hb_x, hb_y⟩
      · exfalso
        have hb_x : b ∈ seq.xEntries := by
          exact (mem_xEntries_iff).2 ⟨step, hstep, Or.inr hx⟩
        have hb_y : b ∈ seq.yEntries := by
          exact (mem_yEntries_iff).2 ⟨stepb, hstepb_mem, Or.inr hyb⟩
        exact eq_case_other_member_not_double cs hcs seq heq c hc hb_mem hb_ne
          ⟨hb_x, hb_y⟩
    · rcases hform_stepb with hxb | hxb | hyb | hyb
      · exfalso
        have hb_y : b ∈ seq.yEntries := by
          exact (mem_yEntries_iff).2 ⟨step, hstep, Or.inl hy⟩
        have hb_x : b ∈ seq.xEntries := by
          exact (mem_xEntries_iff).2 ⟨stepb, hstepb_mem, Or.inl hxb⟩
        exact eq_case_other_member_not_double cs hcs seq heq c hc hb_mem hb_ne
          ⟨hb_x, hb_y⟩
      · exfalso
        have hb_y : b ∈ seq.yEntries := by
          exact (mem_yEntries_iff).2 ⟨step, hstep, Or.inl hy⟩
        have hb_x : b ∈ seq.xEntries := by
          exact (mem_xEntries_iff).2 ⟨stepb, hstepb_mem, Or.inr hxb⟩
        exact eq_case_other_member_not_double cs hcs seq heq c hc hb_mem hb_ne
          ⟨hb_x, hb_y⟩
      · exact unique_yStepFor seq hstep hstepb_mem (Or.inl hy) (Or.inl hyb)
      · exact unique_yStepFor seq hstep hstepb_mem (Or.inl hy) (Or.inr hyb)
    · rcases hform_stepb with hxb | hxb | hyb | hyb
      · exfalso
        have hb_y : b ∈ seq.yEntries := by
          exact (mem_yEntries_iff).2 ⟨step, hstep, Or.inr hy⟩
        have hb_x : b ∈ seq.xEntries := by
          exact (mem_xEntries_iff).2 ⟨stepb, hstepb_mem, Or.inl hxb⟩
        exact eq_case_other_member_not_double cs hcs seq heq c hc hb_mem hb_ne
          ⟨hb_x, hb_y⟩
      · exfalso
        have hb_y : b ∈ seq.yEntries := by
          exact (mem_yEntries_iff).2 ⟨step, hstep, Or.inr hy⟩
        have hb_x : b ∈ seq.xEntries := by
          exact (mem_xEntries_iff).2 ⟨stepb, hstepb_mem, Or.inr hxb⟩
        exact eq_case_other_member_not_double cs hcs seq heq c hc hb_mem hb_ne
          ⟨hb_x, hb_y⟩
      · exact unique_yStepFor seq hstep hstepb_mem (Or.inr hy) (Or.inl hyb)
      · exact unique_yStepFor seq hstep hstepb_mem (Or.inr hy) (Or.inr hyb)
  have hlt_xy := xDouble_lt_yDoubleIdx_of_xy_split cs hcs seq heq c hc hsplit_xy
  have hlo' :
      xDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
        stepIdx stepb seq.steps := by
    omega
  have hhi' :
      stepIdx stepb seq.steps <
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
    omega
  simpa [hEq] using ⟨hlo', hhi'⟩

private theorem nonDouble_member_not_mem_prefix_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {b : α}
    (hb_mem : b ∈ c.members)
    (hb_ne : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc) :
    ∀ s ∈ pre, Body.orig b ∉ [s.1, s.2] := by
  intro s hs hsMention
  have hsplit_pre :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq c hc ::
            (mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) := by
    simpa [List.append_assoc] using hsplit_xy
  have hs_seq : s ∈ seq.steps := by
    rw [hsplit_pre]
    exact List.mem_append.mpr <| Or.inl hs
  have hbetween :=
    nonDouble_member_step_strict_between_xy_split cs hcs seq heq c hc
      hsplit_xy hb_mem hb_ne hs_seq hsMention
  have hidx_s :
      stepIdx s seq.steps < xDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
    rcases exists_split_of_mem pre hs with ⟨preL, preR, hpre_split⟩
    have hsplit_s :
        seq.steps =
          preL ++ s :: (preR ++
            xDoubleStepOf_eq_case cs hcs seq heq c hc ::
              (mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)) := by
      simp [hsplit_pre, hpre_split, List.append_assoc]
    have hidx_s' :
        stepIdx s seq.steps = preL.length := by
      simpa using idxOf_eq_length_pre_of_split hsplit_s
        (step_not_mem_prefix_of_split hsplit_s seq.distinct_pairs)
    have hidx_x :
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length := by
      simpa using xDoubleStepIdx_of_xy_split cs hcs seq heq c hc hsplit_xy
    rw [hidx_s', hidx_x]
    rw [hpre_split, List.length_append, List.length_cons]
    omega
  exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt hbetween.1) hidx_s)

private theorem nonDouble_member_not_mem_suffix_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {b : α}
    (hb_mem : b ∈ c.members)
    (hb_ne : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc) :
    ∀ s ∈ suf, Body.orig b ∉ [s.1, s.2] := by
  intro s hs hsMention
  have hsplit_right :
      seq.steps =
        (pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: mid) ++
          yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf := by
    simpa [List.append_assoc] using hsplit_xy
  have hs_seq : s ∈ seq.steps := by
    rw [hsplit_right]
    simp [hs]
  have hbetween :=
    nonDouble_member_step_strict_between_xy_split cs hcs seq heq c hc
      hsplit_xy hb_mem hb_ne hs_seq hsMention
  rcases exists_split_of_mem suf hs with ⟨sufL, sufR, hsuf_split⟩
  have hsplit_s :
      seq.steps =
        (pre ++
          xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++
          yDoubleStepOf_eq_case cs hcs seq heq c hc ::
          sufL) ++ s :: sufR := by
    simp [hsplit_xy, hsuf_split, List.append_assoc]
  have hidx_s :
      stepIdx s seq.steps =
        (pre ++
          xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++
          yDoubleStepOf_eq_case cs hcs seq heq c hc ::
          sufL).length := by
    simpa using idxOf_eq_length_pre_of_split hsplit_s
      (step_not_mem_prefix_of_split hsplit_s seq.distinct_pairs)
  have hidx_y :
      yDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length + 1 + mid.length := by
    simpa using yDoubleStepIdx_of_xy_split cs hcs seq heq c hc hsplit_xy
  rw [hidx_s, hidx_y] at hbetween
  simp only [List.length_append, List.length_cons] at hbetween
  omega

private theorem doubleEntry_not_mem_prefix_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) :
    ∀ s ∈ pre, Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∉ [s.1, s.2] := by
  intro s hs hsMention
  have hsplit_pre :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq c hc ::
            (mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) := by
    simpa [List.append_assoc] using hsplit_xy
  have hs_seq : s ∈ seq.steps := by
    rw [hsplit_pre]
    exact List.mem_append.mpr <| Or.inl hs
  have hs_eq :
      s = xDoubleStepOf_eq_case cs hcs seq heq c hc ∨
        s = yDoubleStepOf_eq_case cs hcs seq heq c hc :=
    doubleEntryStep_eq_xDouble_or_yDouble_of_eq_case cs hcs seq heq c hc hs_seq hsMention
  rcases hs_eq with hs_eq | hs_eq
  · have hs_not : xDoubleStepOf_eq_case cs hcs seq heq c hc ∉ pre :=
      step_not_mem_prefix_of_split
        hsplit_pre
        seq.distinct_pairs
    exact hs_not (hs_eq ▸ hs)
  · have hidx_s :
        stepIdx s seq.steps < xDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
      rcases exists_split_of_mem pre hs with ⟨preL, preR, hpre_split⟩
      have hsplit_s :
          seq.steps =
            preL ++ s :: (preR ++
              xDoubleStepOf_eq_case cs hcs seq heq c hc ::
                (mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)) := by
        simp [hsplit_pre, hpre_split, List.append_assoc]
      have hidx_s' :
          stepIdx s seq.steps = preL.length := by
        simpa using idxOf_eq_length_pre_of_split hsplit_s
          (step_not_mem_prefix_of_split hsplit_s seq.distinct_pairs)
      have hidx_x :
          xDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length := by
        simpa using xDoubleStepIdx_of_xy_split cs hcs seq heq c hc hsplit_xy
      rw [hidx_s', hidx_x]
      rw [hpre_split, List.length_append, List.length_cons]
      omega
    have hidx_y :
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
          yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
      exact xDouble_lt_yDoubleIdx_of_xy_split cs hcs seq heq c hc hsplit_xy
    rw [hs_eq] at hidx_s
    exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt hidx_y) hidx_s)

private theorem doubleEntry_not_mem_suffix_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) :
    ∀ s ∈ suf, Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc) ∉ [s.1, s.2] := by
  intro s hs hsMention
  have hsplit_right :
      seq.steps =
        (pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: mid) ++
          yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf := by
    simpa [List.append_assoc] using hsplit_xy
  have hs_seq : s ∈ seq.steps := by
    rw [hsplit_right]
    simp [hs]
  have hs_eq :
      s = xDoubleStepOf_eq_case cs hcs seq heq c hc ∨
        s = yDoubleStepOf_eq_case cs hcs seq heq c hc :=
    doubleEntryStep_eq_xDouble_or_yDouble_of_eq_case cs hcs seq heq c hc hs_seq hsMention
  rcases hs_eq with hs_eq | hs_eq
  · have hidx_s :
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
          stepIdx s seq.steps := by
      rcases exists_split_of_mem suf hs with ⟨sufL, sufR, hsuf_split⟩
      have hsplit_s :
          seq.steps =
            (pre ++
              xDoubleStepOf_eq_case cs hcs seq heq c hc ::
              mid ++
              yDoubleStepOf_eq_case cs hcs seq heq c hc ::
              sufL) ++ s :: sufR := by
        simp [hsplit_xy, hsuf_split, List.append_assoc]
      have hidx_s' :
          stepIdx s seq.steps =
            (pre ++
              xDoubleStepOf_eq_case cs hcs seq heq c hc ::
              mid ++
              yDoubleStepOf_eq_case cs hcs seq heq c hc ::
              sufL).length := by
        simpa using idxOf_eq_length_pre_of_split hsplit_s
          (step_not_mem_prefix_of_split hsplit_s seq.distinct_pairs)
      have hidx_y :
          yDoubleStepIdxOf_eq_case cs hcs seq heq c hc = pre.length + 1 + mid.length := by
        simpa using yDoubleStepIdx_of_xy_split cs hcs seq heq c hc hsplit_xy
      rw [hidx_s', hidx_y]
      simp only [List.length_append, List.length_cons]
      omega
    have hxy :
        xDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
          yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
      exact xDouble_lt_yDoubleIdx_of_xy_split cs hcs seq heq c hc hsplit_xy
    rw [hs_eq] at hidx_s
    have hidx_s' :
        yDoubleStepIdxOf_eq_case cs hcs seq heq c hc <
          xDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
      simpa [xDoubleStepIdxOf_eq_case] using hidx_s
    exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt hxy) hidx_s')
  · have hs_not : yDoubleStepOf_eq_case cs hcs seq heq c hc ∉ suf :=
      step_not_mem_suffix_of_split hsplit_right seq.distinct_pairs
    exact hs_not (hs_eq ▸ hs)

private theorem cycle_image_yStep_order_contradiction_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {u v : α}
    (hu_mem : u ∈ c.members)
    (hv_mem : v ∈ c.members)
    (hu_ne : u ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hv_ne : v ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (himg : cycleProduct cs (Body.orig u) = Body.orig v)
    {midL between midR : List (Body α × Body α)}
    {stepU stepV : Body α × Body α}
    (hmid : mid = midL ++ stepU :: between ++ stepV :: midR)
    (hyU : YStepFor u stepU)
    (hyV : YStepFor v stepV) :
    False := by
  have hstepU_mem : stepU ∈ seq.steps := by
    rw [hsplit_xy]
    simp [hmid, List.append_assoc]
  have hstepV_mem : stepV ∈ seq.steps := by
    rw [hsplit_xy]
    simp [hmid, List.append_assoc]
  have hnot_v_all_x :
      ∀ s ∈ seq.steps, ¬ XStepFor v s := by
    intro s hs hx
    have hv_y : v ∈ seq.yEntries := by
      exact (mem_yEntries_iff).2 ⟨stepV, hstepV_mem, hyV⟩
    have hv_x : v ∈ seq.xEntries := by
      exact (mem_xEntries_iff).2 ⟨s, hs, hx⟩
    exact eq_case_other_member_not_double cs hcs seq heq c hc hv_mem hv_ne
      ⟨hv_x, hv_y⟩
  have hnot_u_all_x :
      ∀ s ∈ seq.steps, ¬ XStepFor u s := by
    intro s hs hx
    have hu_y : u ∈ seq.yEntries := by
      exact (mem_yEntries_iff).2 ⟨stepU, hstepU_mem, hyU⟩
    have hu_x : u ∈ seq.xEntries := by
      exact (mem_xEntries_iff).2 ⟨s, hs, hx⟩
    exact eq_case_other_member_not_double cs hcs seq heq c hc hu_mem hu_ne
      ⟨hu_x, hu_y⟩
  let preV := midL ++ stepU :: between
  have hdecomp :
      mid = preV ++ stepV :: midR := by
    simp [preV, hmid, List.append_assoc]
  have hnot_v_preV_x :
      ∀ s ∈ preV, ¬ XStepFor v s := by
    intro s hs
    exact hnot_v_all_x s (by
      rw [hsplit_xy]
      simp [hdecomp, hs, List.append_assoc])
  have hnot_v_preV_y :
      ∀ s ∈ preV, ¬ YStepFor v s := by
    intro s hs hyS
    have hs_mem : s ∈ seq.steps := by
      rw [hsplit_xy]
      simp [hdecomp, hs, List.append_assoc]
    have hsEq : s = stepV :=
      unique_yStepFor seq hs_mem hstepV_mem hyS hyV
    have hsplit_global :
        seq.steps =
          (pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: preV) ++
            stepV ::
            (midR ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) := by
      simp [hsplit_xy, hdecomp, preV, List.append_assoc]
    have hnot_prefix :
        stepV ∉ pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: preV :=
      step_not_mem_prefix_of_split hsplit_global seq.distinct_pairs
    exact hnot_prefix <| List.mem_append.mpr <|
      Or.inr <| List.mem_cons.mpr <| Or.inr (hsEq ▸ hs)
  have hpreV_fix_v :
      runScript preV (Body.orig v : Body α) = Body.orig v := by
    apply runScript_fix_orig_of_sublist_no_hStep seq hnoXY preV
    · intro s hs
      rw [hsplit_xy]
      simp [hdecomp, hs, List.append_assoc]
    · exact hnot_v_preV_x
    · exact hnot_v_preV_y
  have hnot_u_midR_x :
      ∀ s ∈ midR, ¬ XStepFor u s := by
    intro s hs
    exact hnot_u_all_x s (by
      rw [hsplit_xy]
      simp [hdecomp, hs, List.append_assoc])
  have hnot_u_midR_y :
      ∀ s ∈ midR, ¬ YStepFor u s := by
    intro s hs hyS
    have hs_mem : s ∈ seq.steps := by
      rw [hsplit_xy]
      simp [hdecomp, hs, List.append_assoc]
    have hsEq : s = stepU :=
      unique_yStepFor seq hs_mem hstepU_mem hyS hyU
    have hsplit_global :
        seq.steps =
          (pre ++
            xDoubleStepOf_eq_case cs hcs seq heq c hc ::
            midL) ++
            stepU ::
            (between ++ stepV :: (midR ++
              yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)) := by
      simp [hsplit_xy, hmid, List.append_assoc]
    have hnot_suffix :
        stepU ∉
          between ++ stepV :: (midR ++
            yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) :=
      step_not_mem_suffix_of_split hsplit_global seq.distinct_pairs
    have hstepU_in_suffix :
        stepU ∈
          between ++ stepV :: (midR ++
            yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) := by
      have hu_midR : stepU ∈ midR := hsEq ▸ hs
      have hmem_tail :
          stepU ∈
            midR ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf :=
        List.mem_append.mpr (Or.inl hu_midR)
      have hmem_cons :
          stepU ∈
            stepV :: midR ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf :=
        List.mem_cons.mpr (Or.inr hmem_tail)
      exact List.mem_append.mpr (Or.inr hmem_cons)
    exact hnot_suffix hstepU_in_suffix
  have hmidR_not_u :
      runScript midR Body.y ≠ Body.orig u := by
    apply runScript_avoids_orig_of_sublist_no_hStep seq hnoXY midR
    · intro s hs
      rw [hsplit_xy]
      simp [hdecomp, hs, List.append_assoc]
    · exact hnot_u_midR_x
    · exact hnot_u_midR_y
    · simp
  have hmid_not_u :
      runScript mid (Body.orig v : Body α) ≠ Body.orig u := by
    rw [hdecomp, runScript_append_apply, runScript_cons, Perm.mul_apply, hpreV_fix_v]
    rcases hyV with rfl | rfl <;> simpa [Equiv.swap_comm] using hmidR_not_u
  have hmid_eq_u :
      runScript mid (Body.orig v : Body α) = Body.orig u :=
    runScript_middle_maps_cycle_image_of_split cs hcs seq heq c hc hsplit_xy
      hu_mem hv_mem hu_ne hv_ne
      (nonDouble_member_not_mem_prefix_of_xy_split cs hcs seq heq c hc hsplit_xy
        hv_mem hv_ne)
      (nonDouble_member_not_mem_suffix_of_xy_split cs hcs seq heq c hc hsplit_xy
        hu_mem hu_ne)
      himg
  exact hmid_not_u hmid_eq_u

private theorem exists_yStep_in_mid_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) :
    ∃ step ∈ mid, ∃ a, YStepFor a step := by
  let a := doubleEntryOf_eq_case cs hcs seq heq c hc
  have ha_mem : a ∈ c.members := doubleEntryOf_eq_case_mem cs hcs seq heq c hc
  obtain ⟨b, hb_mem, hba, himg⟩ := cycleProduct_image_member cs hcs c hc a ha_mem
  have hmid_b :
      runScript mid (Body.orig b : Body α) = Body.y := by
    apply runScript_middle_maps_image_doubleEntry_to_y_of_split cs hcs seq heq c hc hsplit_xy
    · exact hb_mem
    · exact hba
    · exact nonDouble_member_not_mem_prefix_of_xy_split cs hcs seq heq c hc hsplit_xy
        hb_mem hba
    · exact doubleEntry_not_mem_suffix_of_xy_split cs hcs seq heq c hc hsplit_xy
    · simpa [a] using himg
  by_contra hnone
  push_neg at hnone
  have hsub_mid : ∀ s ∈ mid, s ∈ seq.steps := by
    intro s hs
    rw [hsplit_xy]
    simp [hs, List.append_assoc]
  have havoid :
      runScript mid (Body.orig b : Body α) ≠ Body.y :=
    runScript_avoids_y_of_sublist_no_ySteps seq hnoXY mid hsub_mid hnone (by simp)
  exact havoid hmid_b

private theorem exists_leftmost_internalGapY_in_mid_of_xy_split_of_no_external
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    (hnoExt : ∀ s ∈ mid, ¬ ExternalGapYStepOf_eq_case cs hcs seq heq c hc s) :
    ∃ preI stepI sufI,
      mid = preI ++ stepI :: sufI ∧
      InternalGapYStepOf_eq_case cs hcs seq heq c hc stepI ∧
      ∀ s ∈ preI, ¬ InternalGapYStepOf_eq_case cs hcs seq heq c hc s := by
  classical
  have hex_int :
      ∃ step ∈ mid, InternalGapYStepOf_eq_case cs hcs seq heq c hc step := by
    rcases exists_yStep_in_mid_of_xy_split cs hcs seq hnoXY heq c hc hsplit_xy with
      ⟨step, hstep_mid, a, hys⟩
    have hgap_strict :=
      gap_strict_of_mid_member_of_xy_split cs hcs seq heq c hc hsplit_xy hstep_mid
    have hgap : GapYStepOf_eq_case cs hcs seq heq c hc step := by
      refine ⟨⟨a, hys⟩, Nat.le_of_lt hgap_strict.1, Nat.le_of_lt hgap_strict.2⟩
    by_cases ha_mem : a ∈ c.members
    · exact ⟨step, hstep_mid, ⟨a, hys, ha_mem, hgap⟩⟩
    · exact False.elim (hnoExt step hstep_mid ⟨a, hys, ha_mem, hgap⟩)
  rcases exists_split_leftmost
      (p := InternalGapYStepOf_eq_case cs hcs seq heq c hc) mid hex_int with
    ⟨preI, stepI, sufI, hsplitI, hInt, hpreI⟩
  exact ⟨preI, stepI, sufI, hsplitI, hInt, hpreI⟩

private theorem internalGapYStep_member_ne_double_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {step : Body α × Body α}
    (hstep_mid : step ∈ mid)
    (hInt : InternalGapYStepOf_eq_case cs hcs seq heq c hc step) :
    ∃ a, YStepFor a step ∧ a ∈ c.members ∧
      a ≠ doubleEntryOf_eq_case cs hcs seq heq c hc := by
  rcases hInt with ⟨a, hy, ha_mem, _⟩
  have hstep_mem : step ∈ seq.steps := by
    rw [hsplit_xy]
    simp [hstep_mid, List.append_assoc]
  have ha_ne :
      a ≠ doubleEntryOf_eq_case cs hcs seq heq c hc := by
    intro hEq
    have hy_double :
        YStepFor (doubleEntryOf_eq_case cs hcs seq heq c hc) step := by
      simpa [hEq] using hy
    have hstepEq :
        step = yDoubleStepOf_eq_case cs hcs seq heq c hc := by
      exact unique_yStepFor seq hstep_mem
        (yDoubleStepOf_eq_case_mem cs hcs seq heq c hc) hy_double
        (yDoubleStepOf_eq_case_spec cs hcs seq heq c hc)
    have hsplit_right :
        seq.steps =
          (pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: mid) ++
            yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf := by
      simpa [List.append_assoc] using hsplit_xy
    have hnot_prefix :
        yDoubleStepOf_eq_case cs hcs seq heq c hc ∉
          pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: mid :=
      step_not_mem_prefix_of_split hsplit_right seq.distinct_pairs
    have hnot_mid :
        yDoubleStepOf_eq_case cs hcs seq heq c hc ∉ mid := by
      intro hy_mid
      exact hnot_prefix <|
        List.mem_append.mpr <| Or.inr <| List.mem_cons.mpr <| Or.inr hy_mid
    exact hnot_mid (hstepEq ▸ hstep_mid)
  exact ⟨a, hy, ha_mem, ha_ne⟩

private theorem no_yStep_before_leftmost_internal_of_no_external_xy
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    (hnoExt : ∀ s ∈ mid, ¬ ExternalGapYStepOf_eq_case cs hcs seq heq c hc s)
    {preI sufI : List (Body α × Body α)}
    {stepI : Body α × Body α}
    (hsplitI : mid = preI ++ stepI :: sufI)
    (_hInt : InternalGapYStepOf_eq_case cs hcs seq heq c hc stepI)
    (hpreI : ∀ s ∈ preI, ¬ InternalGapYStepOf_eq_case cs hcs seq heq c hc s) :
    ∀ s ∈ preI, ∀ a, ¬ YStepFor a s := by
  intro s hs a hys
  have hs_mid : s ∈ mid := by
    rw [hsplitI]
    exact List.mem_append.mpr (Or.inl hs)
  have hs_gap_strict :=
    gap_strict_of_mid_member_of_xy_split cs hcs seq heq c hc hsplit_xy hs_mid
  have hs_gap : GapYStepOf_eq_case cs hcs seq heq c hc s := by
    refine ⟨⟨a, hys⟩, Nat.le_of_lt hs_gap_strict.1, Nat.le_of_lt hs_gap_strict.2⟩
  by_cases ha_mem : a ∈ c.members
  · exact hpreI s hs ⟨a, hys, ha_mem, hs_gap⟩
  · exact hnoExt s hs_mid ⟨a, hys, ha_mem, hs_gap⟩

private theorem leftmost_internalGapY_data_of_no_external_xy
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    (hnoExt : ∀ s ∈ mid, ¬ ExternalGapYStepOf_eq_case cs hcs seq heq c hc s) :
    ∃ preI stepI sufI a,
      mid = preI ++ stepI :: sufI ∧
      YStepFor a stepI ∧
      a ∈ c.members ∧
      a ≠ doubleEntryOf_eq_case cs hcs seq heq c hc ∧
      (∀ s ∈ preI, ∀ b, ¬ YStepFor b s) ∧
      (∀ s ∈ seq.steps, ¬ XStepFor a s) ∧
      (∀ s ∈ sufI, ¬ YStepFor a s) := by
  rcases exists_leftmost_internalGapY_in_mid_of_xy_split_of_no_external
      cs hcs seq hnoXY heq c hc hsplit_xy hnoExt with
    ⟨preI, stepI, sufI, hsplitI, hInt, hpreI⟩
  have hstepI_mid : stepI ∈ mid := by
    rw [hsplitI]
    exact List.mem_append.mpr <| Or.inr <| List.mem_cons.mpr <| Or.inl rfl
  rcases internalGapYStep_member_ne_double_of_xy_split
      cs hcs seq heq c hc hsplit_xy
      hstepI_mid
      hInt with
    ⟨a, hyI, ha_mem, ha_ne_double⟩
  have hstepI_mem : stepI ∈ seq.steps := by
    rw [hsplit_xy]
    simp [hsplitI, List.append_assoc]
  have hnot_a_x_anywhere :
      ∀ s ∈ seq.steps, ¬ XStepFor a s :=
    internalGapYStep_nonDouble_no_x_anywhere cs hcs seq heq c hc
      hstepI_mem hyI ha_mem ha_ne_double
  have hno_preI_y :
      ∀ s ∈ preI, ∀ b, ¬ YStepFor b s :=
    no_yStep_before_leftmost_internal_of_no_external_xy cs hcs seq heq c hc
      hsplit_xy hnoExt hsplitI hInt hpreI
  have hsplit_ext :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          (preI ++ stepI :: (sufI ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)) := by
    simp [hsplit_xy, hsplitI, List.append_assoc]
  have hsplit_suffix :
      preI ++ stepI :: (sufI ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) =
        preI ++ stepI :: (sufI ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) := rfl
  obtain ⟨a', hyI', _, hno_a_suf⟩ :=
    internalGapYStep_no_y_mentions_in_suffix_of_split cs hcs seq heq c hc
      hsplit_ext
      hsplit_suffix
      hInt
  have ha'_eq : a' = a := by
    exact helper_step_mentions_eq (seq.helper_constraint stepI hstepI_mem)
      (by rcases hyI' with rfl | rfl <;> simp)
      (by rcases hyI with rfl | rfl <;> simp)
  refine ⟨preI, stepI, sufI, a, hsplitI, hyI, ha_mem, ha_ne_double, hno_preI_y, hnot_a_x_anywhere, ?_⟩
  intro s hs
  have hs_tail :
      s ∈ sufI ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf := by
    exact List.mem_append.mpr (Or.inl hs)
  simpa [ha'_eq] using hno_a_suf s hs_tail

private theorem leftmost_internal_successor_y_contradiction_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {preI sufI between midR : List (Body α × Body α)}
    {stepI stepV : Body α × Body α}
    {a v : α}
    (hsplitI : mid = preI ++ stepI :: sufI)
    (hyI : YStepFor a stepI)
    (ha_mem : a ∈ c.members)
    (ha_ne : a ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hno_preI_y : ∀ s ∈ preI, ∀ b, ¬ YStepFor b s)
    (hsufI : sufI = between ++ stepV :: midR)
    (hyV : YStepFor v stepV)
    (hv_mem : v ∈ c.members)
    (hv_ne : v ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (himg : cycleProduct cs (Body.orig a) = Body.orig v) :
    False := by
  have hstepV_not_preI : stepV ∉ preI := by
    intro hs
    exact hno_preI_y stepV hs v hyV
  have hmid :
      mid = preI ++ stepI :: between ++ stepV :: midR := by
    simp [hsplitI, hsufI, List.append_assoc]
  exact cycle_image_yStep_order_contradiction_of_xy_split cs hcs seq hnoXY heq c hc
    hsplit_xy ha_mem hv_mem ha_ne hv_ne himg hmid hyI hyV

private theorem leftmost_internal_imageDouble_contradiction_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {preI sufI : List (Body α × Body α)}
    {stepI : Body α × Body α}
    {a : α}
    (hsplitI : mid = preI ++ stepI :: sufI)
    (hyI : YStepFor a stepI)
    (ha_mem : a ∈ c.members)
    (ha_ne : a ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hno_preI_y : ∀ s ∈ preI, ∀ b, ¬ YStepFor b s)
    (hnot_a_x_anywhere : ∀ s ∈ seq.steps, ¬ XStepFor a s)
    (hnot_a_sufI_y : ∀ s ∈ sufI, ¬ YStepFor a s)
    (himg :
      cycleProduct cs (Body.orig a) =
        Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) :
    False := by
  have hsub_preI : ∀ s ∈ preI, s ∈ seq.steps := by
    intro s hs
    rw [hsplit_xy]
    simp [hsplitI, hs, List.append_assoc]
  have hsub_sufI : ∀ s ∈ sufI, s ∈ seq.steps := by
    intro s hs
    rw [hsplit_xy]
    simp [hsplitI, hs, List.append_assoc]
  have hnot_a_preI_x : ∀ s ∈ preI, ¬ XStepFor a s := by
    intro s hs
    exact hnot_a_x_anywhere s (hsub_preI s hs)
  have hnot_a_preI_y : ∀ s ∈ preI, ¬ YStepFor a s := by
    intro s hs
    exact hno_preI_y s hs a
  have hpreI_x_ne_a : runScript preI Body.x ≠ Body.orig a := by
    apply runScript_avoids_orig_of_sublist_no_hStep seq hnoXY preI hsub_preI
      hnot_a_preI_x hnot_a_preI_y
    simp
  have hpreI_x_ne_y : runScript preI Body.x ≠ Body.y := by
    apply runScript_avoids_y_of_sublist_no_ySteps seq hnoXY preI hsub_preI hno_preI_y
    simp
  have hnot_a_sufI_x : ∀ s ∈ sufI, ¬ XStepFor a s := by
    intro s hs
    exact hnot_a_x_anywhere s (hsub_sufI s hs)
  have hsufI_x_ne_a :
      runScript sufI (runScript preI Body.x) ≠ Body.orig a := by
    apply runScript_avoids_orig_of_sublist_no_hStep seq hnoXY sufI hsub_sufI
      hnot_a_sufI_x hnot_a_sufI_y
    exact hpreI_x_ne_a
  have hmid_x_ne_a : runScript mid Body.x ≠ Body.orig a := by
    rw [hsplitI, runScript_append_apply, runScript_cons, Perm.mul_apply]
    rcases hyI with hyI | hyI
    · rw [hyI]
      have hswap_fix :
          Equiv.swap Body.y (Body.orig a) (runScript preI Body.x) =
            runScript preI Body.x := by
        exact Equiv.swap_apply_of_ne_of_ne hpreI_x_ne_y hpreI_x_ne_a
      rw [hswap_fix]
      exact hsufI_x_ne_a
    · rw [hyI]
      have hswap_fix :
          Equiv.swap (Body.orig a) Body.y (runScript preI Body.x) =
            runScript preI Body.x := by
        exact Equiv.swap_apply_of_ne_of_ne hpreI_x_ne_a hpreI_x_ne_y
      rw [hswap_fix]
      exact hsufI_x_ne_a
  have hmid_x_eq : runScript mid Body.x = Body.orig a := by
    apply runScript_middle_maps_x_to_preimage_doubleEntry_of_split cs hcs seq heq c hc hsplit_xy
    · exact ha_mem
    · exact ha_ne
    · exact doubleEntry_not_mem_prefix_of_xy_split cs hcs seq heq c hc hsplit_xy
    · exact nonDouble_member_not_mem_suffix_of_xy_split cs hcs seq heq c hc hsplit_xy
        ha_mem ha_ne
    · exact himg
  exact hmid_x_ne_a hmid_x_eq

private theorem leftmost_internal_imageNonDouble_contradiction_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {preI sufI : List (Body α × Body α)}
    {stepI : Body α × Body α}
    {a b : α}
    (hsplitI : mid = preI ++ stepI :: sufI)
    (hyI : YStepFor a stepI)
    (ha_mem : a ∈ c.members)
    (ha_ne : a ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hno_preI_y : ∀ s ∈ preI, ∀ bb, ¬ YStepFor bb s)
    (hnot_a_x_anywhere : ∀ s ∈ seq.steps, ¬ XStepFor a s)
    (hnot_a_sufI_y : ∀ s ∈ sufI, ¬ YStepFor a s)
    (hb_mem : b ∈ c.members)
    (hb_ne : b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (himg : cycleProduct cs (Body.orig a) = Body.orig b) :
    False := by
  have hsub_preI : ∀ s ∈ preI, s ∈ seq.steps := by
    intro s hs
    rw [hsplit_xy]
    simp [hsplitI, hs, List.append_assoc]
  have hsub_sufI : ∀ s ∈ sufI, s ∈ seq.steps := by
    intro s hs
    rw [hsplit_xy]
    simp [hsplitI, hs, List.append_assoc]
  have hpreI_b_ne_y : runScript preI (Body.orig b) ≠ Body.y := by
    apply runScript_avoids_y_of_sublist_no_ySteps seq hnoXY preI hsub_preI hno_preI_y
    simp
  have hnot_a_sufI_x : ∀ s ∈ sufI, ¬ XStepFor a s := by
    intro s hs
    exact hnot_a_x_anywhere s (hsub_sufI s hs)
  have hmid_not_a : runScript mid (Body.orig b) ≠ Body.orig a := by
    rw [hsplitI, runScript_append_apply, runScript_cons, Perm.mul_apply]
    have hswap_not_a :
        Equiv.swap stepI.1 stepI.2 (runScript preI (Body.orig b)) ≠ Body.orig a := by
      rcases hyI with hyI | hyI
      · rw [hyI]
        intro hEq
        have : runScript preI (Body.orig b) = Body.y := by
          apply (Equiv.swap Body.y (Body.orig a)).injective
          exact hEq.trans (Equiv.swap_apply_left _ _).symm
        exact hpreI_b_ne_y this
      · rw [hyI]
        intro hEq
        have : runScript preI (Body.orig b) = Body.y := by
          apply (Equiv.swap (Body.orig a) Body.y).injective
          exact hEq.trans (Equiv.swap_apply_right _ _).symm
        exact hpreI_b_ne_y this
    apply runScript_avoids_orig_of_sublist_no_hStep seq hnoXY sufI hsub_sufI
      hnot_a_sufI_x hnot_a_sufI_y
    exact hswap_not_a
  have hmid_eq_a :
      runScript mid (Body.orig b) = Body.orig a := by
    apply runScript_middle_maps_cycle_image_of_split cs hcs seq heq c hc hsplit_xy
    · exact ha_mem
    · exact hb_mem
    · exact ha_ne
    · exact hb_ne
    · exact nonDouble_member_not_mem_prefix_of_xy_split cs hcs seq heq c hc hsplit_xy
        hb_mem hb_ne
    · exact nonDouble_member_not_mem_suffix_of_xy_split cs hcs seq heq c hc hsplit_xy
        ha_mem ha_ne
    · exact himg
  exact hmid_not_a hmid_eq_a

private theorem leftmost_internal_image_case_contradiction_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {preI sufI : List (Body α × Body α)}
    {stepI : Body α × Body α}
    {a b : α}
    (hsplitI : mid = preI ++ stepI :: sufI)
    (hyI : YStepFor a stepI)
    (ha_mem : a ∈ c.members)
    (ha_ne : a ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hno_preI_y : ∀ s ∈ preI, ∀ bb, ¬ YStepFor bb s)
    (hnot_a_x_anywhere : ∀ s ∈ seq.steps, ¬ XStepFor a s)
    (hnot_a_sufI_y : ∀ s ∈ sufI, ¬ YStepFor a s)
    (hb_mem : b ∈ c.members)
    (himg : cycleProduct cs (Body.orig a) = Body.orig b)
    (hb_case :
      b = doubleEntryOf_eq_case cs hcs seq heq c hc ∨
        ∃ between stepV midR,
          sufI = between ++ stepV :: midR ∧
          YStepFor b stepV ∧
          b ≠ doubleEntryOf_eq_case cs hcs seq heq c hc) :
    False := by
  rcases hb_case with rfl | ⟨between, stepV, midR, hsufI, hyV, hb_ne⟩
  · exact leftmost_internal_imageDouble_contradiction_of_xy_split cs hcs seq hnoXY heq c hc
      hsplit_xy hsplitI hyI ha_mem ha_ne hno_preI_y hnot_a_x_anywhere hnot_a_sufI_y himg
  · exact leftmost_internal_successor_y_contradiction_of_xy_split cs hcs seq hnoXY heq c hc
      hsplit_xy hsplitI hyI ha_mem ha_ne hno_preI_y hsufI hyV hb_mem hb_ne himg

private theorem no_externalGapY_contradiction_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    (hnoExt : ∀ s ∈ mid, ¬ ExternalGapYStepOf_eq_case cs hcs seq heq c hc s) :
    False := by
  rcases leftmost_internalGapY_data_of_no_external_xy cs hcs seq hnoXY heq c hc hsplit_xy hnoExt with
    ⟨preI, stepI, sufI, a, hsplitI, hyI, ha_mem, ha_ne, hno_preI_y,
      hnot_a_x_anywhere, hnot_a_sufI_y⟩
  obtain ⟨b, hb_mem, hba, himg⟩ := cycleProduct_image_member cs hcs c hc a ha_mem
  by_cases hb_double : b = doubleEntryOf_eq_case cs hcs seq heq c hc
  · exact leftmost_internal_imageDouble_contradiction_of_xy_split cs hcs seq hnoXY heq c hc
      hsplit_xy hsplitI hyI ha_mem ha_ne hno_preI_y hnot_a_x_anywhere hnot_a_sufI_y
      (by simpa [hb_double] using himg)
  · exact leftmost_internal_imageNonDouble_contradiction_of_xy_split cs hcs seq hnoXY heq c hc
      hsplit_xy hsplitI hyI ha_mem ha_ne hno_preI_y hnot_a_x_anywhere hnot_a_sufI_y
      hb_mem hb_double himg

private theorem exists_externalGapY_of_eq_case_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) :
    ∃ step ∈ mid, ExternalGapYStepOf_eq_case cs hcs seq heq c hc step := by
  by_contra hnone
  push_neg at hnone
  exact no_externalGapY_contradiction_of_xy_split cs hcs seq hnoXY heq c hc hsplit_xy hnone

private theorem exists_externalGapY_of_minGap_xy
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          mid ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf) :
    ∃ step ∈ mid,
      ExternalGapYStepOf_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) step := by
  exact exists_externalGapY_of_eq_case_xy_split cs hcs seq hnoXY heq
    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
    hsplit_xy

private theorem runScript_mid_maps_external_to_y_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {midL midR : List (Body α × Body α)}
    {stepE : Body α × Body α}
    {h : α}
    (hmid : mid = midL ++ stepE :: midR)
    (hyE : YStepFor h stepE)
    (hnot_h_midL_x : ∀ s ∈ midL, ¬ XStepFor h s)
    (hnot_h_midL_y : ∀ s ∈ midL, ¬ YStepFor h s)
    (hnot_midR_y : ∀ s ∈ midR, ∀ b, ¬ YStepFor b s) :
    runScript mid (Body.orig h : Body α) = Body.y := by
  have hmidL_fix_h :
      runScript midL (Body.orig h : Body α) = Body.orig h := by
    apply runScript_fix_orig_of_sublist_no_hStep seq hnoXY midL
    · intro s hs
      rw [hsplit_xy]
      simp [hmid, hs, List.append_assoc]
    · exact hnot_h_midL_x
    · exact hnot_h_midL_y
  have hmidR_fix_y :
      runScript midR Body.y = Body.y := by
    apply runScript_fix_y_of_sublist_no_ySteps seq hnoXY midR
    · intro s hs
      rw [hsplit_xy]
      simp [hmid, hs, List.append_assoc]
    · exact hnot_midR_y
  rw [hmid, runScript_append_apply, runScript_cons, Perm.mul_apply, hmidL_fix_h]
  rcases hyE with rfl | rfl <;> simp [hmidR_fix_y, Equiv.swap_comm]

private theorem externalGapY_yDouble_contradiction_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {midL midR : List (Body α × Body α)}
    {stepE : Body α × Body α}
    {h : α}
    (hmid : mid = midL ++ stepE :: midR)
    (hyE : YStepFor h stepE)
    (hnot_mem_c : h ∉ c.members)
    (hnot_h_midL_x : ∀ s ∈ midL, ¬ XStepFor h s)
    (hnot_h_midL_y : ∀ s ∈ midL, ¬ YStepFor h s)
    (hnot_midR_y : ∀ s ∈ midR, ∀ b, ¬ YStepFor b s) :
    False := by
  have hmid_h :
      runScript mid (Body.orig h : Body α) = Body.y :=
    runScript_mid_maps_external_to_y_of_xy_split cs hcs seq hnoXY heq c hc
      hsplit_xy hmid hyE hnot_h_midL_x hnot_h_midL_y hnot_midR_y
  let a := doubleEntryOf_eq_case cs hcs seq heq c hc
  have ha_mem : a ∈ c.members := doubleEntryOf_eq_case_mem cs hcs seq heq c hc
  obtain ⟨b, hb_mem, hba, himg⟩ := cycleProduct_image_member cs hcs c hc a ha_mem
  have hmid_b :
      runScript mid (Body.orig b : Body α) = Body.y := by
    apply runScript_middle_maps_image_doubleEntry_to_y_of_split cs hcs seq heq c hc hsplit_xy
    · exact hb_mem
    · exact hba
    · exact nonDouble_member_not_mem_prefix_of_xy_split cs hcs seq heq c hc hsplit_xy
        hb_mem hba
    · exact doubleEntry_not_mem_suffix_of_xy_split cs hcs seq heq c hc hsplit_xy
    · simpa [a] using himg
  have hEq : (Body.orig h : Body α) = Body.orig b := by
    exact (runScript mid).injective (hmid_h.trans hmid_b.symm)
  exact hnot_mem_c (Body.orig.inj hEq ▸ hb_mem)

private theorem externalGapY_internalNonDouble_contradiction_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {midL preI midR : List (Body α × Body α)}
    {stepE stepI : Body α × Body α}
    {h a : α}
    (hmid :
      mid = midL ++ stepE :: preI ++ stepI :: midR)
    (hyE : YStepFor h stepE)
    (hnot_mem_c : h ∉ c.members)
    (hyI : YStepFor a stepI)
    (ha_mem : a ∈ c.members)
    (ha_ne_double : a ≠ doubleEntryOf_eq_case cs hcs seq heq c hc)
    (hnot_h_midL_x : ∀ s ∈ midL, ¬ XStepFor h s)
    (hnot_h_midL_y : ∀ s ∈ midL, ¬ YStepFor h s)
    (hnot_preI_y : ∀ s ∈ preI, ∀ b, ¬ YStepFor b s)
    (hnot_a_midR_x : ∀ s ∈ midR, ¬ XStepFor a s)
    (hnot_a_midR_y : ∀ s ∈ midR, ¬ YStepFor a s) :
    False := by
  have ha_ne_h : a ≠ h := by
    intro hah
    exact hnot_mem_c (hah ▸ ha_mem)
  have hmid_h :
      runScript mid (Body.orig h : Body α) = Body.orig a :=
    runScript_mid_maps_external_to_internal_of_xy_split cs hcs seq hnoXY heq c hc
      hsplit_xy hmid hyE hyI ha_ne_h
      hnot_h_midL_x hnot_h_midL_y hnot_preI_y hnot_a_midR_x hnot_a_midR_y
  obtain ⟨b, hb_mem, hba, himg⟩ := cycleProduct_image_member cs hcs c hc a ha_mem
  by_cases hb_double : b = doubleEntryOf_eq_case cs hcs seq heq c hc
  · have hmid_x :
        runScript mid Body.x = Body.orig a := by
      apply runScript_middle_maps_x_to_preimage_doubleEntry_of_split cs hcs seq heq c hc hsplit_xy
      · exact ha_mem
      · exact ha_ne_double
      · exact doubleEntry_not_mem_prefix_of_xy_split cs hcs seq heq c hc hsplit_xy
      · exact nonDouble_member_not_mem_suffix_of_xy_split cs hcs seq heq c hc hsplit_xy
          ha_mem ha_ne_double
      · simpa [hb_double] using himg
    have hEq : (Body.orig h : Body α) = Body.x := by
      exact (runScript mid).injective (hmid_h.trans hmid_x.symm)
    cases hEq
  · have hmid_b :
        runScript mid (Body.orig b : Body α) = Body.orig a := by
      apply runScript_middle_maps_cycle_image_of_split cs hcs seq heq c hc hsplit_xy
      · exact ha_mem
      · exact hb_mem
      · exact ha_ne_double
      · exact hb_double
      · exact nonDouble_member_not_mem_prefix_of_xy_split cs hcs seq heq c hc hsplit_xy
          hb_mem hb_double
      · exact nonDouble_member_not_mem_suffix_of_xy_split cs hcs seq heq c hc hsplit_xy
          ha_mem ha_ne_double
      · exact himg
    have hEq : (Body.orig h : Body α) = Body.orig b := by
      exact (runScript mid).injective (hmid_h.trans hmid_b.symm)
    exact hnot_mem_c (Body.orig.inj hEq ▸ hb_mem)

private theorem rightmost_internalGapY_eq_imageDouble_of_xy_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc ::
          mid ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf)
    {midL midR : List (Body α × Body α)}
    {stepI : Body α × Body α}
    (hmid : mid = midL ++ stepI :: midR)
    (hInt : InternalGapYStepOf_eq_case cs hcs seq heq c hc stepI)
    (hnot_midR_y : ∀ s ∈ midR, ∀ b, ¬ YStepFor b s) :
    ∃ h, YStepFor h stepI ∧ h ∈ c.members ∧
      h ≠ doubleEntryOf_eq_case cs hcs seq heq c hc ∧
      cycleProduct cs (Body.orig (doubleEntryOf_eq_case cs hcs seq heq c hc)) = Body.orig h := by
  rcases hInt with ⟨h, hyI, hh_mem, hgapI⟩
  have hstepI_mem : stepI ∈ seq.steps := by
    rw [hsplit_xy]
    simp [hmid, List.append_assoc]
  have hh_ne_double : h ≠ doubleEntryOf_eq_case cs hcs seq heq c hc := by
    intro hEq
    have hy_double :
        YStepFor (doubleEntryOf_eq_case cs hcs seq heq c hc) stepI := by
      simpa [hEq] using hyI
    have hstepEq :
        stepI = yDoubleStepOf_eq_case cs hcs seq heq c hc := by
      exact unique_yStepFor seq hstepI_mem
        (yDoubleStepOf_eq_case_mem cs hcs seq heq c hc) hy_double
        (yDoubleStepOf_eq_case_spec cs hcs seq heq c hc)
    have hnot_prefix :
        yDoubleStepOf_eq_case cs hcs seq heq c hc ∉
          pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: mid := by
      have hsplit_right :
          seq.steps =
            (pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: mid) ++
              yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf := by
        simpa [List.append_assoc] using hsplit_xy
      exact step_not_mem_prefix_of_split hsplit_right seq.distinct_pairs
    have hnot_mid :
        yDoubleStepOf_eq_case cs hcs seq heq c hc ∉ mid := by
      intro hy_mid
      exact hnot_prefix <| List.mem_append.mpr <|
        Or.inr <| List.mem_cons.mpr <| Or.inr hy_mid
    exact hnot_mid (hmid ▸ List.mem_append.mpr <| Or.inr <| List.mem_cons.mpr <| Or.inl hstepEq.symm)
  have hnot_h_midL_x :
      ∀ s ∈ midL, ¬ XStepFor h s := by
    intro s hs
    exact internalGapYStep_nonDouble_no_x_anywhere cs hcs seq heq c hc hstepI_mem hyI hh_mem hh_ne_double
      s (by
        rw [hsplit_xy]
        simp [hmid, hs, List.append_assoc])
  have hnot_h_midL_y :
      ∀ s ∈ midL, ¬ YStepFor h s := by
    intro s hs hyS
    have hs_mem : s ∈ seq.steps := by
      rw [hsplit_xy]
      simp [hmid, hs, List.append_assoc]
    have hsEq : s = stepI :=
      unique_yStepFor seq hs_mem hstepI_mem hyS hyI
    have hsplit_global :
        seq.steps =
          (pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: midL) ++
            stepI ::
            (midR ++ yDoubleStepOf_eq_case cs hcs seq heq c hc :: suf) := by
      simp [hsplit_xy, hmid, List.append_assoc]
    have hnot_prefix :
        stepI ∉ pre ++ xDoubleStepOf_eq_case cs hcs seq heq c hc :: midL :=
      step_not_mem_prefix_of_split hsplit_global seq.distinct_pairs
    have hnot : stepI ∉ midL := by
      intro hmem
      exact hnot_prefix <| List.mem_append.mpr <|
        Or.inr <| List.mem_cons.mpr <| Or.inr hmem
    exact hnot (hsEq ▸ hs)
  have hmid_h :
      runScript mid (Body.orig h : Body α) = Body.y :=
    runScript_mid_maps_external_to_y_of_xy_split cs hcs seq hnoXY heq c hc
      hsplit_xy hmid hyI hnot_h_midL_x hnot_h_midL_y hnot_midR_y
  let a := doubleEntryOf_eq_case cs hcs seq heq c hc
  obtain ⟨b, hb_mem, hba, himg⟩ := cycleProduct_image_member cs hcs c hc a
    (doubleEntryOf_eq_case_mem cs hcs seq heq c hc)
  have hmid_b :
      runScript mid (Body.orig b : Body α) = Body.y := by
    apply runScript_middle_maps_image_doubleEntry_to_y_of_split cs hcs seq heq c hc hsplit_xy
    · exact hb_mem
    · exact hba
    · exact nonDouble_member_not_mem_prefix_of_xy_split cs hcs seq heq c hc hsplit_xy
        hb_mem hba
    · exact doubleEntry_not_mem_suffix_of_xy_split cs hcs seq heq c hc hsplit_xy
    · simpa [a] using himg
  have hEq : h = b := by
    exact Body.orig.inj ((runScript mid).injective (hmid_h.trans hmid_b.symm))
  refine ⟨h, hyI, hh_mem, hh_ne_double, ?_⟩
  simpa [a, hEq] using himg

private theorem exists_rightmost_externalGapY_step_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    (hex :
      ∃ step ∈ seq.steps, ExternalGapYStepOf_eq_case cs hcs seq heq c hc step) :
    ∃ pre step suf,
      seq.steps = pre ++ step :: suf ∧
      ExternalGapYStepOf_eq_case cs hcs seq heq c hc step ∧
      ∀ s ∈ suf, ¬ ExternalGapYStepOf_eq_case cs hcs seq heq c hc s := by
  classical
  rcases exists_split_rightmost
      (p := ExternalGapYStepOf_eq_case cs hcs seq heq c hc) seq.steps hex with
    ⟨pre, step, suf, hsplit, hprop, hsuf⟩
  exact ⟨pre, step, suf, hsplit, hprop, hsuf⟩

private theorem exists_rightmost_externalGapY_of_minGap_xy
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          mid ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf) :
    ∃ preE stepE sufE,
      seq.steps = preE ++ stepE :: sufE ∧
      ExternalGapYStepOf_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) stepE ∧
      ∀ s ∈ sufE, ¬ ExternalGapYStepOf_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) s := by
  rcases exists_externalGapY_of_minGap_xy cs hcs hcs_nonempty seq hnoXY heq hsplit_xy with
    ⟨step, hstep_mid, hExt⟩
  have hstep_mem : step ∈ seq.steps := by
    rw [hsplit_xy]
    simp [hstep_mid, List.append_assoc]
  exact exists_rightmost_externalGapY_step_of_eq_case cs hcs seq heq
    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
    ⟨step, hstep_mem, hExt⟩

private theorem externalGapYStep_has_other_cycle_of_eq_case
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {step : Body α × Body α} (hstep : step ∈ seq.steps)
    (hExt : ExternalGapYStepOf_eq_case cs hcs seq heq c hc step) :
    ∃ h d, YStepFor h step ∧ d ∈ cs ∧ h ∈ d.members ∧ d ≠ c := by
  rcases hExt with ⟨h, hy, hnotc, _hgap⟩
  have hmem :
      h ∈ ((cs.map Cycle.members).flatten).toFinset :=
    orig_step_mem_members_of_eq_case cs hcs seq heq hstep (Or.inl hy)
  have hmem' : h ∈ (cs.map Cycle.members).flatten := by
    simpa using hmem
  rw [mem_flatten_members_iff] at hmem'
  rcases hmem' with ⟨d, hd, hdm⟩
  have hdc : d ≠ c := by
    intro hEq
    subst d
    exact hnotc hdm
  exact ⟨h, d, hy, hd, hdm, hdc⟩

private theorem other_gap_mention_of_external_forces_nested_cycle
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    {h : α}
    {stepE stepH : Body α × Body α}
    (hstepE : stepE ∈ seq.steps)
    (hyE : YStepFor h stepE)
    (hnot_mem_c : h ∉ c.members)
    (hgapE : GapYStepOf_eq_case cs hcs seq heq c hc stepE)
    (hstepE_gap_strict :
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) <
        stepIdx stepE seq.steps ∧
      stepIdx stepE seq.steps <
        max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc))
    (hstepH : stepH ∈ seq.steps)
    (hh_stepH : Body.orig h ∈ [stepH.1, stepH.2])
    (hstepH_ne : stepH ≠ stepE)
    (hstepH_gap :
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) <
        stepIdx stepH seq.steps ∧
      stepIdx stepH seq.steps <
        max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc)) :
    ∃ d, ∃ hd : d ∈ cs, d ≠ c ∧
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) <
        xDoubleStepIdxOf_eq_case cs hcs seq heq d hd ∧
      xDoubleStepIdxOf_eq_case cs hcs seq heq d hd <
        max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
            (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) ∧
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) <
        yDoubleStepIdxOf_eq_case cs hcs seq heq d hd ∧
      yDoubleStepIdxOf_eq_case cs hcs seq heq d hd <
        max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
            (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) := by
  have hstepE_mentions : Body.orig h ∈ [stepE.1, stepE.2] := by
    rcases hyE with rfl | rfl <;> simp
  obtain ⟨h', d, hyE', hd, hh_mem_d, hdc⟩ :=
    externalGapYStep_has_other_cycle_of_eq_case cs hcs seq heq c hc hstepE
      ⟨h, hyE, hnot_mem_c, hgapE⟩
  have hstepE_mentions' : Body.orig h' ∈ [stepE.1, stepE.2] := by
    rcases hyE' with rfl | rfl <;> simp
  have hh_eq : h' = h := by
    exact helper_step_mentions_eq (seq.helper_constraint stepE hstepE) hstepE_mentions' hstepE_mentions
  subst h'
  have hstepH_form :=
    step_form_of_helper_and_orig_mem (seq.helper_constraint stepH hstepH) hh_stepH
  have hxH : XStepFor h stepH := by
    rcases hstepH_form with hx | hx | hy | hy
    · exact Or.inl hx
    · exact Or.inr hx
    · exfalso
      have : stepH = stepE :=
        unique_yStepFor seq hstepH hstepE (Or.inl hy) hyE
      exact hstepH_ne this
    · exfalso
      have : stepH = stepE :=
        unique_yStepFor seq hstepH hstepE (Or.inr hy) hyE
      exact hstepH_ne this
  have hh_x : h ∈ seq.xEntries := by
    exact (mem_xEntries_iff).2 ⟨stepH, hstepH, hxH⟩
  have hh_y : h ∈ seq.yEntries := by
    exact (mem_yEntries_iff).2 ⟨stepE, hstepE, hyE⟩
  have hh_double_eq : h = doubleEntryOf_eq_case cs hcs seq heq d hd := by
    exact (Classical.choose_spec (existsUnique_doubleEntry_of_eq_case cs hcs seq heq d hd)).2 h
      ⟨hh_mem_d, hh_x, hh_y⟩
  have hx_eq :
      stepH = xDoubleStepOf_eq_case cs hcs seq heq d hd := by
    subst hh_double_eq
    exact unique_xStepFor seq hstepH
      (xDoubleStepOf_eq_case_mem cs hcs seq heq d hd) hxH
      (xDoubleStepOf_eq_case_spec cs hcs seq heq d hd)
  have hy_eq :
      stepE = yDoubleStepOf_eq_case cs hcs seq heq d hd := by
    subst hh_double_eq
    exact unique_yStepFor seq hstepE
      (yDoubleStepOf_eq_case_mem cs hcs seq heq d hd) hyE
      (yDoubleStepOf_eq_case_spec cs hcs seq heq d hd)
  refine ⟨d, hd, hdc, ?_, ?_, ?_, ?_⟩
  · simpa [xDoubleStepIdxOf_eq_case, hx_eq] using hstepH_gap.1
  · simpa [xDoubleStepIdxOf_eq_case, hx_eq] using hstepH_gap.2
  · simpa [yDoubleStepIdxOf_eq_case, hy_eq] using hstepE_gap_strict.1
  · simpa [yDoubleStepIdxOf_eq_case, hy_eq] using hstepE_gap_strict.2

private theorem gapOf_eq_case_lt_of_nested
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs)
    (d : Cycle α) (hd : d ∈ cs)
    (hx_in :
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) <
        xDoubleStepIdxOf_eq_case cs hcs seq heq d hd ∧
      xDoubleStepIdxOf_eq_case cs hcs seq heq d hd <
        max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc))
    (hy_in :
      min (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc) <
        yDoubleStepIdxOf_eq_case cs hcs seq heq d hd ∧
      yDoubleStepIdxOf_eq_case cs hcs seq heq d hd <
        max (xDoubleStepIdxOf_eq_case cs hcs seq heq c hc)
          (yDoubleStepIdxOf_eq_case cs hcs seq heq c hc)) :
    gapOf_eq_case cs hcs seq heq d hd <
      gapOf_eq_case cs hcs seq heq c hc := by
  unfold gapOf_eq_case
  omega

private theorem minGapCycleOf_eq_case_no_nested_doubleEntry_cycle
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (d : Cycle α) (hd : d ∈ cs)
    (hx_in : (
      min
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) <
        xDoubleStepIdxOf_eq_case cs hcs seq heq d hd ∧
      xDoubleStepIdxOf_eq_case cs hcs seq heq d hd <
        max
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))))
    (hy_in : (
      min
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) <
        yDoubleStepIdxOf_eq_case cs hcs seq heq d hd ∧
      yDoubleStepIdxOf_eq_case cs hcs seq heq d hd <
        max
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)))) :
    False := by
  have hlt :=
    gapOf_eq_case_lt_of_nested cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
      d hd hx_in hy_in
  have hmin := minGapCycleOf_eq_case_min cs hcs hcs_nonempty seq heq d hd
  omega

private theorem other_gap_mention_of_external_contradiction
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    {h : α}
    {stepE stepH : Body α × Body α}
    (hstepE : stepE ∈ seq.steps)
    (hyE : YStepFor h stepE)
    (hnot_mem_c0 :
      h ∉ (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq).members)
    (hgapE : GapYStepOf_eq_case cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) stepE)
    (hstepE_gap_strict :
      min
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) <
        stepIdx stepE seq.steps ∧
      stepIdx stepE seq.steps <
        max
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)))
    (hstepH : stepH ∈ seq.steps)
    (hh_stepH : Body.orig h ∈ [stepH.1, stepH.2])
    (hstepH_ne : stepH ≠ stepE)
    (hstepH_gap :
      min
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) <
        stepIdx stepH seq.steps ∧
      stepIdx stepH seq.steps <
        max
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))) :
    False := by
  obtain ⟨d, hd, hdc, hxlo, hxhi, hylo, hyhi⟩ :=
    other_gap_mention_of_external_forces_nested_cycle cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
      hstepE hyE hnot_mem_c0 hgapE hstepE_gap_strict
      hstepH hh_stepH hstepH_ne hstepH_gap
  exact minGapCycleOf_eq_case_no_nested_doubleEntry_cycle cs hcs hcs_nonempty seq heq
    d hd ⟨hxlo, hxhi⟩ ⟨hylo, hyhi⟩

private theorem other_mid_mention_of_external_contradiction_of_minGap_xy
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          mid ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf)
    {stepE stepH : Body α × Body α} {h : α}
    (hstepE : stepE ∈ seq.steps)
    (hyE : YStepFor h stepE)
    (hnot_mem_c0 :
      h ∉ (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq).members)
    (hgapE : GapYStepOf_eq_case cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) stepE)
    (hstepH_mid : stepH ∈ mid)
    (hh_stepH : Body.orig h ∈ [stepH.1, stepH.2])
    (hstepH_ne : stepH ≠ stepE) :
    False := by
  have hstepE_gap_strict :=
    externalGapYStep_strict_between_doubleIdx_of_xy_split cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
      hsplit_xy hstepE ⟨h, hyE, hnot_mem_c0, hgapE⟩
  have hxy :
      xDoubleStepIdxOf_eq_case cs hcs seq heq
          (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
          (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) <
        yDoubleStepIdxOf_eq_case cs hcs seq heq
          (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
          (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) := by
    exact xDouble_lt_yDoubleIdx_of_xy_split cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
      hsplit_xy
  have hstepE_gap :
      min
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) <
        stepIdx stepE seq.steps ∧
      stepIdx stepE seq.steps <
        max
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) := by
    constructor <;> omega
  have hstepH_gap :
      min
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) <
        stepIdx stepH seq.steps ∧
      stepIdx stepH seq.steps <
        max
          (xDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
          (yDoubleStepIdxOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) :=
    gap_strict_of_mid_member_of_xy_split cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
      hsplit_xy hstepH_mid
  have hstepH : stepH ∈ seq.steps := by
    rw [hsplit_xy]
    simp [hstepH_mid]
  exact other_gap_mention_of_external_contradiction cs hcs hcs_nonempty seq heq
    hstepE hyE hnot_mem_c0 hgapE hstepE_gap
    hstepH hh_stepH hstepH_ne hstepH_gap

private theorem external_no_other_mentions_in_mid_of_minGap_xy
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          mid ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf)
    {midL midR : List (Body α × Body α)}
    {stepE : Body α × Body α} {h : α}
    (hmid : mid = midL ++ stepE :: midR)
    (hstepE : stepE ∈ seq.steps)
    (hyE : YStepFor h stepE)
    (hnot_mem_c0 :
      h ∉ (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq).members)
    (hgapE : GapYStepOf_eq_case cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) stepE) :
    (∀ s ∈ midL, Body.orig h ∉ [s.1, s.2]) ∧
      (∀ s ∈ midR, Body.orig h ∉ [s.1, s.2]) := by
  constructor
  · intro s hs hsMention
    have hs_mid : s ∈ mid := by
      rw [hmid]
      exact List.mem_append.mpr (Or.inl hs)
    have hs_ne : s ≠ stepE := by
      intro hEq
      have hsplit_global :
          seq.steps =
            (pre ++
              xDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
              midL) ++
              stepE ::
              (midR ++
                yDoubleStepOf_eq_case cs hcs seq heq
                  (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                  (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
                suf) := by
        simp [hsplit_xy, hmid, List.append_assoc]
      have hs_not :
          stepE ∉
            pre ++
              xDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
              midL :=
        step_not_mem_prefix_of_split hsplit_global seq.distinct_pairs
      have hs_mem_prefix :
          stepE ∈
            pre ++
              xDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
              midL := by
        exact List.mem_append.mpr <| Or.inr <| List.mem_cons.mpr <| Or.inr (hEq ▸ hs)
      exact hs_not hs_mem_prefix
    exact other_mid_mention_of_external_contradiction_of_minGap_xy cs hcs hcs_nonempty seq heq
      hsplit_xy hstepE hyE hnot_mem_c0 hgapE hs_mid hsMention hs_ne
  · intro s hs hsMention
    have hs_mid : s ∈ mid := by
      rw [hmid]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hs)))
    have hs_ne : s ≠ stepE := by
      intro hEq
      have hsplit_global :
          seq.steps =
            (pre ++
              xDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
              midL) ++
              stepE ::
              (midR ++
                yDoubleStepOf_eq_case cs hcs seq heq
                  (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                  (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
                suf) := by
        simp [hsplit_xy, hmid, List.append_assoc]
      have hs_not :
          stepE ∉
            midR ++
              yDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
              suf :=
        step_not_mem_suffix_of_split hsplit_global seq.distinct_pairs
      have hs_mem_suffix :
          stepE ∈
            midR ++
              yDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
              suf := by
        exact List.mem_append.mpr <| Or.inl (hEq ▸ hs)
      exact hs_not hs_mem_suffix
    exact other_mid_mention_of_external_contradiction_of_minGap_xy cs hcs hcs_nonempty seq heq
      hsplit_xy hstepE hyE hnot_mem_c0 hgapE hs_mid hsMention hs_ne

private theorem exists_rightmost_externalGapY_data_of_minGap_xy
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          mid ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf) :
    ∃ preE midL stepE midR sufE h,
      seq.steps = preE ++ stepE :: sufE ∧
      mid = midL ++ stepE :: midR ∧
      YStepFor h stepE ∧
      h ∉ (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq).members ∧
      GapYStepOf_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) stepE ∧
      (∀ s ∈ sufE, ¬ ExternalGapYStepOf_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) s) := by
  rcases exists_rightmost_externalGapY_of_minGap_xy cs hcs hcs_nonempty seq hnoXY heq hsplit_xy with
    ⟨preE, stepE, sufE, hsplit_ext, hExt, hsuf_ext⟩
  have hstepE_mem : stepE ∈ seq.steps := by
    rw [hsplit_ext]
    simp
  obtain ⟨midL, midR, hmid⟩ :=
    exists_mid_split_at_externalGapY_of_xy_split cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
      hsplit_xy hstepE_mem hExt
  rcases hExt with ⟨h, hyE, hnot_mem_c0, hgapE⟩
  exact ⟨preE, midL, stepE, midR, sufE, h, hsplit_ext, hmid, hyE, hnot_mem_c0, hgapE, hsuf_ext⟩

/-- Once a rightmost external gap-`y` step inside the minimum-gap interval is split off,
    its global suffix is exactly the local remainder of the gap followed by the final
    `y`-double step and the original tail. -/
private theorem suffix_after_external_eq_of_minGap_xy
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          mid ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf)
    {preE sufE midL midR : List (Body α × Body α)}
    {stepE : Body α × Body α}
    (hsplit_ext : seq.steps = preE ++ stepE :: sufE)
    (hmid : mid = midL ++ stepE :: midR) :
    sufE =
      midR ++
        yDoubleStepOf_eq_case cs hcs seq heq
          (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
          (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
        suf := by
  have hsplit_global :
      seq.steps =
        (pre ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          midL) ++
          stepE ::
          (midR ++
            yDoubleStepOf_eq_case cs hcs seq heq
              (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
              (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
            suf) := by
    simp [hsplit_xy, hmid, List.append_assoc]
  have hidx_ext : stepIdx stepE seq.steps = preE.length := by
    simpa using idxOf_eq_length_pre_of_split hsplit_ext
      (step_not_mem_prefix_of_split hsplit_ext seq.distinct_pairs)
  have hidx_global :
      stepIdx stepE seq.steps =
        (pre ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          midL).length := by
    simpa using idxOf_eq_length_pre_of_split hsplit_global
      (step_not_mem_prefix_of_split hsplit_global seq.distinct_pairs)
  have hlen :
      preE.length =
        (pre ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          midL).length := by
    omega
  calc
    sufE = seq.steps.drop (preE.length + 1) := by
      rw [hsplit_ext]
      simp
    _ =
        seq.steps.drop
          ((pre ++
            xDoubleStepOf_eq_case cs hcs seq heq
              (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
              (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
            midL).length + 1) := by
          simp [hlen]
    _ =
        midR ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf := by
            have hsplit_global' :
                seq.steps =
                  (pre ++
                    [xDoubleStepOf_eq_case cs hcs seq heq
                      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)] ++
                    midL ++
                    [stepE]) ++
                    (midR ++
                      yDoubleStepOf_eq_case cs hcs seq heq
                        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
                      suf) := by
              simp [hsplit_xy, hmid, List.append_assoc]
            have hprefix_len :
                (pre ++
                  [xDoubleStepOf_eq_case cs hcs seq heq
                    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)] ++
                  midL ++
                  [stepE]).length =
                  (pre ++
                    xDoubleStepOf_eq_case cs hcs seq heq
                      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
                    midL).length + 1 := by
              simp [List.append_assoc]
              omega
            rw [hsplit_global', ← hprefix_len]
            rw [List.drop_append_of_le_length (i :=
              (pre ++
                [xDoubleStepOf_eq_case cs hcs seq heq
                  (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                  (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)] ++
                midL ++
                [stepE]).length) (show
                (pre ++
                  [xDoubleStepOf_eq_case cs hcs seq heq
                    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)] ++
                  midL ++
                  [stepE]).length ≤
                (pre ++
                  [xDoubleStepOf_eq_case cs hcs seq heq
                    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)] ++
                  midL ++
                  [stepE]).length by
                rfl)]
            simp [List.append_assoc]

theorem rightmost_externalGapY_contradiction_of_minGap_xy
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (hnoXY : ¬ seq.hasHelperSwap)
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_xy :
      seq.steps =
        pre ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          mid ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf) :
    False := by
  rcases exists_rightmost_externalGapY_data_of_minGap_xy cs hcs hcs_nonempty seq hnoXY heq
      hsplit_xy with
    ⟨preE, midL, stepE, midR, sufE, h,
      hsplit_ext, hmid, hyE, hnot_mem_c0, hgapE, hsuf_ext⟩
  have hstepE_mem : stepE ∈ seq.steps := by
    rw [hsplit_ext]
    simp
  have hExt :
      ExternalGapYStepOf_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
        stepE := ⟨h, hyE, hnot_mem_c0, hgapE⟩
  rcases exists_leftmost_internalGapY_step_right_of_external_of_xy_split cs hcs seq heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
      hsplit_xy hsplit_ext hExt with
    ⟨preI, stepI, sufI, hsplit_int, hInt, hpreI⟩
  rcases hInt with ⟨a, hyI, ha_mem, hgapI⟩
  have hsufE_eq :
      sufE =
        midR ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf :=
    suffix_after_external_eq_of_minGap_xy cs hcs hcs_nonempty seq heq
      hsplit_xy hsplit_ext hmid
  have hstepI_mem : stepI ∈ seq.steps := by
    rw [hsplit_ext]
    simp [hsplit_int]
  have hno_h_mid :=
      external_no_other_mentions_in_mid_of_minGap_xy cs hcs hcs_nonempty seq heq
        hsplit_xy hmid hstepE_mem hyE hnot_mem_c0 hgapE
  have hnot_h_midL : ∀ s ∈ midL, Body.orig h ∉ [s.1, s.2] := hno_h_mid.1
  have hnot_h_midR : ∀ s ∈ midR, Body.orig h ∉ [s.1, s.2] := hno_h_mid.2
  have hnot_h_midL_x : ∀ s ∈ midL, ¬ XStepFor h s := by
    intro s hs hxS
    exact hnot_h_midL s hs (by rcases hxS with rfl | rfl <;> simp)
  have hnot_h_midL_y : ∀ s ∈ midL, ¬ YStepFor h s := by
    intro s hs hyS
    exact hnot_h_midL s hs (by rcases hyS with rfl | rfl <;> simp)
  have hyDouble_not_preI :
      yDoubleStepOf_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ∉ preI := by
    intro hy_mem
    exact hpreI _ hy_mem
      (yDoubleStep_internalGapY_of_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
  by_cases ha_double :
      a = doubleEntryOf_eq_case cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
  · have hstepI_eq :
        stepI =
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) := by
      exact unique_yStepFor seq hstepI_mem
        (yDoubleStepOf_eq_case_mem cs hcs seq heq
          (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
          (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
        (by simpa [ha_double] using hyI)
        (yDoubleStepOf_eq_case_spec cs hcs seq heq
          (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
          (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
    have hmidR_eq : midR = preI := by
      have hsplit_y_global :
          seq.steps =
            (preE ++ stepE :: midR) ++
              yDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
              suf := by
        simp [hsplit_ext, hsufE_eq, List.append_assoc]
      have hidx₁ :
          stepIdx
              (yDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
              seq.steps =
            (preE ++ stepE :: midR).length := by
        simpa using idxOf_eq_length_pre_of_split hsplit_y_global
          (step_not_mem_prefix_of_split hsplit_y_global seq.distinct_pairs)
      have hsplit_int' :
          sufE =
            preI ++
              yDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
              sufI := by
        simpa [hstepI_eq] using hsplit_int
      have hsplit_y_global' :
          seq.steps =
            (preE ++ stepE :: preI) ++
              yDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
              sufI := by
        simp [hsplit_ext, hsplit_int', List.append_assoc]
      have hidx₂ :
          stepIdx
              (yDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq))
              seq.steps =
            (preE ++ stepE :: preI).length := by
        simpa using idxOf_eq_length_pre_of_split hsplit_y_global'
          (step_not_mem_prefix_of_split hsplit_y_global' seq.distinct_pairs)
      have hlen :
          (preE ++ stepE :: midR).length =
            (preE ++ stepE :: preI).length := by
        rw [← hidx₂]
        exact hidx₁.symm
      have hlen' : midR.length = preI.length := by
        simp only [List.length_append, List.length_cons] at hlen
        omega
      have htake₁ : sufE.take midR.length = midR := by
        rw [hsufE_eq]
        simp
      have htake₂ : sufE.take preI.length = preI := by
        rw [hsplit_int']
        simp
      rw [hlen'] at htake₁
      exact htake₁.symm.trans htake₂
    have hnot_midR_y : ∀ s ∈ midR, ∀ b, ¬ YStepFor b s := by
      rw [hmidR_eq]
      exact no_yStep_between_rightmost_external_and_next_internal cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
        hnoXY hsplit_ext hExt hsuf_ext hsplit_int ⟨a, hyI, ha_mem, hgapI⟩ hpreI
    exact externalGapY_yDouble_contradiction_of_xy_split cs hcs seq hnoXY heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
      hsplit_xy hmid hyE hnot_mem_c0
      hnot_h_midL_x hnot_h_midL_y hnot_midR_y
  · have hstepI_not_suf : stepI ∉ suf := by
      intro hs
      exact nonDouble_member_not_mem_suffix_of_xy_split cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
        hsplit_xy ha_mem ha_double stepI hs (by
          rcases hyI with rfl | rfl <;> simp)
    have hstepI_in_midR : stepI ∈ midR := by
      have hmem_sufE : stepI ∈ sufE := by
        rw [hsplit_int]
        simp
      rw [hsufE_eq] at hmem_sufE
      rcases List.mem_append.mp hmem_sufE with hmidR | htail
      · exact hmidR
      · rcases List.mem_cons.mp htail with hEq | hs
        · have hy_double :
              YStepFor a
                (yDoubleStepOf_eq_case cs hcs seq heq
                  (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                  (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) := by
            simpa [hEq] using hyI
          have hmentions_a :
              Body.orig a ∈
                [(yDoubleStepOf_eq_case cs hcs seq heq
                    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)).1,
                  (yDoubleStepOf_eq_case cs hcs seq heq
                    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)).2] := by
            rcases hy_double with h | h <;> simp [h]
          have hmentions_double :
              Body.orig
                  (doubleEntryOf_eq_case cs hcs seq heq
                    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) ∈
                [(yDoubleStepOf_eq_case cs hcs seq heq
                    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)).1,
                  (yDoubleStepOf_eq_case cs hcs seq heq
                    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)).2] := by
            rcases yDoubleStepOf_eq_case_spec cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) with h | h <;>
              simp [h]
          have ha_eq :
              a =
                doubleEntryOf_eq_case cs hcs seq heq
                  (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                  (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) := by
            exact helper_step_mentions_eq
              (seq.helper_constraint _
                (yDoubleStepOf_eq_case_mem cs hcs seq heq
                  (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                  (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)))
              hmentions_a
              hmentions_double
          exact False.elim (ha_double ha_eq)
        · exact False.elim (hstepI_not_suf hs)
    rcases exists_split_of_mem midR hstepI_in_midR with ⟨preIR, midR', hmidR_split⟩
    have hsufE_eq' :
        sufE = preIR ++ stepI :: (midR' ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf) := by
      rw [hsufE_eq, hmidR_split]
      simp [List.append_assoc]
    have hpreIR_eq : preIR = preI := by
      have hsplit_stepI_global₁ :
          seq.steps =
            (preE ++ stepE :: preIR) ++
              stepI ::
              (midR' ++
                yDoubleStepOf_eq_case cs hcs seq heq
                  (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                  (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
                suf) := by
        simp [hsplit_ext, hsufE_eq', List.append_assoc]
      have hsplit_stepI_global₂ :
          seq.steps =
            (preE ++ stepE :: preI) ++ stepI :: sufI := by
        simp [hsplit_ext, hsplit_int, List.append_assoc]
      have hidx₁ :
          stepIdx stepI seq.steps = (preE ++ stepE :: preIR).length := by
        simpa using idxOf_eq_length_pre_of_split hsplit_stepI_global₁
          (step_not_mem_prefix_of_split hsplit_stepI_global₁ seq.distinct_pairs)
      have hidx₂ :
          stepIdx stepI seq.steps = (preE ++ stepE :: preI).length := by
        simpa using idxOf_eq_length_pre_of_split hsplit_stepI_global₂
          (step_not_mem_prefix_of_split hsplit_stepI_global₂ seq.distinct_pairs)
      have hlen :
          (preE ++ stepE :: preIR).length =
            (preE ++ stepE :: preI).length := by
        rw [← hidx₂]
        exact hidx₁.symm
      have hlen' : preIR.length = preI.length := by
        simp only [List.length_append, List.length_cons] at hlen
        omega
      have htake₁ : sufE.take preIR.length = preIR := by
        rw [hsufE_eq']
        simp
      have htake₂ : sufE.take preI.length = preI := by
        rw [hsplit_int]
        simp
      rw [hlen'] at htake₁
      exact htake₁.symm.trans htake₂
    subst preIR
    have hmid_full :
        mid = midL ++ stepE :: preI ++ stepI :: midR' := by
      simp [hmid, hmidR_split, List.append_assoc]
    have hnot_preI_y :
        ∀ s ∈ preI, ∀ b, ¬ YStepFor b s :=
      no_yStep_between_rightmost_external_and_next_internal cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
        hnoXY hsplit_ext hExt hsuf_ext hsplit_int ⟨a, hyI, ha_mem, hgapI⟩ hpreI
    have hnot_a_midR'_x : ∀ s ∈ midR', ¬ XStepFor a s := by
      intro s hs
      exact internalGapYStep_nonDouble_no_x_anywhere cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
        hstepI_mem hyI ha_mem ha_double s (by
          rw [hsplit_xy]
          simp [hmid_full, hs, List.append_assoc])
    have hnot_a_midR'_y : ∀ s ∈ midR', ¬ YStepFor a s := by
      intro s hs hyS
      have hs_mem : s ∈ seq.steps := by
        rw [hsplit_xy]
        simp [hmid_full, hs, List.append_assoc]
      have hs_eq : s = stepI :=
        unique_yStepFor seq hs_mem hstepI_mem hyS hyI
      have hs_not : stepI ∉ midR' := by
        intro hmem
        have hsplit_stepI_global₁ :
            seq.steps =
              (preE ++ stepE :: preI) ++
                stepI ::
                (midR' ++
                  yDoubleStepOf_eq_case cs hcs seq heq
                    (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                    (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
                  suf) := by
          simp [hsplit_ext, hsufE_eq', List.append_assoc]
        have hstepI_not_suffix :
            stepI ∉ midR' ++
              yDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
              suf := by
          exact step_not_mem_suffix_of_split hsplit_stepI_global₁ seq.distinct_pairs
        exact hstepI_not_suffix (List.mem_append.mpr (Or.inl hmem))
      exact hs_not (hs_eq ▸ hs)
    exact externalGapY_internalNonDouble_contradiction_of_xy_split cs hcs seq hnoXY heq
      (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
      (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
      hsplit_xy hmid_full hyE hnot_mem_c0 hyI ha_mem ha_double
      hnot_h_midL_x hnot_h_midL_y hnot_preI_y hnot_a_midR'_x hnot_a_midR'_y

def swapHelpersStep (step : Body α × Body α) : Body α × Body α :=
  (helperSwap step.1, helperSwap step.2)

omit [Fintype α] in
private theorem swapHelpersStep_involutive :
    Function.Involutive (swapHelpersStep (α := α)) := by
  intro step
  rcases step with ⟨u, v⟩
  simp [swapHelpersStep, helperSwap]

omit [Fintype α] in
private theorem swapHelpersStep_injective :
    Function.Injective (swapHelpersStep (α := α)) :=
  swapHelpersStep_involutive.injective

omit [Fintype α] in
private theorem UsesHelper_swapHelpersStep_iff {step : Body α × Body α} :
    UsesHelper (swapHelpersStep step) ↔ UsesHelper step := by
  rcases step with ⟨u, v⟩
  cases u <;> cases v <;>
    simp [UsesHelper, swapHelpersStep, helperSwap, Equiv.swap_apply_def]

omit [Fintype α] in
private theorem swapHelpersStep_XStepFor_iff {a : α} {step : Body α × Body α} :
    XStepFor a (swapHelpersStep step) ↔ YStepFor a step := by
  rcases step with ⟨u, v⟩
  cases u <;> cases v <;>
    simp [XStepFor, YStepFor, swapHelpersStep, helperSwap, Equiv.swap_apply_def]

omit [Fintype α] in
private theorem swapHelpersStep_YStepFor_iff {a : α} {step : Body α × Body α} :
    YStepFor a (swapHelpersStep step) ↔ XStepFor a step := by
  rcases step with ⟨u, v⟩
  cases u <;> cases v <;>
    simp [XStepFor, YStepFor, swapHelpersStep, helperSwap, Equiv.swap_apply_def]

omit [Fintype α] in
private theorem swap_perm_swapHelpersStep (step : Body α × Body α) :
    Equiv.swap (swapHelpersStep step).1 (swapHelpersStep step).2 =
      helperSwap * Equiv.swap step.1 step.2 * helperSwap := by
  rcases step with ⟨u, v⟩
  simp [swapHelpersStep]
  rw [← Equiv.symm_trans_swap_trans u v helperSwap]
  ext z
  rfl

omit [Fintype α] in
theorem runScript_map_swapHelpersStep
    (steps : List (Body α × Body α)) :
    runScript (steps.map swapHelpersStep) = helperSwap * runScript steps * helperSwap := by
  induction steps with
  | nil =>
      simp [runScript, helperSwap]
  | cons step rest ih =>
      calc
        runScript (swapHelpersStep step :: rest.map swapHelpersStep)
            = runScript (rest.map swapHelpersStep) *
                Equiv.swap (swapHelpersStep step).1 (swapHelpersStep step).2 := by
                  simp [runScript]
        _ = (helperSwap * runScript rest * helperSwap) *
              (helperSwap * Equiv.swap step.1 step.2 * helperSwap) := by
                rw [ih, swap_perm_swapHelpersStep]
        _ = helperSwap * (runScript rest * Equiv.swap step.1 step.2) * helperSwap := by
              have hcancel :
                  helperSwap * (helperSwap * (Equiv.swap step.1 step.2 * helperSwap)) =
                    Equiv.swap step.1 step.2 * helperSwap := by
                rw [← mul_assoc, helperSwap_mul_self, one_mul]
              calc
                (helperSwap * runScript rest * helperSwap) *
                    (helperSwap * Equiv.swap step.1 step.2 * helperSwap)
                    = helperSwap *
                        (runScript rest * (helperSwap * (helperSwap *
                          (Equiv.swap step.1 step.2 * helperSwap)))) := by
                            simp [mul_assoc]
                _ = helperSwap * (runScript rest * (Equiv.swap step.1 step.2 * helperSwap)) := by
                      rw [hcancel]
                _ = helperSwap * (runScript rest * Equiv.swap step.1 step.2) * helperSwap := by
                      simp [mul_assoc]
        _ = helperSwap * runScript (step :: rest) * helperSwap := by
              simp [runScript, mul_assoc]

noncomputable def swapHelpersRepairSeq
    (cs : List (Cycle α))
    (seq : RepairSeq (cycleProduct cs)) :
    RepairSeq (cycleProduct cs) :=
  { steps := seq.steps.map swapHelpersStep
    helper_constraint := by
      intro step hstep
      rcases List.mem_map.mp hstep with ⟨s, hs, rfl⟩
      exact (UsesHelper_swapHelpersStep_iff).2 (seq.helper_constraint s hs)
    nontrivial := by
      intro step hstep
      rcases List.mem_map.mp hstep with ⟨s, hs, rfl⟩
      intro hEq
      have hEq' : helperSwap s.1 = helperSwap s.2 := by
        simpa [swapHelpersStep] using hEq
      exact seq.nontrivial s hs (helperSwap.injective hEq')
    distinct_pairs := by
      have hmap :
          (seq.steps.map swapHelpersStep).map stepPair =
            (seq.steps.map stepPair).map (Sym2.map helperSwap) := by
        ext s
        simp [swapHelpersStep, stepPair, Sym2.map_pair_eq]
      rw [hmap]
      exact seq.distinct_pairs.map (Sym2.map.injective helperSwap.injective)
    undoes := by
      calc
        runScript (seq.steps.map swapHelpersStep) * cycleProduct cs
            = helperSwap * runScript seq.steps * helperSwap * cycleProduct cs := by
                rw [runScript_map_swapHelpersStep]
        _ = helperSwap * runScript seq.steps * (helperSwap * cycleProduct cs) := by
              simp [mul_assoc]
        _ = helperSwap * runScript seq.steps * (cycleProduct cs * helperSwap) := by
              rw [(helperSwap_commute_cycleProduct cs).eq]
        _ = (helperSwap * runScript seq.steps * cycleProduct cs) * helperSwap := by
              simp [mul_assoc]
        _ = helperSwap * (runScript seq.steps * cycleProduct cs) * helperSwap := by
              simp [mul_assoc]
        _ = helperSwap * 1 * helperSwap := by rw [seq.undoes]
        _ = 1 := by simp [helperSwap_mul_self] }

omit [Fintype α] in
private theorem mem_xEntries_swapHelpersRepairSeq_iff
    (cs : List (Cycle α))
    (seq : RepairSeq (cycleProduct cs))
    {a : α} :
    a ∈ (swapHelpersRepairSeq cs seq).xEntries ↔ a ∈ seq.yEntries := by
  rw [mem_xEntries_iff (seq := swapHelpersRepairSeq cs seq), mem_yEntries_iff (seq := seq)]
  constructor
  · rintro ⟨step, hstep, hx⟩
    rcases List.mem_map.mp hstep with ⟨s, hs, rfl⟩
    exact ⟨s, hs, (swapHelpersStep_XStepFor_iff).1 hx⟩
  · rintro ⟨step, hstep, hy⟩
    exact ⟨swapHelpersStep step, List.mem_map.mpr ⟨step, hstep, rfl⟩,
      (swapHelpersStep_XStepFor_iff).2 hy⟩

omit [Fintype α] in
private theorem mem_yEntries_swapHelpersRepairSeq_iff
    (cs : List (Cycle α))
    (seq : RepairSeq (cycleProduct cs))
    {a : α} :
    a ∈ (swapHelpersRepairSeq cs seq).yEntries ↔ a ∈ seq.xEntries := by
  rw [mem_yEntries_iff (seq := swapHelpersRepairSeq cs seq), mem_xEntries_iff (seq := seq)]
  constructor
  · rintro ⟨step, hstep, hy⟩
    rcases List.mem_map.mp hstep with ⟨s, hs, rfl⟩
    exact ⟨s, hs, (swapHelpersStep_YStepFor_iff).1 hy⟩
  · rintro ⟨step, hstep, hx⟩
    exact ⟨swapHelpersStep step, List.mem_map.mpr ⟨step, hstep, rfl⟩,
      (swapHelpersStep_YStepFor_iff).2 hx⟩

private theorem doubleEntryOf_eq_case_swapHelpersRepairSeq
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    doubleEntryOf_eq_case cs hcs
        (swapHelpersRepairSeq cs seq)
        (by simpa [swapHelpersRepairSeq] using heq) c hc =
      doubleEntryOf_eq_case cs hcs seq heq c hc := by
  let a := doubleEntryOf_eq_case cs hcs seq heq c hc
  have ha :=
    Classical.choose_spec (existsUnique_doubleEntry_of_eq_case cs hcs seq heq c hc)
  symm
  apply (Classical.choose_spec
    (existsUnique_doubleEntry_of_eq_case cs hcs
      (swapHelpersRepairSeq cs seq)
      (by simpa [swapHelpersRepairSeq] using heq) c hc)).2 a
  refine ⟨ha.1.1, ?_, ?_⟩
  · exact (mem_xEntries_swapHelpersRepairSeq_iff cs seq).2 ha.1.2.2
  · exact (mem_yEntries_swapHelpersRepairSeq_iff cs seq).2 ha.1.2.1

private theorem xDoubleStepOf_eq_case_swapHelpersRepairSeq
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    xDoubleStepOf_eq_case cs hcs
        (swapHelpersRepairSeq cs seq)
        (by simpa [swapHelpersRepairSeq] using heq) c hc =
      swapHelpersStep (yDoubleStepOf_eq_case cs hcs seq heq c hc) := by
  let seqSwap := swapHelpersRepairSeq cs seq
  let heqSwap :
      seqSwap.steps.length = (cs.map fun c => c.members.length).sum + cs.length :=
    by simpa [seqSwap, swapHelpersRepairSeq] using heq
  let a := doubleEntryOf_eq_case cs hcs seq heq c hc
  have ha_eq :
      doubleEntryOf_eq_case cs hcs seqSwap heqSwap c hc = a := by
    simpa [seqSwap, heqSwap, a] using
      doubleEntryOf_eq_case_swapHelpersRepairSeq cs hcs seq heq c hc
  have hstep_mem :
      swapHelpersStep (yDoubleStepOf_eq_case cs hcs seq heq c hc) ∈ seqSwap.steps := by
    exact List.mem_map.mpr
      ⟨yDoubleStepOf_eq_case cs hcs seq heq c hc, yDoubleStepOf_eq_case_mem cs hcs seq heq c hc, rfl⟩
  have hstep_x :
      XStepFor a (swapHelpersStep (yDoubleStepOf_eq_case cs hcs seq heq c hc)) := by
    simpa [swapHelpersStep_XStepFor_iff] using
      (yDoubleStepOf_eq_case_spec cs hcs seq heq c hc)
  apply unique_xStepFor seqSwap
  · exact xDoubleStepOf_eq_case_mem cs hcs seqSwap heqSwap c hc
  · exact hstep_mem
  · simpa [ha_eq] using xDoubleStepOf_eq_case_spec cs hcs seqSwap heqSwap c hc
  · simpa [ha_eq] using hstep_x

private theorem yDoubleStepOf_eq_case_swapHelpersRepairSeq
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    yDoubleStepOf_eq_case cs hcs
        (swapHelpersRepairSeq cs seq)
        (by simpa [swapHelpersRepairSeq] using heq) c hc =
      swapHelpersStep (xDoubleStepOf_eq_case cs hcs seq heq c hc) := by
  let seqSwap := swapHelpersRepairSeq cs seq
  let heqSwap :
      seqSwap.steps.length = (cs.map fun c => c.members.length).sum + cs.length :=
    by simpa [seqSwap, swapHelpersRepairSeq] using heq
  let a := doubleEntryOf_eq_case cs hcs seq heq c hc
  have ha_eq :
      doubleEntryOf_eq_case cs hcs seqSwap heqSwap c hc = a := by
    simpa [seqSwap, heqSwap, a] using
      doubleEntryOf_eq_case_swapHelpersRepairSeq cs hcs seq heq c hc
  have hstep_mem :
      swapHelpersStep (xDoubleStepOf_eq_case cs hcs seq heq c hc) ∈ seqSwap.steps := by
    exact List.mem_map.mpr
      ⟨xDoubleStepOf_eq_case cs hcs seq heq c hc, xDoubleStepOf_eq_case_mem cs hcs seq heq c hc, rfl⟩
  have hstep_y :
      YStepFor a (swapHelpersStep (xDoubleStepOf_eq_case cs hcs seq heq c hc)) := by
    simpa [swapHelpersStep_YStepFor_iff] using
      (xDoubleStepOf_eq_case_spec cs hcs seq heq c hc)
  apply unique_yStepFor seqSwap
  · exact yDoubleStepOf_eq_case_mem cs hcs seqSwap heqSwap c hc
  · exact hstep_mem
  · simpa [ha_eq] using yDoubleStepOf_eq_case_spec cs hcs seqSwap heqSwap c hc
  · simpa [ha_eq] using hstep_y

omit [Fintype α] in
private theorem stepIdx_map_swapHelpersStep
    (seq : RepairSeq π)
    {step : Body α × Body α} (hmem : step ∈ seq.steps) :
    stepIdx (swapHelpersStep step) (seq.steps.map swapHelpersStep) =
      stepIdx step seq.steps := by
  rcases exists_split_of_mem seq.steps hmem with ⟨pre, suf, hsplit⟩
  have hnot_pre : step ∉ pre :=
    step_not_mem_prefix_of_split hsplit seq.distinct_pairs
  have hsplit_map :
      seq.steps.map swapHelpersStep =
        pre.map swapHelpersStep ++ swapHelpersStep step :: suf.map swapHelpersStep := by
    simp [hsplit, List.map_append, swapHelpersStep]
  have hnot_pre_map : swapHelpersStep step ∉ pre.map swapHelpersStep := by
    intro hmem_map
    rcases List.mem_map.mp hmem_map with ⟨s, hs, hs_eq⟩
    have hs_step : s = step := swapHelpersStep_injective hs_eq
    exact hnot_pre (hs_step ▸ hs)
  calc
    stepIdx (swapHelpersStep step) (seq.steps.map swapHelpersStep) = pre.length := by
      simpa using idxOf_eq_length_pre_of_split hsplit_map hnot_pre_map
    _ = stepIdx step seq.steps := by
      symm
      simpa using idxOf_eq_length_pre_of_split hsplit hnot_pre

private theorem xDoubleStepIdxOf_eq_case_swapHelpersRepairSeq
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    xDoubleStepIdxOf_eq_case cs hcs
        (swapHelpersRepairSeq cs seq)
        (by simpa [swapHelpersRepairSeq] using heq) c hc =
      yDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
  let seqSwap := swapHelpersRepairSeq cs seq
  let heqSwap :
      seqSwap.steps.length = (cs.map fun c => c.members.length).sum + cs.length :=
    by simpa [seqSwap, swapHelpersRepairSeq] using heq
  unfold xDoubleStepIdxOf_eq_case yDoubleStepIdxOf_eq_case
  rw [xDoubleStepOf_eq_case_swapHelpersRepairSeq cs hcs seq heq c hc]
  simpa [seqSwap] using
    stepIdx_map_swapHelpersStep seq
      (hmem := yDoubleStepOf_eq_case_mem cs hcs seq heq c hc)

private theorem yDoubleStepIdxOf_eq_case_swapHelpersRepairSeq
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    yDoubleStepIdxOf_eq_case cs hcs
        (swapHelpersRepairSeq cs seq)
        (by simpa [swapHelpersRepairSeq] using heq) c hc =
      xDoubleStepIdxOf_eq_case cs hcs seq heq c hc := by
  let seqSwap := swapHelpersRepairSeq cs seq
  let heqSwap :
      seqSwap.steps.length = (cs.map fun c => c.members.length).sum + cs.length :=
    by simpa [seqSwap, swapHelpersRepairSeq] using heq
  unfold yDoubleStepIdxOf_eq_case xDoubleStepIdxOf_eq_case
  rw [yDoubleStepOf_eq_case_swapHelpersRepairSeq cs hcs seq heq c hc]
  simpa [seqSwap] using
    stepIdx_map_swapHelpersStep seq
      (hmem := xDoubleStepOf_eq_case_mem cs hcs seq heq c hc)

private theorem gapOf_eq_case_swapHelpersRepairSeq
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    (c : Cycle α) (hc : c ∈ cs) :
    gapOf_eq_case cs hcs
        (swapHelpersRepairSeq cs seq)
        (by simpa [swapHelpersRepairSeq] using heq) c hc =
      gapOf_eq_case cs hcs seq heq c hc := by
  unfold gapOf_eq_case
  rw [xDoubleStepIdxOf_eq_case_swapHelpersRepairSeq cs hcs seq heq c hc,
    yDoubleStepIdxOf_eq_case_swapHelpersRepairSeq cs hcs seq heq c hc]
  omega

private theorem minGapCycleMemberOf_eq_case_swapHelpersRepairSeq
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length) :
    minGapCycleMemberOf_eq_case cs hcs hcs_nonempty
        (swapHelpersRepairSeq cs seq)
        (by simpa [swapHelpersRepairSeq] using heq) =
      minGapCycleMemberOf_eq_case cs hcs hcs_nonempty seq heq := by
  classical
  unfold minGapCycleMemberOf_eq_case
  simp only
  have hf :
      (fun c : { c // c ∈ cs } =>
        gapOf_eq_case cs hcs (swapHelpersRepairSeq cs seq)
          (by simpa [swapHelpersRepairSeq] using heq) c.1 c.2) =
      (fun c : { c // c ∈ cs } =>
        gapOf_eq_case cs hcs seq heq c.1 c.2) := by
    funext c
    exact gapOf_eq_case_swapHelpersRepairSeq cs hcs seq heq c.1 c.2
  simp [hf]

private theorem minGapCycleOf_eq_case_swapHelpersRepairSeq
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length) :
    minGapCycleOf_eq_case cs hcs hcs_nonempty
        (swapHelpersRepairSeq cs seq)
        (by simpa [swapHelpersRepairSeq] using heq) =
      minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq := by
  simpa [minGapCycleOf_eq_case] using
    congrArg Subtype.val
      (minGapCycleMemberOf_eq_case_swapHelpersRepairSeq cs hcs hcs_nonempty seq heq)

theorem swapHelpersRepairSeq_xy_split_of_yx_split
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ [])
    (seq : RepairSeq (cycleProduct cs))
    (heq : seq.steps.length = (cs.map fun c => c.members.length).sum + cs.length)
    {pre mid suf : List (Body α × Body α)}
    (hsplit_yx :
      seq.steps =
        pre ++
          yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          mid ++
          xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq) ::
          suf) :
    (swapHelpersRepairSeq cs seq).steps =
      pre.map swapHelpersStep ++
        xDoubleStepOf_eq_case cs hcs
          (swapHelpersRepairSeq cs seq)
          (by simpa [swapHelpersRepairSeq] using heq)
          (minGapCycleOf_eq_case cs hcs hcs_nonempty
            (swapHelpersRepairSeq cs seq)
            (by simpa [swapHelpersRepairSeq] using heq))
          (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty
            (swapHelpersRepairSeq cs seq)
            (by simpa [swapHelpersRepairSeq] using heq)) ::
        mid.map swapHelpersStep ++
        yDoubleStepOf_eq_case cs hcs
          (swapHelpersRepairSeq cs seq)
          (by simpa [swapHelpersRepairSeq] using heq)
          (minGapCycleOf_eq_case cs hcs hcs_nonempty
            (swapHelpersRepairSeq cs seq)
            (by simpa [swapHelpersRepairSeq] using heq))
          (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty
            (swapHelpersRepairSeq cs seq)
            (by simpa [swapHelpersRepairSeq] using heq)) ::
        suf.map swapHelpersStep := by
  let seqSwap := swapHelpersRepairSeq cs seq
  let heqSwap :
      seqSwap.steps.length = (cs.map fun c => c.members.length).sum + cs.length :=
    by simpa [seqSwap, swapHelpersRepairSeq] using heq
  have hmin :
      minGapCycleOf_eq_case cs hcs hcs_nonempty seqSwap heqSwap =
        minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq :=
    minGapCycleOf_eq_case_swapHelpersRepairSeq cs hcs hcs_nonempty seq heq
  have hx :
      xDoubleStepOf_eq_case cs hcs seqSwap heqSwap
          (minGapCycleOf_eq_case cs hcs hcs_nonempty seqSwap heqSwap)
          (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seqSwap heqSwap) =
        swapHelpersStep
          (yDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) := by
    simpa [seqSwap, heqSwap, hmin] using
      xDoubleStepOf_eq_case_swapHelpersRepairSeq cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
  have hy :
      yDoubleStepOf_eq_case cs hcs seqSwap heqSwap
          (minGapCycleOf_eq_case cs hcs hcs_nonempty seqSwap heqSwap)
          (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seqSwap heqSwap) =
        swapHelpersStep
          (xDoubleStepOf_eq_case cs hcs seq heq
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) := by
    simpa [seqSwap, heqSwap, hmin] using
      yDoubleStepOf_eq_case_swapHelpersRepairSeq cs hcs seq heq
        (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
        (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)
  calc
    seqSwap.steps
        = pre.map swapHelpersStep ++
            swapHelpersStep
              (yDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) ::
            mid.map swapHelpersStep ++
            swapHelpersStep
              (xDoubleStepOf_eq_case cs hcs seq heq
                (minGapCycleOf_eq_case cs hcs hcs_nonempty seq heq)
                (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seq heq)) ::
            suf.map swapHelpersStep := by
              simp [seqSwap, swapHelpersRepairSeq, hsplit_yx, List.map_append, List.append_assoc]
    _ = pre.map swapHelpersStep ++
          xDoubleStepOf_eq_case cs hcs seqSwap heqSwap
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seqSwap heqSwap)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seqSwap heqSwap) ::
          mid.map swapHelpersStep ++
          yDoubleStepOf_eq_case cs hcs seqSwap heqSwap
            (minGapCycleOf_eq_case cs hcs hcs_nonempty seqSwap heqSwap)
            (minGapCycleOf_eq_case_mem cs hcs hcs_nonempty seqSwap heqSwap) ::
          suf.map swapHelpersStep := by
            simp [hx, hy, List.append_assoc]


end Futurama
end Project
