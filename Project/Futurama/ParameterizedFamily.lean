import Project.Futurama.FiniteBridge

open Equiv Equiv.Perm

namespace Project
namespace Futurama

/-!
# Futurama Parameterized Family Layer

This module contains the parameterised cut-family construction and the
default-schedule compatibility facts, culminating in the strongest
permutation-level constructive endpoints.

## Architecture

Definitions in this file are presented in two parallel families:

* **Parameterised family** (the general backend). For any cycle `c`
  and any cut position `cut : Fin c.tail.length`, `repairScriptAt c cut`
  / `repairPermAt c cut` is a valid repair, and at the cycle-list
  level `undoScriptAt cuts` / `undoScriptOfPermAt σ cuts` correctly
  inverts the corresponding `cycleProduct` / `liftPerm` target.
* **Default route** (the pedagogical entry point). The four named
  endpoints `futuramaTheoremStrong{,FullSpec}` and
  `futuramaTheoremOfPermStrong{,FullSpec}` are defined as
  specialisations of their parameterised counterparts at
  `defaultSchedule cs` / `defaultSchedule (factorCycles σ)`, via the
  bridge lemmas `repairScript_eq_repairScriptAt_default`,
  `undoScript_eq_undoScriptAt_default`, etc.

## Main definitions

* `prefixMembers` / `suffixMembers` / `pivotOf` — combinatorial
  decomposition of `c.tail` at a cut position.
* `helperScript` — generic "sweep" with a chosen helper.
* `repairScriptAt` / `repairPermAt` — parameterised single-cycle
  repair script and its `runScript` permutation.
* `CutSchedule` — inductive datatype encoding "a cut for each cycle".
* `repairScriptsAt` / `repairProductAt` / `undoScriptAt` —
  cycle-list parameterised counterparts of `repairScripts` /
  `repairProduct` / `undoScript`.
* `undoScriptOfPermAt` — `Perm α`-level parameterised repair via
  `factorCycles σ`.
* `defaultCut` / `defaultSchedule` — canonical cut choices that
  recover the default-route definitions.

## Main results (constructive endpoint family)

Parameterised, cycle-list level:
* `futuramaTheoremAt`, `futuramaTheoremStrongAt`,
  `futuramaTheoremStrongAtFullSpec`.

Parameterised, Perm-level (require `[Fintype α]`):
* `futuramaTheoremOfPermAt`, `futuramaTheoremOfPermStrongAt`,
  `futuramaTheoremOfPermStrongAtFullSpec`.

Default-route, cycle-list level (binds only `[DecidableEq α]`):
* `futuramaTheoremStrong`, `futuramaTheoremStrongFullSpec`.

Default-route, Perm-level:
* `futuramaTheoremOfPermStrong`, `futuramaTheoremOfPermStrongFullSpec`.

The bridge between the two families is captured by the `@[simp]`
lemmas `repairScript_eq_repairScriptAt_default`,
`repairProduct_eq_repairProductAt_default`,
`undoScript_eq_undoScriptAt_default`, and
`undoScriptOfPerm_eq_undoScriptOfPermAt_default`.
-/

variable {α : Type*} [DecidableEq α]

section ParameterizedFamily

variable [Fintype α]

omit [DecidableEq α] [Fintype α] in
private theorem take_pair_drop_eq_param
    (l : List α) {n : ℕ} (hn : n + 1 < l.length) :
    l = l.take n ++ [l[n], l[n + 1]] ++ l.drop (n + 2) := by
  have hn0 : n < l.length := Nat.lt_of_succ_lt hn
  have hn1 : n + 1 < l.length := hn
  calc
    l = l.take n ++ l.drop n := by symm; exact List.take_append_drop n l
    _ = l.take n ++ (l[n] :: l.drop (n + 1)) := by
          rw [List.cons_getElem_drop_succ (h := hn0)]
    _ = l.take n ++ [l[n]] ++ l.drop (n + 1) := by simp
    _ = l.take n ++ [l[n]] ++ (l[n + 1] :: l.drop (n + 2)) := by
          rw [List.cons_getElem_drop_succ (l := l) (n := n + 1) (h := hn1)]
    _ = l.take n ++ [l[n], l[n + 1]] ++ l.drop (n + 2) := by simp [List.append_assoc]

omit [Fintype α] in
private theorem formPerm_apply_of_adjacent_split_param
    (l pre suf : List α) (a b : α)
    (hl : l = pre ++ [a, b] ++ suf)
    (hnodup : l.Nodup) :
    l.formPerm a = b := by
  subst hl
  have hlt : pre.length + 1 < (pre ++ [a, b] ++ suf).length := by
    simp
  calc
    (pre ++ [a, b] ++ suf).formPerm a
        = (pre ++ [a, b] ++ suf).formPerm ((pre ++ [a, b] ++ suf)[pre.length]) := by
            simp
    _ = (pre ++ [a, b] ++ suf)[pre.length + 1] := by
          simpa using
            (List.formPerm_apply_lt_getElem (pre ++ [a, b] ++ suf) hnodup pre.length hlt)
    _ = b := by simp

omit [Fintype α] in
private theorem cyclePerm_apply_orig_of_not_mem_param (c : Cycle α) (a : α) (ha : a ∉ c.members) :
    cyclePerm c (Body.orig a) = Body.orig a := by
  rw [cyclePerm]
  apply cyclePermAux_orig_of_not_mem
  simp [Cycle.members, Cycle.tail] at ha ⊢
  exact ha

omit [Fintype α] in
private theorem cyclePerm_eq_liftPerm_membersReverseFormPerm_param (c : Cycle α) :
    cyclePerm c = liftPerm c.members.reverse.formPerm := by
  rw [cyclePerm, cyclePermAux_eq_formPerm_reverse]
  simpa [List.map_reverse] using (formPerm_map_orig c.members.reverse)

omit [Fintype α] in
private theorem cyclePerm_apply_orig_mem_membersReverse_eq_next_param
    (c : Cycle α) {a : α} (ha : a ∈ c.members.reverse) :
    cyclePerm c (Body.orig a) = Body.orig (c.members.reverse.next a ha) := by
  rw [cyclePerm_eq_liftPerm_membersReverseFormPerm_param]
  rw [liftPerm_apply_orig]
  exact congrArg Body.orig
    (List.formPerm_apply_mem_eq_next (List.nodup_reverse.2 c.nodup) a ha)

omit [Fintype α] in
private theorem cyclePerm_apply_orig_mem_members_eq_prev_param
    (c : Cycle α) {a : α} (ha : a ∈ c.members) :
    cyclePerm c (Body.orig a) = Body.orig (c.members.prev a ha) := by
  have hrev : a ∈ c.members.reverse := by
    simpa using List.mem_reverse.mpr ha
  rw [cyclePerm_apply_orig_mem_membersReverse_eq_next_param c hrev]
  congr
  simpa using (List.next_reverse_eq_prev c.members c.nodup a ha)

/-- A generic helper-first script that swaps a fixed helper with each listed original body. -/
def helperScript (h : Body α) (xs : List α) : List (Body α × Body α) :=
  xs.map (fun a => (h, Body.orig a))

omit [DecidableEq α] [Fintype α] in
theorem mem_helperScript_iff {h : Body α} {xs : List α} {step : Body α × Body α} :
    step ∈ helperScript h xs ↔ ∃ a ∈ xs, step = (h, Body.orig a) := by
  simp [helperScript, eq_comm]

omit [DecidableEq α] [Fintype α] in
@[simp] theorem helperScript_nil (h : Body α) :
    helperScript h ([] : List α) = [] := rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem helperScript_cons (h : Body α) (a : α) (xs : List α) :
    helperScript h (a :: xs) = (h, Body.orig a) :: helperScript h xs := by
  simp [helperScript]

omit [DecidableEq α] [Fintype α] in
@[simp] theorem helperScript_length (h : Body α) (xs : List α) :
    (helperScript h xs).length = xs.length := by
  simp [helperScript]

omit [Fintype α] in
theorem runScript_helperScript_eq_formPerm
    (h : Body α) (xs : List α)
    (hxs : (h :: xs.map Body.orig).Nodup) :
    runScript (helperScript h xs) = (h :: xs.map Body.orig).formPerm := by
  induction xs using List.reverseRecOn generalizing h with
  | nil =>
      simp [helperScript]
  | append_singleton xs a ih =>
      have hsplit : helperScript h (xs ++ [a]) = helperScript h xs ++ [(h, Body.orig a)] := by
        simp [helperScript, List.map_append]
      rw [hsplit, runScript_append]
      simp [runScript]
      have htail : (xs.map Body.orig ++ [Body.orig a]).Nodup := by
        simpa [List.map_append] using hxs.of_cons
      have hmapnodup : (xs.map Body.orig).Nodup := (List.nodup_append.mp htail).1
      have hnotmap : h ∉ xs.map Body.orig := by
        intro hm
        exact hxs.notMem (by simp [List.map_append, hm])
      have hxs' : (h :: xs.map Body.orig).Nodup := by
        exact List.nodup_cons.mpr ⟨hnotmap, hmapnodup⟩
      have ih' := ih h hxs'
      rw [ih']
      change swap h (Body.orig a) * (h :: xs.map Body.orig).formPerm =
        (h :: (xs.map Body.orig ++ [Body.orig a])).formPerm
      let l' : List (Body α) := Body.orig a :: h :: xs.map Body.orig
      have hl' : l'.Nodup := by
        have hrot : l' ~r (h :: xs.map Body.orig ++ [Body.orig a]) := by
          refine ⟨1, ?_⟩
          simp [l']
        exact (List.IsRotated.nodup_iff hrot).2 (by simpa [List.map_append] using hxs)
      have hrotEq :
          (h :: List.map Body.orig (xs ++ [a])).formPerm =
            swap (Body.orig a) h * (h :: xs.map Body.orig).formPerm := by
        simpa [l', List.map_append, List.formPerm_cons_cons] using
          (List.formPerm_rotate l' hl' 1)
      calc
        swap h (Body.orig a) * (h :: xs.map Body.orig).formPerm
            = swap (Body.orig a) h * (h :: xs.map Body.orig).formPerm := by
                simp [swap_comm]
        _ = (h :: List.map Body.orig (xs ++ [a])).formPerm := hrotEq.symm
        _ = (h :: (xs.map Body.orig ++ [Body.orig a])).formPerm := by
              simp [List.map_append]

omit [DecidableEq α] [Fintype α] in
theorem helperScript_nodup
    (h : Body α) (xs : List α)
    (hxs : (h :: xs.map Body.orig).Nodup) :
    (helperScript h xs).Nodup := by
  let f : α → Body α × Body α := fun a => (h, Body.orig a)
  have hinj : Function.Injective f := by
    intro a b hEq
    have hsnd : Body.orig a = Body.orig b := by
      exact congrArg Prod.snd hEq
    simpa using Body.orig.inj hsnd
  have hnodup : xs.Nodup := by
    have hmap : (xs.map Body.orig).Nodup := hxs.of_cons
    simpa using (List.nodup_map_iff (fun x y h => Body.orig.inj h)).1 hmap
  simpa [helperScript, f] using hnodup.map hinj

omit [Fintype α] in
@[simp] theorem runScript_helperScript_apply_head
    (h : Body α) (a : α) (rest : List α)
    (hnodup : (h :: (a :: rest).map Body.orig).Nodup) :
    runScript (helperScript h (a :: rest)) h = Body.orig a := by
  rw [runScript_helperScript_eq_formPerm h (a :: rest) hnodup]
  simpa using List.formPerm_apply_head h (Body.orig a) (rest.map Body.orig) hnodup

omit [Fintype α] in
@[simp] theorem runScript_helperScript_apply_last
    (h : Body α) (xs : List α) (a : α)
    (hnodup : (h :: (xs ++ [a]).map Body.orig).Nodup) :
    runScript (helperScript h (xs ++ [a])) (Body.orig a) = h := by
  rw [runScript_helperScript_eq_formPerm h (xs ++ [a]) hnodup]
  simp [List.map_append]

omit [Fintype α] in
theorem runScript_helperScript_x_apply_orig_of_not_mem
    (xs : List α) {a : α}
    (hnodup : (Body.x :: xs.map Body.orig).Nodup)
    (ha : a ∉ xs) :
    runScript (helperScript Body.x xs) (Body.orig a) = Body.orig a := by
  have hnot : Body.orig a ∉ Body.x :: xs.map Body.orig := by
    simp [ha]
  rw [runScript_helperScript_eq_formPerm Body.x xs hnodup]
  exact List.formPerm_apply_of_notMem hnot

omit [Fintype α] in
theorem runScript_helperScript_y_apply_orig_of_not_mem
    (xs : List α) {a : α}
    (hnodup : (Body.y :: xs.map Body.orig).Nodup)
    (ha : a ∉ xs) :
    runScript (helperScript Body.y xs) (Body.orig a) = Body.orig a := by
  have hnot : Body.orig a ∉ Body.y :: xs.map Body.orig := by
    simp [ha]
  rw [runScript_helperScript_eq_formPerm Body.y xs hnodup]
  exact List.formPerm_apply_of_notMem hnot

omit [Fintype α] in
@[simp] theorem runScript_helperScript_x_fix_y (xs : List α)
    (hnodup : (Body.x :: xs.map Body.orig).Nodup) :
    runScript (helperScript Body.x xs) Body.y = Body.y := by
  have hnot : Body.y ∉ Body.x :: xs.map Body.orig := by
    simp
  rw [runScript_helperScript_eq_formPerm Body.x xs hnodup]
  exact List.formPerm_apply_of_notMem hnot

omit [Fintype α] in
@[simp] theorem runScript_helperScript_y_fix_x (xs : List α)
    (hnodup : (Body.y :: xs.map Body.orig).Nodup) :
    runScript (helperScript Body.y xs) Body.x = Body.x := by
  have hnot : Body.x ∉ Body.y :: xs.map Body.orig := by
    simp
  rw [runScript_helperScript_eq_formPerm Body.y xs hnodup]
  exact List.formPerm_apply_of_notMem hnot

omit [Fintype α] in
theorem runScript_helperScript_apply_adjacent
    (h : Body α) (pre suf : List α) (u v : α)
    (hnodup : (h :: (pre ++ [u, v] ++ suf).map Body.orig).Nodup) :
    runScript (helperScript h (pre ++ [u, v] ++ suf)) (Body.orig u) = Body.orig v := by
  rw [runScript_helperScript_eq_formPerm h (pre ++ [u, v] ++ suf) hnodup]
  simpa [List.map_append, List.append_assoc] using
    (formPerm_apply_of_adjacent_split_param
      (l := (h :: pre.map Body.orig) ++ [Body.orig u, Body.orig v] ++ suf.map Body.orig)
      (pre := h :: pre.map Body.orig)
      (suf := suf.map Body.orig)
      (a := Body.orig u)
      (b := Body.orig v)
      rfl
      (by simpa [List.map_append, List.append_assoc] using hnodup))

omit [Fintype α] in
theorem runScript_helperScript_apply_mem_eq_next
    (h : Body α) (xs : List α) {a : α} (ha : a ∈ xs)
    (hnodup : (h :: xs.map Body.orig).Nodup) :
    runScript (helperScript h xs) (Body.orig a) =
      (h :: xs.map Body.orig).next (Body.orig a) (by simp [ha]) := by
  rw [runScript_helperScript_eq_formPerm h xs hnodup]
  exact List.formPerm_apply_mem_eq_next hnodup (Body.orig a) (by simp [ha])

/-- A parameterised single-cycle repair family. The cut chooses the
first tail element handled by helper `y`; equivalently, it determines the pivot
`a_{i+1}` in the parameterised family. -/
def prefixMembers (c : Cycle α) (cut : Fin c.tail.length) : List α :=
  c.first :: c.tail.take cut.1

def suffixMembers (c : Cycle α) (cut : Fin c.tail.length) : List α :=
  c.tail.drop cut.1

def pivotOf (c : Cycle α) (cut : Fin c.tail.length) : α :=
  c.tail.get cut

omit [DecidableEq α] [Fintype α] in
@[simp] theorem prefixMembers_eq (c : Cycle α) (cut : Fin c.tail.length) :
    prefixMembers c cut = c.first :: c.tail.take cut.1 := rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem suffixMembers_eq (c : Cycle α) (cut : Fin c.tail.length) :
    suffixMembers c cut = c.tail.drop cut.1 := rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem pivotOf_eq_get (c : Cycle α) (cut : Fin c.tail.length) :
    pivotOf c cut = c.tail.get cut := rfl

omit [DecidableEq α] [Fintype α] in
theorem members_eq_prefixMembers_append_suffixMembers (c : Cycle α) (cut : Fin c.tail.length) :
    c.members = prefixMembers c cut ++ suffixMembers c cut := by
  simp [Cycle.members, prefixMembers, suffixMembers, Cycle.tail, List.take_append_drop]

omit [DecidableEq α] [Fintype α] in
theorem suffixMembers_eq_pivot_cons (c : Cycle α) (cut : Fin c.tail.length) :
    suffixMembers c cut = pivotOf c cut :: c.tail.drop (cut.1 + 1) := by
  simp [suffixMembers, pivotOf]
  exact (List.cons_getElem_drop_succ (l := c.tail) (n := cut.1) (h := cut.2)).symm

omit [DecidableEq α] [Fintype α] in
theorem suffixMembers_ne_nil (c : Cycle α) (cut : Fin c.tail.length) :
    suffixMembers c cut ≠ [] := by
  rw [suffixMembers_eq_pivot_cons]
  simp

omit [DecidableEq α] [Fintype α] in
theorem prefixMembers_ne_nil (c : Cycle α) (cut : Fin c.tail.length) :
    prefixMembers c cut ≠ [] := by
  simp [prefixMembers]

omit [DecidableEq α] [Fintype α] in
theorem prefixMembers_nodup (c : Cycle α) (cut : Fin c.tail.length) :
    (prefixMembers c cut).Nodup := by
  exact c.nodup.sublist ((List.take_sublist cut.1 c.tail).cons₂ _)

omit [DecidableEq α] [Fintype α] in
theorem suffixMembers_nodup (c : Cycle α) (cut : Fin c.tail.length) :
    (suffixMembers c cut).Nodup := by
  exact c.nodup_tail.sublist (by
    simpa [suffixMembers] using List.drop_sublist cut.1 c.tail)

omit [DecidableEq α] [Fintype α] in
theorem prefixMembers_eq_members_take (c : Cycle α) (cut : Fin c.tail.length) :
    prefixMembers c cut = c.members.take (cut.1 + 1) := by
  simp [prefixMembers, Cycle.members, Cycle.tail]

omit [DecidableEq α] [Fintype α] in
theorem suffixMembers_eq_members_drop (c : Cycle α) (cut : Fin c.tail.length) :
    suffixMembers c cut = c.members.drop (cut.1 + 1) := by
  simp [suffixMembers, Cycle.members, Cycle.tail]

omit [DecidableEq α] [Fintype α] in
theorem mem_suffixMembers_not_mem_prefixMembers
    (c : Cycle α) (cut : Fin c.tail.length) {a : α}
    (ha : a ∈ suffixMembers c cut) :
    a ∉ prefixMembers c cut := by
  rw [prefixMembers_eq_members_take]
  rw [suffixMembers_eq_members_drop] at ha
  intro hpre
  have hdisj :
      List.Disjoint (c.members.take (cut.1 + 1)) (c.members.drop (cut.1 + 1)) := by
    apply List.disjoint_take_drop c.nodup
    simp
  exact hdisj hpre ha

omit [DecidableEq α] [Fintype α] in
theorem mem_prefixMembers_not_mem_suffixMembers
    (c : Cycle α) (cut : Fin c.tail.length) {a : α}
    (ha : a ∈ prefixMembers c cut) :
    a ∉ suffixMembers c cut := by
  rw [suffixMembers_eq_members_drop]
  rw [prefixMembers_eq_members_take] at ha
  intro hsuf
  have hdisj :
      List.Disjoint (c.members.take (cut.1 + 1)) (c.members.drop (cut.1 + 1)) := by
    apply List.disjoint_take_drop c.nodup
    simp
  exact hdisj ha hsuf

omit [DecidableEq α] [Fintype α] in
theorem prefixMembers_helper_nodup_x (c : Cycle α) (cut : Fin c.tail.length) :
    (Body.x :: (prefixMembers c cut).map Body.orig).Nodup := by
  have hmap :
      ((prefixMembers c cut).map Body.orig).Nodup := by
    exact (prefixMembers_nodup c cut).map
      (show Function.Injective Body.orig from fun _ _ h => Body.orig.inj h)
  refine List.nodup_cons.mpr ⟨?_, hmap⟩
  intro hmem
  rcases List.mem_map.mp hmem with ⟨a, _, hEq⟩
  cases hEq

omit [DecidableEq α] [Fintype α] in
theorem suffixMembers_helper_nodup_y (c : Cycle α) (cut : Fin c.tail.length) :
    (Body.y :: (suffixMembers c cut).map Body.orig).Nodup := by
  have hmap :
      ((suffixMembers c cut).map Body.orig).Nodup := by
    exact (suffixMembers_nodup c cut).map
      (show Function.Injective Body.orig from fun _ _ h => Body.orig.inj h)
  refine List.nodup_cons.mpr ⟨?_, hmap⟩
  intro hmem
  rcases List.mem_map.mp hmem with ⟨a, _, hEq⟩
  cases hEq

omit [DecidableEq α] [Fintype α] in
theorem first_not_mem_suffixMembers (c : Cycle α) (cut : Fin c.tail.length) :
    c.first ∉ suffixMembers c cut := by
  intro hmem
  have htail : c.first ∈ c.tail := by
    simpa [suffixMembers] using List.mem_of_mem_drop hmem
  simp [Cycle.tail, c.first_ne_second, c.not_mem_rest_first] at htail

omit [Fintype α] in
theorem runScript_helperScript_prefix_apply_last
    (c : Cycle α) (cut : Fin c.tail.length) :
    runScript (helperScript Body.x (prefixMembers c cut))
      (Body.orig ((prefixMembers c cut).getLast (prefixMembers_ne_nil c cut))) = Body.x := by
  rw [runScript_helperScript_eq_formPerm Body.x (prefixMembers c cut) (prefixMembers_helper_nodup_x c cut)]
  have hmapne : (prefixMembers c cut).map Body.orig ≠ [] := by
    simp
  rw [← List.getLast_map (f := Body.orig) (l := prefixMembers c cut) (h := hmapne)]
  simp

omit [Fintype α] in
theorem runScript_helperScript_suffix_apply_last
    (c : Cycle α) (cut : Fin c.tail.length) :
    runScript (helperScript Body.y (suffixMembers c cut))
      (Body.orig ((suffixMembers c cut).getLast (suffixMembers_ne_nil c cut))) = Body.y := by
  rw [runScript_helperScript_eq_formPerm Body.y (suffixMembers c cut) (suffixMembers_helper_nodup_y c cut)]
  have hmapne : (suffixMembers c cut).map Body.orig ≠ [] := by
    simp
  rw [← List.getLast_map (f := Body.orig) (l := suffixMembers c cut) (h := hmapne)]
  simpa using (List.formPerm_apply_getLast Body.y ((suffixMembers c cut).map Body.orig))

omit [DecidableEq α] [Fintype α] in
theorem pivot_mem_suffixMembers (c : Cycle α) (cut : Fin c.tail.length) :
    pivotOf c cut ∈ suffixMembers c cut := by
  rw [suffixMembers_eq_pivot_cons]
  simp

omit [DecidableEq α] [Fintype α] in
theorem members_eq_prefixMembers_append_pivotDrop
    (c : Cycle α) (cut : Fin c.tail.length) :
    c.members = prefixMembers c cut ++ pivotOf c cut :: c.tail.drop (cut.1 + 1) := by
  rw [members_eq_prefixMembers_append_suffixMembers c cut, suffixMembers_eq_pivot_cons c cut]

omit [DecidableEq α] [Fintype α] in
theorem pivot_mem_members (c : Cycle α) (cut : Fin c.tail.length) :
    pivotOf c cut ∈ c.members := by
  rw [members_eq_prefixMembers_append_suffixMembers c cut]
  exact List.mem_append_right _ (pivot_mem_suffixMembers c cut)

omit [Fintype α] in
theorem prev_append_cons_eq_getLast
    (pre : List α) (x : α) (suf : List α)
    (hpre : pre ≠ [])
    (hnodup : (pre ++ x :: suf).Nodup) :
    (pre ++ x :: suf).prev x (by simp) = pre.getLast hpre := by
  induction pre with
  | nil =>
      contradiction
  | cons a pre ih =>
      cases pre with
      | nil =>
          have hxne : x ≠ a := by
            intro hEq
            subst hEq
            simp at hnodup
          simpa using List.prev_cons_cons_of_ne (y := a) (l := suf) (x := x) (h := by simp) hxne
      | cons b pre =>
          have hxne_a : x ≠ a := by
            intro hEq
            subst hEq
            exact hnodup.notMem (by simp)
          have hxne_b : x ≠ b := by
            intro hEq
            subst hEq
            exact hnodup.of_cons.notMem (by simp)
          have htail : ((b :: pre) ++ x :: suf).Nodup := by
            simpa using hnodup.of_cons
          have hpre' : (b :: pre : List α) ≠ [] := by
            simp
          have hstep :
              (a :: b :: pre ++ x :: suf).prev x (by simp) =
                ((b :: pre) ++ x :: suf).prev x (by simp [hxne_b]) := by
            simpa [List.append_assoc, hxne_a, hxne_b] using
              (List.prev_ne_cons_cons (y := a) (z := b) (l := pre ++ x :: suf)
                (x := x) (h := by simp) hxne_a hxne_b)
          rw [hstep]
          simpa [List.append_assoc] using ih hpre' htail

omit [Fintype α] in
theorem prev_eq_getLast_of_eq_append_cons
    (l pre suf : List α) (x : α)
    (hpre : pre ≠ [])
    (hl : l.Nodup)
    (hlist : l = pre ++ x :: suf)
    (hx : x ∈ l) :
    l.prev x hx = pre.getLast hpre := by
  simpa [hlist] using
    (prev_append_cons_eq_getLast (pre := pre) (x := x) (suf := suf) hpre
      (by simpa [hlist] using hl))

omit [DecidableEq α] [Fintype α] in
theorem exists_append_pair_of_mem_ne_head
    (l : List α) (hne : l ≠ []) {a : α}
    (ha : a ∈ l) (hhead : a ≠ l[0]'(List.length_pos_iff_ne_nil.mpr hne)) :
    ∃ pre p suf, l = pre ++ [p, a] ++ suf := by
  have hlen : 0 < l.length := by
    exact List.length_pos_iff_ne_nil.mpr hne
  obtain ⟨j, hj, hja⟩ := List.getElem_of_mem ha
  cases j with
  | zero =>
      exfalso
      exact hhead hja.symm
  | succ i =>
      refine ⟨l.take i, l[i], l.drop (i + 2), ?_⟩
      simpa [hja] using (take_pair_drop_eq_param l (n := i) hj)

omit [Fintype α] in
theorem prev_eq_left_of_eq_append_pair
    (l pre suf : List α) (p a : α)
    (hl : l.Nodup)
    (hlist : l = pre ++ [p, a] ++ suf) :
    l.prev a (by simp [hlist]) = p := by
  have hpre : pre ++ [p] ≠ [] := by simp
  have hprev :
      l.prev a (by simp [hlist]) = (pre ++ [p]).getLast hpre := by
    exact prev_eq_getLast_of_eq_append_cons
      (l := l) (pre := pre ++ [p]) (x := a) (suf := suf) hpre hl
      (by simp [List.append_assoc, hlist])
      (by simp [hlist])
  rw [hprev]
  simp

omit [DecidableEq α] [Fintype α] in
theorem first_ne_pivotOf (c : Cycle α) (cut : Fin c.tail.length) :
    c.first ≠ pivotOf c cut := by
  intro hEq
  exact first_not_mem_suffixMembers c cut (hEq ▸ pivot_mem_suffixMembers c cut)

omit [DecidableEq α] [Fintype α] in
theorem not_mem_prefixMembers_of_not_mem_members
    (c : Cycle α) (cut : Fin c.tail.length) {a : α}
    (ha : a ∉ c.members) :
    a ∉ prefixMembers c cut := by
  intro hmem
  exact ha ((members_eq_prefixMembers_append_suffixMembers c cut).symm ▸ List.mem_append_left _ hmem)

omit [DecidableEq α] [Fintype α] in
theorem not_mem_suffixMembers_of_not_mem_members
    (c : Cycle α) (cut : Fin c.tail.length) {a : α}
    (ha : a ∉ c.members) :
    a ∉ suffixMembers c cut := by
  intro hmem
  exact ha ((members_eq_prefixMembers_append_suffixMembers c cut).symm ▸ List.mem_append_right _ hmem)

omit [Fintype α] in
theorem runScript_helperScript_suffix_apply_y
    (c : Cycle α) (cut : Fin c.tail.length) :
    runScript (helperScript Body.y (suffixMembers c cut)) Body.y = Body.orig (pivotOf c cut) := by
  rw [runScript_helperScript_eq_formPerm Body.y (suffixMembers c cut) (suffixMembers_helper_nodup_y c cut)]
  rw [suffixMembers_eq_pivot_cons]
  have hsuf : (Body.y :: Body.orig (pivotOf c cut) :: (c.tail.drop (cut.1 + 1)).map Body.orig).Nodup := by
    have hsuf0 : (Body.y :: (suffixMembers c cut).map Body.orig).Nodup :=
      suffixMembers_helper_nodup_y c cut
    rw [suffixMembers_eq_pivot_cons, List.map_cons] at hsuf0
    exact hsuf0
  simpa [List.map_cons] using
    (List.formPerm_apply_head Body.y (Body.orig (pivotOf c cut)) ((c.tail.drop (cut.1 + 1)).map Body.orig) hsuf)

omit [Fintype α] in
theorem cyclePerm_apply_orig_first_eq_suffix_getLast
    (c : Cycle α) (cut : Fin c.tail.length) :
    cyclePerm c (Body.orig c.first) =
      Body.orig ((suffixMembers c cut).getLast (suffixMembers_ne_nil c cut)) := by
  have hfirstmem : c.first ∈ c.members := by
    simp [Cycle.members]
  rw [cyclePerm_apply_orig_mem_members_eq_prev_param c hfirstmem]
  have hprev :
      c.members.prev c.first hfirstmem = c.members.getLast (by simp [Cycle.members]) := by
    simp [Cycle.members]
  rw [hprev]
  have hlast :
      c.members.getLast (by simp [Cycle.members]) =
        (suffixMembers c cut).getLast (suffixMembers_ne_nil c cut) := by
    simp
  simp

omit [Fintype α] in
theorem cyclePerm_apply_orig_pivot_eq_prefix_getLast
    (c : Cycle α) (cut : Fin c.tail.length) :
    cyclePerm c (Body.orig (pivotOf c cut)) =
      Body.orig ((prefixMembers c cut).getLast (prefixMembers_ne_nil c cut)) := by
  have hpivotmem : pivotOf c cut ∈ c.members := pivot_mem_members c cut
  rw [cyclePerm_apply_orig_mem_members_eq_prev_param c hpivotmem]
  simpa using
    congrArg Body.orig
      (prev_eq_getLast_of_eq_append_cons
        (l := c.members)
        (pre := prefixMembers c cut)
        (x := pivotOf c cut)
        (suf := c.tail.drop (cut.1 + 1))
        (hpre := prefixMembers_ne_nil c cut)
        (hl := c.nodup)
        (hlist := members_eq_prefixMembers_append_pivotDrop c cut)
        (hx := hpivotmem))

/-- Parameterised single-cycle repair script.

Given a cycle `c` and a cut position `cut : Fin c.tail.length`, this
splits `c.tail` at `cut`, sweeps the prefix with helper `x`, sweeps
the suffix with helper `y`, and closes with the canonical
`finishScript c.first (pivotOf c cut)`. The default route recovers
as `repairScriptAt c (defaultCut c)`. The `cut` parameter ranges
over the entire `c.tail.length`-element family; all choices yield
correct repair scripts (the cut family covers all admissible
`(prefix, suffix)` partitions of the cycle tail). -/
def repairScriptAt (c : Cycle α) (cut : Fin c.tail.length) : List (Body α × Body α) :=
  helperScript Body.x (prefixMembers c cut) ++
    helperScript Body.y (suffixMembers c cut) ++
    finishScript c.first (pivotOf c cut)

omit [DecidableEq α] [Fintype α] in
theorem mem_repairScriptAt_canonical
    (c : Cycle α) (cut : Fin c.tail.length) {step : Body α × Body α}
    (h : step ∈ repairScriptAt c cut) : CanonicalStep step := by
  rw [repairScriptAt, List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_append] at h
    rcases h with hx | hy
    · rcases (mem_helperScript_iff).1 hx with ⟨a, _, rfl⟩
      exact Or.inl ⟨a, rfl⟩
    · rcases (mem_helperScript_iff).1 hy with ⟨a, _, rfl⟩
      exact Or.inr <| Or.inl ⟨a, rfl⟩
  · rcases (mem_finishScript_iff).1 h with hstep | hstep
    · rcases hstep with rfl
      exact Or.inl ⟨_, rfl⟩
    · rcases hstep with rfl
      exact Or.inr <| Or.inl ⟨_, rfl⟩

omit [DecidableEq α] [Fintype α] in
theorem mem_repairScriptAt_second_mem_members
    (c : Cycle α) (cut : Fin c.tail.length) {step : Body α × Body α}
    (h : step ∈ repairScriptAt c cut) :
    ∃ a ∈ c.members, step.2 = Body.orig a := by
  rw [repairScriptAt, List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_append] at h
    rcases h with hx | hy
    · rcases (mem_helperScript_iff).1 hx with ⟨a, ha, hstep⟩
      refine ⟨a, ?_, congrArg Prod.snd hstep⟩
      exact (members_eq_prefixMembers_append_suffixMembers c cut).symm ▸ List.mem_append_left _ ha
    · rcases (mem_helperScript_iff).1 hy with ⟨a, ha, hstep⟩
      refine ⟨a, ?_, congrArg Prod.snd hstep⟩
      exact (members_eq_prefixMembers_append_suffixMembers c cut).symm ▸ List.mem_append_right _ ha
  · rcases (mem_finishScript_iff).1 h with hstep | hstep
    · refine ⟨pivotOf c cut, pivot_mem_members c cut, congrArg Prod.snd hstep⟩
    · refine ⟨c.first, by simp [Cycle.members], congrArg Prod.snd hstep⟩

omit [DecidableEq α] [Fintype α] in
theorem not_mem_repairScriptAt_helperSwap (c : Cycle α) (cut : Fin c.tail.length) :
    (Body.x, Body.y) ∉ repairScriptAt c cut := by
  intro h
  rcases mem_repairScriptAt_second_mem_members c cut h with ⟨a, _, hsnd⟩
  cases hsnd

omit [DecidableEq α] [Fintype α] in
theorem repairScriptAt_nodup (c : Cycle α) (cut : Fin c.tail.length) :
    (repairScriptAt c cut).Nodup := by
  have hx : (helperScript Body.x (prefixMembers c cut)).Nodup :=
    helperScript_nodup Body.x (prefixMembers c cut) (prefixMembers_helper_nodup_x c cut)
  have hy : (helperScript Body.y (suffixMembers c cut)).Nodup :=
    helperScript_nodup Body.y (suffixMembers c cut) (suffixMembers_helper_nodup_y c cut)
  have hfinish : (finishScript c.first (pivotOf c cut)).Nodup := by
    simp [finishScript]
  have hxy : List.Disjoint (helperScript Body.x (prefixMembers c cut))
      (helperScript Body.y (suffixMembers c cut)) := by
    rw [List.disjoint_left]
    intro step hs hd
    rcases (mem_helperScript_iff).1 hs with ⟨a, _, hxa⟩
    rcases (mem_helperScript_iff).1 hd with ⟨b, _, hyb⟩
    have hEq : (Body.x : Body α) = Body.y := by
      exact congrArg Prod.fst (hxa.symm.trans hyb)
    cases hEq
  have hxfinish : List.Disjoint (helperScript Body.x (prefixMembers c cut))
      (finishScript c.first (pivotOf c cut)) := by
    rw [List.disjoint_left]
    intro step hs hf
    rcases (mem_helperScript_iff).1 hs with ⟨a, ha, rfl⟩
    rcases (mem_finishScript_iff).1 hf with hstep | hstep
    · have hEq : a = pivotOf c cut := by
        exact Body.orig.inj (congrArg Prod.snd hstep)
      exact (mem_suffixMembers_not_mem_prefixMembers c cut (pivot_mem_suffixMembers c cut)) (hEq ▸ ha)
    · simp at hstep
  have hyfinish : List.Disjoint (helperScript Body.y (suffixMembers c cut))
      (finishScript c.first (pivotOf c cut)) := by
    rw [List.disjoint_left]
    intro step hs hf
    rcases (mem_helperScript_iff).1 hs with ⟨a, ha, rfl⟩
    rcases (mem_finishScript_iff).1 hf with hstep | hstep
    · simp at hstep
    · have hEq : a = c.first := by
        exact Body.orig.inj (congrArg Prod.snd hstep)
      exact first_not_mem_suffixMembers c cut (hEq ▸ ha)
  have hxyNodup :
      (helperScript Body.x (prefixMembers c cut) ++ helperScript Body.y (suffixMembers c cut)).Nodup :=
    hx.append hy hxy
  have hxyfinish :
      List.Disjoint
        (helperScript Body.x (prefixMembers c cut) ++ helperScript Body.y (suffixMembers c cut))
        (finishScript c.first (pivotOf c cut)) := by
    rw [List.disjoint_left]
    intro step hmem hf
    rcases List.mem_append.mp hmem with hs | hs
    · exact hxfinish hs hf
    · exact hyfinish hs hf
  simpa [repairScriptAt, List.append_assoc] using hxyNodup.append hfinish hxyfinish

omit [DecidableEq α] [Fintype α] in
theorem repairScriptAt_disjoint_of_cycle_disjoint {c d : Cycle α}
    (hcd : Cycle.Disjoint c d) (cutc : Fin c.tail.length) (cutd : Fin d.tail.length) :
    List.Disjoint (repairScriptAt c cutc) (repairScriptAt d cutd) := by
  rw [List.disjoint_left]
  intro step hs hd
  rcases mem_repairScriptAt_second_mem_members c cutc hs with ⟨a, ha, hsa⟩
  rcases mem_repairScriptAt_second_mem_members d cutd hd with ⟨b, hb, hsb⟩
  have hab : a = b := by
    exact Body.orig.inj (hsa.symm.trans hsb)
  exact hcd ha (hab ▸ hb)

/-- The permutation induced by a chosen member of the parameterised single-cycle family. -/
def repairPermAt (c : Cycle α) (cut : Fin c.tail.length) : Perm (Body α) :=
  runScript (repairScriptAt c cut)

omit [Fintype α] in
theorem repairPermAt_mul_cyclePerm_apply_x (c : Cycle α) (cut : Fin c.tail.length) :
    (repairPermAt c cut * cyclePerm c) Body.x = Body.y := by
  calc
    (repairPermAt c cut * cyclePerm c) Body.x
        = runScript (finishScript c.first (pivotOf c cut))
            (runScript (helperScript Body.y (suffixMembers c cut))
              (runScript (helperScript Body.x (prefixMembers c cut))
                (cyclePerm c Body.x))) := by
                  simp [repairPermAt, repairScriptAt, Perm.mul_apply, runScript_append_apply]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut))
            (runScript (helperScript Body.x (prefixMembers c cut)) Body.x)) := by
              simp [cyclePerm]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut))
            (Body.orig c.first)) := by
              simpa [prefixMembers] using
                congrArg
                  (fun z => runScript (finishScript c.first (pivotOf c cut))
                    (runScript (helperScript Body.y (suffixMembers c cut)) z))
                  (runScript_helperScript_apply_head Body.x c.first (c.tail.take cut.1)
                    (prefixMembers_helper_nodup_x c cut))
    _ = runScript (finishScript c.first (pivotOf c cut)) (Body.orig c.first) := by
          rw [runScript_helperScript_y_apply_orig_of_not_mem (suffixMembers c cut)
            (suffixMembers_helper_nodup_y c cut) (first_not_mem_suffixMembers c cut)]
    _ = Body.y := by
          simpa using finishScript_apply_first c.first (pivotOf c cut) (first_ne_pivotOf c cut)

omit [Fintype α] in
theorem repairPermAt_mul_cyclePerm_apply_y (c : Cycle α) (cut : Fin c.tail.length) :
    (repairPermAt c cut * cyclePerm c) Body.y = Body.x := by
  calc
    (repairPermAt c cut * cyclePerm c) Body.y
        = runScript (finishScript c.first (pivotOf c cut))
            (runScript (helperScript Body.y (suffixMembers c cut))
              (runScript (helperScript Body.x (prefixMembers c cut))
                (cyclePerm c Body.y))) := by
                  simp [repairPermAt, repairScriptAt, Perm.mul_apply, runScript_append_apply]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut))
            (runScript (helperScript Body.x (prefixMembers c cut)) Body.y)) := by
              simp [cyclePerm]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut)) Body.y) := by
              simpa using
                congrArg
                  (fun z => runScript (finishScript c.first (pivotOf c cut))
                    (runScript (helperScript Body.y (suffixMembers c cut)) z))
                  (runScript_helperScript_x_fix_y (prefixMembers c cut) (prefixMembers_helper_nodup_x c cut))
    _ = runScript (finishScript c.first (pivotOf c cut)) (Body.orig (pivotOf c cut)) := by
          simpa using
            congrArg
              (fun z => runScript (finishScript c.first (pivotOf c cut)) z)
              (runScript_helperScript_suffix_apply_y c cut)
    _ = Body.x := by
          simp [finishScript_apply_second]

omit [Fintype α] in
theorem repairPermAt_mul_cyclePerm_apply_orig_pivot
    (c : Cycle α) (cut : Fin c.tail.length) :
    (repairPermAt c cut * cyclePerm c) (Body.orig (pivotOf c cut)) = Body.orig (pivotOf c cut) := by
  calc
    (repairPermAt c cut * cyclePerm c) (Body.orig (pivotOf c cut))
        = runScript (finishScript c.first (pivotOf c cut))
            (runScript (helperScript Body.y (suffixMembers c cut))
              (runScript (helperScript Body.x (prefixMembers c cut))
                (cyclePerm c (Body.orig (pivotOf c cut))))) := by
                  simp [repairPermAt, repairScriptAt, Perm.mul_apply, runScript_append_apply]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut))
            (runScript (helperScript Body.x (prefixMembers c cut))
              (Body.orig ((prefixMembers c cut).getLast (prefixMembers_ne_nil c cut))))) := by
          rw [cyclePerm_apply_orig_pivot_eq_prefix_getLast c cut]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut)) Body.x) := by
          rw [runScript_helperScript_prefix_apply_last c cut]
    _ = runScript (finishScript c.first (pivotOf c cut)) Body.x := by
          rw [runScript_helperScript_y_fix_x (suffixMembers c cut) (suffixMembers_helper_nodup_y c cut)]
    _ = Body.orig (pivotOf c cut) := by
          simpa using finishScript_apply_x c.first (pivotOf c cut) (first_ne_pivotOf c cut)

omit [Fintype α] in
theorem repairPermAt_mul_cyclePerm_apply_orig_of_not_mem
    (c : Cycle α) (cut : Fin c.tail.length) {a : α}
    (ha : a ∉ c.members) :
    (repairPermAt c cut * cyclePerm c) (Body.orig a) = Body.orig a := by
  have hprefix : a ∉ prefixMembers c cut :=
    not_mem_prefixMembers_of_not_mem_members c cut ha
  have hsuffix : a ∉ suffixMembers c cut :=
    not_mem_suffixMembers_of_not_mem_members c cut ha
  have hfirst : a ≠ c.first := by
    intro hEq
    exact ha (by simp [Cycle.members, hEq])
  have hpivot : a ≠ pivotOf c cut := by
    intro hEq
    exact hsuffix (hEq ▸ pivot_mem_suffixMembers c cut)
  calc
    (repairPermAt c cut * cyclePerm c) (Body.orig a)
        = runScript (finishScript c.first (pivotOf c cut))
            (runScript (helperScript Body.y (suffixMembers c cut))
              (runScript (helperScript Body.x (prefixMembers c cut))
                (cyclePerm c (Body.orig a)))) := by
                  simp [repairPermAt, repairScriptAt, Perm.mul_apply, runScript_append_apply]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut))
            (runScript (helperScript Body.x (prefixMembers c cut)) (Body.orig a))) := by
              rw [cyclePerm_apply_orig_of_not_mem_param c a ha]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut)) (Body.orig a)) := by
              rw [runScript_helperScript_x_apply_orig_of_not_mem (prefixMembers c cut)
                (prefixMembers_helper_nodup_x c cut) hprefix]
    _ = runScript (finishScript c.first (pivotOf c cut)) (Body.orig a) := by
          rw [runScript_helperScript_y_apply_orig_of_not_mem (suffixMembers c cut)
            (suffixMembers_helper_nodup_y c cut) hsuffix]
    _ = Body.orig a := by
          simpa using finishScript_apply_orig_of_ne hfirst hpivot

omit [Fintype α] in
theorem repairPermAt_mul_cyclePerm_apply_orig_prefixInterior
    (c : Cycle α) (cut : Fin c.tail.length) {a : α}
    (ha : a ∈ prefixMembers c cut) (hfirst : a ≠ c.first) :
    (repairPermAt c cut * cyclePerm c) (Body.orig a) = Body.orig a := by
  obtain ⟨pre, p, suf, hpre⟩ :=
    exists_append_pair_of_mem_ne_head
      (l := prefixMembers c cut)
      (hne := prefixMembers_ne_nil c cut)
      (ha := ha)
      (hhead := by simpa [prefixMembers] using hfirst)
  have hamem : a ∈ c.members := by
    exact (members_eq_prefixMembers_append_suffixMembers c cut).symm ▸ List.mem_append_left _ ha
  have hsuffixFix : a ∉ suffixMembers c cut := by
    exact mem_prefixMembers_not_mem_suffixMembers c cut ha
  have hpivot : a ≠ pivotOf c cut := by
    intro hEq
    exact hsuffixFix (hEq ▸ pivot_mem_suffixMembers c cut)
  have hfull :
      c.members = pre ++ [p, a] ++ (suf ++ pivotOf c cut :: c.tail.drop (cut.1 + 1)) := by
    rw [members_eq_prefixMembers_append_pivotDrop c cut, hpre]
    simp [List.append_assoc]
  have hcycle :
      cyclePerm c (Body.orig a) = Body.orig p := by
    rw [cyclePerm_apply_orig_mem_members_eq_prev_param c hamem]
    exact congrArg Body.orig <|
      prev_eq_left_of_eq_append_pair
        (l := c.members)
        (pre := pre)
        (p := p)
        (a := a)
        (suf := suf ++ pivotOf c cut :: c.tail.drop (cut.1 + 1))
        (hl := c.nodup)
        (hlist := hfull)
  have hprefixListNodup : (pre ++ [p, a] ++ suf).Nodup := by
    have htmp := prefixMembers_nodup c cut
    rw [hpre] at htmp
    exact htmp
  have hprefixMapNodup : ((pre ++ [p, a] ++ suf).map Body.orig).Nodup := by
    exact hprefixListNodup.map (show Function.Injective Body.orig from fun _ _ h => Body.orig.inj h)
  have hprefixNodup : (Body.x :: (pre ++ [p, a] ++ suf).map Body.orig).Nodup := by
    refine List.nodup_cons.mpr ?_
    refine ⟨?_, hprefixMapNodup⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨b, _, hEq⟩
    cases hEq
  have hxblock :
      runScript (helperScript Body.x (prefixMembers c cut)) (Body.orig p) = Body.orig a := by
    rw [hpre]
    simpa [List.map_append, List.append_assoc] using
      (runScript_helperScript_apply_adjacent Body.x pre suf p a hprefixNodup)
  calc
    (repairPermAt c cut * cyclePerm c) (Body.orig a)
        = runScript (finishScript c.first (pivotOf c cut))
            (runScript (helperScript Body.y (suffixMembers c cut))
              (runScript (helperScript Body.x (prefixMembers c cut))
                (cyclePerm c (Body.orig a)))) := by
                  simp [repairPermAt, repairScriptAt, Perm.mul_apply, runScript_append_apply]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut))
            (runScript (helperScript Body.x (prefixMembers c cut)) (Body.orig p))) := by
          rw [hcycle]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut)) (Body.orig a)) := by
          rw [hxblock]
    _ = runScript (finishScript c.first (pivotOf c cut)) (Body.orig a) := by
          rw [runScript_helperScript_y_apply_orig_of_not_mem (suffixMembers c cut)
            (suffixMembers_helper_nodup_y c cut) hsuffixFix]
    _ = Body.orig a := by
          simpa using finishScript_apply_orig_of_ne hfirst hpivot

omit [Fintype α] in
theorem repairPermAt_mul_cyclePerm_apply_orig_first
    (c : Cycle α) (cut : Fin c.tail.length) :
    (repairPermAt c cut * cyclePerm c) (Body.orig c.first) = Body.orig c.first := by
  calc
    (repairPermAt c cut * cyclePerm c) (Body.orig c.first)
        = runScript (finishScript c.first (pivotOf c cut))
            (runScript (helperScript Body.y (suffixMembers c cut))
              (runScript (helperScript Body.x (prefixMembers c cut))
                (cyclePerm c (Body.orig c.first)))) := by
                  simp [repairPermAt, repairScriptAt, Perm.mul_apply, runScript_append_apply]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut))
            (runScript (helperScript Body.x (prefixMembers c cut))
              (Body.orig ((suffixMembers c cut).getLast (suffixMembers_ne_nil c cut))))) := by
          rw [cyclePerm_apply_orig_first_eq_suffix_getLast c cut]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut))
            (Body.orig ((suffixMembers c cut).getLast (suffixMembers_ne_nil c cut)))) := by
          have hnot :
              ((suffixMembers c cut).getLast (suffixMembers_ne_nil c cut)) ∉ prefixMembers c cut := by
            exact mem_suffixMembers_not_mem_prefixMembers c cut (List.getLast_mem _)
          rw [runScript_helperScript_x_apply_orig_of_not_mem (prefixMembers c cut)
            (prefixMembers_helper_nodup_x c cut) hnot]
    _ = runScript (finishScript c.first (pivotOf c cut)) Body.y := by
          rw [runScript_helperScript_suffix_apply_last c cut]
    _ = Body.orig c.first := by
          simp [finishScript_apply_y]

omit [Fintype α] in
theorem repairPermAt_mul_cyclePerm_apply_orig_suffixInterior
    (c : Cycle α) (cut : Fin c.tail.length) {a : α}
    (ha : a ∈ suffixMembers c cut) (hpivot0 : a ≠ pivotOf c cut) :
    (repairPermAt c cut * cyclePerm c) (Body.orig a) = Body.orig a := by
  obtain ⟨pre, p, suf, hsuf⟩ :=
    exists_append_pair_of_mem_ne_head
      (l := suffixMembers c cut)
      (hne := suffixMembers_ne_nil c cut)
      (ha := ha)
      (hhead := by simpa [suffixMembers_eq_pivot_cons] using hpivot0)
  have hamem : a ∈ c.members := by
    exact (members_eq_prefixMembers_append_suffixMembers c cut).symm ▸ List.mem_append_right _ ha
  have hpInSuffix : p ∈ suffixMembers c cut := by
    rw [hsuf]
    simp
  have hprefixFix : p ∉ prefixMembers c cut := by
    exact mem_suffixMembers_not_mem_prefixMembers c cut hpInSuffix
  have hfirst : a ≠ c.first := by
    intro hEq
    exact first_not_mem_suffixMembers c cut (hEq ▸ ha)
  have hfull :
      c.members = (prefixMembers c cut ++ pre) ++ [p, a] ++ suf := by
    rw [members_eq_prefixMembers_append_suffixMembers c cut, hsuf]
    simp [List.append_assoc]
  have hcycle :
      cyclePerm c (Body.orig a) = Body.orig p := by
    rw [cyclePerm_apply_orig_mem_members_eq_prev_param c hamem]
    exact congrArg Body.orig <|
      prev_eq_left_of_eq_append_pair
        (l := c.members)
        (pre := prefixMembers c cut ++ pre)
        (p := p)
        (a := a)
        (suf := suf)
        (hl := c.nodup)
        (hlist := hfull)
  have hsuffixListNodup : (pre ++ [p, a] ++ suf).Nodup := by
    have htmp := suffixMembers_nodup c cut
    rw [hsuf] at htmp
    exact htmp
  have hsuffixMapNodup : ((pre ++ [p, a] ++ suf).map Body.orig).Nodup := by
    exact hsuffixListNodup.map (show Function.Injective Body.orig from fun _ _ h => Body.orig.inj h)
  have hsuffixNodup : (Body.y :: (pre ++ [p, a] ++ suf).map Body.orig).Nodup := by
    refine List.nodup_cons.mpr ?_
    refine ⟨?_, hsuffixMapNodup⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨b, _, hEq⟩
    cases hEq
  have hyblock :
      runScript (helperScript Body.y (suffixMembers c cut)) (Body.orig p) = Body.orig a := by
    rw [hsuf]
    simpa [List.map_append, List.append_assoc] using
      (runScript_helperScript_apply_adjacent Body.y pre suf p a hsuffixNodup)
  calc
    (repairPermAt c cut * cyclePerm c) (Body.orig a)
        = runScript (finishScript c.first (pivotOf c cut))
            (runScript (helperScript Body.y (suffixMembers c cut))
              (runScript (helperScript Body.x (prefixMembers c cut))
                (cyclePerm c (Body.orig a)))) := by
                  simp [repairPermAt, repairScriptAt, Perm.mul_apply, runScript_append_apply]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut))
            (runScript (helperScript Body.x (prefixMembers c cut)) (Body.orig p))) := by
          rw [hcycle]
    _ = runScript (finishScript c.first (pivotOf c cut))
          (runScript (helperScript Body.y (suffixMembers c cut)) (Body.orig p)) := by
          rw [runScript_helperScript_x_apply_orig_of_not_mem (prefixMembers c cut)
            (prefixMembers_helper_nodup_x c cut) hprefixFix]
    _ = runScript (finishScript c.first (pivotOf c cut)) (Body.orig a) := by
          rw [hyblock]
    _ = Body.orig a := by
          simpa using finishScript_apply_orig_of_ne hfirst hpivot0

omit [Fintype α] in
theorem repairPermAt_mul_cyclePerm
    (c : Cycle α) (cut : Fin c.tail.length) :
    repairPermAt c cut * cyclePerm c = helperSwap := by
  ext z
  cases z with
  | x =>
      simpa [helperSwap] using repairPermAt_mul_cyclePerm_apply_x c cut
  | y =>
      simpa [helperSwap] using repairPermAt_mul_cyclePerm_apply_y c cut
  | orig a =>
      by_cases hamem : a ∈ c.members
      · by_cases hfirst : a = c.first
        · subst hfirst
          simpa [helperSwap] using repairPermAt_mul_cyclePerm_apply_orig_first c cut
        · by_cases hpivot : a = pivotOf c cut
          · subst hpivot
            simpa [helperSwap] using repairPermAt_mul_cyclePerm_apply_orig_pivot c cut
          · have hsplit : a ∈ prefixMembers c cut ∨ a ∈ suffixMembers c cut := by
              have hmem' : a ∈ prefixMembers c cut ++ suffixMembers c cut := by
                exact (members_eq_prefixMembers_append_suffixMembers c cut).symm ▸ hamem
              exact List.mem_append.mp hmem'
            rcases hsplit with hpre | hsuf
            · simpa [helperSwap] using
                (repairPermAt_mul_cyclePerm_apply_orig_prefixInterior c cut hpre hfirst)
            · simpa [helperSwap] using
                (repairPermAt_mul_cyclePerm_apply_orig_suffixInterior c cut hsuf hpivot)
      · simpa [helperSwap] using
          (repairPermAt_mul_cyclePerm_apply_orig_of_not_mem c cut hamem)

omit [Fintype α] in
theorem repairPermAt_eq_repairPerm
    (c : Cycle α) (cut : Fin c.tail.length) :
    repairPermAt c cut = repairPerm c := by
  calc
    repairPermAt c cut = (repairPermAt c cut * cyclePerm c) * (cyclePerm c)⁻¹ := by
      simp [mul_assoc]
    _ = helperSwap * (cyclePerm c)⁻¹ := by
      rw [repairPermAt_mul_cyclePerm]
    _ = (repairPerm c * cyclePerm c) * (cyclePerm c)⁻¹ := by
      rw [repairPerm_mul_cyclePerm]
    _ = repairPerm c := by
      simp [mul_assoc]

/-- The canonical cut selecting the existing concrete single-cycle script. -/
def defaultCut (c : Cycle α) : Fin c.tail.length :=
  ⟨0, by
    simp [Cycle.tail]⟩

omit [DecidableEq α] [Fintype α] in
@[simp] theorem repairScript_eq_repairScriptAt_default (c : Cycle α) :
    repairScript c = repairScriptAt c (defaultCut c) := by
  simp [repairScriptAt, defaultCut, repairScript, helperScript, finishScript, Cycle.tail, sweepScript]

omit [Fintype α] in
@[simp] theorem repairPerm_eq_repairPermAt_default (c : Cycle α) :
    repairPerm c = repairPermAt c (defaultCut c) := by
  simp [repairPerm, repairPermAt]

/-- A dependent schedule choosing one cut for each cycle in a list. -/
inductive CutSchedule : List (Cycle α) → Type _
  | nil : CutSchedule []
  | cons {c : Cycle α} {cs : List (Cycle α)}
      (cut : Fin c.tail.length) (rest : CutSchedule cs) :
      CutSchedule (c :: cs)

/-- Concatenate the chosen parameterised repair blocks cycle by cycle. -/
def repairScriptsAt : {cs : List (Cycle α)} → CutSchedule cs → List (Body α × Body α)
  | [], .nil => []
  | c :: _, .cons cut rest =>
      repairScriptAt c cut ++ repairScriptsAt rest

omit [DecidableEq α] [Fintype α] in
theorem mem_repairScriptsAt_canonical :
    {cs : List (Cycle α)} → {cuts : CutSchedule cs} → {step : Body α × Body α} →
      step ∈ repairScriptsAt cuts → CanonicalStep step
  | [], .nil, _, h => by
      cases h
  | _ :: _, .cons cut rest, _, h => by
      rw [repairScriptsAt, List.mem_append] at h
      rcases h with h | h
      · exact mem_repairScriptAt_canonical _ _ h
      · exact mem_repairScriptsAt_canonical h

omit [DecidableEq α] [Fintype α] in
theorem mem_repairScriptsAt_second_mem_members :
    {cs : List (Cycle α)} → {cuts : CutSchedule cs} → {step : Body α × Body α} →
      step ∈ repairScriptsAt cuts → ∃ c ∈ cs, ∃ a ∈ c.members, step.2 = Body.orig a
  | [], .nil, _, h => by
      cases h
  | _ :: _, .cons cut rest, _, h => by
      rw [repairScriptsAt, List.mem_append] at h
      rcases h with h | h
      · rcases mem_repairScriptAt_second_mem_members _ _ h with ⟨a, ha, hsnd⟩
        exact ⟨_, by simp, a, ha, hsnd⟩
      · rcases mem_repairScriptsAt_second_mem_members h with ⟨d, hd, a, ha, hsnd⟩
        exact ⟨d, by simp [hd], a, ha, hsnd⟩

/-- The permutation induced by the chosen parameterised repair blocks. -/
def repairProductAt : {cs : List (Cycle α)} → CutSchedule cs → Perm (Body α)
  | [], .nil => 1
  | c :: _, .cons cut rest =>
      repairProductAt rest * repairPermAt c cut

/-- The complete parameterised repair script, including the same parity cleanup
as the existing `undoScript`. -/
def undoScriptAt : {cs : List (Cycle α)} → CutSchedule cs → List (Body α × Body α)
  | cs, cuts => repairScriptsAt cuts ++ finalCleanupScript cs

omit [DecidableEq α] [Fintype α] in
theorem mem_undoScriptAt_canonical :
    {cs : List (Cycle α)} → {cuts : CutSchedule cs} → {step : Body α × Body α} →
      step ∈ undoScriptAt cuts → CanonicalStep step
  | cs, cuts, step, h => by
      rw [undoScriptAt, List.mem_append] at h
      exact h.elim mem_repairScriptsAt_canonical mem_finalCleanupScript_canonical

omit [DecidableEq α] [Fintype α] in
theorem mem_undoScriptAt_usesHelper :
    {cs : List (Cycle α)} → {cuts : CutSchedule cs} → {step : Body α × Body α} →
      step ∈ undoScriptAt cuts → UsesHelper step
  | _, _, _, h => (mem_undoScriptAt_canonical h).usesHelper

omit [DecidableEq α] [Fintype α] in
theorem mem_undoScriptAt_nontrivial :
    {cs : List (Cycle α)} → {cuts : CutSchedule cs} → {step : Body α × Body α} →
      step ∈ undoScriptAt cuts → step.1 ≠ step.2
  | _, _, _, h => (mem_undoScriptAt_canonical h).nontrivial

omit [DecidableEq α] [Fintype α] in
theorem not_mem_repairScriptsAt_helperSwap :
    {cs : List (Cycle α)} → {cuts : CutSchedule cs} →
      (Body.x, Body.y) ∉ repairScriptsAt cuts
  | [], .nil => by
      simp [repairScriptsAt]
  | _ :: _, .cons cut rest => by
      intro h
      rcases mem_repairScriptsAt_second_mem_members h with ⟨c, hc, a, ha, hsnd⟩
      cases hsnd

omit [DecidableEq α] [Fintype α] in
theorem repairScriptsAt_nodup :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
      cs.Pairwise Cycle.Disjoint → (repairScriptsAt cuts).Nodup
  | [], .nil => by
      intro hcs
      simp [repairScriptsAt]
  | c :: cs, .cons cut rest => by
      intro hcs
      rw [List.pairwise_cons] at hcs
      have hrest : (repairScriptsAt rest).Nodup := repairScriptsAt_nodup rest hcs.2
      have hdisj : List.Disjoint (repairScriptAt c cut) (repairScriptsAt rest) := by
        rw [List.disjoint_left]
        intro step hs hd
        rcases mem_repairScriptAt_second_mem_members c cut hs with ⟨a, ha, hsa⟩
        rcases mem_repairScriptsAt_second_mem_members hd with ⟨d, hd, b, hb, hsb⟩
        have hab : a = b := by
          exact Body.orig.inj (hsa.symm.trans hsb)
        exact hcs.1 d hd ha (hab ▸ hb)
      simpa [repairScriptsAt] using (repairScriptAt_nodup c cut).append hrest hdisj

omit [DecidableEq α] [Fintype α] in
theorem undoScriptAt_nodup :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
      cs.Pairwise Cycle.Disjoint → (undoScriptAt cuts).Nodup
  | cs, cuts => by
      intro hcs
      rw [undoScriptAt]
      have hrepair : (repairScriptsAt cuts).Nodup := repairScriptsAt_nodup cuts hcs
      have hcleanup : (finalCleanupScript cs).Nodup := by
        by_cases hparity : cs.length % 2 = 0
        · simp [finalCleanupScript, hparity]
        · simp [finalCleanupScript, hparity]
      have hdisj : List.Disjoint (repairScriptsAt cuts) (finalCleanupScript cs) := by
        by_cases hparity : cs.length % 2 = 0
        · simp [finalCleanupScript, hparity]
        · rw [finalCleanupScript, if_neg hparity, List.disjoint_right]
          intro step hcleanup hrepair
          have hstep : step = (Body.x, Body.y) := by
            simpa using hcleanup
          subst step
          exact not_mem_repairScriptsAt_helperSwap hrepair
      exact hrepair.append hcleanup hdisj

omit [DecidableEq α] [Fintype α] in
theorem undoScriptAt_stepPairs_nodup :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
      cs.Pairwise Cycle.Disjoint → ((undoScriptAt cuts).map stepPair).Nodup
  | cs, cuts => by
      intro hcs
      refine List.Nodup.map_on ?_ (undoScriptAt_nodup cuts hcs)
      intro step₁ h₁ step₂ h₂ hpair
      exact stepPair_injective_of_canonical
        (mem_undoScriptAt_canonical h₁) (mem_undoScriptAt_canonical h₂) hpair

omit [Fintype α] in
theorem runScript_repairScriptsAt : {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
    runScript (repairScriptsAt cuts) = repairProductAt cuts
  | [], .nil => by
      simp [repairScriptsAt, repairProductAt]
  | _ :: _, .cons cut rest => by
      simp [repairScriptsAt, repairProductAt, runScript_append, runScript_repairScriptsAt, repairPermAt]

omit [Fintype α] in
theorem repairProductAt_mul_cycleProduct :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
      repairProductAt cuts * cycleProduct cs = residualPerm cs
  | [], .nil => by
      simp [repairProductAt, cycleProduct, residualPerm]
  | c :: cs, .cons cut rest => by
      calc
        repairProductAt (.cons cut rest) * cycleProduct (c :: cs)
            = repairProductAt rest * (repairPermAt c cut * cyclePerm c) * cycleProduct cs := by
                simp [repairProductAt, cycleProduct, mul_assoc]
        _ = repairProductAt rest * helperSwap * cycleProduct cs := by
              rw [repairPermAt_mul_cyclePerm]
        _ = repairProductAt rest * cycleProduct cs * helperSwap := by
              calc
                repairProductAt rest * helperSwap * cycleProduct cs
                    = repairProductAt rest * (helperSwap * cycleProduct cs) := by
                        simp [mul_assoc]
                _ = repairProductAt rest * (cycleProduct cs * helperSwap) := by
                      rw [(helperSwap_commute_cycleProduct cs).eq]
                _ = repairProductAt rest * cycleProduct cs * helperSwap := by
                      simp [mul_assoc]
        _ = residualPerm cs * helperSwap := by
              rw [repairProductAt_mul_cycleProduct rest]
        _ = residualPerm (c :: cs) := by
              simp [residualPerm]

omit [Fintype α] in
theorem runScript_undoScriptAt :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
      runScript (undoScriptAt cuts) =
        (if cs.length % 2 = 0 then 1 else helperSwap) * repairProductAt cuts
  | cs, cuts => by
      rw [undoScriptAt, runScript_append, runScript_repairScriptsAt]
      by_cases h : cs.length % 2 = 0
      · simp [finalCleanupScript, h]
      · have h' : cs.length % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one cs.length with h0 | h1
          · contradiction
          · exact h1
        simp [finalCleanupScript, h', helperSwap, runScript]

omit [Fintype α] in
theorem runScript_undoScriptAt_mul_cycleProduct :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
      runScript (undoScriptAt cuts) * cycleProduct cs = 1
  | cs, cuts => by
      rw [runScript_undoScriptAt, mul_assoc, repairProductAt_mul_cycleProduct, residualPerm_eq_parity]
      by_cases h : cs.length % 2 = 0
      · simp [h]
      · have h' : cs.length % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one cs.length with h0 | h1
          · contradiction
          · exact h1
        simp [h', helperSwap_mul_self]

omit [Fintype α] in
theorem futuramaTheoremAt :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
      runScript (undoScriptAt cuts) * cycleProduct cs = 1
  | _, cuts => runScript_undoScriptAt_mul_cycleProduct cuts

omit [Fintype α] in
/-- Parameterised cycle-list strong endpoint: for any `cuts : CutSchedule cs`,
the resulting `undoScriptAt cuts` correctly inverts `cycleProduct cs`,
has `Nodup` step list, distinct unordered transposition pairs, and
every step uses a helper. The strong companion of `futuramaTheoremAt`,
bundling the five facts consumed by downstream validators. -/
theorem futuramaTheoremStrongAt :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
      cs.Pairwise Cycle.Disjoint →
      runScript (undoScriptAt cuts) * cycleProduct cs = 1 ∧
        (undoScriptAt cuts).Nodup ∧
        ((undoScriptAt cuts).map stepPair).Nodup ∧
        ∀ step ∈ undoScriptAt cuts, UsesHelper step
  | cs, cuts => by
      intro hcs
      refine ⟨futuramaTheoremAt cuts, undoScriptAt_nodup cuts hcs,
        undoScriptAt_stepPairs_nodup cuts hcs, ?_⟩
      intro step hstep
      exact mem_undoScriptAt_usesHelper hstep

omit [Fintype α] in
/-- Full parameterised cycle-list endpoint including explicit nontriviality of every step. -/
theorem futuramaTheoremStrongAtFullSpec :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
      cs.Pairwise Cycle.Disjoint →
      runScript (undoScriptAt cuts) * cycleProduct cs = 1 ∧
        (undoScriptAt cuts).Nodup ∧
        ((undoScriptAt cuts).map stepPair).Nodup ∧
        (∀ step ∈ undoScriptAt cuts, UsesHelper step) ∧
        (∀ step ∈ undoScriptAt cuts, step.1 ≠ step.2)
  | cs, cuts => by
      intro hcs
      rcases futuramaTheoremStrongAt cuts hcs with
        ⟨hcorrect, hnodup, hstepPairs, hhelpers⟩
      refine ⟨hcorrect, hnodup, hstepPairs, hhelpers, ?_⟩
      intro step hstep
      exact mem_undoScriptAt_nontrivial hstep

/-- The canonical schedule recovering the current concrete repair script path. -/
def defaultSchedule : (cs : List (Cycle α)) → CutSchedule cs
  | [] => .nil
  | c :: cs => .cons (defaultCut c) (defaultSchedule cs)

omit [DecidableEq α] [Fintype α] in
@[simp] theorem repairScripts_eq_repairScriptsAt_default (cs : List (Cycle α)) :
    repairScripts cs = repairScriptsAt (defaultSchedule cs) := by
  induction cs with
  | nil =>
      rw [repairScripts_nil]
      rfl
  | cons c cs ih =>
      rw [repairScripts_cons]
      simp [-repairScripts_eq_flatMap, repairScriptsAt, defaultSchedule,
        repairScript_eq_repairScriptAt_default, ih]

omit [Fintype α] in
@[simp] theorem repairProduct_eq_repairProductAt_default (cs : List (Cycle α)) :
    repairProduct cs = repairProductAt (defaultSchedule cs) := by
  induction cs with
  | nil =>
      simp [repairProductAt, defaultSchedule, repairProduct]
  | cons c cs ih =>
      simp [repairProduct, repairProductAt, defaultSchedule, repairPerm_eq_repairPermAt_default,
        ih]

omit [Fintype α] in
theorem repairProductAt_eq_repairProduct :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) → repairProductAt cuts = repairProduct cs
  | [], .nil => by
      simp [repairProductAt, repairProduct]
  | c :: cs, .cons cut rest => by
      rw [repairProductAt, repairProduct, repairPermAt_eq_repairPerm, repairProductAt_eq_repairProduct rest]

omit [Fintype α] in
theorem runScript_undoScriptAt_eq_runScript_undoScript :
    {cs : List (Cycle α)} → (cuts : CutSchedule cs) →
      runScript (undoScriptAt cuts) = runScript (undoScript cs)
  | cs, cuts => by
      rw [runScript_undoScriptAt, runScript_undoScript, repairProductAt_eq_repairProduct]

omit [DecidableEq α] [Fintype α] in
@[simp] theorem undoScript_eq_undoScriptAt_default (cs : List (Cycle α)) :
    undoScript cs = undoScriptAt (defaultSchedule cs) := by
  rw [undoScript, undoScriptAt, repairScripts_eq_repairScriptsAt_default]

variable [Fintype α]

/-- Parameterised permutation-level repair script obtained from a chosen cut schedule on
the cycle factorisation of `σ`. -/
noncomputable def undoScriptOfPermAt (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    List (Body α × Body α) :=
  undoScriptAt cuts

-- `[Fintype α]` is needed for statement elaboration via `factorCycles σ` but
-- not referenced in the proof term; keep the binder and narrow the linter.
set_option linter.unusedSectionVars false in
theorem futuramaTheoremOfPermAt (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    runScript (undoScriptOfPermAt σ cuts) * liftPerm σ = 1 := by
  rw [undoScriptOfPermAt, ← cycleProduct_factorCycles]
  exact futuramaTheoremAt cuts

set_option linter.unusedSectionVars false in
/-- Parameterised permutation-level strong endpoint: instantiates
`futuramaTheoremStrongAt` to the cycle-list `factorCycles σ`. For
any cut schedule, `undoScriptOfPermAt σ cuts` correctly inverts
`liftPerm σ` while preserving the four machine-side invariants. -/
theorem futuramaTheoremOfPermStrongAt (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    runScript (undoScriptOfPermAt σ cuts) * liftPerm σ = 1 ∧
      (undoScriptOfPermAt σ cuts).Nodup ∧
      ((undoScriptOfPermAt σ cuts).map stepPair).Nodup ∧
      ∀ step ∈ undoScriptOfPermAt σ cuts, UsesHelper step := by
  rcases futuramaTheoremStrongAt cuts (factorCycles_pairwise_disjoint σ) with
    ⟨hcorrect, hnodup, hstepPairs, hhelpers⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [undoScriptOfPermAt, cycleProduct_factorCycles] using hcorrect
  · simpa [undoScriptOfPermAt] using hnodup
  · simpa [undoScriptOfPermAt] using hstepPairs
  · simpa [undoScriptOfPermAt] using hhelpers

set_option linter.unusedSectionVars false in
/-- Full parameterised permutation-level endpoint including explicit nontriviality
of every produced step. -/
theorem futuramaTheoremOfPermStrongAtFullSpec (σ : Perm α) (cuts : CutSchedule (factorCycles σ)) :
    runScript (undoScriptOfPermAt σ cuts) * liftPerm σ = 1 ∧
      (undoScriptOfPermAt σ cuts).Nodup ∧
      ((undoScriptOfPermAt σ cuts).map stepPair).Nodup ∧
      (∀ step ∈ undoScriptOfPermAt σ cuts, UsesHelper step) ∧
      (∀ step ∈ undoScriptOfPermAt σ cuts, step.1 ≠ step.2) := by
  rcases futuramaTheoremOfPermStrongAt σ cuts with
    ⟨hcorrect, hnodup, hstepPairs, hhelpers⟩
  refine ⟨hcorrect, hnodup, hstepPairs, hhelpers, ?_⟩
  intro step hstep
  exact mem_undoScriptAt_nontrivial (by simpa [undoScriptOfPermAt] using hstep)

-- The four default-route public endpoints live here and are defined
-- as specialisations of the parameterized `*At` family at
-- `defaultSchedule`. `*_defaultSchedule` aliases are retained as thin
-- pass-throughs.

-- The `omit [Fintype α] in` is required because the cycle-list endpoint
-- `futuramaTheoremStrong` is stated under only `[DecidableEq α]`, and
-- the proof path through `futuramaTheoremStrongAt` + `defaultSchedule`
-- introduces no genuine `[Fintype α]` dependency.
omit [Fintype α] in
/-- Default-route cycle-list strong endpoint. Defined as the
specialisation of `futuramaTheoremStrongAt` at `defaultSchedule cs`.
Conjuncts: correctness, list-level Nodup, unordered-pair Nodup,
helper inclusion of every step. -/
theorem futuramaTheoremStrong (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint) :
    runScript (undoScript cs) * cycleProduct cs = 1 ∧
      (undoScript cs).Nodup ∧
      ((undoScript cs).map stepPair).Nodup ∧
      ∀ step ∈ undoScript cs, UsesHelper step := by
  simpa [undoScript_eq_undoScriptAt_default] using
    (futuramaTheoremStrongAt (cuts := defaultSchedule cs) hcs)

omit [Fintype α] in
theorem futuramaTheoremStrong_defaultSchedule (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint) :
    runScript (undoScript cs) * cycleProduct cs = 1 ∧
      (undoScript cs).Nodup ∧
      ((undoScript cs).map stepPair).Nodup ∧
      ∀ step ∈ undoScript cs, UsesHelper step :=
  futuramaTheoremStrong cs hcs

-- Perm-level theorems retain `set_option linter.unusedSectionVars false in`:
-- the statement already requires `[Fintype α]` via `undoScriptOfPerm σ` /
-- `factorCycles σ`, but Lean's elaborator auto-includes a second `[Fintype α]`
-- from the section variable. The resulting duplicate-binder shape matches the
-- pre-existing `futuramaTheoremOfPermStrongAt` family and the old FiniteBridge
-- signatures; it is a Lean 4 elaboration quirk that preserves instance
-- resolution and does not affect downstream callers.
set_option linter.unusedSectionVars false in
/-- Default-route permutation-level strong endpoint. The most
human-readable form of the constructive Futurama theorem: for any
finite permutation `σ`, the canonical `undoScriptOfPerm σ` undoes
`liftPerm σ` and satisfies the four machine-side conditions
(list-level Nodup, unordered-pair Nodup, helper inclusion). Defined
as the specialisation of `futuramaTheoremOfPermStrongAt` at
`defaultSchedule (factorCycles σ)`. -/
theorem futuramaTheoremOfPermStrong (σ : Perm α) :
    runScript (undoScriptOfPerm σ) * liftPerm σ = 1 ∧
      (undoScriptOfPerm σ).Nodup ∧
      ((undoScriptOfPerm σ).map stepPair).Nodup ∧
      ∀ step ∈ undoScriptOfPerm σ, UsesHelper step := by
  simpa [undoScriptOfPermAt, undoScriptOfPerm, undoScript_eq_undoScriptAt_default] using
    (futuramaTheoremOfPermStrongAt σ (defaultSchedule (factorCycles σ)))

set_option linter.unusedSectionVars false in
theorem futuramaTheoremOfPermStrong_defaultSchedule (σ : Perm α) :
    runScript (undoScriptOfPerm σ) * liftPerm σ = 1 ∧
      (undoScriptOfPerm σ).Nodup ∧
      ((undoScriptOfPerm σ).map stepPair).Nodup ∧
      ∀ step ∈ undoScriptOfPerm σ, UsesHelper step :=
  futuramaTheoremOfPermStrong σ

set_option linter.unusedSectionVars false in
@[simp] theorem undoScriptOfPerm_eq_undoScriptOfPermAt_default (σ : Perm α) :
    undoScriptOfPerm σ = undoScriptOfPermAt σ (defaultSchedule (factorCycles σ)) := by
  simp [undoScriptOfPermAt, undoScriptOfPerm, undoScript_eq_undoScriptAt_default]

-- `omit [Fintype α]`: same reasoning as for `futuramaTheoremStrong` above.
omit [Fintype α] in
/-- Full-spec default-route cycle-list endpoint. Adds the
`step.1 ≠ step.2` (every-step-non-identity) conjunct on top of
`futuramaTheoremStrong`, matching the strongest external
specification of the constructive Futurama theorem. -/
theorem futuramaTheoremStrongFullSpec
    (cs : List (Cycle α)) (hcs : cs.Pairwise Cycle.Disjoint) :
    runScript (undoScript cs) * cycleProduct cs = 1 ∧
      (undoScript cs).Nodup ∧
      ((undoScript cs).map stepPair).Nodup ∧
      (∀ step ∈ undoScript cs, UsesHelper step) ∧
      (∀ step ∈ undoScript cs, step.1 ≠ step.2) := by
  simpa [undoScript_eq_undoScriptAt_default] using
    (futuramaTheoremStrongAtFullSpec (cuts := defaultSchedule cs) hcs)

set_option linter.unusedSectionVars false in
/-- Full-spec default-route permutation-level endpoint. The
strongest single-statement external specification of the constructive
Futurama theorem: arbitrary `σ` is undone by the canonical
`undoScriptOfPerm σ` with all five machine-side conditions
(correctness, list Nodup, unordered-pair Nodup, helper inclusion,
every-step-non-identity). -/
theorem futuramaTheoremOfPermStrongFullSpec (σ : Perm α) :
    runScript (undoScriptOfPerm σ) * liftPerm σ = 1 ∧
      (undoScriptOfPerm σ).Nodup ∧
      ((undoScriptOfPerm σ).map stepPair).Nodup ∧
      (∀ step ∈ undoScriptOfPerm σ, UsesHelper step) ∧
      (∀ step ∈ undoScriptOfPerm σ, step.1 ≠ step.2) := by
  simpa [undoScriptOfPermAt, undoScriptOfPerm, undoScript_eq_undoScriptAt_default] using
    (futuramaTheoremOfPermStrongAtFullSpec σ (defaultSchedule (factorCycles σ)))

end ParameterizedFamily

end Futurama
end Project
