import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.Sign

open Equiv Equiv.Perm

namespace Project
namespace Futurama

/-!
# Futurama Core Cycle Layer

This module contains the single-cycle constructive core used by the
Futurama theorem: body labels, cycle syntax, the executable cycle
repair script, its permutation semantics, and the single-cycle
machine-side step facts consumed by the schedule layer and downstream
modules.

## Main definitions

* `Body α` — the extended state space `α ⊕ {x, y}` with two helper bodies.
* `Cycle α` — the project's `(first, second, rest)` cycle representation
  (always length ≥ 2, enforced by `nodup`).
* `cyclePerm` — the permutation associated with a cycle (orientation
  caveat documented at its declaration).
* `runScript` — left-to-right execution of a list of swaps as a
  composed `Perm (Body α)`.
* `repairScript` — the canonical (default) per-cycle repair script.
* `repairPerm` — the permutation realised by `runScript repairScript`.
* `UsesHelper`, `stepPair`, `CanonicalStep` — machine-side step
  predicates consumed throughout the development.
-/

inductive Body (α : Type*)
  | orig : α → Body α
  | x : Body α
  | y : Body α
  deriving DecidableEq, Repr

instance [Fintype α] [DecidableEq α] : Fintype (Body α) where
  elems := (Finset.univ.image Body.orig) ∪ {Body.x, Body.y}
  complete := by
    intro b; cases b with
    | orig a => exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    | x => exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    | y => exact Finset.mem_union_right _ (Finset.mem_insert.mpr (.inr (Finset.mem_singleton_self _)))

variable {α : Type*} [DecidableEq α]

/-- A nontrivial cycle, written as `first :: second :: rest`. -/
structure Cycle (α : Type*) where
  first : α
  second : α
  rest : List α
  nodup : (first :: second :: rest).Nodup

namespace Cycle

def members (c : Cycle α) : List α :=
  c.first :: c.second :: c.rest

def tail (c : Cycle α) : List α :=
  c.second :: c.rest

omit [DecidableEq α] in
@[simp] theorem members_eq (c : Cycle α) :
    c.members = c.first :: c.second :: c.rest := rfl

omit [DecidableEq α] in
@[simp] theorem tail_eq (c : Cycle α) :
    c.tail = c.second :: c.rest := rfl

omit [DecidableEq α] in
theorem first_ne_second (c : Cycle α) : c.first ≠ c.second := by
  intro h
  exact c.nodup.notMem (by simp [h])

omit [DecidableEq α] in
theorem mem_members_of_mem_tail (c : Cycle α) {a : α} (ha : a ∈ c.tail) :
    a ∈ c.members := by
  simpa [Cycle.members, Cycle.tail] using List.mem_cons_of_mem _ ha

omit [DecidableEq α] in
theorem not_mem_rest_first (c : Cycle α) : c.first ∉ c.rest := by
  intro h
  exact c.nodup.notMem (by simp [h])

omit [DecidableEq α] in
theorem not_mem_rest_second (c : Cycle α) : c.second ∉ c.rest := by
  simpa [Cycle.tail] using c.nodup.of_cons.notMem

omit [DecidableEq α] in
theorem nodup_tail (c : Cycle α) : c.tail.Nodup := by
  simpa [Cycle.tail] using c.nodup.of_cons

end Cycle

/-- The helper transposition. -/
def helperSwap : Perm (Body α) :=
  swap Body.x Body.y

/-- Swap helper `x` with an original body. -/
def swapX (a : α) : Perm (Body α) :=
  swap Body.x (.orig a)

/-- Swap helper `y` with an original body. -/
def swapY (a : α) : Perm (Body α) :=
  swap Body.y (.orig a)

/-- The placement induced by a cycle:
`a₁ ↦ aₖ`, `a₂ ↦ a₁`, ..., `aₖ ↦ aₖ₋₁`. -/
def cyclePermAux : α → List α → Perm (Body α)
  | _, [] => 1
  | prev, a :: rest => cyclePermAux a rest * swap (.orig a) (.orig prev)

/-- The cyclic permutation associated with `c = (first, second, rest)`.

Implementation note (orientation): `cyclePerm c` is the **inverse** of
the paper's standard cycle notation `(c.first c.second c.rest...)`.
Concretely, `cyclePerm c` sends
`c.first ↦ c.last, c.second ↦ c.first, ..., c.last ↦ c.second-from-last`,
which is the action `(map orig c.members).reverse.formPerm` (see
`cyclePermAux_eq_formPerm_reverse`). The inverse-orientation choice is
why the bridge into Mathlib's `Equiv.Perm.IsCycle` machinery treats
`cycleProduct` as a "scramble that can be undone" rather than as the
cycle itself; the orientation caveat is documented in
`paper_correspondence.md` Section 6. -/
def cyclePerm (c : Cycle α) : Perm (Body α) :=
  cyclePermAux c.first c.tail

theorem cyclePermAux_eq_formPerm_reverse (first : α) (tail : List α) :
    cyclePermAux first tail = (List.map Body.orig (first :: tail)).reverse.formPerm := by
  induction tail generalizing first with
  | nil =>
      simp [cyclePermAux]
  | cons a rest ih =>
      rw [cyclePermAux]
      simp [ih, List.formPerm_append_pair]

/-- Repair instructions as an executable list of swaps.

For one cycle `c`, these are the helper-`y` sweep steps used by the default
single-cycle repair block. The later definitions `repairScriptAt` and
`repairPermAt` formalize the full parameterised family, while
`repairScript` remains the canonical default-cut executable block. -/
def sweepScript (tail : List α) : List (Body α × Body α) :=
  tail.map (fun a => (Body.y, Body.orig a))

/-- Repair instructions as an executable list of swaps. -/
def finishScript (first second : α) : List (Body α × Body α) :=
  [(Body.x, Body.orig second), (Body.y, Body.orig first)]

/-- The full executable repair block for a single cycle. -/
def repairScript (c : Cycle α) : List (Body α × Body α) :=
  (Body.x, Body.orig c.first) ::
    sweepScript c.tail ++ finishScript c.first c.second

/-- Execute a list of body swaps from left to right. -/
def runScript : List (Body α × Body α) → Perm (Body α)
  | [] => 1
  | (u, v) :: steps => runScript steps * swap u v

/-- Keeler's repair program for one cycle.

The theorem `repairPerm_mul_cyclePerm` below is the formal counterpart of the
paper's cycle-local claim that the repair block for `Cᵢ` leaves only the helper
swap `(x y)`. -/
def repairPerm (c : Cycle α) : Perm (Body α) :=
  runScript (repairScript c)

omit [DecidableEq α] in
@[simp] theorem sweepScript_nil :
    sweepScript ([] : List α) = [] := rfl

omit [DecidableEq α] in
@[simp] theorem sweepScript_cons (a : α) (rest : List α) :
    sweepScript (a :: rest) = (Body.y, Body.orig a) :: sweepScript rest := by
  simp [sweepScript]

omit [DecidableEq α] in
@[simp] theorem sweepScript_length (tail : List α) :
    (sweepScript tail).length = tail.length := by
  simp [sweepScript]

omit [DecidableEq α] in
@[simp] theorem finishScript_length (first second : α) :
    (finishScript first second).length = 2 := by
  simp [finishScript]

omit [DecidableEq α] in
@[simp] theorem repairScript_length (c : Cycle α) :
    (repairScript c).length = c.members.length + 2 := by
  simp [repairScript, Cycle.members, Cycle.tail, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem finishScript_apply_x (first second : α) (h : first ≠ second) :
    runScript (finishScript first second) Body.x = Body.orig second := by
  rw [finishScript, runScript, mul_apply, swap_apply_left]
  have hy : (Body.orig second : Body α) ≠ Body.y := by simp
  have hfirst : (Body.orig second : Body α) ≠ Body.orig first := by
    simpa using h.symm
  simpa using (swap_apply_of_ne_of_ne (a := Body.y) (b := Body.orig first) (x := Body.orig second) hy hfirst)

@[simp] theorem finishScript_apply_y (first second : α) :
    runScript (finishScript first second) Body.y = Body.orig first := by
  simp [finishScript, runScript, mul_apply, swap_apply_of_ne_of_ne]

@[simp] theorem finishScript_apply_first (first second : α) (h : first ≠ second) :
    runScript (finishScript first second) (Body.orig first) = Body.y := by
  simp [finishScript, runScript, mul_apply, h, swap_apply_of_ne_of_ne]

@[simp] theorem finishScript_apply_second (first second : α) :
    runScript (finishScript first second) (Body.orig second) = Body.x := by
  simp [finishScript, runScript, mul_apply, swap_apply_of_ne_of_ne]

@[simp] theorem finishScript_apply_orig_of_ne {first second a : α}
    (hfa : a ≠ first) (hsa : a ≠ second) :
    runScript (finishScript first second) (Body.orig a) = Body.orig a := by
  simp [finishScript, runScript, mul_apply, swap_apply_of_ne_of_ne, hfa, hsa]

@[simp] theorem runScript_nil : runScript ([] : List (Body α × Body α)) = (1 : Perm (Body α)) :=
  rfl

@[simp] theorem runScript_cons (u v : Body α) (steps : List (Body α × Body α)) :
    runScript ((u, v) :: steps) = runScript steps * swap u v :=
  rfl

@[simp] theorem runScript_singleton (u v : Body α) :
    runScript ([(u, v)] : List (Body α × Body α)) = swap u v := by
  simp [runScript]

@[simp] theorem runScript_singleton_apply (u v : Body α) (z : Body α) :
    runScript ([(u, v)] : List (Body α × Body α)) z = swap u v z := by
  simp [runScript]

theorem runScript_append (steps₁ steps₂ : List (Body α × Body α)) :
    runScript (steps₁ ++ steps₂) = runScript steps₂ * runScript steps₁ := by
  induction steps₁ with
  | nil =>
      simp [runScript]
  | cons step steps ih =>
      rcases step with ⟨u, v⟩
      simp [runScript, ih, mul_assoc]

theorem runScript_append_apply (steps₁ steps₂ : List (Body α × Body α)) (z : Body α) :
    runScript (steps₁ ++ steps₂) z = runScript steps₂ (runScript steps₁ z) := by
  rw [runScript_append, mul_apply]

@[simp] theorem cyclePermAux_apply_x (first : α) (tail : List α) :
    cyclePermAux first tail Body.x = Body.x := by
  induction tail generalizing first with
  | nil =>
      simp [cyclePermAux]
  | cons a rest ih =>
      simp [cyclePermAux, ih, swap_apply_of_ne_of_ne]

@[simp] theorem cyclePermAux_apply_y (first : α) (tail : List α) :
    cyclePermAux first tail Body.y = Body.y := by
  induction tail generalizing first with
  | nil =>
      simp [cyclePermAux]
  | cons a rest ih =>
      simp [cyclePermAux, ih, swap_apply_of_ne_of_ne]

@[simp] theorem cyclePermAux_skip_head {first a b : α} {rest : List α}
    (hab : b ≠ a) (hbf : b ≠ first) :
    cyclePermAux first (a :: rest) (Body.orig b) =
      cyclePermAux a rest (Body.orig b) := by
  rw [cyclePermAux, mul_apply, swap_apply_of_ne_of_ne]
  · simpa using hab
  · simpa using hbf

@[simp] theorem cyclePermAux_orig_of_not_mem {first a : α} {tail : List α}
    (ha : a ∉ first :: tail) :
    cyclePermAux first tail (Body.orig a) = Body.orig a := by
  induction tail generalizing first with
  | nil =>
      simp [cyclePermAux] at ha ⊢
  | cons b rest ih =>
      simp at ha
      rcases ha with ⟨hfirst, hneq, hrest⟩
      rw [cyclePermAux_skip_head hneq hfirst]
      simpa [hneq, hrest] using ih (first := b) (by simp [hneq, hrest])

@[simp] theorem cyclePermAux_head (first a : α) (rest : List α)
    (hfa : first ≠ a) (h : first ∉ rest) :
    cyclePermAux first (a :: rest) (Body.orig a) = Body.orig first := by
  rw [cyclePermAux, mul_apply, swap_apply_left]
  exact cyclePermAux_orig_of_not_mem (by simp [hfa, h])

@[simp] theorem cyclePermAux_first_step (first a : α) (rest : List α) :
    cyclePermAux first (a :: rest) (Body.orig first) =
      cyclePermAux a rest (Body.orig a) := by
  simp [cyclePermAux, mul_apply]

@[simp] theorem runScript_sweep_x (tail : List α) :
    runScript (sweepScript tail) Body.x = Body.x := by
  induction tail with
  | nil =>
      simp [sweepScript]
  | cons a rest ih =>
      rw [sweepScript_cons, runScript_cons, mul_apply, swap_apply_of_ne_of_ne]
      · simpa using ih
      · simp
      · simp

@[simp] theorem runScript_sweep_orig_of_not_mem {tail : List α} {a : α}
    (ha : a ∉ tail) :
    runScript (sweepScript tail) (Body.orig a) = Body.orig a := by
  induction tail with
  | nil =>
      simp [sweepScript]
  | cons b rest ih =>
      simp at ha
      rcases ha with ⟨hab, hrest⟩
      rw [sweepScript_cons, runScript_cons, mul_apply, swap_apply_of_ne_of_ne]
      · exact ih hrest
      · simp
      · simpa using hab

@[simp] theorem runScript_sweep_y {a : α} {rest : List α}
    (h : (a :: rest).Nodup) :
    runScript (sweepScript (a :: rest)) Body.y = Body.orig a := by
  cases rest with
  | nil =>
      simp [sweepScript, runScript]
  | cons b rest =>
      rw [sweepScript_cons, runScript_cons, mul_apply, swap_apply_left]
      exact runScript_sweep_orig_of_not_mem h.notMem

@[simp] theorem runScript_sweep_head {a : α} {rest : List α}
    (h : (a :: rest).Nodup) :
    runScript (sweepScript (a :: rest)) (Body.orig a) =
      match rest with
      | [] => Body.y
      | b :: _ => Body.orig b := by
  cases rest with
  | nil =>
      simp [sweepScript, runScript]
  | cons b rest =>
      rw [sweepScript_cons, runScript_cons, mul_apply, swap_apply_right]
      exact runScript_sweep_y (a := b) (rest := rest) (by simpa using h.of_cons)

@[simp] theorem runScript_sweep_skip_head {a b : α} {rest : List α}
    (hab : b ≠ a) :
    runScript (sweepScript (a :: rest)) (Body.orig b) =
      runScript (sweepScript rest) (Body.orig b) := by
  rw [sweepScript_cons, runScript_cons, mul_apply, swap_apply_of_ne_of_ne]
  · simp
  · simpa using hab

theorem runScript_sweep_cycle_head (head : α) (rest : List α)
    (h : (head :: rest).Nodup) :
    runScript (sweepScript rest)
      (swap Body.y (Body.orig head) (cyclePermAux head rest (Body.orig head))) = Body.y := by
  induction rest generalizing head with
  | nil =>
      simp [sweepScript, cyclePermAux]
  | cons a tail ih =>
      have hhead : head ≠ a := by
        intro hEq
        exact h.notMem (by simp [hEq])
      have hnot : head ∉ tail := by
        intro hm
        exact h.notMem (by simp [hhead, hm])
      have hfix : cyclePermAux a tail (Body.orig head) = Body.orig head := by
        exact cyclePermAux_orig_of_not_mem (first := a) (tail := tail) (a := head)
          (by simp [hhead, hnot])
      have hneqhead : cyclePermAux a tail (Body.orig a) ≠ Body.orig head := by
        intro hEq
        have := (cyclePermAux a tail).injective (hEq.trans hfix.symm)
        have hae : a = head := by
          simpa using this
        exact hhead hae.symm
      have hneqy : cyclePermAux a tail (Body.orig a) ≠ Body.y := by
        intro hEq
        have := (cyclePermAux a tail).injective (hEq.trans (cyclePermAux_apply_y a tail).symm)
        cases this
      rw [sweepScript_cons, runScript_cons, mul_apply, cyclePermAux_first_step]
      have hsimp :
          swap Body.y (Body.orig head) (cyclePermAux a tail (Body.orig a)) =
            cyclePermAux a tail (Body.orig a) := by
        exact swap_apply_of_ne_of_ne hneqy hneqhead
      rw [hsimp]
      exact ih a (by simpa using h.of_cons)

theorem runScript_sweep_cycle_rest {head a : α} {rest : List α}
    (h : (head :: rest).Nodup) (ha : a ∈ rest) :
    runScript (sweepScript rest)
      (swap Body.y (Body.orig head) (cyclePermAux head rest (Body.orig a))) = Body.orig a := by
  induction rest generalizing head with
  | nil =>
      cases ha
  | cons b tail ih =>
      rcases List.mem_cons.1 ha with hEq | ha
      · have hhead : head ≠ b := by
          intro hEq
          exact h.notMem (by simp [hEq])
        have hnot : head ∉ tail := by
          intro hm
          exact h.notMem (by simp [hhead, hm])
        subst a
        rw [cyclePermAux_head head b tail hhead hnot]
        simpa [sweepScript_cons, runScript_cons, mul_apply] using
          runScript_sweep_orig_of_not_mem (tail := tail) (a := b) h.of_cons.notMem
      · have hhead : head ≠ b := by
          intro hEq
          exact h.notMem (by simp [hEq])
        have hnot : head ∉ tail := by
          intro hm
          exact h.notMem (by simp [hhead, hm])
        have hab : a ≠ b := by
          intro hEq
          subst a
          exact h.of_cons.notMem ha
        have hahead : a ≠ head := by
          intro hEq
          subst a
          exact h.notMem (by simp [ha])
        have hfix : cyclePermAux b tail (Body.orig head) = Body.orig head := by
          exact cyclePermAux_orig_of_not_mem (first := b) (tail := tail) (a := head)
            (by simp [hhead, hnot])
        have hneqhead : cyclePermAux b tail (Body.orig a) ≠ Body.orig head := by
          intro hEq
          have := (cyclePermAux b tail).injective (hEq.trans hfix.symm)
          exact hahead (by simpa using this)
        have hneqy : cyclePermAux b tail (Body.orig a) ≠ Body.y := by
          intro hEq
          have := (cyclePermAux b tail).injective (hEq.trans (cyclePermAux_apply_y b tail).symm)
          cases this
        rw [sweepScript_cons, runScript_cons, mul_apply, cyclePermAux_skip_head hab hahead]
        have hsimp :
            swap Body.y (Body.orig head) (cyclePermAux b tail (Body.orig a)) =
              cyclePermAux b tail (Body.orig a) := by
          exact swap_apply_of_ne_of_ne hneqy hneqhead
        rw [hsimp]
        exact ih (head := b) (by simpa using h.of_cons) ha

theorem repairPerm_mul_cyclePerm_apply (c : Cycle α) (z : Body α) :
    (repairPerm c * cyclePerm c) z =
      runScript (finishScript c.first c.second)
        (runScript (sweepScript c.rest)
          (swap Body.y (Body.orig c.second)
            (swap Body.x (Body.orig c.first) (cyclePerm c z)))) := by
  simp [repairPerm, repairScript, cyclePerm, Cycle.tail, runScript_append, runScript_cons,
    sweepScript_cons, mul_apply]

set_option linter.unnecessarySimpa false in
/-- Paper correspondence: for a single cycle `Cᵢ`, the repair block `σᵢ`
turns `Cᵢ` into the helper swap `(x y)`. -/
theorem repairPerm_mul_cyclePerm (c : Cycle α) :
    repairPerm c * cyclePerm c = helperSwap := by
  ext z
  cases z with
  | x =>
      rw [repairPerm_mul_cyclePerm_apply]
      have hcyc : cyclePerm c Body.x = Body.x := by
        simp [cyclePerm]
      have hswapx : swap Body.x (Body.orig c.first) Body.x = Body.orig c.first := by
        simp
      rw [hcyc, hswapx, swap_apply_of_ne_of_ne]
      · rw [runScript_sweep_orig_of_not_mem (tail := c.rest) (a := c.first) c.not_mem_rest_first]
        simpa [helperSwap] using finishScript_apply_first c.first c.second c.first_ne_second
      · simp
      · simpa using c.first_ne_second
  | y =>
      rw [repairPerm_mul_cyclePerm_apply]
      have hcyc : cyclePerm c Body.y = Body.y := by
        simp [cyclePerm]
      have hswapx : swap Body.x (Body.orig c.first) Body.y = Body.y := by
        exact swap_apply_of_ne_of_ne (by simp) (by simp)
      rw [hcyc, hswapx, swap_apply_left]
      rw [runScript_sweep_orig_of_not_mem (tail := c.rest) (a := c.second) c.not_mem_rest_second]
      simpa [helperSwap] using finishScript_apply_second c.first c.second
  | orig a =>
      by_cases hfirst : a = c.first
      · subst hfirst
        rw [repairPerm_mul_cyclePerm_apply]
        have hcyc :
            cyclePerm c (Body.orig c.first) =
              cyclePermAux c.second c.rest (Body.orig c.second) := by
          simp [cyclePerm, Cycle.tail, cyclePermAux_first_step]
        have hsweep :
            runScript (sweepScript c.rest)
              (swap Body.y (Body.orig c.second)
                (cyclePermAux c.second c.rest (Body.orig c.second))) = Body.y := by
          simpa using runScript_sweep_cycle_head c.second c.rest c.nodup_tail
        have hfix :
            cyclePermAux c.second c.rest (Body.orig c.first) = Body.orig c.first := by
          exact cyclePermAux_orig_of_not_mem (first := c.second) (tail := c.rest) (a := c.first)
            (by simp [c.first_ne_second, c.not_mem_rest_first])
        have hneqfirst :
            cyclePermAux c.second c.rest (Body.orig c.second) ≠ Body.orig c.first := by
          intro hEq
          have hsame := (cyclePermAux c.second c.rest).injective (hEq.trans hfix.symm)
          have hs : c.second = c.first := by
            simpa using hsame
          exact c.first_ne_second hs.symm
        have hneqx :
            cyclePermAux c.second c.rest (Body.orig c.second) ≠ Body.x := by
          intro hEq
          have hsame := (cyclePermAux c.second c.rest).injective
            (hEq.trans (cyclePermAux_apply_x c.second c.rest).symm)
          cases hsame
        have hswapx :
            swap Body.x (Body.orig c.first)
              (cyclePermAux c.second c.rest (Body.orig c.second)) =
              cyclePermAux c.second c.rest (Body.orig c.second) := by
          exact swap_apply_of_ne_of_ne hneqx hneqfirst
        rw [hcyc, hswapx, hsweep]
        rw [helperSwap, swap_apply_of_ne_of_ne] <;> simp
      · by_cases hsecond : a = c.second
        · subst hsecond
          rw [repairPerm_mul_cyclePerm_apply]
          have hcyc :
              cyclePerm c (Body.orig c.second) = Body.orig c.first := by
            simpa [cyclePerm, Cycle.tail] using
              cyclePermAux_head c.first c.second c.rest c.first_ne_second c.not_mem_rest_first
          have hswapx : swap Body.x (Body.orig c.first) (Body.orig c.first) = Body.x := by
            simp
          have hswapy : swap Body.y (Body.orig c.second) Body.x = Body.x := by
            exact swap_apply_of_ne_of_ne (by simp) (by simp)
          rw [hcyc, hswapx, hswapy, runScript_sweep_x]
          simpa [helperSwap] using finishScript_apply_x c.first c.second c.first_ne_second
        · by_cases hmem : a ∈ c.rest
          · have hsweep :
              runScript (sweepScript c.rest)
                (swap Body.y (Body.orig c.second)
                  (cyclePermAux c.second c.rest (Body.orig a))) = Body.orig a := by
              simpa using runScript_sweep_cycle_rest
                (head := c.second) (a := a) (rest := c.rest) c.nodup_tail hmem
            have hfix :
                cyclePermAux c.second c.rest (Body.orig c.first) = Body.orig c.first := by
              exact cyclePermAux_orig_of_not_mem (first := c.second) (tail := c.rest) (a := c.first)
                (by simp [c.first_ne_second, c.not_mem_rest_first])
            have hneqfirst :
                cyclePermAux c.second c.rest (Body.orig a) ≠ Body.orig c.first := by
              intro hEq
              have hsame := (cyclePermAux c.second c.rest).injective (hEq.trans hfix.symm)
              exact hfirst (by simpa using hsame)
            have hneqx :
                cyclePermAux c.second c.rest (Body.orig a) ≠ Body.x := by
              intro hEq
              have hsame := (cyclePermAux c.second c.rest).injective
                (hEq.trans (cyclePermAux_apply_x c.second c.rest).symm)
              cases hsame
            rw [repairPerm_mul_cyclePerm_apply]
            have hcyc :
                cyclePerm c (Body.orig a) =
                  cyclePermAux c.second c.rest (Body.orig a) := by
              simpa [cyclePerm, Cycle.tail] using
                cyclePermAux_skip_head (first := c.first) (a := c.second) (b := a)
                  (rest := c.rest) (by simpa using hsecond) (by simpa using hfirst)
            have hswapx :
                swap Body.x (Body.orig c.first) (cyclePermAux c.second c.rest (Body.orig a)) =
                  cyclePermAux c.second c.rest (Body.orig a) := by
              exact swap_apply_of_ne_of_ne hneqx hneqfirst
            rw [hcyc, hswapx, hsweep]
            simpa [helperSwap] using finishScript_apply_orig_of_ne hfirst hsecond
          · have htail : a ∉ c.second :: c.rest := by
              simp [hsecond, hmem]
            rw [repairPerm_mul_cyclePerm_apply]
            have hcyc : cyclePerm c (Body.orig a) = Body.orig a := by
              simpa [cyclePerm, Cycle.tail] using
                cyclePermAux_orig_of_not_mem (first := c.first) (tail := c.second :: c.rest) (a := a)
                  (by simp [hfirst, hsecond, hmem])
            have hswapx : swap Body.x (Body.orig c.first) (Body.orig a) = Body.orig a := by
              exact swap_apply_of_ne_of_ne (by simp) (by simpa using hfirst)
            have hswapy : swap Body.y (Body.orig c.second) (Body.orig a) = Body.orig a := by
              exact swap_apply_of_ne_of_ne (by simp) (by simpa using hsecond)
            rw [hcyc, hswapx, hswapy]
            rw [runScript_sweep_orig_of_not_mem (tail := c.rest) (a := a) hmem]
            simpa [helperSwap] using finishScript_apply_orig_of_ne hfirst hsecond

/-- Two cycles are disjoint when they mention no common original label. -/
abbrev Cycle.Disjoint (c d : Cycle α) : Prop :=
  List.Disjoint c.members d.members

def UsesHelper (step : Body α × Body α) : Prop :=
  step.1 = Body.x ∨ step.1 = Body.y ∨ step.2 = Body.x ∨ step.2 = Body.y

/-- All repair steps have one of the canonical helper-first shapes. -/
def CanonicalStep (step : Body α × Body α) : Prop :=
  (∃ a : α, step = (Body.x, Body.orig a)) ∨
    (∃ a : α, step = (Body.y, Body.orig a)) ∨
    step = (Body.x, Body.y)

/-- Forget the orientation of a swap step, keeping only the unordered pair of bodies. -/
def stepPair (step : Body α × Body α) : Sym2 (Body α) :=
  s(step.1, step.2)

omit [DecidableEq α] in
theorem CanonicalStep.usesHelper {step : Body α × Body α} (h : CanonicalStep step) :
    UsesHelper step := by
  rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl <;> simp [UsesHelper]

omit [DecidableEq α] in
theorem CanonicalStep.nontrivial {step : Body α × Body α} (h : CanonicalStep step) :
    step.1 ≠ step.2 := by
  rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl <;> simp

omit [DecidableEq α] in
theorem mem_sweepScript_iff {tail : List α} {step : Body α × Body α} :
    step ∈ sweepScript tail ↔ ∃ a ∈ tail, step = (Body.y, Body.orig a) := by
  simp [sweepScript, eq_comm]

omit [DecidableEq α] in
theorem mem_finishScript_iff {first second : α} {step : Body α × Body α} :
    step ∈ finishScript first second ↔
      step = (Body.x, Body.orig second) ∨ step = (Body.y, Body.orig first) := by
  simp [finishScript]

omit [DecidableEq α] in
theorem mem_repairScript_iff (c : Cycle α) {step : Body α × Body α} :
    step ∈ repairScript c ↔
      (∃ a ∈ c.members, step = (Body.y, Body.orig a)) ∨
      (∃ a ∈ [c.first, c.second], step = (Body.x, Body.orig a)) := by
  constructor
  · intro h
    have h' :
        step = (Body.x, Body.orig c.first) ∨
          step ∈ sweepScript c.tail ∨
            step ∈ finishScript c.first c.second := by
      simpa [repairScript, List.mem_append, or_assoc, or_left_comm] using h
    rcases h' with hstep | hsweep | hfinish
    · exact Or.inr ⟨c.first, by simp, hstep⟩
    · rcases (mem_sweepScript_iff).1 hsweep with ⟨a, ha, hstep⟩
      exact Or.inl ⟨a, c.mem_members_of_mem_tail ha, hstep⟩
    · rcases (mem_finishScript_iff).1 hfinish with hstep | hstep
      · exact Or.inr ⟨c.second, by simp, hstep⟩
      · exact Or.inl ⟨c.first, by simp [Cycle.members], hstep⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · have ha' : a = c.first ∨ a ∈ c.tail := by
        simpa [Cycle.members, Cycle.tail] using ha
      rcases ha' with rfl | ha'
      · simp [repairScript, finishScript]
      · have hsweep : (Body.y, Body.orig a) ∈ sweepScript c.tail := by
          exact (mem_sweepScript_iff).2 ⟨a, ha', rfl⟩
        have happ :
            (Body.y, Body.orig a) ∈ sweepScript c.tail ++ finishScript c.first c.second := by
          exact List.mem_append.2 (Or.inl hsweep)
        exact List.mem_cons.2 (Or.inr happ)
    · simp at ha
      rcases ha with rfl | rfl
      · simp [repairScript]
      · simp [repairScript, finishScript]

omit [DecidableEq α] in
theorem mem_repairScript_canonical {c : Cycle α} {step : Body α × Body α}
    (h : step ∈ repairScript c) : CanonicalStep step := by
  rcases (mem_repairScript_iff c).1 h with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩
  · exact Or.inr <| Or.inl ⟨a, rfl⟩
  · exact Or.inl ⟨a, rfl⟩


omit [DecidableEq α] in
theorem sweepScript_nodup {tail : List α} (h : tail.Nodup) :
    (sweepScript tail).Nodup := by
  let f : α → Body α × Body α := fun a => ((Body.y : Body α), Body.orig a)
  have hinj : Function.Injective f := by
    intro a b hEq
    injection hEq with _ horig
    injection horig
  simpa [sweepScript, f] using h.map hinj

omit [DecidableEq α] in
theorem repairScript_nodup (c : Cycle α) :
    (repairScript c).Nodup := by
  have hsweep : (sweepScript c.tail).Nodup :=
    sweepScript_nodup c.nodup_tail
  have hfinish : (finishScript c.first c.second).Nodup := by
    simp [finishScript]
  have hdisj : List.Disjoint (sweepScript c.tail) (finishScript c.first c.second) := by
    rw [List.disjoint_left]
    intro step hs hf
    rcases (mem_sweepScript_iff).1 hs with ⟨a, ha, rfl⟩
    rcases (mem_finishScript_iff).1 hf with hstep | hstep
    · simp at hstep
    · have hEq : a = c.first := by
        have horig : Body.orig a = Body.orig c.first := by
          exact congrArg Prod.snd hstep
        injection horig
      have : c.first ∈ c.tail := by simpa [hEq] using ha
      simp [Cycle.tail, c.first_ne_second, c.not_mem_rest_first] at this
  refine List.Nodup.cons ?_ (hsweep.append hfinish hdisj)
  intro hmem
  have hmem' :
      (Body.x, Body.orig c.first) ∈ sweepScript c.tail ∨
        (Body.x, Body.orig c.first) ∈ finishScript c.first c.second := by
    simpa using hmem
  rcases hmem' with hs | hf
  · rcases (mem_sweepScript_iff).1 hs with ⟨a, _, hstep⟩
    simp at hstep
  · rcases (mem_finishScript_iff).1 hf with hstep | hstep
    · injection hstep with _ horig
      have hEq : c.first = c.second := by
        injection horig
      exact c.first_ne_second hEq
    · simp at hstep

omit [DecidableEq α] in
theorem repairScript_disjoint_of_cycle_disjoint {c d : Cycle α}
    (hcd : Cycle.Disjoint c d) :
    List.Disjoint (repairScript c) (repairScript d) := by
  rw [List.disjoint_left]
  intro step hs hd
  rcases (mem_repairScript_iff c).1 hs with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rcases (mem_repairScript_iff d).1 hd with ⟨b, hb, hstep⟩ | ⟨b, hb, hstep⟩
    · have hEq : Body.orig a = Body.orig b := by
        exact congrArg Prod.snd hstep
      have hab : a = b := by
        injection hEq
      exact hcd ha (hab ▸ hb)
    · simp at hstep
  · rcases (mem_repairScript_iff d).1 hd with ⟨b, hb, hstep⟩ | ⟨b, hb, hstep⟩
    · simp at hstep
    · have hEq : Body.orig a = Body.orig b := by
        exact congrArg Prod.snd hstep
      have hab : a = b := by
        injection hEq
      have hca : a ∈ c.members := by
        have ha' : a = c.first ∨ a = c.second := by simpa using ha
        rcases ha' with rfl | rfl <;> simp [Cycle.members]
      have hdb : b ∈ d.members := by
        have hb' : b = d.first ∨ b = d.second := by simpa using hb
        rcases hb' with rfl | rfl <;> simp [Cycle.members]
      exact hcd hca (hab.symm ▸ hdb)

omit [DecidableEq α] in
theorem not_mem_repairScript_helperSwap (c : Cycle α) :
    (Body.x, Body.y) ∉ repairScript c := by
  intro h
  rcases (mem_repairScript_iff c).1 h with ⟨a, _, hstep⟩ | ⟨a, _, hstep⟩
  · simp at hstep
  · simp at hstep

omit [DecidableEq α] in
theorem stepPair_injective_of_canonical {step₁ step₂ : Body α × Body α}
    (h₁ : CanonicalStep step₁) (h₂ : CanonicalStep step₂)
    (hpair : stepPair step₁ = stepPair step₂) : step₁ = step₂ := by
  rcases h₁ with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · rcases h₂ with ⟨b, rfl⟩ | ⟨b, rfl⟩ | rfl
    · simp [stepPair] at hpair
      simp [hpair]
    · simp [stepPair] at hpair
    · simp [stepPair] at hpair
  · rcases h₂ with ⟨b, rfl⟩ | ⟨b, rfl⟩ | rfl
    · simp [stepPair] at hpair
    · simp [stepPair] at hpair
      simp [hpair]
    · simp [stepPair] at hpair
  · rcases h₂ with ⟨b, rfl⟩ | ⟨b, rfl⟩ | rfl
    · simp [stepPair] at hpair
    · simp [stepPair] at hpair
    · rfl


end Futurama
end Project
