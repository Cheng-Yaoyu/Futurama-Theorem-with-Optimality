import Project.Futurama.CoreCycle
import Project.Futurama.CoreSchedule
import Project.Futurama.FiniteBridge
import Project.Futurama.ParameterizedFamily
import Project.Futurama.Optimality.RepairSeq
import Project.Futurama.Optimality.LowerBound.Layer0
import Project.Futurama.Optimality.LowerBound.Layer1
import Project.Futurama.Optimality.LowerBound.Layer2

/-!
# Optimality / UpperBound — Evans/Huang/Nguyen optimal construction λ

This file hosts the explicit `n + r + 2`-factor construction that
realises paper Theorem 1's upper bound:

* `optimalScript : List (Cycle α) → List (Body α × Body α)` — the
  cycle-list level construction;
* `optimalScriptOfPerm σ : List (Body α × Body α)` — the `Perm α`
  level specialisation via `factorCycles σ`;
* `optimalScript_correct` / `_length` / `_usesHelper` /
  `_nontrivial` / `_nodup` / `_stepPairs_nodup` and the
  `optimalScriptOfPerm_*` siblings packaging the four machine-side
  invariants;
* `futuramaTheorem1OfPerm` — the three-conjunct theorem packaging
  on the explicit witness;
* `optimalRepairSeqOfPerm` — the `RepairSeq` existence witness;
* `futuramaTheorem1Full` — the single-declaration existence form.

**Embedded definitional-equality regression checks**: this file ends
with a nine-line `example := rfl` block that pins down the layered
paper-λ block hierarchy (`firstYStep`, `gyBlock`, `gxBlock`,
`leadBlock`, `coreOptimalScript`, `optimalScript`, `sweepScript`,
`swapHelpersStep`, `optimalScriptOfPerm`). The block lives **inside**
`section OptimalUpperBound` so the private block definitions remain
visible. If a future edit accidentally breaks any of the layered
`def`-equalities, the build fails immediately at one of the `rfl`
lines.
-/

open Equiv Equiv.Perm

namespace Project
namespace Futurama

variable {α : Type*} [DecidableEq α] [Fintype α]

-- Section 7: Optimal Upper Bound — Evans/Huang/Nguyen λ
-- ═══════════════════════════════════════════════

section OptimalUpperBound

/-- The first `y`-step `(y, a_1)` in the paper's λ construction
(paper §3.1, "first move involving y"). -/
private def firstYStep (c : Cycle α) : Body α × Body α :=
  (Body.y, Body.orig c.first)

/-- The `G_1(y)` block of paper Theorem 1's λ for cycle `c`: sweeps
`c.tail` with helper `y`, ending on `firstYStep`. Has length
`c.tail.length + 1 = c.members.length`. -/
private def gyBlock (c : Cycle α) : List (Body α × Body α) :=
  sweepScript c.tail ++ [firstYStep c]

/-- The `G_1(x)` block of paper Theorem 1's λ for cycle `c`: the
helper-swap involution applied to `gyBlock c`. Same length as
`gyBlock c`. -/
private def gxBlock (c : Cycle α) : List (Body α × Body α) :=
  (gyBlock c).map swapHelpersStep

/-- The "lead" block of paper Theorem 1's λ for the head cycle: the
`(a_1 x)` opening transposition, then the full `gyBlock c`, then the
`(a_k x)` closing transposition. Has length `c.members.length + 2`. -/
private def leadBlock (c : Cycle α) : List (Body α × Body α) :=
  (Body.x, Body.orig c.first) :: gyBlock c ++ [(Body.x, Body.orig c.second)]

/-- The core of paper Theorem 1's optimal product λ on a cycle list,
without the trailing helper-swap. For `c :: cs`: prepend the tail
cycles' `firstYStep`s, then `leadBlock c`, then concatenate the
tail's `gxBlock`s. Has length `n + r + 1` where `n` is the total
cycle support and `r` is the number of cycles. -/
private def coreOptimalScript : List (Cycle α) → List (Body α × Body α)
  | [] => []
  | c :: cs =>
      cs.reverse.map firstYStep ++ leadBlock c ++ cs.flatMap gxBlock

/-- The executable list form of paper Theorem 1's optimal product
`λ`: `coreOptimalScript` followed by the trailing helper-swap
`(x, y)`. Has length `n + r + 2` for any non-empty cycle list (with
`n = total support`, `r = number of cycles`). -/
def optimalScript : List (Cycle α) → List (Body α × Body α)
  | [] => []
  | c :: cs => coreOptimalScript (c :: cs) ++ [(Body.x, Body.y)]

omit [DecidableEq α] [Fintype α] in
@[simp] theorem firstYStep_fst (c : Cycle α) :
    (firstYStep c).1 = Body.y := rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem firstYStep_snd (c : Cycle α) :
    (firstYStep c).2 = Body.orig c.first := rfl

omit [DecidableEq α] [Fintype α] in
private theorem gyBlock_eq_map_swapY (c : Cycle α) :
    gyBlock c = (c.tail ++ [c.first]).map (fun a => (Body.y, Body.orig a)) := by
  simp [gyBlock, firstYStep, sweepScript, List.map_append]

omit [Fintype α] in
private theorem gxBlock_eq_map_swapX (c : Cycle α) :
    gxBlock c = (c.tail ++ [c.first]).map (fun a => (Body.x, Body.orig a)) := by
  rw [gxBlock, gyBlock_eq_map_swapY]
  induction (c.tail ++ [c.first]) with
  | nil =>
      simp
  | cons a l ih =>
      simp [swapHelpersStep, helperSwap, swap_apply_of_ne_of_ne, ih]

omit [DecidableEq α] [Fintype α] in
@[simp] private theorem gyBlock_length (c : Cycle α) :
    (gyBlock c).length = c.members.length := by
  simp [gyBlock, firstYStep, Cycle.members, Cycle.tail]

omit [Fintype α] in
@[simp] private theorem gxBlock_length (c : Cycle α) :
    (gxBlock c).length = c.members.length := by
  rw [gxBlock_eq_map_swapX]
  simp [Cycle.members, Cycle.tail]

omit [DecidableEq α] [Fintype α] in
@[simp] private theorem leadBlock_length (c : Cycle α) :
    (leadBlock c).length = c.members.length + 2 := by
  simp [leadBlock, Cycle.members]

omit [Fintype α] in
@[simp] theorem optimalScript_nil :
    optimalScript ([] : List (Cycle α)) = [] := rfl

omit [Fintype α] in
@[simp] theorem optimalScript_cons (c : Cycle α) (cs : List (Cycle α)) :
    optimalScript (c :: cs) = coreOptimalScript (c :: cs) ++ [(Body.x, Body.y)] := rfl

omit [Fintype α] in
private theorem coreOptimalScript_snoc (c : Cycle α) (cs : List (Cycle α)) (d : Cycle α) :
    coreOptimalScript ((c :: cs) ++ [d]) =
      [firstYStep d] ++ coreOptimalScript (c :: cs) ++ gxBlock d := by
  simp [coreOptimalScript, List.reverse_cons, List.flatMap_append, List.append_assoc]

omit [Fintype α] in
private theorem cycleProduct_append (cs ds : List (Cycle α)) :
    cycleProduct (cs ++ ds) = cycleProduct cs * cycleProduct ds := by
  induction cs with
  | nil =>
      simp [cycleProduct]
  | cons c cs ih =>
      simp [cycleProduct, ih, mul_assoc]

omit [Fintype α] in
private theorem cyclePerm_orig_ne_x (c : Cycle α) (a : α) :
    cyclePerm c (Body.orig a) ≠ Body.x := by
  rw [cyclePerm_eq_liftPerm_membersReverseFormPerm, liftPerm_apply_orig]
  simp

omit [Fintype α] in
private theorem cyclePerm_orig_ne_y (c : Cycle α) (a : α) :
    cyclePerm c (Body.orig a) ≠ Body.y := by
  rw [cyclePerm_eq_liftPerm_membersReverseFormPerm, liftPerm_apply_orig]
  simp

omit [Fintype α] in
private theorem cyclePerm_apply_orig_second (c : Cycle α) :
    cyclePerm c (Body.orig c.second) = Body.orig c.first := by
  simpa [cyclePerm, Cycle.tail] using
    cyclePermAux_head c.first c.second c.rest c.first_ne_second c.not_mem_rest_first

omit [Fintype α] in
private theorem cyclePerm_orig_ne_first_of_ne_second
    (c : Cycle α) {a : α} (ha : a ≠ c.second) :
    cyclePerm c (Body.orig a) ≠ Body.orig c.first := by
  intro hEq
  have hsecond : cyclePerm c (Body.orig c.second) = Body.orig c.first :=
    cyclePerm_apply_orig_second c
  have hsame := (cyclePerm c).injective (hEq.trans hsecond.symm)
  exact ha (by simpa using hsame)

omit [Fintype α] in
private theorem runScript_sweep_tail_cycleFirst (c : Cycle α) :
    runScript (sweepScript c.tail) (cyclePerm c (Body.orig c.first)) = Body.y := by
  simpa [cyclePerm, Cycle.tail, runScript_cons, mul_apply, cyclePermAux_first_step] using
    runScript_sweep_cycle_head c.second c.rest c.nodup_tail

omit [Fintype α] in
private theorem runScript_sweep_tail_cycleRest (c : Cycle α) {a : α} (ha : a ∈ c.rest) :
    runScript (sweepScript c.tail) (cyclePerm c (Body.orig a)) = Body.orig a := by
  have hfirst : a ≠ c.first := by
    intro hEq
    subst a
    exact c.not_mem_rest_first ha
  have hsecond : a ≠ c.second := by
    intro hEq
    subst a
    exact c.not_mem_rest_second ha
  simpa [cyclePerm, Cycle.tail, runScript_cons, mul_apply, hfirst, hsecond] using
    runScript_sweep_cycle_rest (head := c.second) (a := a) (rest := c.rest) c.nodup_tail ha

omit [Fintype α] in
private theorem runScript_gyBlock_mul_swapY_mul_cyclePerm_apply
    (c : Cycle α) (z : Body α) :
    (runScript (gyBlock c) * swapY c.first * cyclePerm c) z =
      swap Body.y (Body.orig c.first)
        (runScript (sweepScript c.tail)
          (swap Body.y (Body.orig c.first) (cyclePerm c z))) := by
  simp [gyBlock, firstYStep, runScript_append, runScript_cons, mul_apply, swapY]

private theorem runScript_gyBlock_mul_swapY_mul_cyclePerm
    (c : Cycle α) :
    runScript (gyBlock c) * swapY c.first * cyclePerm c = 1 := by
  ext z
  cases z with
  | x =>
      simp [gyBlock, runScript_append_apply, firstYStep, swapY, Cycle.tail,
        swap_apply_of_ne_of_ne, cyclePerm_fix_x]
  | y =>
      have hinner :
          runScript (sweepScript c.tail) (swapY c.first (cyclePerm c Body.y)) = Body.orig c.first := by
        simpa [cyclePerm_fix_y, swapY, Cycle.tail, c.first_ne_second, c.not_mem_rest_first] using
          (runScript_sweep_orig_of_not_mem (tail := c.tail) (a := c.first)
            (by simp [Cycle.tail, c.first_ne_second, c.not_mem_rest_first]))
      rw [mul_apply, mul_apply, gyBlock, runScript_append_apply, hinner]
      simp [firstYStep]
  | orig a =>
      by_cases hfirst : a = c.first
      · subst hfirst
        have hfix :
            cyclePermAux c.second c.rest (Body.orig c.first) = Body.orig c.first := by
          exact cyclePermAux_orig_of_not_mem (first := c.second) (tail := c.rest) (a := c.first)
            (by simp [c.first_ne_second, c.not_mem_rest_first])
        have hneqfirst :
            cyclePerm c (Body.orig c.first) ≠ Body.orig c.first := by
          intro hEq
          have hsame := (cyclePermAux c.second c.rest).injective (hEq.trans hfix.symm)
          have hs : c.second = c.first := by
            simpa [cyclePerm, Cycle.tail, cyclePermAux_first_step] using hsame
          exact c.first_ne_second hs.symm
        have hneqy :
            cyclePerm c (Body.orig c.first) ≠ Body.y := by
          exact cyclePerm_orig_ne_y c c.first
        have hinner :
            runScript (sweepScript c.tail)
              (swapY c.first (cyclePerm c (Body.orig c.first))) = Body.y := by
          have hfixY :
              swapY c.first (cyclePerm c (Body.orig c.first)) = cyclePerm c (Body.orig c.first) := by
            exact swap_apply_of_ne_of_ne hneqy hneqfirst
          simpa [hfixY] using runScript_sweep_tail_cycleFirst c
        rw [mul_apply, mul_apply, gyBlock, runScript_append_apply, hinner]
        simp [firstYStep]
      · by_cases hsecond : a = c.second
        · subst hsecond
          have hinner :
              runScript (sweepScript c.tail)
                (swapY c.first (cyclePerm c (Body.orig c.second))) = Body.orig c.second := by
            simpa [cyclePerm_apply_orig_second c, swapY] using runScript_sweep_y c.nodup_tail
          rw [mul_apply, mul_apply, gyBlock, runScript_append_apply, hinner]
          exact swap_apply_of_ne_of_ne (by simp) (by
            intro h
            have hs : c.second = c.first := Body.orig.inj h
            exact c.first_ne_second hs.symm)
        · by_cases hmem : a ∈ c.rest
          · have hneqfirst :
                cyclePerm c (Body.orig a) ≠ Body.orig c.first := by
              exact cyclePerm_orig_ne_first_of_ne_second c hsecond
            have hneqy :
                cyclePerm c (Body.orig a) ≠ Body.y := by
              exact cyclePerm_orig_ne_y c a
            have hinner :
                runScript (sweepScript c.tail)
                  (swapY c.first (cyclePerm c (Body.orig a))) = Body.orig a := by
              have hfixY :
                  swapY c.first (cyclePerm c (Body.orig a)) = cyclePerm c (Body.orig a) := by
                exact swap_apply_of_ne_of_ne hneqy hneqfirst
              simpa [hfixY] using runScript_sweep_tail_cycleRest c hmem
            rw [mul_apply, mul_apply, gyBlock, runScript_append_apply, hinner]
            exact swap_apply_of_ne_of_ne (by simp) (by simpa using hfirst)
          ·
            have hcyc : cyclePerm c (Body.orig a) = Body.orig a := by
              simpa [cyclePerm, Cycle.tail] using
                cyclePermAux_orig_of_not_mem (first := c.first) (tail := c.second :: c.rest)
                  (a := a) (by simp [hfirst, hsecond, hmem])
            have hfixY :
                swap Body.y (Body.orig c.first) (Body.orig a) = Body.orig a := by
              exact swap_apply_of_ne_of_ne (by simp) (by simpa using hfirst)
            have hinner :
                runScript (sweepScript c.tail)
                  (swapY c.first (cyclePerm c (Body.orig a))) = Body.orig a := by
              have hfixY' : swapY c.first (cyclePerm c (Body.orig a)) = Body.orig a := by
                simpa [hcyc] using hfixY
              simpa [hfixY'] using
                (runScript_sweep_orig_of_not_mem (tail := c.tail) (a := a)
                  (by simp [Cycle.tail, hsecond, hmem]))
            rw [mul_apply, mul_apply, gyBlock, runScript_append_apply, hinner]
            exact swap_apply_of_ne_of_ne (by simp) (by simpa using hfirst)

private theorem gxBlock_mul_helperSwap_mul_swapY_mul_cyclePerm
    (c : Cycle α) :
    runScript (gxBlock c) * helperSwap * swapY c.first * cyclePerm c = helperSwap := by
  rw [gxBlock, runScript_map_swapHelpersStep]
  calc
    helperSwap * runScript (gyBlock c) * helperSwap * helperSwap * swapY c.first * cyclePerm c
        = helperSwap * (runScript (gyBlock c) * swapY c.first * cyclePerm c) := by
            simp [mul_assoc, helperSwap_mul_self]
    _ = helperSwap := by simp [runScript_gyBlock_mul_swapY_mul_cyclePerm]

omit [Fintype α] in
private theorem leadBlock_mul_cyclePerm_apply (c : Cycle α) (z : Body α) :
    (runScript (leadBlock c) * cyclePerm c) z =
      swap Body.x (Body.orig c.second)
        (swap Body.y (Body.orig c.first)
          (runScript (sweepScript c.tail)
            (swap Body.x (Body.orig c.first) (cyclePerm c z)))) := by
  simp [leadBlock, gyBlock, firstYStep, runScript_append, runScript_cons, mul_apply]

private theorem leadBlock_mul_cyclePerm (c : Cycle α) :
    runScript (leadBlock c) * cyclePerm c = helperSwap := by
  have hgy : ∀ z : Body α, runScript (gyBlock c) (swapY c.first (cyclePerm c z)) = z := by
    intro z
    have hz := congrArg (fun π : Perm (Body α) => π z) (runScript_gyBlock_mul_swapY_mul_cyclePerm c)
    simpa [mul_apply] using hz
  ext z
  cases z with
  | x =>
      have hmid :
          runScript ((Body.x, Body.orig c.first) :: gyBlock c) Body.x = Body.y := by
        simpa [runScript_cons, mul_apply, swapX, cyclePerm_fix_y, swapY] using hgy Body.y
      rw [mul_apply, leadBlock, runScript_append_apply, cyclePerm_fix_x, hmid]
      exact swap_apply_of_ne_of_ne (by simp) (by simp)
  | y =>
      have hmid :
          runScript ((Body.x, Body.orig c.first) :: gyBlock c) Body.y = Body.orig c.second := by
        simpa [runScript_cons, mul_apply, swapX, cyclePerm_apply_orig_second c, swapY] using
          hgy (Body.orig c.second)
      rw [mul_apply, leadBlock, runScript_append_apply, cyclePerm_fix_y, hmid]
      simp [helperSwap]
  | orig a =>
      by_cases hfirst : a = c.first
      · subst hfirst
        have hfix :
            cyclePermAux c.second c.rest (Body.orig c.first) = Body.orig c.first := by
          exact cyclePermAux_orig_of_not_mem (first := c.second) (tail := c.rest) (a := c.first)
            (by simp [c.first_ne_second, c.not_mem_rest_first])
        have hneqfirst :
            cyclePerm c (Body.orig c.first) ≠ Body.orig c.first := by
          intro hEq
          have hsame := (cyclePermAux c.second c.rest).injective (hEq.trans hfix.symm)
          have hs : c.second = c.first := by
            simpa [cyclePerm, Cycle.tail, cyclePermAux_first_step] using hsame
          exact c.first_ne_second hs.symm
        have hneqx :
            cyclePerm c (Body.orig c.first) ≠ Body.x := by
          exact cyclePerm_orig_ne_x c c.first
        have hneqy :
            cyclePerm c (Body.orig c.first) ≠ Body.y := by
          exact cyclePerm_orig_ne_y c c.first
        have hmid :
            runScript ((Body.x, Body.orig c.first) :: gyBlock c)
              (cyclePerm c (Body.orig c.first)) = Body.orig c.first := by
          rw [runScript_cons, mul_apply]
          have hfixX :
              swap Body.x (Body.orig c.first) (cyclePerm c (Body.orig c.first)) =
                cyclePerm c (Body.orig c.first) := by
            exact swap_apply_of_ne_of_ne hneqx hneqfirst
          have hfixY :
              swap Body.y (Body.orig c.first) (cyclePerm c (Body.orig c.first)) =
                cyclePerm c (Body.orig c.first) := by
            exact swap_apply_of_ne_of_ne hneqy hneqfirst
          rw [hfixX]
          simpa [swapY, hfixY] using hgy (Body.orig c.first)
        rw [mul_apply, leadBlock, runScript_append_apply, hmid]
        exact swap_apply_of_ne_of_ne (by simp) (by
          intro h
          exact c.first_ne_second (Body.orig.inj h))
      · by_cases hsecond : a = c.second
        · subst hsecond
          have hmid :
              runScript ((Body.x, Body.orig c.first) :: gyBlock c) (Body.orig c.first) = Body.x := by
            simpa [runScript_cons, mul_apply, swapX, cyclePerm_fix_x, swapY] using hgy Body.x
          rw [mul_apply, leadBlock, runScript_append_apply, cyclePerm_apply_orig_second c, hmid]
          rfl
        · by_cases hmem : a ∈ c.rest
          · have hneqfirst :
                cyclePerm c (Body.orig a) ≠ Body.orig c.first := by
              exact cyclePerm_orig_ne_first_of_ne_second c hsecond
            have hneqx :
                cyclePerm c (Body.orig a) ≠ Body.x := by
              exact cyclePerm_orig_ne_x c a
            have hneqy :
                cyclePerm c (Body.orig a) ≠ Body.y := by
              exact cyclePerm_orig_ne_y c a
            have hmid :
                runScript ((Body.x, Body.orig c.first) :: gyBlock c)
                  (cyclePerm c (Body.orig a)) = Body.orig a := by
              rw [runScript_cons, mul_apply]
              have hfixX :
                  swap Body.x (Body.orig c.first) (cyclePerm c (Body.orig a)) =
                    cyclePerm c (Body.orig a) := by
                exact swap_apply_of_ne_of_ne hneqx hneqfirst
              have hfixY :
                  swap Body.y (Body.orig c.first) (cyclePerm c (Body.orig a)) =
                    cyclePerm c (Body.orig a) := by
                exact swap_apply_of_ne_of_ne hneqy hneqfirst
              rw [hfixX]
              simpa [swapY, hfixY] using hgy (Body.orig a)
            rw [mul_apply, leadBlock, runScript_append_apply, hmid]
            exact swap_apply_of_ne_of_ne (by simp) (by simpa using hsecond)
          · have hcyc : cyclePerm c (Body.orig a) = Body.orig a := by
              simpa [cyclePerm, Cycle.tail] using
                cyclePermAux_orig_of_not_mem (first := c.first) (tail := c.second :: c.rest)
                  (a := a) (by simp [hfirst, hsecond, hmem])
            have hmid :
                runScript ((Body.x, Body.orig c.first) :: gyBlock c) (Body.orig a) = Body.orig a := by
              rw [runScript_cons, mul_apply]
              have hfixX :
                  swap Body.x (Body.orig c.first) (Body.orig a) = Body.orig a := by
                exact swap_apply_of_ne_of_ne (by simp) (by simpa using hfirst)
              have hfixY :
                  swap Body.y (Body.orig c.first) (Body.orig a) = Body.orig a := by
                exact swap_apply_of_ne_of_ne (by simp) (by simpa using hfirst)
              rw [hfixX]
              simpa [hcyc, swapY, hfixY] using hgy (Body.orig a)
            rw [mul_apply, leadBlock, runScript_append_apply, hcyc, hmid]
            exact swap_apply_of_ne_of_ne (by simp) (by simpa using hsecond)

private theorem swapY_disjoint_cycleProduct_of_not_mem
    (cs : List (Cycle α)) (a : α)
    (ha : ∀ c ∈ cs, a ∉ c.members) :
    Equiv.Perm.Disjoint (swapY a) (cycleProduct cs) := by
  intro z
  cases z with
  | x =>
      exact Or.inr (cycleProduct_fix_x cs)
  | y =>
      exact Or.inr (cycleProduct_apply_y cs)
  | orig b =>
      by_cases hba : b = a
      · subst hba
        exact Or.inr (cycleProduct_fix_of_not_mem cs ha)
      · exact Or.inl (by simp [swapY, hba, swap_apply_of_ne_of_ne])

private theorem swapY_commute_cycleProduct_of_not_mem
    (cs : List (Cycle α)) (a : α)
    (ha : ∀ c ∈ cs, a ∉ c.members) :
    Commute (swapY a) (cycleProduct cs) :=
  (swapY_disjoint_cycleProduct_of_not_mem cs a ha).commute

private theorem coreOptimalScript_mul_cycleProduct
    (c : Cycle α) (cs : List (Cycle α))
    (hcs : (c :: cs).Pairwise Cycle.Disjoint) :
    runScript (coreOptimalScript (c :: cs)) * cycleProduct (c :: cs) = helperSwap := by
  induction cs using List.reverseRecOn with
  | nil =>
      simp [coreOptimalScript, leadBlock_mul_cyclePerm]
  | @append_singleton cs d ih =>
      have hpair_append : (c :: cs ++ [d]).Pairwise Cycle.Disjoint := hcs
      have hsplit := List.pairwise_append.1 hpair_append
      have hprev : (c :: cs).Pairwise Cycle.Disjoint := hsplit.1
      have hd_prev : ∀ e ∈ (c :: cs), Cycle.Disjoint e d := by
        intro e he
        exact hsplit.2.2 e he d (by simp)
      have hshape : c :: (cs ++ [d]) = (c :: cs) ++ [d] := by simp
      rw [hshape, coreOptimalScript_snoc, runScript_append, runScript_append, cycleProduct_append]
      simp only [cycleProduct]
      calc
        runScript (gxBlock d) *
            (runScript (coreOptimalScript (c :: cs)) * swapY d.first) *
            (cycleProduct (c :: cs) * cyclePerm d)
            = runScript (gxBlock d) * runScript (coreOptimalScript (c :: cs)) *
                swapY d.first * cycleProduct (c :: cs) * cyclePerm d := by
                  simp [mul_assoc]
        _ = runScript (gxBlock d) * runScript (coreOptimalScript (c :: cs)) *
              (cycleProduct (c :: cs) * swapY d.first) * cyclePerm d := by
                have hcomm := (swapY_commute_cycleProduct_of_not_mem (c :: cs) d.first (by
                  intro e he hem
                  exact hd_prev e he hem (by simp [Cycle.members]))).eq
                calc
                  runScript (gxBlock d) * runScript (coreOptimalScript (c :: cs)) *
                      swapY d.first * cycleProduct (c :: cs) * cyclePerm d
                      =
                      runScript (gxBlock d) * runScript (coreOptimalScript (c :: cs)) *
                        (swapY d.first * cycleProduct (c :: cs)) * cyclePerm d := by
                          simp [mul_assoc]
                  _ =
                      runScript (gxBlock d) * runScript (coreOptimalScript (c :: cs)) *
                        (cycleProduct (c :: cs) * swapY d.first) * cyclePerm d := by
                          rw [hcomm]
        _ = runScript (gxBlock d) *
              (runScript (coreOptimalScript (c :: cs)) * cycleProduct (c :: cs)) *
              swapY d.first * cyclePerm d := by
                simp [mul_assoc]
        _ = runScript (gxBlock d) * helperSwap * swapY d.first * cyclePerm d := by
              rw [ih hprev]
        _ = helperSwap := gxBlock_mul_helperSwap_mul_swapY_mul_cyclePerm d

theorem optimalScript_correct
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint)
    (hcs_nonempty : cs ≠ []) :
    runScript (optimalScript cs) * cycleProduct cs = 1 := by
  rcases List.exists_cons_of_ne_nil hcs_nonempty with ⟨c, cs', rfl⟩
  rw [optimalScript_cons, runScript_append, runScript_cons]
  calc
    (helperSwap * runScript (coreOptimalScript (c :: cs'))) * cycleProduct (c :: cs')
        = helperSwap * (runScript (coreOptimalScript (c :: cs')) * cycleProduct (c :: cs')) := by
            simp [mul_assoc]
    _ = helperSwap * helperSwap := by rw [coreOptimalScript_mul_cycleProduct c cs' hcs]
    _ = 1 := by simp [helperSwap_mul_self]

set_option linter.unusedSectionVars false in
@[simp] theorem optimalScript_length_cons (c : Cycle α) (cs : List (Cycle α)) :
    (optimalScript (c :: cs)).length =
      ((c :: cs).map fun d => d.members.length).sum + (c :: cs).length + 2 := by
  simp [optimalScript, coreOptimalScript, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  omega

theorem optimalScript_length
    (cs : List (Cycle α))
    (hcs_nonempty : cs ≠ []) :
    (optimalScript cs).length =
      (cs.map fun c => c.members.length).sum + cs.length + 2 := by
  rcases List.exists_cons_of_ne_nil hcs_nonempty with ⟨c, cs', rfl⟩
  simpa using optimalScript_length_cons c cs'

omit [DecidableEq α] [Fintype α] in
private theorem mem_gyBlock_iff {c : Cycle α} {step : Body α × Body α} :
    step ∈ gyBlock c ↔ ∃ a ∈ c.members, step = (Body.y, Body.orig a) := by
  rw [gyBlock_eq_map_swapY, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    simp [Cycle.members, Cycle.tail] at ha ⊢
    tauto
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    simp [Cycle.members, Cycle.tail] at ha ⊢
    tauto

omit [Fintype α] in
private theorem mem_gxBlock_iff {c : Cycle α} {step : Body α × Body α} :
    step ∈ gxBlock c ↔ ∃ a ∈ c.members, step = (Body.x, Body.orig a) := by
  rw [gxBlock_eq_map_swapX, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    simpa [Cycle.members, Cycle.tail, List.mem_append, or_assoc, or_left_comm, or_comm] using ha
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    simpa [Cycle.members, Cycle.tail, List.mem_append, or_assoc, or_left_comm, or_comm] using ha

omit [DecidableEq α] [Fintype α] in
private theorem mem_leadBlock_iff {c : Cycle α} {step : Body α × Body α} :
    step ∈ leadBlock c ↔
      step = (Body.x, Body.orig c.first) ∨
      step = (Body.x, Body.orig c.second) ∨
      ∃ a ∈ c.members, step = (Body.y, Body.orig a) := by
  simp [leadBlock, mem_gyBlock_iff, or_comm]

omit [Fintype α] in
private theorem mem_coreOptimalScript_iff
    {c : Cycle α} {cs : List (Cycle α)} {step : Body α × Body α} :
    step ∈ coreOptimalScript (c :: cs) ↔
      (∃ d ∈ cs, firstYStep d = step) ∨
      step ∈ leadBlock c ∨
      (∃ d ∈ cs, step ∈ gxBlock d) := by
  simp [coreOptimalScript, List.mem_flatMap, or_left_comm]

omit [DecidableEq α] [Fintype α] in
private theorem mem_firstYStep_canonical {c : Cycle α} {step : Body α × Body α}
    (h : step = firstYStep c) : CanonicalStep step := by
  subst h
  exact Or.inr <| Or.inl ⟨c.first, rfl⟩

omit [DecidableEq α] [Fintype α] in
private theorem mem_gyBlock_canonical {c : Cycle α} {step : Body α × Body α}
    (h : step ∈ gyBlock c) : CanonicalStep step := by
  rcases (mem_gyBlock_iff).1 h with ⟨a, _, rfl⟩
  exact Or.inr <| Or.inl ⟨a, rfl⟩

omit [Fintype α] in
private theorem mem_gxBlock_canonical {c : Cycle α} {step : Body α × Body α}
    (h : step ∈ gxBlock c) : CanonicalStep step := by
  rcases (mem_gxBlock_iff).1 h with ⟨a, _, rfl⟩
  exact Or.inl ⟨a, rfl⟩

omit [DecidableEq α] [Fintype α] in
private theorem mem_leadBlock_canonical {c : Cycle α} {step : Body α × Body α}
    (h : step ∈ leadBlock c) : CanonicalStep step := by
  rcases (mem_leadBlock_iff).1 h with rfl | rfl | ⟨a, _, rfl⟩
  · exact Or.inl ⟨c.first, rfl⟩
  · exact Or.inl ⟨c.second, rfl⟩
  · exact Or.inr <| Or.inl ⟨a, rfl⟩

omit [Fintype α] in
private theorem mem_coreOptimalScript_canonical
    {c : Cycle α} {cs : List (Cycle α)} {step : Body α × Body α}
    (h : step ∈ coreOptimalScript (c :: cs)) : CanonicalStep step := by
  rcases (mem_coreOptimalScript_iff).1 h with h | h | h
  · rcases h with ⟨d, _, hEq⟩
    rw [← hEq]
    exact mem_firstYStep_canonical rfl
  · exact mem_leadBlock_canonical h
  · rcases h with ⟨d, _, hd⟩
    exact mem_gxBlock_canonical hd

set_option linter.unusedSectionVars false in
theorem mem_optimalScript_canonical {cs : List (Cycle α)} {step : Body α × Body α}
    (h : step ∈ optimalScript cs) : CanonicalStep step := by
  cases cs with
  | nil =>
      simp [optimalScript] at h
  | cons c cs =>
      rw [optimalScript_cons, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact mem_coreOptimalScript_canonical h
      · exact Or.inr <| Or.inr rfl

theorem optimalScript_usesHelper {cs : List (Cycle α)} {step : Body α × Body α}
    (h : step ∈ optimalScript cs) : UsesHelper step :=
  (mem_optimalScript_canonical h).usesHelper

theorem optimalScript_nontrivial {cs : List (Cycle α)} {step : Body α × Body α}
    (h : step ∈ optimalScript cs) : step.1 ≠ step.2 := by
  rcases mem_optimalScript_canonical h with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact Body.noConfusion
  · exact Body.noConfusion
  · exact Body.noConfusion

omit [DecidableEq α] [Fintype α] in
private theorem cycle_ne_of_disjoint {c d : Cycle α} (hcd : Cycle.Disjoint c d) : c ≠ d := by
  intro hEq
  subst d
  exact hcd (a := c.first) (by simp [Cycle.members]) (by simp [Cycle.members])

omit [DecidableEq α] [Fintype α] in
private theorem tail_append_first_nodup (c : Cycle α) :
    (c.tail ++ [c.first]).Nodup := by
  have hdisj : List.Disjoint c.tail [c.first] := by
    rw [List.disjoint_right]
    intro a hsingle hmem
    rcases List.mem_singleton.1 hsingle with rfl
    simp [Cycle.tail, c.first_ne_second, c.not_mem_rest_first] at hmem
  exact c.nodup_tail.append (by simp) hdisj

omit [DecidableEq α] [Fintype α] in
private theorem gyBlock_nodup (c : Cycle α) : (gyBlock c).Nodup := by
  let f : α → Body α × Body α := fun a => (Body.y, Body.orig a)
  have hinj : Function.Injective f := by
    intro a b hEq
    injection hEq with _ hOrig
    exact Body.orig.inj hOrig
  rw [gyBlock_eq_map_swapY]
  exact (tail_append_first_nodup c).map hinj

omit [Fintype α] in
private theorem gxBlock_nodup (c : Cycle α) : (gxBlock c).Nodup := by
  let f : α → Body α × Body α := fun a => (Body.x, Body.orig a)
  have hinj : Function.Injective f := by
    intro a b hEq
    injection hEq with _ hOrig
    exact Body.orig.inj hOrig
  rw [gxBlock_eq_map_swapX]
  exact (tail_append_first_nodup c).map hinj

omit [DecidableEq α] [Fintype α] in
private theorem leadBlock_nodup (c : Cycle α) : (leadBlock c).Nodup := by
  have hmid_disj : List.Disjoint (gyBlock c) [(Body.x, Body.orig c.second)] := by
    rw [List.disjoint_right]
    intro step hsingle hs
    rcases List.mem_singleton.1 hsingle with rfl
    rcases (mem_gyBlock_iff).1 hs with ⟨a, _, hstep⟩
    cases hstep
  have htail : (gyBlock c ++ [(Body.x, Body.orig c.second)]).Nodup := by
    exact (gyBlock_nodup c).append (by simp) hmid_disj
  refine List.Nodup.cons ?_ htail
  intro hmem
  have hmem' :
      (Body.x, Body.orig c.first) ∈ gyBlock c ∨
        (Body.x, Body.orig c.first) ∈ ([(Body.x, Body.orig c.second)] : List (Body α × Body α)) := by
    simpa [List.mem_append] using hmem
  rcases hmem' with hs | hs
  · rcases (mem_gyBlock_iff).1 hs with ⟨a, _, hstep⟩
    simp at hstep
  · have hs' : ((Body.x, Body.orig c.first) : Body α × Body α) =
      ((Body.x, Body.orig c.second) : Body α × Body α) := by
      have hs'' :
          (Body.x, Body.orig c.first) ∈
            ([(Body.x, Body.orig c.second)] : List (Body α × Body α)) := hs
      simpa using hs''
    have : c.first = c.second := by
      injection hs' with _ hOrig
      exact Body.orig.inj hOrig
    exact c.first_ne_second this

omit [Fintype α] in
private theorem gxBlock_disjoint_of_cycle_disjoint {c d : Cycle α}
    (hcd : Cycle.Disjoint c d) :
    List.Disjoint (gxBlock c) (gxBlock d) := by
  rw [List.disjoint_left]
  intro step hs hd
  rcases (mem_gxBlock_iff).1 hs with ⟨a, ha, rfl⟩
  rcases (mem_gxBlock_iff).1 hd with ⟨b, hb, hstep⟩
  injection hstep with _ hOrig
  exact hcd ha (Body.orig.inj hOrig ▸ hb)

omit [Fintype α] in
private theorem firstYStep_not_mem_gxBlock (c d : Cycle α) :
    firstYStep c ∉ gxBlock d := by
  intro h
  rcases (mem_gxBlock_iff).1 h with ⟨a, _, hstep⟩
  simp [firstYStep] at hstep

omit [DecidableEq α] [Fintype α] in
private theorem firstYStep_not_mem_leadBlock_of_disjoint {c d : Cycle α}
    (hcd : Cycle.Disjoint c d) :
    firstYStep d ∉ leadBlock c := by
  intro h
  rcases (mem_leadBlock_iff).1 h with h | h | h
  · simp [firstYStep] at h
  · simp [firstYStep] at h
  · rcases h with ⟨a, ha, hstep⟩
    injection hstep with _ hOrig
    exact hcd ha (Body.orig.inj hOrig ▸ by simp [Cycle.members])

omit [Fintype α] in
private theorem leadBlock_disjoint_of_gxBlock_of_cycle_disjoint {c d : Cycle α}
    (hcd : Cycle.Disjoint c d) :
    List.Disjoint (leadBlock c) (gxBlock d) := by
  rw [List.disjoint_left]
  intro step hs hd
  rcases (mem_leadBlock_iff).1 hs with hs | hs | hs
  · subst hs
    rcases (mem_gxBlock_iff).1 hd with ⟨a, ha, hstep⟩
    injection hstep with _ hOrig
    exact hcd (by simp [Cycle.members]) (Body.orig.inj hOrig ▸ ha)
  · subst hs
    rcases (mem_gxBlock_iff).1 hd with ⟨a, ha, hstep⟩
    injection hstep with _ hOrig
    exact hcd (by simp [Cycle.members]) (Body.orig.inj hOrig ▸ ha)
  · rcases hs with ⟨a, _, hstepY⟩
    rcases (mem_gxBlock_iff).1 hd with ⟨b, _, hstepX⟩
    rw [hstepY] at hstepX
    simp at hstepX

omit [DecidableEq α] [Fintype α] in
private theorem firstYSteps_nodup {cs : List (Cycle α)} (hcs : cs.Pairwise Cycle.Disjoint) :
    (cs.reverse.map firstYStep).Nodup := by
  have hsymm : Symmetric (fun a b : Cycle α => Cycle.Disjoint a b) := by
    intro a b h
    simpa [Cycle.Disjoint] using h.symm
  rw [List.map_reverse]
  apply List.nodup_reverse.2
  have hpair_ne : cs.Pairwise (fun d e : Cycle α => d ≠ e) := by
    exact hcs.imp fun {_ _} h => cycle_ne_of_disjoint h
  have hnd : cs.Nodup := by
    simpa [List.Nodup] using hpair_ne
  refine List.Nodup.map_on ?_ hnd
  intro d hd e he hEq
  by_cases hde : d = e
  · exact hde
  · have hdisj : Cycle.Disjoint d e := hcs.forall hsymm hd he hde
    have hfirst : d.first = e.first := by
      injection hEq with _ hOrig
      exact Body.orig.inj hOrig
    exfalso
    exact hdisj (a := d.first) (by simp [Cycle.members]) (by simp [hfirst, Cycle.members])

omit [Fintype α] in
private theorem gxBlocks_nodup {cs : List (Cycle α)} (hcs : cs.Pairwise Cycle.Disjoint) :
    (cs.flatMap gxBlock).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro c hc
    exact gxBlock_nodup c
  · exact hcs.imp fun {_ _} h => gxBlock_disjoint_of_cycle_disjoint h

omit [Fintype α] in
private theorem not_mem_coreOptimalScript_helperSwap
    {c : Cycle α} {cs : List (Cycle α)} :
    (Body.x, Body.y) ∉ coreOptimalScript (c :: cs) := by
  intro h
  rcases (mem_coreOptimalScript_iff).1 h with h | h | h
  · rcases h with ⟨d, _, hstep⟩
    simp [firstYStep] at hstep
  · rcases (mem_leadBlock_iff).1 h with hEq | hEq | ⟨a, _, hEq⟩
    · cases hEq
    · cases hEq
    · cases hEq
  · rcases h with ⟨d, _, hd⟩
    rcases (mem_gxBlock_iff).1 hd with ⟨a, _, hstep⟩
    simp at hstep

omit [Fintype α] in
private theorem coreOptimalScript_nodup
    (c : Cycle α) (cs : List (Cycle α))
    (hcs : (c :: cs).Pairwise Cycle.Disjoint) :
    (coreOptimalScript (c :: cs)).Nodup := by
  rw [coreOptimalScript]
  have hsplit := List.pairwise_cons.1 hcs
  have hy : (cs.reverse.map firstYStep).Nodup := firstYSteps_nodup hsplit.2
  have hlead : (leadBlock c).Nodup := leadBlock_nodup c
  have hgx : (cs.flatMap gxBlock).Nodup := gxBlocks_nodup hsplit.2
  have hy_lead : List.Disjoint (cs.reverse.map firstYStep) (leadBlock c) := by
    rw [List.disjoint_left]
    intro step hs hd
    rw [List.mem_map] at hs
    rcases hs with ⟨d, hd', rfl⟩
    exact firstYStep_not_mem_leadBlock_of_disjoint (hsplit.1 d (by simpa using hd')) hd
  have hy_gx : List.Disjoint (cs.reverse.map firstYStep) (cs.flatMap gxBlock) := by
    rw [List.disjoint_left]
    intro step hs hd
    rw [List.mem_map] at hs
    rcases hs with ⟨d, _, rfl⟩
    rcases List.mem_flatMap.1 hd with ⟨e, _, he⟩
    exact firstYStep_not_mem_gxBlock d e he
  have hlead_gx : List.Disjoint (leadBlock c) (cs.flatMap gxBlock) := by
    rw [List.disjoint_left]
    intro step hs hd
    rcases List.mem_flatMap.1 hd with ⟨d, hd', hdx⟩
    exact leadBlock_disjoint_of_gxBlock_of_cycle_disjoint (hsplit.1 d hd') hs hdx
  have hrest : (leadBlock c ++ cs.flatMap gxBlock).Nodup := by
    exact hlead.append hgx hlead_gx
  simpa [List.append_assoc] using hy.append hrest (by
    rw [List.disjoint_left]
    intro step hs hrest'
    simp only [List.mem_append] at hrest'
    exact hrest'.elim (fun h => hy_lead hs h) (fun h => hy_gx hs h))

set_option linter.unusedSectionVars false in
theorem optimalScript_nodup
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint) :
    (optimalScript cs).Nodup := by
  cases cs with
  | nil =>
      simp [optimalScript]
  | cons c cs =>
      rw [optimalScript_cons]
      exact (coreOptimalScript_nodup c cs hcs).append (by simp)
        (by
          rw [List.disjoint_right]
          intro step hmem hs
          have hstep : step = (Body.x, Body.y) := by simpa using hmem
          subst step
          exact not_mem_coreOptimalScript_helperSwap hs)

theorem optimalScript_stepPairs_nodup
    (cs : List (Cycle α))
    (hcs : cs.Pairwise Cycle.Disjoint) :
    ((optimalScript cs).map stepPair).Nodup := by
  refine List.Nodup.map_on ?_ (optimalScript_nodup cs hcs)
  intro step₁ h₁ step₂ h₂ hpair
  exact stepPair_injective_of_canonical
    (mem_optimalScript_canonical h₁) (mem_optimalScript_canonical h₂) hpair

/-- The optimized executable script for an arbitrary permutation. -/
noncomputable def optimalScriptOfPerm (σ : Perm α) : List (Body α × Body α) :=
  optimalScript (factorCycles σ)

/-- Correctness of the permutation-level optimal repair:
`optimalScriptOfPerm σ` undoes `liftPerm σ`. Routes through
`optimalScript_correct` on `factorCycles σ` via the
`cycleProduct (factorCycles σ) = liftPerm σ` bridge. -/
theorem optimalScriptOfPerm_correct
    (σ : Perm α)
    (hσ : 0 < σ.cycleFactorsFinset.card) :
    runScript (optimalScriptOfPerm σ) * liftPerm σ = 1 := by
  have hnonempty : factorCycles σ ≠ [] := by
    intro hnil
    have hlen : (factorCycles σ).length = 0 := by simp [hnil]
    rw [factorCycles_length] at hlen
    omega
  simpa [optimalScriptOfPerm, cycleProduct_factorCycles σ] using
    optimalScript_correct (cs := factorCycles σ) (factorCycles_pairwise_disjoint σ) hnonempty

/-- Exact length of the permutation-level optimal repair: it has
exactly `n + r + 2` factors, where `n = σ.support.card` is the
size of the moved-element set and `r = σ.cycleFactorsFinset.card`
is the number of non-trivial cycles. This is the upper-bound
half of paper Theorem 1's "best possible" claim. -/
theorem optimalScriptOfPerm_length
    (σ : Perm α)
    (hσ : 0 < σ.cycleFactorsFinset.card) :
    (optimalScriptOfPerm σ).length =
      σ.support.card + σ.cycleFactorsFinset.card + 2 := by
  have hnonempty : factorCycles σ ≠ [] := by
    intro hnil
    have hlen : (factorCycles σ).length = 0 := by simp [hnil]
    rw [factorCycles_length] at hlen
    omega
  calc
    (optimalScriptOfPerm σ).length
        = ((factorCycles σ).map fun c => c.members.length).sum + (factorCycles σ).length + 2 := by
            simpa [optimalScriptOfPerm] using optimalScript_length (cs := factorCycles σ) hnonempty
    _ = σ.support.card + σ.cycleFactorsFinset.card + 2 := by
          rw [factorCycles_membersLengthSum, factorCycles_length]

/-- Optimality of `optimalScriptOfPerm`: no `RepairSeq` for
`liftPerm σ` can be shorter than the explicit construction.
Combines the exact-length theorem with the universal lower
bound `futurama_optimal`. This is the lower-bound half of paper
Theorem 1's "best possible" claim, instantiated at the explicit
witness. -/
theorem optimalScriptOfPerm_isOptimal
    (σ : Perm α)
    (hσ : 0 < σ.cycleFactorsFinset.card)
    (seq : RepairSeq (liftPerm σ)) :
    (optimalScriptOfPerm σ).length ≤ seq.steps.length := by
  calc
    (optimalScriptOfPerm σ).length = σ.support.card + σ.cycleFactorsFinset.card + 2 :=
      optimalScriptOfPerm_length σ hσ
    _ ≤ seq.steps.length := futurama_optimal σ hσ seq

/-- Paper Theorem 1, three-conjunct form, on the **explicit witness**
`optimalScriptOfPerm σ`:

1. correctness — `runScript (optimalScriptOfPerm σ) * liftPerm σ = 1`;
2. exact length — `(optimalScriptOfPerm σ).length = n + r + 2`
   where `n = σ.support.card`, `r = σ.cycleFactorsFinset.card`;
3. best possible — every `RepairSeq` for `liftPerm σ` has length
   at least `(optimalScriptOfPerm σ).length`.

The `nontrivial`/`distinct_pairs`/`helper_constraint` machine-side
conjuncts of the paper statement are carried by the companion
witness `optimalRepairSeqOfPerm`; together the two declarations
cover paper Theorem 1's six conjuncts. See also `futuramaTheorem1Full`
for the equivalent single-declaration existence form. -/
theorem futuramaTheorem1OfPerm
    (σ : Perm α)
    (hσ : 0 < σ.cycleFactorsFinset.card) :
    runScript (optimalScriptOfPerm σ) * liftPerm σ = 1 ∧
      (optimalScriptOfPerm σ).length =
        σ.support.card + σ.cycleFactorsFinset.card + 2 ∧
      ∀ seq : RepairSeq (liftPerm σ),
        (optimalScriptOfPerm σ).length ≤ seq.steps.length := by
  refine ⟨optimalScriptOfPerm_correct σ hσ, optimalScriptOfPerm_length σ hσ, ?_⟩
  intro seq
  exact optimalScriptOfPerm_isOptimal σ hσ seq

/-- Bundled `RepairSeq` witness built from `optimalScriptOfPerm σ`.

Carries the paper Theorem 1 machine-side conjuncts (helper inclusion,
nontriviality, distinct unordered pairs, correctness) as the four
proof-carrying fields of `RepairSeq`. Together with
`futuramaTheorem1OfPerm`'s exact-length + universal lower-bound
conjuncts, this `def` provides the explicit existence witness for
paper Theorem 1.

Noncomputable because `optimalScriptOfPerm` routes through
`factorCycles` (noncomputable due to its dependence on
`Finset.toList`). -/
noncomputable def optimalRepairSeqOfPerm
    (σ : Perm α) (hσ : 0 < σ.cycleFactorsFinset.card) : RepairSeq (liftPerm σ) where
  steps := optimalScriptOfPerm σ
  helper_constraint := by
    intro step hstep
    exact optimalScript_usesHelper hstep
  nontrivial := by
    intro step hstep
    exact optimalScript_nontrivial hstep
  distinct_pairs := by
    simpa [optimalScriptOfPerm] using
      optimalScript_stepPairs_nodup (cs := factorCycles σ) (factorCycles_pairwise_disjoint σ)
  undoes := optimalScriptOfPerm_correct σ hσ

/-- Paper Theorem 1's full claim, packaged as a single declaration.

    The existence body bundles all six conjuncts of paper Theorem 1
    into one statement:

    1. there exists a `RepairSeq` (which by structure-field carries
       correctness `λ P = I`, helper inclusion, nontriviality of every
       step, and distinct unordered pairs);
    2. that `RepairSeq`'s length is exactly `n + r + 2`;
    3. its length is `≤` every other `RepairSeq` (best possible).

    This is the paper-equivalent **single-declaration** form of
    Theorem 1, complementing the explicit-witness pair
    (`futuramaTheorem1OfPerm` + `optimalRepairSeqOfPerm`). The witness
    produced is `optimalRepairSeqOfPerm σ hσ`; the theorem is
    structurally trivial -- its role is to give an external citer
    one statement to reference for "paper Theorem 1 in Lean". -/
theorem futuramaTheorem1Full
    (σ : Perm α) (hσ : 0 < σ.cycleFactorsFinset.card) :
    ∃ seq : RepairSeq (liftPerm σ),
      seq.steps.length = σ.support.card + σ.cycleFactorsFinset.card + 2 ∧
      ∀ seq' : RepairSeq (liftPerm σ), seq.steps.length ≤ seq'.steps.length := by
  refine ⟨optimalRepairSeqOfPerm σ hσ, ?_, fun seq' => ?_⟩
  · simpa [optimalRepairSeqOfPerm] using optimalScriptOfPerm_length σ hσ
  · simpa [optimalRepairSeqOfPerm] using optimalScriptOfPerm_isOptimal σ hσ seq'

-- ═══════════════════════════════════════════════
-- Definitional-equality regression checks
--
-- The nine `example := rfl` lines below pin down the layered
-- definitional equalities of the paper-λ block hierarchy. Each
-- layer is `rfl`-true against the next; if a future edit breaks
-- any of them, the build fails immediately at the offending line.
--
-- These checks live INSIDE `section OptimalUpperBound` so they can
-- reference the private blocks `coreOptimalScript` / `firstYStep`
-- / `gyBlock` / `gxBlock` / `leadBlock`.
-- ═══════════════════════════════════════════════

/-- Pins down the outer `optimalScript` wrapper (cons branch). -/
example (c : Cycle α) :
    optimalScript [c] =
      coreOptimalScript [c] ++ [(Body.x, Body.y)] := rfl

/-- Pins down the multi-cycle wrapper shape of `coreOptimalScript`. -/
example (c : Cycle α) (cs : List (Cycle α)) :
    coreOptimalScript (c :: cs) =
      cs.reverse.map firstYStep ++ leadBlock c ++ cs.flatMap gxBlock := rfl

/-- Pins down the `leadBlock` paper-λ block structure (the
`(a_1 x) :: G_1(y) :: ... :: (a_k x)` skeleton). -/
example (c : Cycle α) :
    leadBlock c =
      (Body.x, Body.orig c.first) :: gyBlock c
        ++ [(Body.x, Body.orig c.second)] := rfl

/-- Pins down the `gyBlock` shape (the `G_1(y)` sweep + final
firstYStep). -/
example (c : Cycle α) :
    gyBlock c = sweepScript c.tail ++ [firstYStep c] := rfl

/-- Pins down the `firstYStep` shape (`(y, a_1)` in paper indexing). -/
example (c : Cycle α) :
    firstYStep c = (Body.y, Body.orig c.first) := rfl

/-- Pins down the `sweepScript` shape (the per-element `(y, a_i)` map).
`sweepScript` lives in `CoreCycle.lean`; this `rfl` confirms it is
the expected shape. -/
example (tail : List α) :
    sweepScript tail = tail.map (fun a => (Body.y, Body.orig a)) := rfl

/-- Pins down the `gxBlock` shape (helper-swap involution applied to
`gyBlock`). -/
example (c : Cycle α) :
    gxBlock c = (gyBlock c).map swapHelpersStep := rfl

/-- Pins down `optimalScriptOfPerm` as the `Perm α`-level
specialisation of `optimalScript ∘ factorCycles`. -/
example (σ : Perm α) :
    optimalScriptOfPerm σ = optimalScript (factorCycles σ) := rfl

/-- Pins down the `coreOptimalScript` nil branch explicitly (the cons
branch is pinned by the multi-cycle equality above). -/
example : coreOptimalScript ([] : List (Cycle α)) = [] := rfl

end OptimalUpperBound

end Futurama
end Project
