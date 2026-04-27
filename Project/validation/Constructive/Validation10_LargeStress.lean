import Project.Futurama
import Project.Futurama.Optimality

/-!
# Validation 10 — Large-cycle deterministic stress

This file extends the deterministic validation suite beyond the
exhaustive `Fin 4` ground covered by V5/V6 in two directions:

## What this file adds

1. **Single-cycle stress at k = 5, 10, 20.** The kernel theorems
   (`optimalScript_correct`, `optimalScript_length`,
   `runScript_undoScript_mul_cycleProduct`) are universally quantified
   over `α`, so these examples are not new mathematical facts; they
   verify the formal statements *instantiate cleanly* on inputs much
   larger than the brute-force corpora can reach (V7 maxes out at
   `Fin 4`). Length checks are by closed-form `optimalScript_length`
   plus `decide` on the resulting `Nat` formula; correctness checks
   are direct applications of the kernel theorem.

2. **Multi-cycle medium-size stress.** Three disjoint 4-cycles on
   `Fin 12` complement V6's hardcoded examples on `Fin 6` (which max
   out at three 2-cycles). This pushes the cycle count beyond V6
   while keeping the total support reasonable.

A randomised companion using Mathlib's `plausible` tactic lives in the
sibling **optional** file
[`Validation11_PlausibleStress.lean`](Validation11_PlausibleStress.lean);
it is not imported by the constructive aggregate so that the default
build path stays `sorry`-clean (the `plausible` tactic in
Mathlib v4.23.0 closes a passing randomised goal with `sorry`).

## Status

`Validation10_LargeStress` is **gating** — it is imported by
`Project.validation.Constructive` and built by `lake build Project`.
Every check reduces to a kernel theorem or to closed-form `Nat`
arithmetic; no `sorry` is introduced.

## Build target

```
lake build Project.validation.Constructive.Validation10_LargeStress
```

## Axiom impact

The length and correctness `example`s use `decide` and the kernel
endpoints, so they remain on the Class I axioms
`{propext, Classical.choice, Quot.sound}`. No Class II axioms are
introduced by this file.
-/

namespace Project
namespace Futurama
namespace Validation10

/-! ## Section 1: Single-cycle stress at `k = 5, 10, 20`

Each example pair (length + correctness) follows the same pattern: the
length is the closed-form `n + r + 2 = k + 1 + 2 = k + 3`, and the
correctness is a direct application of `optimalScript_correct` to a
single-cycle list. -/

/-- The canonical 5-cycle `(0 1 2 3 4)` on `Fin 5`. -/
def cycle5 : Cycle (Fin 5) := ⟨0, 1, [2, 3, 4], by decide⟩

/-- The canonical 10-cycle on `Fin 10`. -/
def cycle10 : Cycle (Fin 10) :=
  ⟨0, 1, [2, 3, 4, 5, 6, 7, 8, 9], by decide⟩

/-- The canonical 20-cycle on `Fin 20`. -/
def cycle20 : Cycle (Fin 20) :=
  ⟨0, 1, [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
   by decide⟩

-- Length tests: `(optimalScript [c]).length = k + 3` (i.e. `n + r + 2`).

example : (optimalScript [cycle5]).length = 5 + 3 := by
  rw [optimalScript_length [cycle5] (List.cons_ne_nil _ _)]
  decide

example : (optimalScript [cycle10]).length = 10 + 3 := by
  rw [optimalScript_length [cycle10] (List.cons_ne_nil _ _)]
  decide

example : (optimalScript [cycle20]).length = 20 + 3 := by
  rw [optimalScript_length [cycle20] (List.cons_ne_nil _ _)]
  decide

-- Correctness tests: direct application of the kernel theorem.

example : runScript (optimalScript [cycle5]) * cycleProduct [cycle5] = 1 :=
  optimalScript_correct [cycle5] (List.pairwise_singleton _ _)
    (List.cons_ne_nil _ _)

example : runScript (optimalScript [cycle10]) * cycleProduct [cycle10] = 1 :=
  optimalScript_correct [cycle10] (List.pairwise_singleton _ _)
    (List.cons_ne_nil _ _)

example : runScript (optimalScript [cycle20]) * cycleProduct [cycle20] = 1 :=
  optimalScript_correct [cycle20] (List.pairwise_singleton _ _)
    (List.cons_ne_nil _ _)

-- Display: confirm the lengths via `#eval`.

#eval (optimalScript [cycle5]).length    -- 8
#eval (optimalScript [cycle10]).length   -- 13
#eval (optimalScript [cycle20]).length   -- 23

/-! ## Section 2: Multi-cycle medium-size stress

Three disjoint 4-cycles on `Fin 12`: `(0 1 2 3)(4 5 6 7)(8 9 10 11)`.

Paper indices: `n = 12`, `r = 3`, optimal length `n + r + 2 = 17`. -/

/-- First 4-cycle on `Fin 12`: `(0 1 2 3)`. -/
def c12a : Cycle (Fin 12) := ⟨0, 1, [2, 3], by decide⟩

/-- Second 4-cycle on `Fin 12`: `(4 5 6 7)`. -/
def c12b : Cycle (Fin 12) := ⟨4, 5, [6, 7], by decide⟩

/-- Third 4-cycle on `Fin 12`: `(8 9 10 11)`. -/
def c12c : Cycle (Fin 12) := ⟨8, 9, [10, 11], by decide⟩

/-- The composite permutation `(0 1 2 3)(4 5 6 7)(8 9 10 11)` on `Fin 12`. -/
def threeFourCycles : List (Cycle (Fin 12)) := [c12a, c12b, c12c]

/-- Pairwise membership in the three cycles is impossible: members of
`c12a` lie in `[0, 4)`, of `c12b` in `[4, 8)`, of `c12c` in `[8, 12)`,
so the underlying `Fin 12` values cannot coincide. We reduce to `Nat`
via `Fin.ext_iff` and close with `omega`. -/
private theorem c12a_disj_c12b : Cycle.Disjoint c12a c12b := by
  intro a ha hb
  simp only [c12a, c12b, Cycle.members, List.mem_cons, List.not_mem_nil,
             or_false, Fin.ext_iff] at ha hb
  omega

private theorem c12a_disj_c12c : Cycle.Disjoint c12a c12c := by
  intro a ha hb
  simp only [c12a, c12c, Cycle.members, List.mem_cons, List.not_mem_nil,
             or_false, Fin.ext_iff] at ha hb
  omega

private theorem c12b_disj_c12c : Cycle.Disjoint c12b c12c := by
  intro a ha hb
  simp only [c12b, c12c, Cycle.members, List.mem_cons, List.not_mem_nil,
             or_false, Fin.ext_iff] at ha hb
  omega

/-- The three cycles are pairwise disjoint. Composed from the three
private leg lemmas above. -/
theorem threeFourCycles_disjoint :
    threeFourCycles.Pairwise Cycle.Disjoint := by
  refine List.Pairwise.cons ?_ ?_
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd'
    · exact c12a_disj_c12b
    · obtain rfl : d = c12c := List.mem_singleton.mp hd'
      exact c12a_disj_c12c
  · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro d hd
    obtain rfl : d = c12c := List.mem_singleton.mp hd
    exact c12b_disj_c12c

example : (optimalScript threeFourCycles).length = 17 := by
  rw [optimalScript_length threeFourCycles (List.cons_ne_nil _ _)]
  decide

example : runScript (optimalScript threeFourCycles) *
    cycleProduct threeFourCycles = 1 :=
  optimalScript_correct threeFourCycles threeFourCycles_disjoint
    (List.cons_ne_nil _ _)

end Validation10
end Futurama
end Project
