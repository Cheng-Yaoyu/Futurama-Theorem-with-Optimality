import Project.Futurama
import Project.Futurama.Optimality

/-!
# *The Prisoner of Benda* — Episode-inspired demonstration

In the *Futurama* episode "The Prisoner of Benda" (S6E10), Professor
Farnsworth's mind-switching machine creates a tangled web of displaced
consciousness among the Planet Express crew. The episode's titular puzzle —
can everyone get back to their own body, given the constraint that the
machine refuses to swap the same pair of bodies twice? — is resolved by
introducing two fresh helpers, the Harlem Globetrotters Sweet Clyde and
Bubblegum Tate (who are also accomplished mathematicians).

This file models a **simplified, episode-inspired slice** of the puzzle in
Lean: a 4-cycle and a 3-cycle with the same moved-body count and cycle
count needed to exhibit the `n + r + 2 = 11` optimum and the `r = 2`
Keeler-vs-optimal coincidence. The actual episode features additional
characters (Wash Bucket, Nikolai, LaBarbara, etc.) and a more tangled
chain of swaps; the slice below is a faithful but pedagogically focused
abstraction. The Globetrotters Sweet Clyde and Bubblegum Tate are
modelled as part of the on-stage cast (with the `Body.x`/`Body.y` helpers
acting as the unmoved-helper extension); in the show they appear only
as external advisors who explain Keeler's algorithm.

The file demonstrates both the constructive Keeler script (`undoScript`)
and the optimal Evans–Huang–Nguyen script (`optimalScript`) restoring
everyone to their original body.

## The simplified slice

After the dust settles in our slice, the configuration is:

```text
Person       Mind is in body
─────────────────────────────
Fry          Bender    ┐
Bender       Hermes    │  the 4-cycle
Hermes       Zoidberg  │
Zoidberg     Fry       ┘

Leela        Amy        ┐
Amy          Professor  │  the 3-cycle
Professor    Leela      ┘
```

So `n = 4 + 3 = 7` (number of moved bodies) and `r = 2` (number of
disjoint cycles). The optimal repair length is `n + r + 2 = 11`. Because
`r = 2` is one of the two values where Keeler's algorithm provably hits
the optimum (the gap formula `(r - 2) + parity` evaluates to 0), Keeler's
`undoScript` also produces 11 swaps for this particular configuration —
the divergence between the two algorithms only kicks in at `r ≥ 3`.

## Orientation note

This file uses the project's `cyclePerm` orientation (see
`Project/Futurama/CoreCycle.lean`), which is the inverse of the paper's
standard cycle notation. Concretely, `cyclePerm c` sends
`c.first ↦ c.last`, `c.second ↦ c.first`, and so on. To represent the
episode's forward-cycle `(Fry Bender Hermes Zoidberg)` (meaning
`Fry ↦ Bender ↦ Hermes ↦ Zoidberg ↦ Fry`), we therefore use the Lean cycle
`⟨Fry, Zoidberg, [Hermes, Bender]⟩` whose `cyclePerm` sends `Fry ↦ Bender`
as required. The full dictionary is documented in
`Project/validation/paper_correspondence.md` §6.

## Build target

```
lake build Project.PrisonerOfBenda
```

All examples below are discharged by `decide` (the cast has 9 elements;
`Body Crew` has 11), so the file builds in well under one second.
-/

namespace Project
namespace Futurama
namespace PrisonerOfBenda

/-- The Planet Express crew plus the two Harlem Globetrotter helpers
(Sweet Clyde and Bubblegum Tate) who appear in S6E10. -/
inductive Crew
  | fry
  | leela
  | bender
  | amy
  | professor
  | zoidberg
  | hermes
  | sweetClyde
  | bubblegumTate
  deriving DecidableEq, Repr

open Crew

/-- Manual `Fintype` instance enumerating the nine crew members. The Mathlib
`deriving Fintype` handler is not available in the imported namespace, so we
provide the instance by hand; the kernel theorems
(`optimalScript_correct`, `optimalScript_length`, `futuramaTheorem`) require
`Fintype Crew` to instantiate the constructive endpoints on `Body Crew`. -/
instance : Fintype Crew where
  elems := {fry, leela, bender, amy, professor, zoidberg, hermes,
            sweetClyde, bubblegumTate}
  complete := fun c => by cases c <;> decide

/-- The 4-cycle `Fry → Bender → Hermes → Zoidberg → Fry` from the
episode, expressed in the project's `cyclePerm` orientation. -/
def cycle1 : Cycle Crew :=
  ⟨fry, zoidberg, [hermes, bender], by decide⟩

/-- The 3-cycle `Leela → Amy → Professor → Leela` from the episode. -/
def cycle2 : Cycle Crew :=
  ⟨leela, professor, [amy], by decide⟩

/-- The simplified slice: a 4-cycle plus a 3-cycle, disjoint. -/
def chaos : List (Cycle Crew) := [cycle1, cycle2]

/-- The two cycles share no characters; the two `cycle.members` lists
are disjoint. Proven by manual case analysis on the nine `Crew`
constructors — `decide` does not synthesise `Decidable` for
`List.Pairwise Cycle.Disjoint` directly because `Cycle.Disjoint` is an
abbrev that the instance resolver does not unfold. The proof stays on
Class I axioms. -/
theorem chaos_disjoint : chaos.Pairwise Cycle.Disjoint := by
  refine List.Pairwise.cons ?_ ?_
  · -- For every `d ∈ [cycle2]`, `Cycle.Disjoint cycle1 d`.
    intro d hd
    obtain rfl : d = cycle2 := List.mem_singleton.mp hd
    intro a ha hb
    cases a <;> simp_all [cycle1, cycle2, Cycle.members]
  · -- `Pairwise Cycle.Disjoint [cycle2]` — singleton case is trivial.
    exact List.pairwise_singleton _ _

theorem chaos_nonempty : chaos ≠ [] :=
  List.cons_ne_nil _ _

/-! ## Verifying the slice permutation

Each character is sent to the body containing their mind. The two helpers
(SweetClyde, BubblegumTate) and the two `Body`-level helpers (`x`, `y`)
are not yet involved in any swap, so they are fixed points of `chaos`. -/

example : cycleProduct chaos (Body.orig fry)       = Body.orig bender    := by decide
example : cycleProduct chaos (Body.orig bender)    = Body.orig hermes    := by decide
example : cycleProduct chaos (Body.orig hermes)    = Body.orig zoidberg  := by decide
example : cycleProduct chaos (Body.orig zoidberg)  = Body.orig fry       := by decide
example : cycleProduct chaos (Body.orig leela)     = Body.orig amy       := by decide
example : cycleProduct chaos (Body.orig amy)       = Body.orig professor := by decide
example : cycleProduct chaos (Body.orig professor) = Body.orig leela     := by decide

example : cycleProduct chaos (Body.orig sweetClyde)    = Body.orig sweetClyde    := by decide
example : cycleProduct chaos (Body.orig bubblegumTate) = Body.orig bubblegumTate := by decide
example : cycleProduct chaos Body.x = Body.x := by decide
example : cycleProduct chaos Body.y = Body.y := by decide

/-! ## The optimal repair script (paper Theorem 1)

For this permutation: `n = 4 + 3 = 7`, `r = 2`, so the optimal length is
`n + r + 2 = 11`. -/

example : (optimalScript chaos).length = 11 := by
  rw [optimalScript_length chaos chaos_nonempty]
  decide

/-- The optimal script restores everyone to their original body. -/
theorem everyone_restored_optimal :
    runScript (optimalScript chaos) * cycleProduct chaos = 1 :=
  optimalScript_correct chaos chaos_disjoint chaos_nonempty

/-! ## Keeler's original script (the chalkboard proof from the episode)

The TV-show / Wikipedia version (`undoScript`) achieves length
`n + 2r + (r mod 2) = 7 + 4 + 0 = 11` for this permutation. -/

example : (undoScript chaos).length = 11 := by
  rw [undoScript_length chaos]
  decide

/-- Keeler's original script also restores everyone. -/
theorem everyone_restored_keeler :
    runScript (undoScript chaos) * cycleProduct chaos = 1 :=
  futuramaTheorem chaos

/-- For the simplified slice (`r = 2`), Keeler's algorithm and the
paper-optimal algorithm produce scripts of identical length. The
Keeler-vs-optimal gap only opens at `r ≥ 3`; see
`Project.Futurama.keeler_achieves_and_gap`. -/
theorem keeler_matches_optimal_at_chaos :
    (undoScript chaos).length = (optimalScript chaos).length := by
  rw [undoScript_length, optimalScript_length chaos chaos_nonempty]
  decide

/-! ## Inspecting the scripts

Run these to see the actual swap lists at the body level. The lists differ
in concrete content (the two algorithms route the helpers differently) but
agree in length and in the final restoration property. -/

#eval (optimalScript chaos).length
#eval (undoScript chaos).length

end PrisonerOfBenda
end Futurama
end Project
