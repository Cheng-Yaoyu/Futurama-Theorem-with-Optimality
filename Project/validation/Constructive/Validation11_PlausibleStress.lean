import Project.validation.Constructive.Validation10_LargeStress
import Plausible

/-!
# Validation 11 — Plausible-driven randomized property tests (optional)

This file is the **optional** randomised companion to V10
(`Validation10_LargeStress.lean`, the deterministic large-cycle stress).
It re-verifies V10's length-formula examples through random sampling
rather than exhaustive enumeration.

## Why optional?

The `plausible` tactic in Mathlib v4.23.0 closes a passing randomised
goal with `sorry` rather than synthesising a kernel proof: passing the
randomised check gives a `Decidable.decide`-true result, but the tactic
does not produce a kernel-checkable derivation, so the goal is closed
with `sorry`. Including this file in the default
`Project.validation.Constructive` aggregate would therefore inject a
`sorry` warning into `lake build Project`. To keep the default build
**`sorry`-clean across the entire codebase**, this file is *not* imported
by `Project.validation.Constructive`; build it directly:

```
lake build Project.validation.Constructive.Validation11_PlausibleStress
```

The randomised property is mathematically redundant with V10 (the
length formula is already verified deterministically there); V11
exists for tooling-level coverage and as a worked example of using
Plausible against the project.

## Axiom impact

The Plausible `example` is closed with the documented Plausible
`sorry`. The `sorry` is **contained** in this validation file only and
does NOT propagate to any kernel theorem; in particular every
`Project.Futurama.*` and `Project.Futurama.Optimality.*` endpoint
remains `sorry`-free, and the default build path
(`lake build Project`, `lake build Project.validation`,
`lake build Project.validation.Constructive`) does not pull in this
file.
-/

namespace Project
namespace Futurama
namespace Validation11

open Validation10

/-- Boolean predicate: for the random index `i`, the corresponding cycle's
`optimalScript` has the expected length. -/
def lengthFormulaForIndex (i : Nat) : Bool :=
  match i % 5 with
  | 0 => decide ((optimalScript [cycle5]).length = 8)         -- 5 + 1 + 2
  | 1 => decide ((optimalScript [cycle10]).length = 13)       -- 10 + 1 + 2
  | 2 => decide ((optimalScript [cycle20]).length = 23)       -- 20 + 1 + 2
  | 3 => decide ((optimalScript threeFourCycles).length = 17) -- 12 + 3 + 2
  | _ => true                                                  -- vacuous

/-- Plausible-driven random property: for any natural index, the length
formula holds on the dispatched cycle structure. Plausible samples
random `Nat`s and checks each; if no counterexample is found the
property is discharged with the documented Plausible `sorry`. -/
example : ∀ i : Nat, lengthFormulaForIndex i := by plausible

end Validation11
end Futurama
end Project
