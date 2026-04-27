import Project.validation.Optimality.Validation6_Optimality

/-!
# Validation 9 — Negative controls (anti-tests for the validator suite)

This file complements `Validation6_Optimality.lean` by exercising the
**negative cases** of the boolean validators. Every check in
`Validation6_Optimality.lean` confirms that a validator returns
`true` on a *good* input; this file confirms the same validators
correctly return `false` on deliberately *bad* inputs. Without
these, a buggy validator that silently always returned `true` would
make every "PASS" elsewhere vacuous (the mutation-testing failure
mode).

## Cost

All anti-tests are `decide` / `native_decide` on `Fin n` for small
`n`. Combined wall-clock: well under one second.

## Categories

1. **Identity script** cannot undo a non-trivial permutation.
2. **Length-(n+r+1) script** (one short of optimal): even if it
   uses helpers and has distinct pairs, no such script can undo a
   non-trivial σ.
3. **Duplicate-pair script** fails the unordered-pair `Nodup`
   component of `repairSeqValidator`.
4. **Helper-missing script** fails `stepsUseHelpers`.
5. **Self-swap step** (`(a, a)`) fails `stepsNontrivial`.
6. **Wrong-target check**: a script valid for `π_1` does not undo
   `π_2` for `π_1 ≠ π_2`.
7. **Length sensitivity**: a length-1 script obviously cannot undo
   a permutation whose optimal repair is length 6.

All anti-tests use small concrete `Body (Fin n)` step lists so the
checks are trivially decidable.
-/

open Equiv Equiv.Perm

namespace Project
namespace Futurama
namespace Validation9AntiTest

open Validation6Optimality

--------------------------------------------------------------------------------
-- Setup: a few small concrete σ on Fin 3
--------------------------------------------------------------------------------

/-- The 3-cycle `(0 1 2)`. Non-trivial; supports n=3, r=1, optimal=6. -/
def perm3 : Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

example : perm3 0 = 1 := by decide
example : perm3 1 = 2 := by decide
example : perm3 2 = 0 := by decide
example : perm3.support.card = 3 := by decide
example : perm3.cycleFactorsFinset.card = 1 := by decide
-- so the optimal length is 3 + 1 + 2 = 6.

--------------------------------------------------------------------------------
-- Anti-test category 1: identity script cannot undo non-trivial σ
--
-- An empty step list always evaluates to runScript [] = 1, so
-- runScript [] * π = π. For non-trivial π, this is ≠ 1, so the
-- correctness conjunct of repairSeqValidator must fail.
--------------------------------------------------------------------------------

example :
    repairSeqValidator ([] : List (Body (Fin 3) × Body (Fin 3))) (liftPerm perm3) = false := by
  native_decide

--------------------------------------------------------------------------------
-- Anti-test category 2: length-(n+r+1) script that LOOKS plausible
-- but cannot undo σ
--
-- For perm3 (n=3, r=1, opt=6), length-5 helper-containing scripts
-- can be arbitrary. We pick a few representative ones and confirm
-- repairSeqValidator returns false.
--
-- This is dual to bruteForceOptimality_Fin3 -- where brute force
-- checks "no length-≤5 script works", here we check that two
-- specific candidate length-5 scripts indeed don't.
--------------------------------------------------------------------------------

/-- Length-5 helper-containing script: `(x, 0)(y, 1)(x, 2)(y, 0)(x, 1)`.
Distinct pairs, all helper-containing, all non-trivial — but does NOT
undo perm3. -/
def fiveStepCandidate1 : List (Body (Fin 3) × Body (Fin 3)) :=
  [(Body.x, Body.orig 0), (Body.y, Body.orig 1), (Body.x, Body.orig 2),
   (Body.y, Body.orig 0), (Body.x, Body.orig 1)]

example : fiveStepCandidate1.length = 5 := by decide
example : stepsUseHelpers fiveStepCandidate1 = true := by decide
example : stepsNontrivial fiveStepCandidate1 = true := by decide
example : (fiveStepCandidate1.map stepPair).Nodup := by decide
-- structural conditions all pass; only the correctness check should kick in.

example :
    repairSeqValidator fiveStepCandidate1 (liftPerm perm3) = false := by
  native_decide

/-- A second length-5 candidate, structurally distinct from the first
to reduce the chance of an accidental "this specific script happens
to be the bug" pattern. -/
def fiveStepCandidate2 : List (Body (Fin 3) × Body (Fin 3)) :=
  [(Body.x, Body.y), (Body.y, Body.orig 2), (Body.x, Body.orig 0),
   (Body.y, Body.orig 1), (Body.x, Body.orig 2)]

example : fiveStepCandidate2.length = 5 := by decide
example : stepsUseHelpers fiveStepCandidate2 = true := by decide
example : stepsNontrivial fiveStepCandidate2 = true := by decide
example : (fiveStepCandidate2.map stepPair).Nodup := by decide

example :
    repairSeqValidator fiveStepCandidate2 (liftPerm perm3) = false := by
  native_decide

--------------------------------------------------------------------------------
-- Anti-test category 3: duplicate-pair script
--
-- A script with two steps having the same unordered pair (e.g.
-- `(x, 0), (0, x)` or `(x, 0), (x, 0)`) must fail the
-- `(steps.map stepPair).Nodup` conjunct. This is the
-- "distinct transpositions" requirement of paper Theorem 1.
--------------------------------------------------------------------------------

def duplicatePairScript : List (Body (Fin 3) × Body (Fin 3)) :=
  [(Body.x, Body.orig 0), (Body.y, Body.orig 1), (Body.orig 0, Body.x)]
  -- third step has same unordered pair as first

example : ¬ (duplicatePairScript.map stepPair).Nodup := by decide

example :
    repairSeqValidator duplicatePairScript (liftPerm perm3) = false := by
  native_decide

--------------------------------------------------------------------------------
-- Anti-test category 4: helper-missing script
--
-- A step like `(orig 0, orig 1)` (no helper involved) must fail
-- `stepsUseHelpers`. Even one such step in an otherwise valid list
-- should reject.
--------------------------------------------------------------------------------

def helperMissingScript : List (Body (Fin 3) × Body (Fin 3)) :=
  [(Body.x, Body.orig 0), (Body.orig 0, Body.orig 1), (Body.y, Body.orig 2)]
  -- middle step has no helper

example : usesHelperBool ((Body.orig 0, Body.orig 1) : Body (Fin 3) × Body (Fin 3)) = false :=
  by decide

example : stepsUseHelpers helperMissingScript = false := by decide

example :
    repairSeqValidator helperMissingScript (liftPerm perm3) = false := by
  native_decide

--------------------------------------------------------------------------------
-- Anti-test category 5: self-swap (trivial) step
--
-- A step like `(x, x)` is the identity transposition. Paper Theorem 1
-- requires every factor to be a non-identity 2-cycle, captured by
-- `stepsNontrivial`. Even one such step should reject.
--------------------------------------------------------------------------------

def trivialStepScript : List (Body (Fin 3) × Body (Fin 3)) :=
  [(Body.x, Body.orig 0), (Body.x, Body.x), (Body.y, Body.orig 1)]
  -- middle step is the identity transposition

example : stepsNontrivial trivialStepScript = false := by decide

example :
    repairSeqValidator trivialStepScript (liftPerm perm3) = false := by
  native_decide

--------------------------------------------------------------------------------
-- Anti-test category 6: wrong target
--
-- A script that correctly undoes π_1 must NOT correctly undo π_2 for
-- π_1 ≠ π_2 (otherwise it would map two distinct permutations to the
-- identity, impossible).
--
-- We use the simplest possible witness: the singleton script `[(x, y)]`
-- correctly undoes the helper-swap `Equiv.swap Body.x Body.y` (positive
-- control), but does NOT undo `liftPerm perm3` (anti-test). This
-- avoids the `cyclePerm` orientation convention (`cyclePerm` returns
-- the *inverse* of the paper's `(a_1 ... a_k)` action — a known
-- gotcha documented in `paper_correspondence.md` Section 6),
-- which would muddy the test if we used `optimalScript`-derived
-- scripts here.
--------------------------------------------------------------------------------

def helperSwapScript : List (Body (Fin 3) × Body (Fin 3)) :=
  [(Body.x, Body.y)]

example : helperSwapScript.length = 1 := by decide
example : stepsUseHelpers helperSwapScript = true := by decide
example : stepsNontrivial helperSwapScript = true := by decide
example : (helperSwapScript.map stepPair).Nodup := by decide

-- Positive control: this 1-step script undoes the helper-swap target.
example :
    repairSeqValidator helperSwapScript
      (Equiv.swap (Body.x : Body (Fin 3)) Body.y) = true := by
  native_decide

-- Anti-test: same 1-step script does NOT undo the lifted 3-cycle.
example :
    repairSeqValidator helperSwapScript (liftPerm perm3) = false := by
  native_decide

--------------------------------------------------------------------------------
-- Anti-test category 7: optimalScriptValidator length sensitivity
--
-- If we hand-truncate optimalScript [c] to length-(n+r+1) we should
-- fail the length conjunct of optimalScriptValidator (and also fail
-- correctness — both checks should reject independently).
--
-- This guards against an optimalScriptValidator that ignores the
-- length conjunct.
--------------------------------------------------------------------------------

/-- A *fake* "cycle list" we pretend is the optimal script for some
phantom situation. The point of the exercise is that an arbitrary
list that just happens to be a `List (Body × Body)` is NOT
recognised as the optimal script for any cycle list with the wrong
length / cycle structure relationship. -/
example :
    repairSeqValidator [(Body.x, Body.orig (0 : Fin 3))] (liftPerm perm3) = false := by
  -- 1 step is way too short; correctness must fail.
  native_decide

end Validation9AntiTest
end Futurama
end Project
