# Constructive Theorem — Validation Summary

This document summarises the validation evidence for the constructive
side of the Futurama formalisation: the multi-cycle repair
construction and its correctness, plus the bridge from arbitrary
finite permutations to the cycle-list framework.

---

## What is validated

The constructive theorem is the formal counterpart of the Wikipedia /
Futurama folk statement:

> Let `A` be a finite set, and let `x`, `y` be two helper bodies not
> in `A`. Any permutation of `A` can be reduced to the identity by
> applying a sequence of distinct transpositions on `A ∪ {x, y}`,
> each containing at least one of `x` or `y`.

The Lean development covers:

* the single-cycle executable repair construction
  (`repairScript` / `repairPerm`);
* multi-cycle composition (`cycleProduct` / `undoScript`)
  with correctness (`futuramaTheorem`);
* the bridge to arbitrary finite permutations via `liftPerm`,
  `factorCycles`, `cycleFromPerm` (giving `undoScriptOfPerm` and
  `futuramaTheoremOfPerm`);
* the parameterised cut family
  (`repairScriptAt` / `undoScriptAt` / `CutSchedule`) with all
  endpoints proved at the parameterised level and recovered at the
  default route as specialisations at `defaultSchedule`;
* the strongest external-spec packaging
  (`futuramaTheoremStrong{,FullSpec}` and
  `futuramaTheoremOfPermStrong{,FullSpec}`), which adds the four
  machine-side conditions (list-level Nodup, unordered-pair Nodup,
  helper inclusion, every-step-non-trivial) on top of correctness.

---

## How it is validated

The validation is layered:

* **Kernel correctness** — `lake build Project.TestProject` and
  `lake build Project.validation.Constructive` both succeed with
  `exit 0`. Zero `sorry`, zero `admit`, zero user-defined axiom
  anywhere in the default build path. The randomised companion file
  `Validation11_PlausibleStress.lean` is **opt-in** (not imported by
  the constructive aggregate), so its Plausible-injected `sorry`
  never enters any default build target.
* **Definition correctness** — every constructive definition (`Body`,
  `Cycle`, `runScript`, `cyclePerm`, `cycleProduct`, `undoScript`,
  `liftPerm`, `factorCycles`, the parameterised family) has a
  documented mathematical role and matches the intended semantics.
* **Statement correctness** — the strongest external-spec endpoints
  (`futuramaTheoremOfPermStrong{,FullSpec}`) match the Wikipedia /
  Futurama statement quoted above.
* **Executable sanity (`Validation2`)** — full-spec closure plus
  exhaustive cut-family checks on representative cycles.
* **Direct lower-level path (`Validation4`)** — re-derives the
  external spec from low-level lemmas, proving the
  source-traceability fact `wikiSingleCycleBlock_eq_repairScriptAt`
  by `rfl`.
* **Cross-semantics on `Fin 4` (`Validation5`)** — exhaustive
  enumeration of all 24 non-trivial `Perm (Fin 4)` cycle structures ×
  all 44 cut schedules, with an executable second semantics
  (`runState`) agreeing with `runScript` at every prefix.
* **Large-cycle deterministic stress (`Validation10_LargeStress`)** —
  single-cycle stress at `k = 5, 10, 20` and three disjoint 4-cycles
  on `Fin 12`. Discharged by the closed-form length theorem +
  `decide` and direct application of `optimalScript_correct`; no
  `sorry` introduced. Pushes coverage beyond the exhaustive `Fin 4`
  ground.

An optional randomised companion
(`Validation11_PlausibleStress.lean`) re-verifies V10's length-formula
examples through Mathlib's `plausible` tactic. Plausible closes a
passing randomised goal with `sorry`, so V11 is **deliberately
excluded** from the constructive aggregate; build it directly via
`lake build Project.validation.Constructive.Validation11_PlausibleStress`
when randomised coverage is desired.

All validation is reproducible via:

```bash
lake build Project.validation.Constructive
```

---

## Axiom baseline

All theorem-level constructive endpoints depend only on the standard
Lean / Mathlib axioms:

```
{propext, Classical.choice, Quot.sound}
```

The exhaustive `Fin 4` cross-semantics check
(`Validation5.exists_perm4_cross_checked`) additionally introduces
`{Lean.ofReduceBool, Lean.trustCompiler}` because it is discharged
via `native_decide`; this is contained inside `Validation5.lean` and
does not propagate to any kernel theorem.

---

## Bottom line

The constructive Futurama theorem is fully formalised and validated
through six layers (kernel correctness, definition correctness,
statement correctness, executable sanity, exhaustive `Fin 4`
cross-semantics, and large-cycle deterministic stress beyond the
exhaustive ground). An optional seventh randomised layer
(`Validation11_PlausibleStress.lean`) is available on direct request.
The literate end-to-end demonstration on an episode-inspired S6E10
slice — a 4-cycle plus a 3-cycle that exhibits the same
`n + r + 2 = 11` optimum and the `r = 2` Keeler-vs-optimal
coincidence — lives in
[`../PrisonerOfBenda.lean`](../PrisonerOfBenda.lean). No remaining
open issue.
