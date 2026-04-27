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

* **Kernel correctness** — `lake build Project.TestProject` succeeds
  with `exit 0`. Zero `sorry`, zero `admit`, zero user-defined axiom.
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
through five layers (kernel correctness, definition correctness,
statement correctness, executable sanity, and exhaustive `Fin 4`
cross-semantics). No remaining open issue.
