import Project.Futurama
import Project.validation.Constructive.Validation2
import Project.validation.Constructive.Validation3
import Project.validation.Constructive.Validation4
import Project.validation.Constructive.Validation5
import Project.validation.Constructive.Validation10_LargeStress

/-!
# Constructive Validation Aggregator

This file is the layer-aggregate entry point for the constructive
side of the validation suite (the multi-cycle repair construction
plus the bridge from arbitrary finite permutations). Run via:

```
lake build Project.validation.Constructive
```

## Aggregated files

* `Validation2.lean` — full external-spec closure plus exhaustive
  cut-family checks on representative cycles.
* `Validation3.lean` — defensive checks, orientation checks,
  negative controls, and deep `#print axioms` audits.
* `Validation4.lean` — direct lower-level external-spec derivation,
  source-traceability fact `wikiSingleCycleBlock_eq_repairScriptAt`
  by `rfl`, and the 24-element `Fin 4` witness corpus.
* `Validation5.lean` — exhaustive cross-semantics over the full
  `Fin 4` witness × cut surface (24 × 44 combinations), discharged
  via `native_decide` (introduces Class II axioms `Lean.ofReduceBool`
  and `Lean.trustCompiler` for `exists_perm4_cross_checked`; these
  do not propagate to any kernel theorem).
* `Validation10_LargeStress.lean` — deterministic single-cycle
  stress at `k = 5, 10, 20` and multi-cycle medium-size stress
  (three disjoint 4-cycles on `Fin 12`). Discharges via the
  closed-form length theorem + `decide` and direct application of
  the kernel correctness theorem. No `sorry` introduced.

## Optional companion (not in this aggregate)

* `Validation11_PlausibleStress.lean` — randomised counterpart to
  V10 using Mathlib's `plausible` tactic. The tactic closes a
  passing randomised goal with `sorry` rather than synthesising a
  kernel proof, so V11 is **deliberately excluded** from this
  aggregate to keep `lake build Project.validation.Constructive`
  and `lake build Project` `sorry`-clean. To run the randomised
  test directly:

  ```
  lake build Project.validation.Constructive.Validation11_PlausibleStress
  ```

  See the V11 file docstring for the full discussion of why
  Plausible is opt-in.

The companion summary lives in
[`constructive_summary.md`](constructive_summary.md).
-/
