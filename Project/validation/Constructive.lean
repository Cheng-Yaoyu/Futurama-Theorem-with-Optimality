import Project.Futurama
import Project.validation.Constructive.Validation2
import Project.validation.Constructive.Validation3
import Project.validation.Constructive.Validation4
import Project.validation.Constructive.Validation5

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

The companion summary lives in
[`constructive_summary.md`](constructive_summary.md).
-/
