import Project.validation.Optimality.AxiomBaseline
import Project.validation.Optimality.Validation6_Optimality
import Project.validation.Optimality.CutFamilyAxioms

-- Optional sub-files (low-cost; uncomment to include in the aggregate
-- build). They are documented and reachable via direct
-- `lake build Project.validation.Optimality.X` regardless.
--
-- * `Validation7_BruteForceOptimality` — exhaustive brute-force on
--   `Fin 3` and `Fin 4`; ~38 s wall-clock via `native_decide`.
-- * `Validation8_Fin5Stress` — `Fin 5` exploration; theorem-level
--   instantiation is fast, but the brute-force `native_decide` calls
--   inside are commented out (16 GB RAM is not enough to push them
--   through; see file docstring for details).
-- * `Validation9_AntiTest` — negative controls confirming the V6
--   boolean validators correctly reject malformed inputs. Fast
--   (< 1 second).
-- * `BruteForceAxioms` — `#print axioms` harness for V7's brute-force
--   theorems (Class II).
--
-- import Project.validation.Optimality.Validation7_BruteForceOptimality
-- import Project.validation.Optimality.Validation8_Fin5Stress
-- import Project.validation.Optimality.Validation9_AntiTest
-- import Project.validation.Optimality.BruteForceAxioms

/-!
# Optimality Validation Aggregator

This file is the layer-aggregate entry point for the optimality side
of the validation suite. It pulls in the core gating files (axiom
baseline, boolean validators on representative cycles, cut-family
uniform lower bound axiom check). Run via:

```
lake build Project.validation.Optimality
```

## Aggregated files

* `AxiomBaseline.lean` — `#print axioms` harness for every public
  optimality endpoint (`futuramaTheorem1OfPerm`, `futurama_optimal`,
  `optimalScriptOfPerm_isOptimal`, `optimalScriptOfPerm_correct`,
  `keeler_achieves_and_gap`, the paper-strong Lemma 1(c)
  `minimal_factorization_has_adjacent_paper`, the single-declaration
  `futuramaTheorem1Full`, `keeler_optimal_single_cycle`, and the two
  closed-form siblings `undoScript_length_single_cycle` /
  `optimalScript_length_single_cycle`).
* `Validation6_Optimality.lean` — boolean validators
  (`repairSeqValidator`, `optimalScriptValidator`, `keelerGapFormula`),
  22 `native_decide` examples on four representative cycle structures
  (3-cycle, 4-cycle, two disjoint 2-cycles, three disjoint 2-cycles),
  cross-semantics agreement at every prefix, and the cut-family
  uniform-lower-bound theorem `cutFamily_uniformLowerBound`.
* `CutFamilyAxioms.lean` — `#print axioms` harness confirming
  `cutFamily_uniformLowerBound` itself is Class I (no `native_decide`
  in its proof body).

## Optional sub-files (commented imports above)

`Validation7_BruteForceOptimality.lean`, `Validation8_Fin5Stress.lean`,
`Validation9_AntiTest.lean`, and `BruteForceAxioms.lean` are not
imported into this aggregate by default. Uncomment the relevant import
line above (or build them individually) to include them. They live
under `Project/validation/Optimality/` and are documented in
`Project/validation/README.md`.
-/
