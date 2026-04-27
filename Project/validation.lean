import Project.validation.Constructive
import Project.validation.Optimality

/-!
# Validation — master entry point

`import Project.validation` (or `lake build Project.validation`)
runs the entire validation suite: both the constructive layer
(`Project.validation.Constructive`) and the optimality layer
(`Project.validation.Optimality`).

## Sub-aggregates

* [`Project.validation.Constructive`](validation/Constructive.lean)
  — `Validation2.lean` … `Validation5.lean`. Validates the
  constructive Wikipedia-style Futurama theorem, including the
  parameterised cut family and the strongest external-spec packaging.
* [`Project.validation.Optimality`](validation/Optimality.lean)
  — `Validation6_Optimality.lean` plus the axiom-baseline
  harnesses. Validates paper Theorem 1, the Lemma 1 family, and the
  Keeler-gap remark.

## Optional sub-files (not pulled in by the master)

* `Project.validation.Optimality.Validation7_BruteForceOptimality`
  — exhaustive brute-force on `Fin 3` and `Fin 4`; ~38 s wall-clock.
* `Project.validation.Optimality.Validation8_Fin5Stress` — `Fin 5`
  exploration; theorem-level instantiation is fast (active), but the
  brute-force `native_decide` calls are commented out (see file
  docstring for time estimates and machine requirements).
* `Project.validation.Optimality.Validation9_AntiTest` — negative
  controls confirming the V6 boolean validators correctly reject
  malformed inputs. Fast (< 1 second).
* `Project.validation.Optimality.BruteForceAxioms` — `#print axioms`
  harness for the V7 brute-force theorems (Class II).

To enable these in the optimality aggregate, uncomment the relevant
import lines at the top of `Project/validation/Optimality.lean`.
Each is also independently buildable via
`lake build Project.validation.Optimality.X`.

## Reading

The validation strategy is documented in
[`Project/validation/README.md`](validation/README.md). One-page
summaries live in
[`constructive_summary.md`](validation/constructive_summary.md) and
[`optimality_summary.md`](validation/optimality_summary.md). The
row-by-row paper-to-Lean correspondence for Theorem 1 + Lemma 1 is
in [`paper_correspondence.md`](validation/paper_correspondence.md).
-/
