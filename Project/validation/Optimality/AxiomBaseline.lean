import Project.TestProject

/-!
# Axiom baseline harness

This file does not introduce any new declaration; it only emits
`#print axioms` output for the Optimality endpoints, so the recorded
axiom baseline can be re-derived from a single `lake env lean`
invocation.

To re-run as part of an aggregate build:

```
lake build Project.validation.Optimality.AxiomBaseline
```

The expected baseline is the Class I set
(`propext`, `Classical.choice`, `Quot.sound`); any axiom outside that
set in the build output indicates a regression.
-/

namespace Project
namespace Futurama

#print axioms futuramaTheorem1OfPerm
#print axioms futurama_optimal
#print axioms optimalScriptOfPerm_isOptimal
#print axioms optimalScriptOfPerm_correct
#print axioms keeler_achieves_and_gap

-- paper-strong Lemma 1(c)
#print axioms minimal_factorization_has_adjacent_paper

-- paper-Theorem-1 full claim, single declaration
#print axioms futuramaTheorem1Full

-- r=1 Keeler-optimal at theorem level
#print axioms keeler_optimal_single_cycle
#print axioms undoScript_length_single_cycle
#print axioms optimalScript_length_single_cycle

end Futurama
end Project
