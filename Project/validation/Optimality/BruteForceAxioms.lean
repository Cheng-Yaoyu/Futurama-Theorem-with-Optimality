import Project.validation.Optimality.Validation7_BruteForceOptimality

/-!
# Brute-force axiom baseline check

The brute-force file `Validation7_BruteForceOptimality.lean` uses
`native_decide` for both Fin 3 and Fin 4 enumeration. This harness
emits `#print axioms` for the brute-force predicate to record that
the file is Class II:
`{propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler}`.
-/

namespace Project.Futurama.Validation7BruteForceOptimality

-- The pure-Bool predicate itself depends only on Class I axioms.
#print axioms bruteForceOptimalityCheck

-- The `native_decide`-discharged theorems pull in Class II
-- (`Lean.ofReduceBool`, `Lean.trustCompiler`).
#print axioms bruteForceOptimality_Fin3
#print axioms bruteForceOptimality_Fin4

end Project.Futurama.Validation7BruteForceOptimality
