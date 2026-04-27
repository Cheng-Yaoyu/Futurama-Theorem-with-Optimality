import Project.validation.Optimality.Validation6_Optimality

/-!
# Cut-family axiom baseline check for the uniform-lower-bound theorem

The theorem `cutFamily_uniformLowerBound` lives in
`Validation6_Optimality.lean`. The file as a whole is Class II
(because of Sections 3-7's `native_decide` examples), but the
theorem's *own* proof is theorem-level and Class I.

This harness emits `#print axioms` for the cut-family theorem to
record that it does not depend on `Lean.ofReduceBool` or
`Lean.trustCompiler`.
-/

namespace Project.Futurama.Validation6Optimality

#print axioms cutFamily_uniformLowerBound

end Project.Futurama.Validation6Optimality
