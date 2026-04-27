import Project.Futurama.Spec
import Project.Futurama.ValidationKit
import Project.Futurama.Optimality

/-!
# Futurama — top-level aggregator

`import Project.Futurama` is the single entry point for downstream code
that wants the constructive theorem surface together with the shared
specification, the validation utilities, and the optimality material.
It re-exports four layers through transitive imports.

## Constructive theorem layer

From `Project.Futurama.Spec`, which transitively imports
`Project.Futurama.CoreCycle`, `Project.Futurama.CoreSchedule`,
`Project.Futurama.FiniteBridge`, and `Project.Futurama.ParameterizedFamily`.

Exposes `Body`, `Cycle`, `UsesHelper`, `cyclePerm`, `cycleProduct`,
`liftPerm`, `factorCycles`, `helperScript`, `repairScript`, `repairScriptAt`,
`undoScript`, `undoScriptAt`, `undoScriptOfPerm`, `undoScriptOfPermAt`,
and the eight named endpoint theorems `futuramaTheoremStrong*` /
`futuramaTheoremOfPermStrong*` / their `*At` variants.

## Shared `RepairSpec` interface layer

From `Project.Futurama.Spec`. Exposes `RepairSpec`, its constructors
(`RepairSpec.ofCycles`, `RepairSpec.ofCyclesAt`,
`RepairSpec.ofPermEndpoint`, `RepairSpec.ofPermDirect`,
`RepairSpec.ofPermAtEndpoint`, `RepairSpec.ofPermAtDirect`), the
projection theorems (`toCorrect`, `toNodupSteps`, `toNodupPairs`,
`toHelperIncluded`, `toProperTransp`, `toStrongTheorem`,
`toFullSpecTheorem`, `toExternalWitness`), the structural tools
(`ext_steps`, `castTarget`), and the neutral external-spec wrappers
(`ExternalRepairSpec`, `ExternalRepairSpecAt`, `externalRepairSpec`,
`externalRepairSpecDirect`, `externalRepairSpecAt`,
`externalRepairSpecAtDirect`, and the corresponding
`externalRepairWitness*` existential witnesses).

## Validation utility layer

From `Project.Futurama.ValidationKit`. Exposes the shared schedule
enumerator `allCutSchedules`, the boolean validators
(`scheduleValidation`, `allSchedulesValidate`,
`scheduleCrossSemanticsValidate`, `allSchedulesCrossSemanticsValidate`,
`usesHelperBool`, `stepsUseHelpers`, `stepsNontrivial`), the alternate
executable semantics (`BodyState`, `swapOccupants`, `stepState`,
`runState`, `stateOfPerm`, `identityState`, `prefixSemanticsAgree`,
`finalStateRestores`), and the `Fin 4` witness corpus
(`perm4Witnesses`, `perm4Images`, `exists_perm4_witness`,
`exists_perm4_cross_checked`).

## Optimality layer

From `Project.Futurama.Optimality`. See
[`Optimality.lean`](Futurama/Optimality.lean) for the layout of the
seven sub-modules covering the Theorem 1 construction, the lower-bound
chain, the Lemma 1 family, and the Keeler-gap remarks.
-/
