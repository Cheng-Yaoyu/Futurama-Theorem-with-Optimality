# Project — code map

Lean 4 source tree for the Futurama Theorem formalisation.

## Top-level

| File | Role |
|------|------|
| [`TestProject.lean`](TestProject.lean) | Top-level façade. Re-exports `Project.Futurama` + `Project.Futurama.Optimality`; hosts a small `Crew` example demonstrating `cyclePerm` / `repairPerm`; emits `#check` diagnostics for every public endpoint. |
| [`Futurama.lean`](Futurama.lean) | Aggregator. `import Project.Futurama` pulls in the constructive theorem layer, the shared `RepairSpec` interface, the validation utilities, and the optimality subtree. |

## Constructive layer — `Futurama/`

| File | Role |
|------|------|
| [`Futurama/CoreCycle.lean`](Futurama/CoreCycle.lean) | `Body` / `Cycle` / `runScript` / `cyclePerm` / `repairScript` / `repairPerm`. Basic types and the single-cycle executable repair. |
| [`Futurama/CoreSchedule.lean`](Futurama/CoreSchedule.lean) | `cycleProduct` / `repairScripts` / `repairProduct` / `undoScript` at the cycle-list level. The cycle-list endpoint `futuramaTheorem` (correctness only). |
| [`Futurama/FiniteBridge.lean`](Futurama/FiniteBridge.lean) | `liftPerm` / `factorCycles` / `cycleFromPerm` — bridge from arbitrary finite permutations to the cycle-list framework. The `factorGraph` graph-theoretic infrastructure used by Lemma 1(a). The `Perm`-level default-route endpoint `futuramaTheoremOfPerm`. |
| [`Futurama/ParameterizedFamily.lean`](Futurama/ParameterizedFamily.lean) | The parameterised cut family (`repairScriptAt`, `CutSchedule`, `undoScriptAt`, `undoScriptOfPermAt`) plus the four named default-route endpoints derived as specialisations at `defaultSchedule`: `futuramaTheoremStrong`, `futuramaTheoremStrongFullSpec`, `futuramaTheoremOfPermStrong`, `futuramaTheoremOfPermStrongFullSpec`. |
| [`Futurama/Spec.lean`](Futurama/Spec.lean) | Shared `RepairSpec` interface — packages a repair script with all five machine-side invariants. Constructors via `RepairSpec.ofCycles`, `RepairSpec.ofCyclesAt`, and the `externalRepairSpec*` family. |
| [`Futurama/ValidationKit.lean`](Futurama/ValidationKit.lean) | Shared executable validators (`stepsUseHelpers`, `stepsNontrivial`, `scheduleValidation`, `runState`, `prefixSemanticsAgree`, …) and the 24-element `perm4Witnesses` corpus exhausting `Perm (Fin 4)`. |

## Optimality subtree — `Futurama/Optimality/`

| File | Role |
|------|------|
| [`Futurama/Optimality.lean`](Futurama/Optimality.lean) | Aggregator. `import Project.Futurama.Optimality` pulls in all seven sub-modules below. |
| [`Futurama/Optimality/RepairSeq.lean`](Futurama/Optimality/RepairSeq.lean) | The `RepairSeq` structure — the lower-bound adversary surface. Five fields mirror paper Theorem 1's machine-side requirements. |
| [`Futurama/Optimality/Lemma1.lean`](Futurama/Optimality/Lemma1.lean) | Lemma 1(a)/(b)/(c) family. Independent of the Theorem 1 proof chain; preserved as a parallel paper-faithful track and as the direct prerequisite for paper Theorems 2 and 3. |
| [`Futurama/Optimality/LowerBound/Layer0.lean`](Futurama/Optimality/LowerBound/Layer0.lean) | First leg `t ≥ n` (entry counting) plus helpers and the gap-argument scaffolding. |
| [`Futurama/Optimality/LowerBound/Layer1.lean`](Futurama/Optimality/LowerBound/Layer1.lean) | Strengthening to `t ≥ n + r` (Evans–Huang–Nguyen's doubling argument). The largest single module of the development. |
| [`Futurama/Optimality/LowerBound/Layer2.lean`](Futurama/Optimality/LowerBound/Layer2.lean) | Closing the gap to `t ≥ n + r + 2` via the parity theorem and the strict-inequality "gap obstruction". Hosts `repair_length_ge_optimal` and the `Perm α`-level corollary `futurama_optimal`. |
| [`Futurama/Optimality/UpperBound.lean`](Futurama/Optimality/UpperBound.lean) | The explicit `n + r + 2`-factor construction `optimalScript` realising paper Theorem 1's λ. The `Perm α`-level packaging `optimalScriptOfPerm`, the three-conjunct theorem `futuramaTheorem1OfPerm`, the `RepairSeq` existence witness `optimalRepairSeqOfPerm`, and the single-declaration form `futuramaTheorem1Full`. |
| [`Futurama/Optimality/Keeler.lean`](Futurama/Optimality/Keeler.lean) | The Keeler-gap remark for all `r ≥ 1`: `keeler_optimal_single_cycle` (`r = 1`) and `keeler_achieves_and_gap` (`r ≥ 2`). |

## Validation — `validation/`

See [`validation/README.md`](validation/README.md).

## Build commands

```bash
# Top-level (constructive + optimality)
lake build Project.TestProject

# Constructive validation aggregate
lake build Project.validation.Constructive

# Optimality validation aggregate
lake build Project.validation.Optimality

# Optional: brute-force optimality on small Fin n (~38 s at Fin 4)
lake build Project.validation.Optimality.Validation7_BruteForceOptimality
lake build Project.validation.Optimality.BruteForceAxioms
```

All return `exit 0`.
