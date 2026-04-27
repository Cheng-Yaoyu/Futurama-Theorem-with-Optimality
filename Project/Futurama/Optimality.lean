import Project.Futurama.Optimality.RepairSeq
import Project.Futurama.Optimality.Lemma1
import Project.Futurama.Optimality.LowerBound.Layer0
import Project.Futurama.Optimality.LowerBound.Layer1
import Project.Futurama.Optimality.LowerBound.Layer2
import Project.Futurama.Optimality.UpperBound
import Project.Futurama.Optimality.Keeler

/-!
# Futurama Optimality — aggregate

`import Project.Futurama.Optimality` is the single entry point for the
optimality side of the Futurama formalisation. It re-exports, via
transitive imports, every public name in seven sub-modules:

| Sub-module                              | Role |
| --------------------------------------- | ---- |
| `Optimality.RepairSeq`                  | The lower-bound adversary surface (`RepairSeq` structure + projections) |
| `Optimality.Lemma1`                     | The Lemma 1(a)/(b)/(c) family (graph-theoretic track) |
| `Optimality.LowerBound.Layer0`          | Helpers + entry counting (`t ≥ n`) |
| `Optimality.LowerBound.Layer1`          | Doubling argument (`t ≥ n + r`) |
| `Optimality.LowerBound.Layer2`          | Parity gap closure (`t ≥ n + r + 2`) and `futurama_optimal` |
| `Optimality.UpperBound`                 | `optimalScript`, the Theorem 1 packaging, and an embedded definitional-equality harness |
| `Optimality.Keeler`                     | Keeler-gap remarks for `r = 1` (`keeler_optimal_single_cycle`) and `r ≥ 2` (`keeler_achieves_and_gap`) |

The seven sub-modules import only the constructive leaf modules
(`Project.Futurama.{CoreCycle, CoreSchedule, FiniteBridge,
ParameterizedFamily}`) plus each other; none imports the
constructive aggregate `Project.Futurama` (which would form a cycle
once that aggregate imports this one).
-/
