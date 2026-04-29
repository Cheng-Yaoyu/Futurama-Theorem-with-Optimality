# Formalising the Futurama Theorem (with optimality)

A complete Lean 4 + Mathlib formalisation of paper

> Ron Evans, Lihua Huang, Tuan Nguyen,
> *Keeler's Theorem and Products of Distinct Transpositions*,
> The American Mathematical Monthly **121** no. 2 (2014), 136–144.

A copy of the paper is included in this repository as
[`keeler2014.pdf`](keeler2014.pdf).

The theorem is the formal counterpart of the puzzle from the *Futurama*
episode "The Prisoner of Benda": a two-body mind-switching machine that
will not work twice on the same pair of bodies. The question — whether
**any** mind-scrambling permutation can be undone, and what the
**minimum** number of switches is — is answered constructively here.

## What is formalised

* **Constructive theorem** (a.k.a. Wikipedia / Futurama folk
  formulation): every finite permutation can be undone using two
  helper bodies, with every step a distinct helper-containing
  transposition. Both the default Keeler route and the parameterised
  cut family are proved.
* **Paper Theorem 1** (the refined Evans–Huang–Nguyen / Keeler
  result): every non-trivial permutation `P = C_1 · · · C_r` of
  disjoint cycles with `n = k_1 + · · · + k_r` can be undone by a
  product of **exactly `n + r + 2`** distinct helper-containing
  transpositions, and **no smaller number suffices**. The Lean
  formalisation provides both the explicit construction
  (`optimalScript`, `optimalScriptOfPerm`) and the matching
  `∀`-quantified lower bound (`futurama_optimal`), packaged together
  as `futuramaTheorem1OfPerm` (and as a single existence form,
  `futuramaTheorem1Full`).
* **Lemma 1 family** of the paper (a, b, c) — fully formalised,
  including the paper-strong form of Lemma 1(c) that exposes the
  `pre ++ [a, b] ++ suf` split and excludes the wrap-around edge.
* **Keeler-gap remark** for all `r ≥ 1`: `keeler_optimal_single_cycle`
  (`r = 1`) and `keeler_achieves_and_gap` (`r ≥ 2`).

The complete paper-to-Lean correspondence is in
[`Project/validation/paper_correspondence.md`](Project/validation/paper_correspondence.md).

## Prerequisites

* **Lean 4** via [`elan`](https://github.com/leanprover/elan) — the
  toolchain is pinned in `lean-toolchain`
  (`leanprover/lean4:v4.23.0`) and `elan` fetches it automatically.
  If you don't have it yet:
  ```bash
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
  ```
* **Mathlib v4.23.0** (the only declared dependency in `lakefile.toml`),
  pulled by `lake update` from the cloud cache (~2 min one-time).
* **OS**: macOS / Linux / Windows (WSL2 recommended for Windows).
* **Disk**: ~2 GB for Mathlib + Lean + build artefacts.
* **RAM**: 8 GB minimum; 16 GB recommended for the optional brute-force
  layer (`Validation7_BruteForceOptimality`).

## Build

From the repo root:

```bash
# First-time setup (downloads Mathlib via cloud cache)
lake update                # ~2 min

# Build everything (kernel + default validation)
lake build                 # ~6 min cold, ~2 s warm
```

Targeted aggregates if you want to build a specific subsystem:

```bash
lake build Project.TestProject              # main façade — #check every public endpoint resolves
lake build Project.validation.Constructive  # constructive (Wikipedia / Keeler) validation
lake build Project.validation.Optimality    # paper Theorem 1 / Lemma 1 / Keeler validation
```

Optional opt-in layers (kept out of `lake build` to keep the default fast):

```bash
lake build Project.validation.Optimality.Validation7_BruteForceOptimality  # ~35 s
lake build Project.validation.Optimality.Validation9_AntiTest              # ~2 s
```

### Build time reference

Wall-clock figures measured on an **Apple Mac mini M4 (16 GB RAM)**
with a warm Mathlib cloud cache. Per-layer rows are incremental
rebuilds (delete the file's `.olean`, rerun `lake build`); the cold L1
figure is `lake clean && lake build Project` on the same machine.

| Target                                                                          | Time                  | Notes                              |
|---------------------------------------------------------------------------------|-----------------------|------------------------------------|
| `lake update` (Mathlib download)                                                | ~2 min                | first-time only                    |
| `lake build Project` (kernel — 1244 jobs)                                       | 5 min 51 s cold; 1.6 s warm | the main soundness check     |
| `lake build` (kernel + default validation aggregates)                           | ~6 min cold; ~2 s warm | adds V5 / V6 / V10                |
| `lake build Project.validation.Optimality.Validation7_BruteForceOptimality`     | 35.3 s                | brute-force on Fin 3, 4 (opt-in)  |
| `lake build Project.validation.Optimality.Validation9_AntiTest`                 | 2.2 s                 | malformed-input rejection (opt-in) |

## Validation suite (per-layer breakdown)

The audit runs eight independent layers of evidence. Layers 1–3 are
structural / paper-correspondence guards; layers 4–8 are executable
corroboration via `native_decide` / `decide` on concrete witnesses.

| Layer                          | What it checks                                                          | Discharge              | Time                       |
|--------------------------------|-------------------------------------------------------------------------|------------------------|----------------------------|
| Kernel correctness             | zero `sorry` / `admit` / user axioms                                    | `lake build Project`   | 5 min 51 s cold; 1.6 s warm |
| Definition correctness         | paper-λ block hierarchy pinned by 9 × `example := rfl`                  | part of L1             | —                          |
| Statement correctness          | paper-vs-Lean row-by-row mapping                                        | `paper_correspondence.md` | manual audit             |
| Executable validators (V6)     | `repairSeqValidator` on 4 cycle shapes                                  | 22 × `native_decide`   | 10.9 s                     |
| Cross-semantics (V5)           | `runState` vs `runScript` on every `Perm (Fin 4)`                       | exhaustive `native_decide` | 2.5 s                  |
| Brute-force (V7, opt-in)       | no `<n+r+2`-script undoes any non-trivial `σ` on `Fin 3, 4`             | exhaustive `native_decide` | 35.3 s; OOM at Fin 5  |
| Anti-tests (V9, opt-in)        | validators reject 7 malformed inputs                                    | `native_decide`        | 2.2 s                      |
| Large-cycle stress (V10)       | kernel endpoint at `k = 5, 10, 20` plus three 4-cycles on `Fin 12`     | closed-form + `decide` | 2.2 s                      |

Layers 1, 2, 4, 5, 8 plus the axiom-baseline harnesses are pulled into
`lake build` by default. The brute-force layer (V7) and anti-tests
layer (V9) are opt-in direct targets, kept out of the default build to
keep it fast.

## What you should see after a successful build

A successful `lake build` ends by listing the axiom dependency of every
public endpoint. The output looks like:

```
info: 'futuramaTheorem1OfPerm'           depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'futurama_optimal'                 depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'optimalScriptOfPerm_isOptimal'    depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'futuramaTheorem1Full'             depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'keeler_optimal_single_cycle'      depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'keeler_achieves_and_gap'          depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'undoScript_length_single_cycle'   depends on axioms: [propext, Quot.sound]
info: 'cutFamily_uniformLowerBound'      depends on axioms: [propext, Classical.choice, Quot.sound]
...
Build completed successfully (1244 jobs).
```

Every `depends on axioms:` line should list a subset of
`{propext, Classical.choice, Quot.sound}` — the standard Lean / Mathlib
axioms (Class I). The optional brute-force target additionally lists
`Lean.ofReduceBool` and `Lean.trustCompiler` — these are confined to
that file by design (see [Soundness](#soundness)).

## Try it on the episode

For a 30-second smoke test, open the literate demonstration:

```bash
lake env lean Project/PrisonerOfBenda.lean
```

You should see all 9 `example := decide` lines and the two
end-of-episode theorems (`everyone_restored_optimal` and
`everyone_restored_keeler`) elaborate in **under one second**.
Successful exit code 0 *is* the proof going through.

The slice models a simplified Planet Express crew:

* a 4-cycle (Fry → Bender → Hermes → Zoidberg)
* a 3-cycle (Leela → Amy → Professor)

with `n = 7` moved bodies and `r = 2` disjoint cycles. The optimal
repair length is `n + r + 2 = 11` swaps — computed by both Keeler's
algorithm (`undoScript`) and the paper-optimal `λ` construction
(`optimalScript`).

## Soundness

* **0** `sorry` / **0** `admit` / **0** user-defined `axiom` / **0**
  `opaque` / **0** `constant` in the default build path
  (`lake build Project`, `lake build Project.validation`,
  `lake build Project.validation.Constructive`,
  `lake build Project.validation.Optimality`).
* All public mathematical endpoints depend only on the standard Lean
  / Mathlib axioms `{propext, Classical.choice, Quot.sound}` (with
  one outlier: `undoScript_length_single_cycle` depends on only
  `{propext, Quot.sound}`).
* `{Lean.ofReduceBool, Lean.trustCompiler}` appear only in two
  `native_decide`-discharged validation theorems
  (`Validation5.exists_perm4_cross_checked` and
  `Validation7BruteForceOptimality.bruteForceOptimality_Fin{3,4}`)
  and are isolated to those validation files.
* The Plausible-driven randomised stress in
  `Validation11_PlausibleStress.lean` is **opt-in** (not imported by
  any aggregate). The `plausible` tactic in Mathlib v4.23.0 closes a
  passing randomised goal with `sorry`, so V11 is built only via
  `lake build Project.validation.Constructive.Validation11_PlausibleStress`;
  it is documented and reachable but does not enter any default
  build target, keeping the rest of the codebase `sorry`-clean.

## Reading order

1. [docs/TripReport.md](docs/TripReport.md) — first-person narrative
   of how the development was actually built, including the war
   stories (the wrap-around bug, the orientation off-by-one, the
   `Fin 5` wall) and the AI-collaboration framing. Read this if you
   want the human side before the technical side.
2. [Project/README.md](Project/README.md) — code map.
3. [Project/PrisonerOfBenda.lean](Project/PrisonerOfBenda.lean) —
   one-page literate demonstration on an episode-inspired S6E10
   slice: 9 characters, 4-cycle + 3-cycle, restored by
   `optimalScript` in 11 swaps.
4. [Project/validation/optimality_summary.md](Project/validation/optimality_summary.md)
   — what the optimality side validates, in one page.
5. [Project/validation/paper_correspondence.md](Project/validation/paper_correspondence.md)
   — paper-to-Lean theorem-by-theorem mapping.
6. [Project/Futurama/Optimality/UpperBound.lean](Project/Futurama/Optimality/UpperBound.lean)
   — paper Theorem 1 construction λ + the central packaging
   (`futuramaTheorem1OfPerm` / `optimalRepairSeqOfPerm` /
   `futuramaTheorem1Full`).
7. [Project/Futurama/Optimality/LowerBound/Layer2.lean](Project/Futurama/Optimality/LowerBound/Layer2.lean)
   — the lower bound `t ≥ n + r + 2` and `futurama_optimal`.
8. [Project/Futurama/Optimality/Lemma1.lean](Project/Futurama/Optimality/Lemma1.lean)
   — Lemma 1(a)/(b)/(c).

## Out of scope

The following are **not** formalised here. They are paper-internal
extensions that build on the Lemma 1 family / parity theorem this
development already proves, and would be natural follow-ups:

* paper Theorem 2 (best possible algorithm for `P_1 := (12)(23)…(n−1,n)`,
  no helpers needed);
* paper Theorem 3 (best possible algorithm for `P_2 := (n,n−1)…(n,1)`,
  one helper needed);
* paper Theorem 4 (necessary and sufficient conditions for the
  identity to be expressible as a product of `m` distinct
  transpositions in `S_n`).

Single-helper / no-helper variants of the original Futurama Theorem
beyond the Keeler-gap remark are also out of scope.

## License

The repository is currently private for course submission. A
`LICENSE` file will be added (and a license selected — most likely
Apache-2.0 to match Mathlib) before the repository is made public.

The Lean formalisation in this repository is the author's original
work; the underlying mathematics is from Evans–Huang–Nguyen 2014
(cited above).
