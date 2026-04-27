# Theorem 1 / Lemma 1 — Paper ↔ Lean Correspondence

This document maps every paper-side object in Section 1, Theorem 1,
and Lemma 1 of Evans–Huang–Nguyen 2014 to its Lean counterpart. The
Lean counterparts live under `Project/Futurama/Optimality/*.lean`;
all names remain in the `Project.Futurama` namespace (not
`Project.Futurama.Optimality.X`) — the directory is module-path
organisation only. `import Project.TestProject` and
`import Project.Futurama` resolve every cited name via the aggregator.

The correspondence distinguishes **fully captured** rows from
**strictly weaker** / **half-public** / **parallel-track** rows so a
reader can see the precise status of each correspondence point.

The phrase "complete mapping" is deliberately avoided. Each row is
labelled with one of:

- **fully captured**: the Lean statement is paper-equivalent, modulo
  Mathlib idiom (e.g. `σ.IsCycle` instead of `2 ≤ k ≤ n`);
- **strictly weaker (proof-strong, statement-weak)**: the Lean public
  statement is weaker than the paper's, but the Lean proof reaches
  paper-strength;
- **half-public**: previously the API exposed only one side of a
  paper equality; the missing side is now exposed publicly;
- **parallel track**: the row is in the Lean development for
  paper-correspondence completeness, but is **not** consumed by the
  Theorem 1 optimality proof chain.

---

## 1. Paper Section 1 — ambient objects

| Paper object                                          | Lean declaration                                  | Status         |
| ----------------------------------------------------- | ------------------------------------------------- | -------------- |
| `S_n` (symmetric group on `n` elements)               | `Perm α` with `α` a `Fintype`                     | fully captured |
| `S_{n+2}` (`n+2`-element extension with helpers)      | `Perm (Body α)`, `Body α = α ⊕ helper_x ⊕ helper_y` | fully captured |
| `x := n + 1`, `y := n + 2`                            | `Body.x`, `Body.y`                                | fully captured |
| Inclusion `S_n ↪ S_{n+2}`                             | `liftPerm` (a `MonoidHom` via `liftPermHom`)      | fully captured |
| Permutation `P ∈ S_n`                                 | `σ : Perm α`                                      | fully captured |
| Cycle decomposition `P = C_1 ... C_r`                 | `factorCycles σ : List (Cycle α)` plus the four supporting theorems (`cycleProduct_factorCycles`, `factorCycles_pairwise_disjoint`, `factorCycles_length`, `factorCycles_membersLengthSum`) | fully captured |
| Total support size `n = k_1 + ... + k_r`              | `σ.support.card`                                  | fully captured |
| Number of cycles `r`                                  | `σ.cycleFactorsFinset.card` (= `(factorCycles σ).length`) | fully captured |
| Right-to-left composition convention                  | Lean's `*` for `Perm` satisfies `(f * g) z = f (g z)` | fully captured |
| Non-triviality assumption `P ≠ I`                     | `0 < σ.cycleFactorsFinset.card`                   | fully captured |

---

## 2. Paper Section 1 — Keeler's `σ` and the question

| Paper object                                                              | Lean declaration                                                   | Status         |
| ------------------------------------------------------------------------- | ------------------------------------------------------------------ | -------------- |
| Product `σ` of distinct transpositions, each containing `x` or `y`, undoing `P` | `RepairSeq` structure                                       | fully captured |
| "transposition factors" (the machine constraint of distinctness)          | `RepairSeq.distinct_pairs` field                                   | fully captured |
| "containing `x` or `y`"                                                   | `RepairSeq.helper_constraint` field (uses `UsesHelper`)            | fully captured |
| "`σ P = I`"                                                               | `RepairSeq.undoes` field (`runScript steps * π = 1`)               | fully captured |
| (implicit) "transposition is a 2-cycle on distinct elements"              | `RepairSeq.nontrivial` field                                       | strict additional structure (paper has it implicit; Lean lifts to explicit) |

---

## 3. Theorem 1 — the construction λ

| Paper object                                                                                            | Lean declaration                                                                                                                                            | Status         |
| ------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------- |
| Explicit construction λ (`n + r + 2` factors)                                                           | `optimalScript` (cycle-list level), `optimalScriptOfPerm` (`Perm α` level)                                                                                  | fully captured |
| `λ P = I`                                                                                               | `optimalScript_correct`, `optimalScriptOfPerm_correct`                                                                                                       | fully captured |
| "λ has exactly `n + r + 2` factors"                                                                     | `optimalScript_length`, `optimalScriptOfPerm_length`                                                                                                         | fully captured |
| "factors of λ are distinct"                                                                             | `optimalScript_nodup` (list-level Nodup) + `optimalScript_stepPairs_nodup` (unordered-pair-level Nodup)                                                      | fully captured |
| "each factor of λ contains an entry in `{x, y}`"                                                        | `optimalScript_usesHelper`                                                                                                                                   | fully captured |
| "(implicit) each factor is a genuine non-identity transposition"                                        | `optimalScript_nontrivial`                                                                                                                                   | fully captured (matches paper's implicit assumption explicitly) |
| Existence of λ as an object                                                                             | `optimalRepairSeqOfPerm σ hσ : RepairSeq (liftPerm σ)`                                                                                                       | fully captured |
| Single-declaration form bundling all six paper conjuncts                                                | `futuramaTheorem1Full σ hσ`: `∃ seq : RepairSeq (liftPerm σ), seq.steps.length = n+r+2 ∧ ∀ seq', seq.steps.length ≤ seq'.steps.length`. The `RepairSeq` structure carries correctness, helper inclusion, distinct unordered pairs, and nontriviality. | fully captured (single decl) |

### 3.1 Theorem 1 paper-equivalent **packaging**

Paper Theorem 1 asserts a *single* claim with several conjuncts:
correctness + length = `n + r + 2` + distinct + helper-included +
(implicit nontrivial) + best-possible.

Lean offers **two equivalent packagings** of the full claim:

#### 3.1.1 Single-declaration form

> `futuramaTheorem1Full σ hσ`

```text
∃ seq : RepairSeq (liftPerm σ),
  seq.steps.length = σ.support.card + σ.cycleFactorsFinset.card + 2 ∧
  ∀ seq' : RepairSeq (liftPerm σ), seq.steps.length ≤ seq'.steps.length
```

The existential witness is a `RepairSeq`, whose four fields already
carry correctness (`undoes`), distinct unordered pairs
(`distinct_pairs`), helper inclusion (`helper_constraint`), and
nontriviality of every step (`nontrivial`). The two extra conjuncts
add the exact length and the universal lower bound. Together,
this single statement captures all six conjuncts of paper Theorem 1.

This form is intended for external citation — a paper, a course
report, or a slide can reference one declaration name to mean
"paper Theorem 1 in Lean".

#### 3.1.2 Explicit-witness pair (kept for direct API use)

> `futuramaTheorem1OfPerm σ hσ` *together with* `optimalRepairSeqOfPerm σ hσ`.

- `futuramaTheorem1OfPerm` supplies correctness + exact length +
  ∀-lower-bound about the **concrete** `optimalScriptOfPerm σ`.
- `optimalRepairSeqOfPerm` supplies the `RepairSeq` witness with
  distinctness + helper-inclusion + nontriviality fields populated
  from the matching `optimalScript_*` lemmas.

This pair is useful when a downstream consumer wants to reference
the explicit witness `optimalScriptOfPerm σ` rather than just an
existentially quantified seq. Both packagings are available and
verifiably interchangeable.

---

## 4. Theorem 1 — "best possible" (lower bound)

| Paper claim                                                | Lean declaration                                                              | Status         |
| ---------------------------------------------------------- | ----------------------------------------------------------------------------- | -------------- |
| ∀ σ undoing `P` with constraints, `length(σ) ≥ n + r + 2`  | `futurama_optimal` (`Perm α` level), `optimalScriptOfPerm_isOptimal`, `repair_length_ge_optimal` (cycle-list level) | fully captured |
| Parity ingredient `t ≡ n + r (mod 2)`                       | `repair_length_parity` (public)                                               | fully captured |
| Entry-counting `t ≥ n`                                      | `repair_length_ge_entries` (public)                                            | fully captured |
| Strengthened entry-counting `t ≥ n + r`                     | `repair_length_ge_entries_add_cycles` (public)                                 | fully captured |
| Equality obstruction `t ≠ n + r`                            | `repair_length_ne_entries_add_cycles` (public)                                 | fully captured |

Note: the Lean lower-bound chain runs through the four
`repair_length_*` theorems above, closed by `omega`. It does **not**
go through Lemma 1. See Section 7.

---

## 5. Lemma 1 — the graph-theoretic facts about minimal factorisations

| Paper statement                                                                                              | Lean declaration                                                                                                          | Status         |
| ------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------- | -------------- |
| Lemma 1(a): k-cycle = product of `t` transpositions ⇒ `t ≥ k − 1`                                             | `transposition_count_ge_cycle_length`                                                                                     | fully captured (Mathlib idiom `σ.IsCycle` ↔ paper's `2 ≤ k ≤ n`) |
| Lemma 1(b): when `t = k − 1`, set of entries `W = V := {a_1, ..., a_k}` (cycle support)                       | Two-direction split:                                                                                                      |               |
| — `V ⊆ W` (trivial direction)                                                                                | `minimal_factorization_covers_support` (public, `~12`-line proof)                                                         | fully captured |
| — `W ⊆ V` (real content of Lemma 1(b))                                                                       | `minimal_factorization_factorEndpoints_mem_support` (public, ~110-line graph-theoretic proof)                             | fully captured |
| — `W ⊆ V` reformulated for `t = Equiv.swap a b` factors                                                      | `minimal_factorization_factorEntries_mem_support` (public, corollary)                                                     | fully captured |
| Lemma 1(c): when `t = k − 1`, at least one factor has form `(a_i a_{i+1})` with `1 ≤ i < k`                   | Two public theorems: `minimal_factorization_has_adjacent` (compatibility shape, allows wrap-around) and `minimal_factorization_has_adjacent_paper` (paper-strong form, exposes the `pre ++ [a, b] ++ suf` split) | fully captured (paper-strong form available) |

### 5.1 Lemma 1(c) paper-vs-Lean status

Two public theorems coexist:

- `minimal_factorization_has_adjacent` (kept for compatibility): the
  weaker conclusion `∃ t ∈ ts, ∃ a ∈ σ.support, t = swap a (σ a)`,
  which permits `a = a_k` (the wrap-around case `σ a_k = a_1`,
  giving `swap a_k a_1`). Useful when the consumer only needs the
  `swap a (σ a)` shape.
- `minimal_factorization_has_adjacent_paper`: the paper-strong
  conclusion

  ```
  ∃ t ∈ ts, ∃ l : List α, ∃ pre suf : List α, ∃ a b : α,
    l.Nodup ∧ l.formPerm = σ ∧ l = pre ++ [a, b] ++ suf ∧ t = swap a b
  ```

  The split shape `pre ++ [a, b] ++ suf` **automatically excludes the
  wrap-around**: a wrap-around factor would need `a` at the end of `l`
  and `b` at the start, which cannot fit a single `[a, b]` adjacency.
  So the public statement now captures paper Lemma 1(c)'s "1 ≤ i < k"
  exclusion exactly.

Both theorems are derived from the same underlying graph argument
via the internal helper `minimal_factorization_has_adjacent_formPerm`.
The weak form is kept for compatibility, but the **paper-strong form
is the one to cite for Lemma 1(c)**: the weak form's conclusion
permits wrap-around (`swap a_k a_1`) and so does not by itself state
the paper claim. The paper-strong form's `pre ++ [a, b] ++ suf` split
makes the wrap-around exclusion structural.

This row is **fully captured**. Both theorems stay on Class I axioms.

---

## 6. The `cyclePerm c` orientation

| Paper convention                                                           | Lean equivalent                                                                                                            |
| -------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------- |
| Cycle `(a_1, ..., a_k)` sends `a_1 ↦ a_2 ↦ ... ↦ a_k ↦ a_1`               | `cyclePerm c` is the **inverse** of paper's cycle when reading `c.first / c.tail` directly: `cyclePermAux first tail = (orig (first :: tail)).reverse.formPerm` |
| Construction of a Lean `Cycle` from a Mathlib cycle `σ : Perm α`           | `cycleFromPerm σ hσ` uses `σ.toList (cycleSeed σ hσ)` (which lists `cycleSeed`, `σ cycleSeed`, ...) then *reverses* via `cycleFromList`. Net: `c.members` = some rotation of `[a_k, a_{k-1}, ..., a_1]`, with the rotation determined by `cycleSeed`. |

### 6.1 Index dictionary (term-by-term match for the `optimalScript` formula)

When the paper writes `(a_1, ..., a_k)` so that paper's `σ` equals
Lean's `cyclePerm c`, the dictionary is:

| paper       | Lean                                          |
| ----------- | --------------------------------------------- |
| `a_1`       | `c.first`                                     |
| `a_2`       | `c.rest.getLast` (last of `c.rest`)           |
| `a_3`       | `c.rest` second-to-last                       |
| ...         | ...                                           |
| `a_{k-1}`   | `c.rest.head`                                 |
| `a_k`       | `c.second`                                    |

Equivalently: paper's `(a_1, a_2, ..., a_{k-1}, a_k)` is Lean's
`(c.first, reverse(c.rest)..., c.second)`.

Specialised entries used by the `optimalScript [c]` formula
(applied left-to-right by `runScript`, mirror of paper's λ written
right-to-left):

| paper symbol     | Lean expression                                                  |
| ---------------- | ---------------------------------------------------------------- |
| `(a_1 x)`        | `(Body.x, Body.orig c.first)` — leadBlock head step              |
| `(a_k x)`        | `(Body.x, Body.orig c.second)` — leadBlock tail step             |
| `G_1(y)`         | gyBlock for `c`: `[(y, a) | a ∈ c.tail] ++ [(y, c.first)]`       |
| `(xy)`           | `(Body.x, Body.y)` — trailing helper-swap                        |

Verified at `k = 3` and `k = 4` by hand-unfolding `optimalScript [c]`
against paper's λ. A naive `a_i ↔ c.members[i]` mapping is **wrong**
for any `k ≥ 3`.

### 6.2 `σ` in Lemma 1(c) is NOT `cyclePerm c`

Lemma 1(c)'s `σ : Perm α` is the **Mathlib-native** cycle, not
`cyclePerm c`. So Lemma 1(c) does **not** depend on the orientation
issue above. A reader who has just finished Section 6.1's
reverse-plus-rotation dictionary should NOT apply that dictionary to
Lemma 1(c).

---

## 7. Track separation: Lemma 1 vs Theorem 1 lower-bound chain

| Track                                  | Lean theorems                                                                                       | Used by Theorem 1's optimality proof? |
| -------------------------------------- | --------------------------------------------------------------------------------------------------- | -------------------------------------- |
| Track A — Lemma 1 family               | `transposition_count_ge_cycle_length`, `minimal_factorization_covers_support`, `minimal_factorization_factorEndpoints_mem_support`, `minimal_factorization_factorEntries_mem_support`, `minimal_factorization_has_adjacent` | NO — parallel paper-faithful track    |
| Track B — entry-counting + parity      | `repair_length_ge_entries`, `repair_length_ge_entries_add_cycles`, `repair_length_parity`, `repair_length_ne_entries_add_cycles` | YES — the actual proof path used by `repair_length_ge_optimal` and `futurama_optimal` |

The independence of these two tracks matters because the actual
optimality proof path (Track B) does not transitively depend on the
Lemma 1 family (Track A). This is recorded here so the correspondence
document is self-contained.

---

## 8. Section 1 remarks — Keeler's σ optimality cases

Paper p.138 remark: "Keeler's algorithm is optimal for `r = 1` and
`r = 2`, but for no other `r`."

| Sub-case                                  | Lean coverage                                                                                                                                                                                    | Status                                |
| ----------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------- |
| `r = 1` (paper: Keeler is optimal)        | `keeler_optimal_single_cycle`: `∀ c : Cycle α, (undoScript [c]).length = (optimalScript [c]).length`. Both sides closed-form `c.members.length + 3 = n + r + 2`, given by `undoScript_length_single_cycle` and `optimalScript_length_single_cycle`. | fully captured (theorem-level)        |
| `r = 2` (paper: Keeler is optimal)        | `keeler_achieves_and_gap` evaluates to gap `(2 - 2) + (2 % 2 = 0 → 0) = 0`. Keeler equals optimum.                                                                                                | fully captured (theorem-level)        |
| `r ≥ 3` (paper: Keeler is NOT optimal)    | `keeler_achieves_and_gap` gives gap `(r - 2) + parity > 0`. Examples: `r = 3 → 2`, `r = 4 → 2`, `r = 5 → 4`. Matches paper's `2r - (r + 2)` formula up to parity correction.                      | fully captured (theorem-level)        |

---

## 9. Statement-level rows

The statement-level correspondence captures:

- paper Theorem 1's full claim ↔ Lean's minimal set
  (`futuramaTheorem1OfPerm` + `optimalRepairSeqOfPerm`);
- the `P ≠ I` hypothesis ↔ `0 < σ.cycleFactorsFinset.card`;
- the universal lower bound ↔ `∀ seq : RepairSeq`-quantification.

### 9.1 Paper Theorem 1's six conjuncts ↔ Lean theorems

| Paper conjunct | Lean theorem(s) | Status |
| -------------- | --------------- | ------ |
| `λ P = I` | first conjunct of `futuramaTheorem1OfPerm`, `optimalScript_correct`, `optimalScriptOfPerm_correct` | fully captured |
| `λ has exactly n + r + 2 factors` | second conjunct of `futuramaTheorem1OfPerm`, `optimalScript_length`, `optimalScriptOfPerm_length` | fully captured |
| each factor of λ contains an entry in `{x, y}` | `optimalScript_usesHelper`, used as `helper_constraint` field of `optimalRepairSeqOfPerm` | fully captured |
| factors of λ are distinct | `optimalScript_nodup` (list-level), `optimalScript_stepPairs_nodup` (unordered-pair-level), used as `distinct_pairs` field of `optimalRepairSeqOfPerm` | fully captured |
| (implicit) each factor is a non-identity transposition | `optimalScript_nontrivial`, used as `nontrivial` field of `optimalRepairSeqOfPerm` | fully captured (paper has it implicit; Lean explicit) |
| `n + r + 2` is best possible | third conjunct of `futuramaTheorem1OfPerm` (∀ seq : RepairSeq, length ≤ ...), `optimalScriptOfPerm_isOptimal`, `futurama_optimal`, `repair_length_ge_optimal` | fully captured |

### 9.2 Hypothesis row

| Paper hypothesis | Lean hypothesis | Status |
| ---------------- | --------------- | ------ |
| "P ≠ I" / "non-trivial permutation" | `0 < σ.cycleFactorsFinset.card` | fully captured (`σ = 1 ⇔ σ.cycleFactorsFinset.card = 0`) |
