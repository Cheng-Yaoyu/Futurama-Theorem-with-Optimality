import Project.TestProject
import Project.PrisonerOfBenda
import Project.validation

/-!
# Project — Futurama Theorem (with optimality)

Top-level root of the `Project` Lean library. Importing this module
pulls in the entire formalisation:

* the constructive Wikipedia / Futurama theorem and the
  parameterised cut family (transitively via `Project.TestProject`);
* paper Theorem 1 of Evans–Huang–Nguyen 2014 — the optimal
  `n + r + 2` upper-bound construction together with the universal
  lower bound (also via `Project.TestProject`);
* the Lemma 1 family and the Keeler-gap remarks;
* a literate reconstruction of the actual S6E10 episode chaos in
  `Project.PrisonerOfBenda` — the 4-cycle (Fry-Bender-Hermes-Zoidberg)
  plus the 3-cycle (Leela-Amy-Professor) restored by `optimalScript`
  in `n + r + 2 = 11` swaps;
* the validation suite — boolean validators, exhaustive small-case
  cross-semantics checks, axiom-baseline harnesses, the optional
  brute-force corroboration on `Fin 3` / `Fin 4`, and the
  large-cycle stress + Plausible randomized layer (via
  `Project.validation`).

`lake build Project` (the default target) builds everything. For
finer-grained targets see [`README.md`](README.md) and
[`Project/README.md`](Project/README.md).
-/
