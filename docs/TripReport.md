# Trip Report: Formalising Paper Theorem 1, Phase by Phase

*A first-person account of building a Lean 4 formalisation of
Evans–Huang–Nguyen 2014's "Keeler's Theorem and Products of Distinct
Transpositions" — from a hand-written skeleton through five phases
of increasing AI delegation.*

---

## The headline

**13,800 lines of kernel proof plus 2,200 lines of executable
validation, about a month of part-time work, paper Theorem 1 with
the full $n + r + 2$ lower bound — built phase-by-phase from a
hand-written sub-lemma skeleton.** The two AI tools that did the
proof-side work, with very different roles in different phases:

- **Codex** running on **GPT-5.4 xhigh** — the proof-side workhorse.
  In the constructive layer it was a Mathlib search engine and a
  stuck-proof unsticker (proofs themselves were mostly hand-written).
  In the optimality chain it filled in proof bodies under our
  pre-written sub-lemma skeleton, with each block reviewed and a
  substantial fraction rewritten on review.
- **Claude Code** running on **Opus 4.6 → 4.7** — the agentic
  workhorse. It drafted the validation suite (V2–V11 plus the
  axiom-baseline harnesses) under high-level instructions, executed
  the late-stage file refactor, and drafted the cross-document
  prose (module docstrings, READMEs, the validation summaries, the
  paper-correspondence document) under high-level prompts.[^pace]

The default `lake build Project` succeeds in 1244 jobs with **zero
`sorry` warnings**, every kernel theorem depends only on
`{propext, Classical.choice, Quot.sound}`, and the brute-force
corroboration on `Fin 3, Fin 4` runs in about 38 seconds on commodity
hardware.

This file is the human-readable counterpart of the academic course
report (submitted separately as a PDF). The course report is the
formal artefact; this is the story of how it got there: the five
phases of the work, the bugs Lean caught that the paper hides, the
moments AI got stuck and we had to step in, and the specific division
of labour we settled on at each phase.

[^pace]: Calendar elapsed; total full-time-equivalent effort,
    weekends included, was roughly 3–4 weeks of focused work. Without
    AI assistance — specifically without Codex as a Mathlib search
    engine in Phase 2 and as a proof-body completion engine in
    Phase 3 — we estimate the same development would have taken us
    4–5 months. Layer 1 alone (the doubling argument, ~5,100 lines
    of densely interconnected private lemmas) would have been a
    semester project on its own.

---

## Phase 1: The skeleton (by hand, with AI as sounding board)

The first thing we wrote was the module skeleton — `Body α`,
`Cycle α`, `runScript`, `cyclePerm`, `repairScript`, then the
dependency graph for `cycleProduct`, `repairProduct`, `liftPerm`,
`factorCycles`, and the named endpoints `futuramaTheorem`,
`futuramaTheoremOfPerm`, `optimalScript`, `futurama_optimal`,
`futuramaTheorem1Full`. Every theorem was stated with `sorry` as the
proof body so the dependency graph type-checked end-to-end before
any real proving started. Sub-lemmas got the same treatment: their
statements went in, the `sorry` placeholder kept the build green,
and we worked depth-first one branch at a time.

The architectural decisions all landed in this phase:

- **`Body α := α ⊕ {x, y}`** as the helper-extended state space, with
  helpers structurally distinct from original elements (rather than
  the comparison project's `x y : α` with `x ∉ σ.support`
  hypothesis — which is simpler but breaks if `α` has no spare
  elements);
- **`Cycle α`** as a structure with explicit `first, second, rest,
  nodup` fields rather than a `List α`-with-hypothesis pattern, so
  the length ≥ 2 invariant is proof-carrying data;
- **two-track separation** between Lemma 1 (graph-theoretic) and
  the entry-counting + parity lower-bound chain — mirroring how the
  paper itself organises Theorems 1 and 2/3;
- **`RepairSeq` (adversary surface, for $\forall$-quantification in
  the lower bound) vs `RepairSpec` (constructor surface, for the
  upper bound's $\exists$ packaging)** as two distinct types rather
  than one;
- **layered upper bound construction**: `firstYStep` → `gyBlock` →
  `leadBlock` → `coreOptimalScript` → `optimalScript`, each a
  private `def` of one expression, so each layer can be reasoned
  about independently and the build can be guarded by a 9-line
  `example := rfl` regression harness against future drift.

These commitments were the team's, but we used AI as a sounding
board throughout. The pattern was: we'd describe a proposed module
breakdown or sub-lemma graph and ask Codex whether the structure was
reasonable, whether a more idiomatic Mathlib pattern existed, or
whether a particular sub-lemma was strictly necessary. Codex would
push back with critique — sometimes pointing at a Mathlib structure
we hadn't considered (`Equiv.Perm.cycleFactorsFinset` rather than
rolling our own), sometimes flagging a sub-lemma as redundant given
others in the graph. We took its feedback when it improved the
design, and ignored it when our paper-driven judgment said
otherwise. The skeleton was 95% ours; the 5% AI advisory share was
in the trim, not the spine.

---

## Phase 2: The constructive theorem (mostly hand + Codex as a Mathlib search engine)

The constructive layer — the "Wikipedia / Keeler" theorem that
*some* helper-containing distinct-transposition repair script always
exists — was where the bulk of the early proof grind happened. About
4,000 lines of Lean covering single-cycle repair (`runScript`,
`repairScript`, `repairPerm`), multi-cycle composition
(`cycleProduct`, `undoScript`, `repairProduct`, `residualPerm`), the
bridge to arbitrary `Perm α` via `liftPerm` and `factorCycles`, the
parameterised cut family (`repairScriptAt`, `CutSchedule`), and the
strongest external-spec packaging (`futuramaTheoremOfPermStrong*`).

We wrote almost all of this by hand. The pattern was: open the
file, look at the next `sorry`, write the proof. The friction
wasn't in the mathematical reasoning — most of these proofs are
short — it was in **finding the right Mathlib lemma**. Mathlib's
`GroupTheory.Perm.*` is enormous and not always discoverable; we
knew "there has to be a lemma that says `cycleFactorsFinset`
decomposes the support into a disjoint union of cycle supports",
but finding it was another matter.

This is where Codex (GPT-5.4 xhigh) earned its keep. Our usage
pattern:

- We'd describe the lemma we needed in informal English ("we need
  a Mathlib fact that says if `σ` is a cycle and `a ∈ σ.support`,
  then `σ a ∈ σ.support` too").
- Codex would suggest 2–4 candidate lemma names from Mathlib.
- We'd grep for them, read the actual Mathlib statement, and use
  the one that fit.

The hit rate was probably 60–70% — Codex was right about the
*shape* of the lemma we needed but often wrong about the exact
name or hypothesis order. This is normal for an LLM that has
Mathlib in its training data but doesn't have today's Mathlib state
mirrored.

The other thing Codex did well in Phase 2: when a `simp` chain or
an `omega` call refused to close, we could paste the goal state and
ask "what's missing from the simp set". Most of the time the
answer was a routine bridge lemma we'd skipped. Maybe a quarter of
those bridge lemmas were already in Mathlib; the rest we wrote
inline.

What Codex was *not* doing in Phase 2: writing whole proofs. The
proofs were ours; Codex was a search engine and a stuck-proof
unsticker. The constructive layer's load-bearing arguments (the
`cycleProduct_factorCycles` bridge, `undoScript_correct`,
`futuramaTheoremOfPermStrong`) all read like proofs a human wrote,
because they are.

---

## Phase 3: Optimality (hand-written skeleton, Codex-completed bodies, block-by-block review)

By the time the constructive layer was done, we had ~4,000 lines of
working Lean as a stylistic and architectural template. The
optimality work — Layer 0 ($t \geq n$), Layer 1 ($t \geq n + r$),
Layer 2 ($t \geq n + r + 2$), the upper bound construction, and the
Lemma 1 family — followed the same skeleton-first discipline. Every
file started with the high-level theorem statements wrapped in
`sorry`, every lemma we knew we'd need was stubbed before any
proving began, and the dependency graph type-checked end-to-end
before filling started.

This is the phase where we changed the AI workflow.

The constructive layer had taught us what proof patterns Lean
expected for this domain: the `runScript` chase, the
`omit [DecidableEq α] [Fintype α] in` annotations on
`Type*`-polymorphic lemmas, the `simp only` call chains that close
a length-arithmetic goal in three lines. Once these patterns were
codified in 4,000 lines of working Lean, **we could let Codex
generate proof bodies** under our skeleton, with our reference code
visible to it as context. The pattern was:

1. We write the skeleton and the theorem statement.
2. We sketch the proof in informal English in a comment.
3. We show Codex the existing constructive proofs that follow the
   same shape.
4. Codex generates a candidate proof body.
5. We read the proof block-by-block, run the build, and either
   accept or rewrite.

Most blocks landed on the second or third iteration. **This is how
Layer 1 got to 5,100 lines without taking a semester.** Layer 1's
combinatorial argument — the doubling argument that says each
cycle forces at least one of its elements to be paired with both
helpers $x$ and $y$ — is densely interconnected (about 120 private
lemmas threading the `xStepFor` / `yStepFor` predicates, an
`xy_split` decomposition, and a `minGapCycle` minimisation), but
the *shape* of each individual lemma is repetitive: "given the
rightmost step that touches element $a$, do a case-analysis on
whether the previous step was an $x$-step or a $y$-step, then chase
what `runScript` does to $a$ in each case".

That is exactly the kind of pattern AI completes well. We wrote
the high-level decomposition (the `xy_split` strategy was ours,
after two earlier attempts that ran into combinatorial blow-up),
we stubbed the 120 private lemma statements, and Codex filled in
the bodies under review. Roughly half of Layer 1's 5,100 lines
were filled in by Codex on the second pass; the rest came from
places where Codex's suggestion was wrong and we had to rewrite,
places where we wrote the proof first because the case analysis
needed a specific order Codex couldn't infer, and the substantial
fraction of "filled in" lines that we ended up rewriting after
review found a subtle mismatch with the rest of the chain.

Layer 0 and Layer 2 were the same workflow at smaller scale. The
upper-bound construction in `UpperBound.lean` was more
hand-written — the layered block hierarchy
(`firstYStep` / `gyBlock` / `leadBlock`) needed to be set up
precisely so the `example := rfl` regression harness at the bottom
of the file would close, and that's not a workflow Codex is good
at. But the *correctness* lemmas about the layered blocks
(`optimalScript_usesHelper`, `optimalScript_nontrivial`,
`optimalScript_stepPairs_nodup`) were the same skeleton-stub-fill
pattern as Layer 1.

---

## The wrap-around bug, or: how our own natural Lean phrasing turned out to be too weak

This is the single biggest "the formalisation revealed something
the prose hides" moment of the project, and it happened entirely
on the human side of the workflow. The relevant paper claim is
Lemma 1(c):

> If a $k$-cycle $\sigma$ equals a product of exactly $k - 1$
> transpositions, then at least one of those transpositions has
> the form $(a_i, a_{i+1})$ with $1 \leq i < k$.

The natural Lean translation, which is what we wrote first, reads:

```lean
∃ t ∈ ts, ∃ a ∈ σ.support, t = Equiv.swap a (σ a)
```

Lean happily proved this. We happily moved on.

The bug is that this statement is **strictly weaker** than the
paper. For $\sigma = (a_1, \ldots, a_k)$ in standard cycle notation,
$\sigma(a_k) = a_1$, so `Equiv.swap a_k (σ a_k) = Equiv.swap a_k a_1`
is a wrap-around transposition — exactly the case the paper's
"$1 \leq i < k$" condition rules out.

We caught this only because we were working on
`paper_correspondence.md` in a separate document-level audit pass,
with our eyes deliberately open for this kind of slack. The fix
was to expose the cycle's underlying list explicitly:

```lean
∃ t ∈ ts, ∃ l : List α, ∃ pre suf : List α, ∃ a b : α,
  l.Nodup ∧ l.formPerm = σ ∧ l = pre ++ [a, b] ++ suf ∧
  t = Equiv.swap a b
```

The split shape `pre ++ [a, b] ++ suf` makes wrap-around
structurally impossible: $a_k$ cannot simultaneously be at the end
of `pre` and $a_1$ at the start of `suf` while also forming a
single `[a, b]` adjacency.

Both forms now coexist as public theorems
(`minimal_factorization_has_adjacent` and
`minimal_factorization_has_adjacent_paper`), both proven from the
same internal helper, both Class I clean.

The lesson: "match the paper" is a continuous discipline, not a
one-time intent. The natural translation of an English mathematical
sentence into Lean almost never preserves a quantifier scope
restriction like "$1 \leq i < k$" — the restriction lives in the
prose, not in the symbol manipulation. Without a paper-correspondence
audit pass, this kind of slack is invisible. After this incident
we formalised the audit as a row-by-row document at
[`Project/validation/paper_correspondence.md`](../Project/validation/paper_correspondence.md)
(~280 lines) with explicit status labels: *fully captured*,
*strictly weaker*, *half-public*, *parallel track*.

---

## The orientation gotcha

The other "wait, what?" moment came from a sanity check. The
cycle $(1\,2\,3)$ on `Fin 3` has $n = 3$, $r = 1$, optimal length
$3 + 1 + 2 = 6$. We instantiated `optimalScript` on the obvious
Lean representation of this cycle and got a script of length
**7**. Off by one.

Three days of staring at `cyclePerm` and the layered block
hierarchy later, we tracked it back to a single sign-error in our
mental model of the `Cycle` structure. Mathlib's `List.formPerm`
sends $a_1 \mapsto a_2 \mapsto \cdots \mapsto a_k \mapsto a_1$. Our
`cyclePerm c` is built via
`(orig (first :: tail)).reverse.formPerm` — which is the
**inverse** of the paper's standard cycle notation.

The dictionary turned out to be:
- $a_1 \leftrightarrow$ `c.first`
- $a_k \leftrightarrow$ `c.second` (yes, `second`, not `last`)
- $a_i \leftrightarrow$ `c.rest[k - 1 - i]` for the middle positions

Not the naive $a_i \leftrightarrow$ `c.members[i]` mapping a
spectator would expect. This is now §6 of
`paper_correspondence.md`, with worked examples at $k = 3$ and
$k = 4$.

This is the kind of bug AI assistance is *bad* at, by the way.
Codex's mental model of the `Cycle` structure was the same as
ours — it formed it from the same docstrings — so it confidently
generated proofs that propagated our orientation mistake forward.
The fix only landed once we asked Codex specifically to compare
the paper's $a_i$ symbols against the literal output of
`optimalScript [c]` for $k = 3$ and $k = 4$. That phrasing forced
the comparison out of "lean on the docstring" mode and into
"compare two concrete artefacts" mode, which is something LLMs do
reliably. Catching subtle convention mismatches like this is a
place where the human, the team, has to know what question to ask.

---

## The wall at $\textsf{Fin}\,5$

`Validation7_BruteForceOptimality.lean` exhaustively enumerates
every distinct-helper-containing script of length less than
$n + r + 2$ on `Fin 3` and `Fin 4` and verifies that none undoes
any non-trivial $\sigma$. About $10^5$ candidates at `Fin 4`,
~38 seconds via `native_decide`. This is a concordance check on
the kernel proof's universal lower bound — useful as an
independent witness that the kernel says what we think it says.

Going to `Fin 5` is intractable. The candidate space is
~$5 \cdot 10^8$, and `native_decide` on this size has to compile a
single boolean expression that exceeds 16 GB of RAM during
compilation. We let it run twice on an M4 mini; both times it
OOM-killed at about 31 minutes, before producing any output.

We documented this in `Validation8_Fin5Stress.lean` (the
theorem-level instantiation at `Fin 5` is fast and is kept active;
the brute-force `native_decide` calls in Sections 4–6 are
commented out with per-section time estimates). The kernel proof
`futurama_optimal` already covers all $n$ universally, so the
`Fin 5` corroboration is not needed for soundness — it is just
corroboration we cannot afford on this hardware.

---

## Phase 4: Validation (agentic, under high-level instructions)

The validation suite — V2 through V11, plus three axiom-baseline
harnesses — is roughly 2,200 lines. Test code is mechanical and
repetitive enough that we ran this phase very differently. We gave
Claude Code and Codex significantly higher autonomy here; our
instructions were at the strategy level rather than the proof
level:

- *"V5: exhaustive cross-semantics on `Fin 4`. Define a second
  executable semantics over a `BodyState` simulator, and verify
  it agrees with `runScript` at every prefix of every cut
  schedule's output."*
- *"V9: anti-tests for the boolean validators in V6. Feed each
  validator a battery of deliberately bad inputs — identity
  script, length-$(n + r + 1)$ script, duplicate pair,
  helper-missing, self-swap, wrong target, length-sensitivity —
  and confirm every one of them returns `false`."*

The agent would draft a complete file, the build would either
pass or surface specific failures, and we'd read the validation
runs to decide whether the coverage was real or whether we needed
to ask for additional cases. The most common follow-up was *"this
validator covers the happy path on three cycle structures; add
the two-disjoint-2-cycles and three-disjoint-2-cycles cases for
V6, and add the negative controls for V9"*.

This phase is also where the Plausible mistake happened. We asked
the agent to add a Plausible-driven randomised property test for
V10, not realising that Mathlib v4.23.0's `plausible` tactic
closes a passing randomised goal with `sorry` rather than
synthesising a kernel proof. The default `lake build Project`
started emitting a `declaration uses 'sorry'` warning, which
contradicted the README's "0 sorry" claim. Caught on a self-review
pass; fixed by pulling the Plausible test out into a separate
opt-in file (`Validation11_PlausibleStress.lean`) not imported by
any aggregate. About 30 minutes of cleanup. The lesson: when you
delegate a phase agentically, you also have to delegate the
*quality bar*, not just the task — but the quality bar still has
to be your call.

---

## Phase 5: Refactor and migration (Claude Code as a file-management agent)

By the end of Phase 4 the file structure had grown organically
and was no longer crisp. Layer 0/1/2 were inside a single
`LowerBound.lean`, which was approaching 8,000 lines and was a
chore to navigate. The original `Tier-A` / `Tier-1` naming
convention had leaked into many module docstrings as process
metadata. Some imports were vestigial.

This is when Claude Code took over as the file-management agent.
Its job was mechanical reorganisation:

- splitting `LowerBound.lean` into `Layer0.lean` / `Layer1.lean` /
  `Layer2.lean` along the natural argument boundaries;
- lifting `RepairSeq` and the `Optimality` aggregate into their
  own files;
- a docstring pass to remove process-trace metadata
  (`Phase 1`/`Phase 2`/`Phase O`/`Tier-A` / `Round P2.X`) and
  replace it with content-driven section headings (`Constructive
  theorem layer`, `Shared RepairSpec interface layer`, etc.);
- drafting the cross-document summaries
  (`constructive_summary.md`, `optimality_summary.md`,
  `paper_correspondence.md`) and the README hierarchy under
  high-level prompts;
- a separate migration round to lift the development out of the
  CS5232 course environment (which had been hosting it alongside
  `LoVe`, `PraVDA`, `Loom`, `Veil`, `Ssreflect`) into a standalone
  Mathlib-only repository, dropping ~3,700 lines of refactor
  scaffolding (an alternative `RepairSpec`-based proof line that
  had been parallel during an earlier refactor round) and ~30 plan
  documents.

The build job count dropped from ~2,065 to 1,244 — a 40% reduction
in dependency resolution work, mostly from no longer pulling in
the Verse-Lab tactic libraries (Loom, Veil, Auto, Ssreflect). The
`set_option loom.semantics.*` lines turned out to be vestigial
(they configure a tactic the development never invoked), so they
came out along with the imports.

This is the phase Claude Code is unambiguously good at. File-level
reorganisation is mechanical, large-scale, easy to verify (does it
still build?), and tedious by hand. We provided the architectural
decisions (what to split, what to keep, what to drop); Claude Code
executed them. The same delegation extended to the
**documentation pass that runs alongside refactor**: module
docstrings, README sections, the validation summaries, and the
paper-correspondence document were all drafted by Claude Code under
high-level prompts and revised against our review notes.
Documentation drafting is a place AI is genuinely productive — the
shape of a Mathlib-style module docstring is highly stylised, and
once the audience and the key claims are pinned down, the prose
fills in mechanically. We kept editorial control on every paragraph
(some passages we rewrote entirely when the AI draft mis-stated the
math), but the volume of documentation in this repository would be
maybe a fifth of what it is without that delegation.

---

## The parallel work

In the middle of the cleanup phase we discovered that **five
months earlier**, Mike Dodds had published a Lean 4
formalisation of the same theorem in a similar project name space
(`FuturamaTheoremLean`, BSD-3, GitHub).[^dodds] Their development
is about 3,400 lines of Lean and proves the constructive Keeler
theorem through a clean four-phase decomposition. They use
`Sym2 α` for unordered transpositions (more idiomatic Mathlib),
they use `x y : α` with `x ∉ σ.support` as helpers (simpler when
$\alpha$ has spare elements), and they have a
[TripReport.md](https://github.com/anthropics/FuturamaTheoremLean/blob/main/docs/TripReport.md)
that we cribbed the structure of for this very file.

The crucial difference: their `OptimalityTheorems.lean` is
explicitly a stub.

```lean
theorem optimal_lower_bound ... :
    seq.length ≥ optimalTranspositionCount σ := by
  sorry

theorem optimal_achievable ... :
    ∃ seq, seq.length = optimalTranspositionCount σ := by
  sorry
```

Their docstring is honest about why: *"Proving optimal_achievable
requires implementing Evans's different algorithm, which is NOT
the same as Keeler's."* This is exactly the work that fills the
rest of this development. The lower bound chain (Layers 0–2,
~6,800 lines), Lemma 1 (~1,300 lines), the optimal upper bound
construction `optimalScript` (~1,000 lines), the bundling into
`futuramaTheorem1OfPerm` and `futuramaTheorem1Full`, and the
Keeler-gap remark for all $r \geq 1$ are all on the optimality
side that they did not attempt.

This is good. Independent formalisation of overlapping content is
exactly how the field is supposed to grow. The fact that we
agreed on the constructive theorem in the
`Sym2`-vs-`Body × Body` and `x ∉ support`-vs-`Body α`
representation choices, while reaching the same kernel-clean
conclusion, is mild but real corroboration that both
formalisations got the constructive part right.

[^dodds]: The Dodds–Claude project is also AI-assisted, and their
    TripReport is openly framed that way ("vibe-coded with
    Claude"). Reading it earlier in the project would have saved
    us time on the constructive layer; reading it after made it
    obvious that the optimality work is where the unique
    contribution sits.

---

## Where AI fit, by phase

By the end we had a clear picture of where AI assistance was a
multiplier and where it wasn't. Writing it out by phase:

| Phase | What AI did | What we did | Roughly, the human/AI split |
|---|---|---|---|
| 1. Skeleton | Codex as sounding board: evaluate proposed module breakdowns, suggest more idiomatic Mathlib patterns, flag redundant sub-lemmas. | Hand-write modules, sub-lemma graph, stub statements with `sorry`; final architectural calls. | ~95% / 5% |
| 2. Constructive | Codex as Mathlib search engine; suggest lemma names; propose missing bridge lemmas when `simp` got stuck. | Hand-write proof bodies; verify lemma names; integrate bridges. | ~80% / 20% |
| 3. Optimality | Codex completes proof bodies under our skeleton, with the existing constructive proofs as visible context. | Write skeleton; sketch each proof in English in a comment; review every block; rewrite a substantial share of Codex's drafts. | ~50% / 50% |
| 4. Validation | Claude Code / Codex agentically draft V2–V11 + axiom-baseline harnesses under high-level instructions. | Write the high-level instructions; analyse validation runs; ask for additional necessary coverage; catch the Plausible `sorry` mistake. | ~30% / 70% |
| 5. Refactor + migration | Claude Code executes file splits, docstring rewrites, dependency cleanup. | Decide what to split, what to keep, what to drop; spot-check every rewritten docstring against the actual code. | ~20% / 80% |
| (Cross-cutting) Documentation | Claude Code drafts module docstrings, README sections, and the cross-document summaries (`constructive_summary.md`, `optimality_summary.md`, `paper_correspondence.md`) under high-level prompts; revises in response to inline review notes. | Define the audience, the structure, and the key claims for each document; review every paragraph; rewrite passages that mis-state the math. | ~30% / 70% |

The split column reads "human percentage / AI percentage" of the
*line-count contribution*, weighted very roughly by file size.
The architectural decisions are 100% human in every phase; the
proof line-count contribution shifts toward AI as the patterns
codify and the work becomes more mechanical.

What we had to drive personally, across all five phases:

- the choice of `RepairSeq` (adversary surface) vs `RepairSpec`
  (constructor surface) as two distinct types;
- the two-track separation between Lemma 1 (graph-theoretic) and
  the entry-counting + parity lower bound chain — mirroring how
  the paper itself organises Theorems 1 and 2/3;
- the layered `private def firstYStep / gyBlock / leadBlock /
  coreOptimalScript / optimalScript` block hierarchy in the
  upper bound, with the embedded 9-line `example := rfl`
  regression guard;
- the `xy_split` strategy for Layer 1 (the third decomposition we
  tried; the first two ran into combinatorial blow-up);
- the orientation diagnosis (Codex's mental model of `Cycle` was
  identical to ours, so the off-by-one was invisible until we
  asked it to compare against a concrete output);
- the wrap-around catch for Lemma 1(c) (entirely a
  paper-correspondence audit catch; Codex would never have asked
  the question);
- the migration architecture decisions — what to drop, what to
  keep, when to stop;
- and this report.

Prof. Sergey puts it well in the closing
"What this all means for the future of PL research?" section of
[*Verifying Move Borrow Checker in Lean*](https://proofsandintuitions.net/2026/03/18/move-borrow-checker-lean/):[^sergey-move]

> *The creative work—designing logics and type systems, choosing
> the right semantics, figuring out non-standard proof
> strategies—still belongs to humans. The tedium—threading a new
> invariant clause through 153 lemmas, or proving that removing a
> key from an [sic] key-value map preserves some property of the
> remaining entries—is exactly what AI handles well. This is a
> good trade.*

We think that's about right.

[^sergey-move]: Ilya Sergey, *Verifying Move Borrow Checker in
    Lean: An AI-Assisted Adventure in PL Metatheory*,
    `proofsandintuitions.net`, 18 March 2026. Full text:
    <https://proofsandintuitions.net/2026/03/18/move-borrow-checker-lean/>.

---

## Honest failure modes

A few specific places AI assistance got it wrong, and what we
had to do about it:

- **Codex's Mathlib name suggestions, Phase 2.** Hit rate
  ~60–70%. Often right about the *shape* of the lemma we needed,
  often wrong about the exact name or hypothesis order. Always
  cross-check against actual Mathlib before using.

- **Codex over-pattern-matching, Phase 3.** Once Codex had seen
  enough Layer 1 lemmas in the same shape, it would auto-suggest
  the same proof body for new lemmas where the case-analysis
  needed a different order. About a third of Layer 1's Codex
  drafts were wrong on the first attempt this way. The
  block-by-block review is non-negotiable — you cannot ship the
  output of an LLM proof generator without reading every block.

- **The Plausible `sorry` discharge, Phase 4.** Discussed above.
  The agent did exactly what we asked; the problem is that we
  asked for the wrong thing because we didn't know Mathlib's
  `plausible` closes with `sorry`. About 30 minutes of cleanup
  to pull V11 out into an opt-in file.

- **The "actual S6E10 episode chaos" claim, Phase 5.** The
  literate demonstration in `Project/PrisonerOfBenda.lean` uses a
  4-cycle + 3-cycle simplification of the show's actual chaos.
  We initially framed it as an "actual reconstruction of the
  episode permutation"; a code review caught that the real S6E10
  features additional characters (Wash Bucket, Nikolai,
  LaBarbara) and that the Globetrotters Sweet Clyde and Bubblegum
  Tate are external advisors rather than on-stage cast. Reframed
  as an "episode-inspired slice" with an explicit footnote. AI
  didn't introduce this slack; we did, in the framing prose.

None of these is fatal. All of them are the kind of thing that
slips through if you treat AI output (or your own first draft) as
authoritative; all of them are caught if you treat both as a
collaborator's first draft.

---

## Proof audits

Independently of the kernel build, the validation suite runs eight
layers of evidence in the default build path, plus one optional
ninth (Plausible). Layers 1–2 are Lean-checked structural guards
(zero `sorry`/`admit`, the `optimalScript` block hierarchy pinned
by an embedded `example := rfl` harness); layer 3 is the
paper-vs-Lean correspondence audit at the document level; layers
4–8 are executable corroboration via `native_decide` / `decide`
on concrete witnesses, including the brute-force concordance check
on `Fin 3, Fin 4` and the negative-control anti-tests in V9.

The axiom-baseline harnesses
([`AxiomBaseline.lean`](../Project/validation/Optimality/AxiomBaseline.lean),
[`CutFamilyAxioms.lean`](../Project/validation/Optimality/CutFamilyAxioms.lean),
[`BruteForceAxioms.lean`](../Project/validation/Optimality/BruteForceAxioms.lean))
emit `#print axioms` output for every public endpoint. If a
future edit accidentally promotes `Lean.ofReduceBool` or
`Lean.trustCompiler` into a kernel proof, those files will print
it.

Anti-tests (V9) close the "validator might silently always return
`true`" blind spot: a battery of seven deliberately bad inputs
fed to the boolean validators of V6, with each expected to return
`false`.

---

## Reflections

**What worked well.**

- *Skeleton-first.* Sketching the theorem statements with `sorry`
  early, then filling in the proofs depth-first, kept momentum
  going through the long Layer 1 stretch. Getting stuck on one
  sub-lemma never blocked the rest of the dependency graph.
- *Phase-staged AI delegation.* Letting AI in slowly — sounding
  board in Phase 1, search engine in Phase 2, body-completion in
  Phase 3, agentic in Phase 4 — meant we always knew what shape
  of output to expect and what to look for in review. The
  opposite mistake (handing everything to an agent up front)
  would have produced 15,000 lines of plausible-looking Lean
  that didn't compose.
- *Paper-correspondence as a discipline.* Writing the row-by-row
  paper-vs-Lean mapping is what caught both the wrap-around bug
  and the orientation gotcha. Without that discipline, the
  development would have shipped with at least one
  strictly-weaker theorem silently passing as paper-equivalent.
- *Treating the Lean kernel as the truth oracle.* Once a proof
  type-checks under axioms `{propext, Classical.choice, Quot.sound}`,
  the result is real, no matter what role AI played in producing
  the source. This makes the AI-assistance question a productivity
  question, not a soundness question.

**What was hard.**

- *Bookkeeping in Layer 1.* Tracking which steps affect which
  cycle's elements through the `xy_split` decomposition, with
  off-by-one indices everywhere, expanded one-sentence informal
  proofs into 50-line case analyses with three nested
  `omit [DecidableEq α] [Fintype α] in` annotations. There is no
  clever workaround for this; you grind it (or you let Codex
  grind it under your review).
- *The gap between "obviously true" and "Lean-checked".*
  `omega` and `decide` close most small goals, but a
  non-trivial fraction of the time a proof needs a custom helper
  lemma whose *statement* is what is hard to find, not the
  *proof*.
- *Knowing what question to ask.* The orientation gotcha
  illustrates this. Both Codex and we had the same mistaken
  mental model of `Cycle`, formed from the same docstring. The
  fix only landed when we asked the right comparison question.
  No amount of AI assistance helps if you don't know what to
  ask.
- *Decidability hygiene.* Lean's instance synthesis sometimes
  fails to look through `abbrev` to find a `Decidable` instance,
  even when one is technically available. We lost about an hour
  on `Decidable (List.Pairwise Cycle.Disjoint chaos)` before
  switching to a manual case-split proof.

---

## Is this proof correct?

The proofs type-check. Lean's kernel has verified every step of
every kernel theorem. The axiom baseline is the standard Lean /
Mathlib set; `Lean.ofReduceBool` and `Lean.trustCompiler` appear
only in two `native_decide`-discharged validation theorems and
are structurally isolated.

But type-checking is not the same as **mathematical** correctness.
If our definition of `optimalScript` does not match the paper's
$\lambda$, the proof is correct in Lean but vacuous about the
paper. The two layers of defence against this are:

1. *Definition correctness.* The 9-line `example := rfl` block at
   the bottom of `UpperBound.lean` pins down the literal layered
   structure of `optimalScript`. If a future refactor ever
   changes the paper-$\lambda$ block hierarchy in a way that
   breaks the layer-by-layer `rfl`-equality, the build fails on
   the offending line.

2. *Paper-correspondence audit.* `paper_correspondence.md` is a
   row-by-row mapping with status labels. The wrap-around bug
   got caught because of this; the orientation gotcha got
   resolved by Section 6's index dictionary. Independent review
   of this document is the most useful kind of feedback we could
   receive on the formalisation.

Independent review is welcome. The repository is at
[`Cheng-Yaoyu/Futurama-Theorem-with-Optimality`](https://github.com/Cheng-Yaoyu/Futurama-Theorem-with-Optimality);
the tagged release is
[`v1.0.0`](https://github.com/Cheng-Yaoyu/Futurama-Theorem-with-Optimality/releases/tag/v1.0.0).

---

## Final thoughts

The phase-by-phase split that emerged is, we think, the honest
template for AI-assisted formalisation at this paper's scale.
Phase 1 (architecture) and the paper-correspondence audit are
human-led, with AI in an advisory role. Phase 2 (the first proof
layer) is human-driven with AI as a search engine. Phase 3 (the
bulk of the proof line-count) is human-skeleton plus AI
body-completion under review. Phase 4 (validation) and Phase 5
(refactor) are agentic under high-level instructions.

The key insight is that **the human role is greatest at the
beginning and the end of each phase, not the middle**. At the
start of a phase you set the architecture, the skeleton, the
proof strategy. At the end you do the review and the audit. The
middle — typing out the 50-line case analyses, finding the right
Mathlib lemma name, mechanically filling in `omit` annotations,
reorganising imports — is where AI replaces the labour, and where
the productivity multiplier compounds across 13,800 lines of
Lean.

The trade, when staged this way, is good. We would have spent six
months grinding Layer 1 without Codex; Codex on its own would
have shipped a strictly-weaker Lemma 1(c), an off-by-one optimal
length on $\textsf{Fin}\,3$, and probably an architecture without
the two-track separation between Lemma 1 and the lower-bound
chain.

Neither side could have done this in a month alone. Together, in
five phases, we did.

---

*April 2026. Feedback welcome at the issues tab of the repository.*
