import Project.Futurama.CoreSchedule

open Equiv Equiv.Perm

namespace Project
namespace Futurama

/-!
# Futurama Finite Bridge Layer

This module bridges the constructive cycle-list theorem to arbitrary
finite permutations by lifting permutations to the helper-body state
space and factoring finite permutations into disjoint cycles.

## Main definitions

* `liftPerm` — embed `σ : Perm α` into `Perm (Body α)` by fixing
  `Body.x` and `Body.y`.
* `liftPermHom` — the same as a `MonoidHom`.
* `cycleFromPerm` — extract a `Cycle α` from a Mathlib `IsCycle σ`
  permutation (orientation matches `cyclePerm`'s reverse-formPerm
  convention; see `CoreCycle.lean`).
* `factorCycles σ` — full disjoint-cycle decomposition of `σ` as a
  `List (Cycle α)`. Noncomputable because it routes through
  `Finset.toList` of `σ.cycleFactorsFinset`.
* `factorGraph` — the graph whose vertices are entries appearing in
  a list of swaps and whose edges record which swap connects which
  pair; the graph-theoretic backbone for Lemma 1(a) in
  `Optimality/Lemma1.lean`.
* `undoScriptOfPerm` — default-route Perm-level repair script
  obtained from `factorCycles`.

## Main results

* `cycleProduct_factorCycles` — the bridge identity
  `cycleProduct (factorCycles σ) = liftPerm σ`.
* `factorCycles_pairwise_disjoint` — the cycles in the
  decomposition are pairwise `Cycle.Disjoint`.
* `futuramaTheoremOfPerm` — the constructive `Perm`-level correctness
  endpoint (default route, correctness only). Stronger packaged
  versions live in `ParameterizedFamily.lean` and are derived via
  `defaultSchedule (factorCycles σ)`.
-/

variable {α : Type*} [DecidableEq α]

section FiniteBridge

variable [Fintype α]

omit [DecidableEq α] [Fintype α] in
theorem listProd_apply_eq_of_forall_apply_eq
    (ts : List (Perm α)) (a : α)
    (hfix : ∀ t ∈ ts, t a = a) :
    ts.prod a = a := by
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      rw [List.prod_cons, Perm.mul_apply, ih]
      · exact hfix t (by simp)
      · intro u hu
        exact hfix u (List.mem_cons_of_mem _ hu)

noncomputable def factorLeft
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (t : Perm α) (ht : t ∈ ts) : α :=
  Classical.choose (hfactors t ht)

noncomputable def factorRight
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (t : Perm α) (ht : t ∈ ts) : α :=
  Classical.choose (Classical.choose_spec (hfactors t ht))

omit [Fintype α] in
theorem factorLeft_ne_factorRight
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (t : Perm α) (ht : t ∈ ts) :
    factorLeft ts hfactors t ht ≠ factorRight ts hfactors t ht :=
  (Classical.choose_spec (Classical.choose_spec (hfactors t ht))).1

omit [Fintype α] in
theorem factor_eq_swap_factorEndpoints
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (t : Perm α) (ht : t ∈ ts) :
    t = Equiv.swap (factorLeft ts hfactors t ht) (factorRight ts hfactors t ht) :=
  (Classical.choose_spec (Classical.choose_spec (hfactors t ht))).2

theorem swap_eq_swap_iff
    {a b x y : α} (hab : a ≠ b) :
    Equiv.swap a b = Equiv.swap x y ↔
      (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  constructor
  · intro h
    by_cases hxy : x = y
    · exfalso
      have happly := congrArg (fun f => f a) h
      exact hab <| by simpa [hxy, Equiv.swap_apply_left, Equiv.swap_self] using happly.symm
    · have hx_mem : x ∈ (Equiv.swap x y).support := by
        rw [Equiv.Perm.mem_support]
        simpa [eq_comm, Equiv.swap_apply_left] using hxy
      have hx_mem' : x ∈ (Equiv.swap a b).support := by simpa [h] using hx_mem
      rw [Equiv.Perm.support_swap hab, Finset.mem_insert, Finset.mem_singleton] at hx_mem'
      rcases hx_mem' with hxa | hxb
      · left
        constructor
        · exact hxa.symm
        · have happly := congrArg (fun f => f a) h
          subst hxa
          simpa [Equiv.swap_apply_left, hxy] using happly
      · right
        constructor
        · have happly := congrArg (fun f => f b) h
          subst hxb
          simpa [Equiv.swap_apply_left, hxy] using happly
        · exact hxb.symm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [Equiv.swap_comm]

noncomputable def factorGraph
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap) : SimpleGraph α where
  Adj x y := ∃ t ∈ ts, t = Equiv.swap x y
  symm := by
    intro x y h
    rcases h with ⟨t, ht, rfl⟩
    exact ⟨Equiv.swap x y, ht, by rw [Equiv.swap_comm]⟩
  loopless := by
    intro x h
    rcases h with ⟨t, ht, htxy⟩
    rcases hfactors t ht with ⟨u, v, huv, htuv⟩
    have hid : Equiv.swap u v = Equiv.refl α := by
      calc
        Equiv.swap u v = t := htuv.symm
        _ = Equiv.swap x x := htxy
        _ = Equiv.refl α := by simp [Equiv.swap_self]
    have hvu : v = u := by
      have := congrArg (fun f => f u) hid
      simpa [Equiv.swap_apply_left] using this
    exact huv hvu.symm

noncomputable instance factorGraphDecidableRel
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap) : DecidableRel (factorGraph ts hfactors).Adj := by
  classical
  infer_instance

omit [Fintype α] in
theorem factorGraph_edge_of_mem
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    {t : Perm α} (ht : t ∈ ts) :
    (factorGraph ts hfactors).Adj
      (factorLeft ts hfactors t ht) (factorRight ts hfactors t ht) := by
  exact ⟨t, ht, factor_eq_swap_factorEndpoints ts hfactors t ht⟩

omit [Fintype α] in
theorem factorLeft_mem_factorGraph_support
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    {t : Perm α} (ht : t ∈ ts) :
    factorLeft ts hfactors t ht ∈ (factorGraph ts hfactors).support := by
  rw [SimpleGraph.mem_support]
  exact ⟨factorRight ts hfactors t ht, factorGraph_edge_of_mem ts hfactors ht⟩

omit [Fintype α] in
theorem factorRight_mem_factorGraph_support
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    {t : Perm α} (ht : t ∈ ts) :
    factorRight ts hfactors t ht ∈ (factorGraph ts hfactors).support := by
  rw [SimpleGraph.mem_support]
  exact ⟨factorLeft ts hfactors t ht, (factorGraph_edge_of_mem ts hfactors ht).symm⟩

theorem factorGraph_edgeFinset_subset
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap) :
    (factorGraph ts hfactors).edgeFinset ⊆
      ts.attach.toFinset.image fun t =>
        s(factorLeft ts hfactors t.1 t.2, factorRight ts hfactors t.1 t.2) := by
  classical
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.inductionOn with
  | hf x y =>
      change (factorGraph ts hfactors).Adj x y at he
      rcases he with ⟨t, ht, hswap⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨⟨t, ht⟩, by simp, ?_⟩
      rw [factor_eq_swap_factorEndpoints ts hfactors t ht] at hswap
      exact (Sym2.eq_iff).2 <|
        (swap_eq_swap_iff (factorLeft_ne_factorRight ts hfactors t ht)).1 hswap

theorem card_edgeFinset_factorGraph_le
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap) :
    (factorGraph ts hfactors).edgeFinset.card ≤ ts.length := by
  classical
  calc
    (factorGraph ts hfactors).edgeFinset.card
      ≤ (ts.attach.toFinset.image fun t =>
            s(factorLeft ts hfactors t.1 t.2, factorRight ts hfactors t.1 t.2)).card := by
            exact Finset.card_le_card (factorGraph_edgeFinset_subset ts hfactors)
    _ ≤ ts.attach.toFinset.card := Finset.card_image_le
    _ ≤ ts.attach.length := by simpa using (List.toFinset_card_le (l := ts.attach))
    _ = ts.length := by simp

omit [Fintype α] in
theorem factorGraph_factor_preserves_component
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    {t : Perm α} (ht : t ∈ ts) (v : α) :
    (factorGraph ts hfactors).connectedComponentMk (t v) =
      (factorGraph ts hfactors).connectedComponentMk v := by
  rw [factor_eq_swap_factorEndpoints ts hfactors t ht]
  let x := factorLeft ts hfactors t ht
  let y := factorRight ts hfactors t ht
  have hxy : x ≠ y := factorLeft_ne_factorRight ts hfactors t ht
  have hadj : (factorGraph ts hfactors).Adj x y :=
    factorGraph_edge_of_mem ts hfactors ht
  by_cases hvx : v = x
  · subst hvx
    simpa [x, y] using (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm
  by_cases hvy : v = y
  · subst hvy
    simpa [x, y] using SimpleGraph.ConnectedComponent.sound hadj.reachable
  · have hfix : Equiv.swap x y v = v := Equiv.swap_apply_of_ne_of_ne hvx hvy
    simp [x, y, hfix]

omit [DecidableEq α] [Fintype α] in
theorem connectedComponentMk_listProd_eq
    (G : SimpleGraph α)
    (ts : List (Perm α))
    (hpres : ∀ t ∈ ts, ∀ v, G.connectedComponentMk (t v) = G.connectedComponentMk v)
    (v : α) :
    G.connectedComponentMk (ts.prod v) = G.connectedComponentMk v := by
  induction ts generalizing v with
  | nil =>
      simp
  | cons t ts ih =>
      rw [List.prod_cons, Perm.mul_apply, hpres t (by simp)]
      exact ih (fun u hu w => hpres u (by simp [hu]) w) v

omit [Fintype α] in
theorem factorGraph_prod_preserves_component
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (v : α) :
    (factorGraph ts hfactors).connectedComponentMk (ts.prod v) =
      (factorGraph ts hfactors).connectedComponentMk v := by
  apply connectedComponentMk_listProd_eq
  intro t ht w
  exact factorGraph_factor_preserves_component ts hfactors ht w

omit [Fintype α] in
theorem factorGraph_pow_preserves_component
    (σ : Perm α)
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = σ)
    (v : α) :
    ∀ n : ℕ,
      (factorGraph ts hfactors).connectedComponentMk ((σ ^ n) v) =
        (factorGraph ts hfactors).connectedComponentMk v := by
  have hσpres :
      ∀ w,
        (factorGraph ts hfactors).connectedComponentMk (σ w) =
          (factorGraph ts hfactors).connectedComponentMk w := by
    intro w
    simpa [hprod] using factorGraph_prod_preserves_component ts hfactors w
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ', Perm.mul_apply, hσpres, ih]

theorem isCycle_support_subset_factorGraph_component
    (σ : Perm α) (hσ : σ.IsCycle)
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = σ)
    {a0 : α} (ha0 : a0 ∈ σ.support) :
    (↑σ.support : Set α) ⊆ (factorGraph ts hfactors).connectedComponentMk a0 := by
  have hpowpres :
      ∀ n : ℕ,
        (factorGraph ts hfactors).connectedComponentMk ((σ ^ n) a0) =
          (factorGraph ts hfactors).connectedComponentMk a0 := by
    exact factorGraph_pow_preserves_component σ ts hfactors hprod a0
  intro b hb
  obtain ⟨n, hn⟩ := hσ.exists_pow_eq (mem_support.mp ha0) (mem_support.mp hb)
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      ((factorGraph ts hfactors).connectedComponentMk a0) b).2 <| by
    simpa [hn] using hpowpres n

/-- Extend a permutation of the original cast to the augmented body type, fixing the helpers. -/
def liftPerm (σ : Perm α) : Perm (Body α) where
  toFun
    | Body.orig a => Body.orig (σ a)
    | Body.x => Body.x
    | Body.y => Body.y
  invFun
    | Body.orig a => Body.orig (σ⁻¹ a)
    | Body.x => Body.x
    | Body.y => Body.y
  left_inv z := by
    cases z <;> simp
  right_inv z := by
    cases z <;> simp

omit [DecidableEq α] [Fintype α] in
@[simp] theorem liftPerm_apply_orig (σ : Perm α) (a : α) :
    liftPerm σ (Body.orig a) = Body.orig (σ a) :=
  rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem liftPerm_apply_x (σ : Perm α) :
    liftPerm σ Body.x = Body.x :=
  rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem liftPerm_apply_y (σ : Perm α) :
    liftPerm σ Body.y = Body.y :=
  rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem liftPerm_one :
    liftPerm (1 : Perm α) = (1 : Perm (Body α)) := by
  ext z
  cases z <;> simp [liftPerm]

omit [DecidableEq α] [Fintype α] in
@[simp] theorem liftPerm_mul (σ τ : Perm α) :
    liftPerm (σ * τ) = liftPerm σ * liftPerm τ := by
  ext z
  cases z <;> simp [liftPerm]

/-- `liftPerm` packaged as a monoid homomorphism. -/
def liftPermHom : Perm α →* Perm (Body α) where
  toFun := liftPerm
  map_one' := liftPerm_one
  map_mul' := liftPerm_mul

omit [DecidableEq α] [Fintype α] in
@[simp] theorem liftPermHom_apply (σ : Perm α) :
    liftPermHom σ = liftPerm σ :=
  rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem liftPerm_prod (ps : List (Perm α)) :
    liftPerm ps.prod = (ps.map liftPerm).prod := by
  simpa using liftPermHom.map_list_prod ps

omit [Fintype α] in
@[simp] theorem liftPerm_swap_orig (a b : α) :
    liftPerm (Equiv.swap a b) = Equiv.swap (Body.orig a) (Body.orig b) := by
  ext z
  cases z with
  | orig c =>
      simp [liftPerm, Equiv.swap_apply_def]
      split_ifs <;> rfl
  | x =>
      simp [liftPerm, Equiv.swap_apply_def]
  | y =>
      simp [liftPerm, Equiv.swap_apply_def]

omit [Fintype α] in
/-- `formPerm` commutes with embedding original bodies into the augmented body type. -/
theorem formPerm_map_orig (l : List α) :
    (l.map Body.orig).formPerm = liftPerm l.formPerm := by
  induction l with
  | nil =>
      simp [liftPerm_one]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [liftPerm_one]
      | cons y ys =>
          simpa [List.map, List.formPerm_cons_cons, liftPerm_mul, liftPerm_swap_orig] using
            congrArg (fun π => Equiv.swap (Body.orig x) (Body.orig y) * π) ih

private def cycleFromReversed : (r : List α) → 2 ≤ r.length → r.Nodup → Cycle α
  | [], hlen, _ => False.elim <| by simp at hlen
  | [a], hlen, _ => False.elim <| by simp at hlen
  | a :: b :: rest, _, hnodup =>
      { first := a
        second := b
        rest := rest
        nodup := by simpa using hnodup }

omit [DecidableEq α] [Fintype α] in
private theorem members_cycleFromReversed (r : List α) (hlenr : 2 ≤ r.length) (hnodupr : r.Nodup) :
    (cycleFromReversed r hlenr hnodupr).members = r := by
  cases r with
  | nil =>
      simp at hlenr
  | cons a tail =>
      cases tail with
      | nil =>
          simp at hlenr
      | cons b rest =>
          rfl

/-- Package a concrete cyclic list into our `Cycle` structure, reversing the list so that
`cyclePerm` matches the ambient permutation's action. -/
def cycleFromList (l : List α) (hlen : 2 ≤ l.length) (hnodup : l.Nodup) : Cycle α :=
  cycleFromReversed l.reverse
    (by simpa [List.length_reverse] using hlen)
    (by simpa using List.nodup_reverse.2 hnodup)

omit [DecidableEq α] [Fintype α] in
@[simp] theorem members_cycleFromList (l : List α) (hlen : 2 ≤ l.length) (hnodup : l.Nodup) :
    (cycleFromList l hlen hnodup).members = l.reverse := by
  simpa [cycleFromList] using
    members_cycleFromReversed l.reverse
      (by simpa [List.length_reverse] using hlen)
      (by simpa using List.nodup_reverse.2 hnodup)

omit [Fintype α] in
private theorem cyclePerm_cycleFromReversed (r : List α) (hlenr : 2 ≤ r.length) (hnodupr : r.Nodup) :
    cyclePerm (cycleFromReversed r hlenr hnodupr) = liftPerm r.reverse.formPerm := by
  cases r with
  | nil =>
      simp at hlenr
  | cons a tail =>
      cases tail with
      | nil =>
          simp at hlenr
      | cons b rest =>
          simpa [List.map_reverse, List.map_append, cycleFromReversed, cyclePerm,
            cyclePermAux_eq_formPerm_reverse] using
            (formPerm_map_orig (rest.reverse ++ [b, a]))

omit [Fintype α] in
theorem cyclePerm_cycleFromList (l : List α) (hlen : 2 ≤ l.length) (hnodup : l.Nodup) :
    cyclePerm (cycleFromList l hlen hnodup) = liftPerm l.formPerm := by
  simpa [cycleFromList, List.reverse_reverse] using
    cyclePerm_cycleFromReversed l.reverse
      (by simpa [List.length_reverse] using hlen)
      (by simpa using List.nodup_reverse.2 hnodup)

/-- A deterministic support element chosen from a cyclic permutation. -/
noncomputable def cycleSeed (σ : Perm α) (hσ : σ.IsCycle) : α :=
  σ.support.toList.head (Finset.Nonempty.toList_ne_nil hσ.nonempty_support)

theorem cycleSeed_mem_support (σ : Perm α) (hσ : σ.IsCycle) :
    cycleSeed σ hσ ∈ σ.support := by
  unfold cycleSeed
  exact Finset.mem_toList.mp (List.head_mem _)

theorem cycleSeed_ne_fixed (σ : Perm α) (hσ : σ.IsCycle) :
    σ (cycleSeed σ hσ) ≠ cycleSeed σ hσ := by
  simpa [Equiv.Perm.mem_support] using cycleSeed_mem_support σ hσ

/-- Convert a cyclic permutation into our ordered `Cycle` representation. -/
noncomputable def cycleFromPerm (σ : Perm α) (hσ : σ.IsCycle) : Cycle α :=
  let x : α := cycleSeed σ hσ
  let hx : x ∈ σ.support := cycleSeed_mem_support σ hσ
  let l := σ.toList x
  cycleFromList l
    ((Equiv.Perm.two_le_length_toList_iff_mem_support).2 hx)
    (Equiv.Perm.nodup_toList σ x)

theorem cyclePerm_cycleFromPerm (σ : Perm α) (hσ : σ.IsCycle) :
    cyclePerm (cycleFromPerm σ hσ) = liftPerm σ := by
  let x : α := cycleSeed σ hσ
  let hx : x ∈ σ.support := cycleSeed_mem_support σ hσ
  let l := σ.toList x
  have hx_ne : σ x ≠ x := by
    simpa [x] using cycleSeed_ne_fixed σ hσ
  have hform : l.formPerm = σ := by
    simpa [l, hσ.cycleOf_eq hx_ne] using (Equiv.Perm.formPerm_toList σ x)
  simpa [cycleFromPerm, x, hx, l, hform] using
    cyclePerm_cycleFromList l
      ((Equiv.Perm.two_le_length_toList_iff_mem_support).2 hx)
      (Equiv.Perm.nodup_toList σ x)

@[simp] theorem members_cycleFromPerm (σ : Perm α) (hσ : σ.IsCycle) :
    (cycleFromPerm σ hσ).members =
      (σ.toList (cycleSeed σ hσ)).reverse := by
  let x : α := cycleSeed σ hσ
  let hx : x ∈ σ.support := cycleSeed_mem_support σ hσ
  let l := σ.toList x
  simpa [cycleFromPerm, x, hx, l] using
    (members_cycleFromList l
      ((Equiv.Perm.two_le_length_toList_iff_mem_support).2 hx)
      (Equiv.Perm.nodup_toList σ x))

theorem mem_members_cycleFromPerm_iff_mem_support (σ : Perm α) (hσ : σ.IsCycle) {a : α} :
    a ∈ (cycleFromPerm σ hσ).members ↔ a ∈ σ.support := by
  let x : α := cycleSeed σ hσ
  let hx : x ∈ σ.support := cycleSeed_mem_support σ hσ
  let l := σ.toList x
  have hmemList : a ∈ l ↔ a ∈ σ.support := by
    calc
      a ∈ l ↔ Equiv.Perm.SameCycle σ x a ∧ x ∈ σ.support := by
        simpa [l] using (Equiv.Perm.mem_toList_iff (p := σ) (x := x) (y := a))
      _ ↔ Equiv.Perm.SameCycle σ x a := by simp [hx]
      _ ↔ a ∈ σ.support := by
        constructor
        · intro hxa
          exact (hxa.mem_support_iff).1 hx
        · intro ha
          exact hσ.sameCycle
            (by simpa [Equiv.Perm.mem_support] using hx)
            (by simpa [Equiv.Perm.mem_support] using ha)
  rw [show (cycleFromPerm σ hσ).members = l.reverse by
    simpa [x, l] using (members_cycleFromPerm σ hσ)]
  simpa using hmemList

theorem members_length_cycleFromPerm (σ : Perm α) (hσ : σ.IsCycle) :
    (cycleFromPerm σ hσ).members.length = σ.support.card := by
  rw [members_cycleFromPerm]
  simp [List.length_reverse, Equiv.Perm.length_toList, hσ.cycleOf_eq (cycleSeed_ne_fixed σ hσ)]

theorem cycleFromPerm_disjoint_of_disjoint {σ τ : Perm α}
    (hσ : σ.IsCycle) (hτ : τ.IsCycle) (hστ : Disjoint σ τ) :
    Cycle.Disjoint (cycleFromPerm σ hσ) (cycleFromPerm τ hτ) := by
  change List.Disjoint (cycleFromPerm σ hσ).members (cycleFromPerm τ hτ).members
  rw [List.disjoint_left]
  intro a ha hb
  have ha' : a ∈ σ.support := (mem_members_cycleFromPerm_iff_mem_support σ hσ).1 ha
  have hb' : a ∈ τ.support := (mem_members_cycleFromPerm_iff_mem_support τ hτ).1 hb
  exact (Finset.disjoint_left.mp hστ.disjoint_support) ha' hb'

/-- Convert a list of cyclic permutation factors into our executable cycle data. -/
noncomputable def factorCyclesFromList (ps : List (Perm α))
    (hcycles : ∀ p ∈ ps, p.IsCycle) : List (Cycle α) :=
  match ps with
  | [] => []
  | p :: ps =>
      cycleFromPerm p (hcycles p (by simp)) ::
        factorCyclesFromList ps (fun q hq => hcycles q (by simp [hq]))

theorem factorCyclesFromList_length (ps : List (Perm α))
    (hcycles : ∀ p ∈ ps, p.IsCycle) :
    (factorCyclesFromList ps hcycles).length = ps.length := by
  induction ps with
  | nil =>
      simp [factorCyclesFromList]
  | cons p ps ih =>
      simp [factorCyclesFromList, ih (fun q hq => hcycles q (by simp [hq]))]

theorem factorCyclesFromList_membersLengthSum (ps : List (Perm α))
    (hcycles : ∀ p ∈ ps, p.IsCycle) :
    ((factorCyclesFromList ps hcycles).map fun c => c.members.length).sum =
      (ps.map fun p => p.support.card).sum := by
  induction ps with
  | nil =>
      simp [factorCyclesFromList]
  | cons p ps ih =>
      rw [factorCyclesFromList, List.map_cons, List.sum_cons, members_length_cycleFromPerm]
      simpa using ih (fun q hq => hcycles q (by simp [hq]))

theorem cycleProduct_factorCyclesFromList (ps : List (Perm α))
    (hcycles : ∀ p ∈ ps, p.IsCycle) :
    cycleProduct (factorCyclesFromList ps hcycles) = liftPerm ps.prod := by
  induction ps with
  | nil =>
      simp [factorCyclesFromList]
  | cons p ps ih =>
      simp [factorCyclesFromList, cyclePerm_cycleFromPerm, liftPerm_mul,
        ih (fun q hq => hcycles q (by simp [hq]))]

theorem cycleFromPerm_disjoint_of_mem_factorCyclesFromList
    (p : Perm α) (hp : p.IsCycle) (ps : List (Perm α))
    (hcycles : ∀ q ∈ ps, q.IsCycle) (hdisj : ∀ q ∈ ps, Disjoint p q) :
    ∀ c ∈ factorCyclesFromList ps hcycles, Cycle.Disjoint (cycleFromPerm p hp) c := by
  induction ps with
  | nil =>
      intro c hc
      simp [factorCyclesFromList] at hc
  | cons q qs ih =>
      intro c hc
      simp [factorCyclesFromList] at hc
      rcases hc with rfl | hc
      · exact cycleFromPerm_disjoint_of_disjoint hp
          (hcycles q (by simp))
          (hdisj q (by simp))
      · exact ih
          (fun r hr => hcycles r (by simp [hr]))
          (fun r hr => hdisj r (by simp [hr]))
          c hc

theorem factorCyclesFromList_pairwise_disjoint (ps : List (Perm α))
    (hcycles : ∀ p ∈ ps, p.IsCycle) (hpair : ps.Pairwise Disjoint) :
    (factorCyclesFromList ps hcycles).Pairwise Cycle.Disjoint := by
  induction ps with
  | nil =>
      simp [factorCyclesFromList]
  | cons p ps ih =>
      rw [factorCyclesFromList, List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · exact cycleFromPerm_disjoint_of_mem_factorCyclesFromList p
          (hcycles p (by simp))
          ps
          (fun q hq => hcycles q (by simp [hq]))
          (fun q hq => (List.pairwise_cons.1 hpair).1 q hq)
      · exact ih
          (fun q hq => hcycles q (by simp [hq]))
          ((List.pairwise_cons.1 hpair).2)

/-- The cycle factors of a finite permutation, converted into our `Cycle` representation. -/
noncomputable def factorCycles (σ : Perm α) : List (Cycle α) :=
  factorCyclesFromList σ.cycleFactorsFinset.toList fun p hp =>
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (by simpa using hp)).1

private theorem cycleFactorsToList_isCycle (σ : Perm α) :
    ∀ p ∈ σ.cycleFactorsFinset.toList, p.IsCycle := by
  intro p hp
  exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (by simpa using hp)).1

private theorem cycleFactorsToList_pairwise_disjoint (σ : Perm α) :
    (σ.cycleFactorsFinset.toList).Pairwise Disjoint := by
  let ps := σ.cycleFactorsFinset.toList
  have hnodup : ps.Nodup := Finset.nodup_toList _
  have hpairSet : (ps.toFinset : Set (Perm α)).Pairwise Disjoint := by
    simpa [ps, Finset.toList_toFinset] using
      (σ.cycleFactorsFinset_pairwise_disjoint : (σ.cycleFactorsFinset : Set (Perm α)).Pairwise Disjoint)
  simpa [ps] using List.pairwise_of_coe_toFinset_pairwise hpairSet hnodup

private theorem cycleFactorsToList_prod (σ : Perm α) :
    (σ.cycleFactorsFinset.toList).prod = σ := by
  let ps := σ.cycleFactorsFinset.toList
  have hnodup : ps.Nodup := Finset.nodup_toList _
  have hcomm : (ps.toFinset : Set (Perm α)).Pairwise (Function.onFun Commute id) := by
    simpa [ps, Finset.toList_toFinset] using
      (σ.cycleFactorsFinset_mem_commute : (σ.cycleFactorsFinset : Set (Perm α)).Pairwise Commute)
  calc
    ps.prod = ps.toFinset.noncommProd id hcomm := by
      simpa using (Finset.noncommProd_toFinset ps id hcomm hnodup).symm
    _ = σ.cycleFactorsFinset.noncommProd id (σ.cycleFactorsFinset_mem_commute) := by
      simp [ps, Finset.toList_toFinset]
    _ = σ := σ.cycleFactorsFinset_noncommProd

theorem factorCycles_length (σ : Perm α) :
    (factorCycles σ).length = σ.cycleFactorsFinset.card := by
  simp [factorCycles, factorCyclesFromList_length]

theorem factorCycles_membersLengthSum (σ : Perm α) :
    ((factorCycles σ).map fun c => c.members.length).sum = σ.support.card := by
  calc
    ((factorCycles σ).map fun c => c.members.length).sum
        = ((σ.cycleFactorsFinset.toList).map fun p => p.support.card).sum := by
            simpa [factorCycles] using
              factorCyclesFromList_membersLengthSum (σ.cycleFactorsFinset.toList)
                (cycleFactorsToList_isCycle σ)
    _ = (σ.cycleFactorsFinset.toList).prod.support.card := by
          simpa using
            (Equiv.Perm.card_support_prod_list_of_pairwise_disjoint
              (l := σ.cycleFactorsFinset.toList) (cycleFactorsToList_pairwise_disjoint σ)).symm
    _ = σ.support.card := by simp [cycleFactorsToList_prod σ]

theorem cycleProduct_factorCycles (σ : Perm α) :
    cycleProduct (factorCycles σ) = liftPerm σ := by
  simpa [factorCycles, cycleFactorsToList_prod σ] using
    cycleProduct_factorCyclesFromList (σ.cycleFactorsFinset.toList)
      (cycleFactorsToList_isCycle σ)

theorem factorCycles_pairwise_disjoint (σ : Perm α) :
    (factorCycles σ).Pairwise Cycle.Disjoint := by
  simpa [factorCycles] using
    factorCyclesFromList_pairwise_disjoint (σ.cycleFactorsFinset.toList)
      (cycleFactorsToList_isCycle σ)
      (cycleFactorsToList_pairwise_disjoint σ)

/-- Keeler's executable repair script for an arbitrary finite permutation of the original cast. -/
noncomputable def undoScriptOfPerm (σ : Perm α) : List (Body α × Body α) :=
  undoScript (factorCycles σ)

theorem undoScriptOfPerm_length (σ : Perm α) :
    (undoScriptOfPerm σ).length =
      σ.support.card + 2 * σ.cycleFactorsFinset.card +
        (if σ.cycleFactorsFinset.card % 2 = 0 then 0 else 1) := by
  rw [undoScriptOfPerm, undoScript_length, factorCycles_membersLengthSum, factorCycles_length]

theorem undoScriptOfPerm_length_le (σ : Perm α) :
    (undoScriptOfPerm σ).length ≤ σ.support.card + 2 * σ.cycleFactorsFinset.card + 1 := by
  rw [undoScriptOfPerm_length]
  by_cases h : σ.cycleFactorsFinset.card % 2 = 0 <;> simp [h]

/-- For permutations with at least two nontrivial cycle factors, Keeler's script length is the
paper's optimal target `n + r + 2` plus the explicit overhead `(r - 2) + parity`. -/
theorem undoScriptOfPerm_length_eq_optimalBound_add_overhead (σ : Perm α)
    (hσ : 2 ≤ σ.cycleFactorsFinset.card) :
    (undoScriptOfPerm σ).length =
      (σ.support.card + σ.cycleFactorsFinset.card + 2) +
        (σ.cycleFactorsFinset.card - 2) +
        (if σ.cycleFactorsFinset.card % 2 = 0 then 0 else 1) := by
  rw [undoScriptOfPerm_length]
  by_cases h : σ.cycleFactorsFinset.card % 2 = 0
  · simp [h]
    omega
  · have h' : σ.cycleFactorsFinset.card % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one σ.cycleFactorsFinset.card with h0 | h1
      · contradiction
      · exact h1
    simp [h']
    omega

/-- Full repair theorem for an arbitrary finite permutation on the original cast.

This is the permutation-level version of the constructive Futurama theorem:
factor the scrambled permutation into disjoint cycles, run Keeler's repair
script on those cycles, and recover the identity. -/
theorem futuramaTheoremOfPerm (σ : Perm α) :
    runScript (undoScriptOfPerm σ) * liftPerm σ = 1 := by
  rw [undoScriptOfPerm, ← cycleProduct_factorCycles]
  exact futuramaTheorem (factorCycles σ)

end FiniteBridge

end Futurama
end Project
