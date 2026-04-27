import Project.Futurama.CoreCycle
import Project.Futurama.CoreSchedule
import Project.Futurama.FiniteBridge

/-!
# Optimality / Lemma 1 — Graph-theoretic facts about minimal factorisations

This file hosts the Lemma 1 family from Evans–Huang–Nguyen 2014:

- Lemma 1(a): a `k`-cycle requires at least `k − 1` transpositions
  (`transposition_count_ge_cycle_length`)
- Lemma 1(b), trivial direction `V ⊆ W`
  (`minimal_factorization_covers_support`)
- Lemma 1(b), non-trivial direction `W ⊆ V`
  (`minimal_factorization_factorEndpoints_mem_support`,
  `minimal_factorization_factorEntries_mem_support`)
- Lemma 1(c): when `t = k − 1`, at least one factor has the form
  `(a_i a_{i+1})` — both a compatibility form
  (`minimal_factorization_has_adjacent`) and a paper-strong form
  that explicitly excludes the wrap-around edge
  (`minimal_factorization_has_adjacent_paper`).

**Track separation note**: this file is the parallel paper-faithful
graph-theoretic track. None of these theorems is consumed by
Theorem 1's lower-bound chain (which lives in
`Optimality/LowerBound/*.lean` and goes through entry counting
plus parity); the two tracks are mathematically independent and
mirror the structure of Evans–Huang–Nguyen's own proof. The file is
therefore a leaf module — it has no downstream consumers in the
optimality development. It is preserved for paper-correspondence
completeness and as a direct prerequisite for any future
formalisation of paper Theorems 2 and 3, which do invoke Lemma 1
explicitly.
-/

open Equiv Equiv.Perm

namespace Project
namespace Futurama

variable {α : Type*} [DecidableEq α]

-- ═══════════════════════════════════════════════
-- Section 2: Lemma 1 — Graph-theoretic
-- ═══════════════════════════════════════════════

/-!
### Lemma 1 (Evans/Huang/Nguyen)

If a `k`-cycle `σ` equals a product of `t` transpositions, then:
- (a) `t ≥ k − 1`
- (b) if `t = k − 1`, the entries are exactly `σ.support`
- (c) if `t = k − 1`, at least one factor is an "adjacent" transposition
-/

variable [Fintype α]

/-- Lemma 1(a): A k-cycle needs at least k−1 transpositions.
    Proof (Evans–Huang–Nguyen, 2014): Build graph G with vertex set W = entries
    in the transposition list, and t edges corresponding to the t transposition
    factors. Since the product equals the k-cycle (a₁...aₖ), the graph G has a
    connected component H whose vertex set contains V = {a₁,...,aₖ}. A connected
    graph with M vertices has at least M−1 edges (Cameron, Theorem 11.2.1),
    so H has ≥ |V|−1 = k−1 edges. Thus t ≥ k−1. -/
theorem transposition_count_ge_cycle_length
    (σ : Perm α) (hσ : σ.IsCycle)
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = σ) :
    σ.support.card - 1 ≤ ts.length := by
  classical
  let G := factorGraph ts hfactors
  obtain ⟨a0, ha0⟩ := hσ.nonempty_support
  let C : G.ConnectedComponent := G.connectedComponentMk a0
  have hsubset : (↑σ.support : Set α) ⊆ C.supp := by
    simpa [G, C] using
      isCycle_support_subset_factorGraph_component σ hσ ts hfactors hprod ha0
  have hsupport_le : σ.support.card ≤ C.supp.toFinset.card := by
    exact Finset.card_le_card (by
      intro a ha
      simpa using hsubset ha)
  have hconn : C.toSimpleGraph.Connected := C.connected_toSimpleGraph
  have hcomponent_edges :
      (C.toSimpleGraph).edgeFinset.card ≤ G.edgeFinset.card := by
    let f : C ↪ α := ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
    have hsubset_map :
        ((C.toSimpleGraph).edgeFinset.map f.sym2Map) ⊆ G.edgeFinset := by
      intro e he
      rw [Finset.mem_map] at he
      rcases he with ⟨e', he', rfl⟩
      rw [SimpleGraph.mem_edgeFinset] at he'
      induction e' using Sym2.inductionOn with
      | hf u v =>
          rw [SimpleGraph.mem_edgeFinset]
          simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using he'
    calc
      (C.toSimpleGraph).edgeFinset.card
        = ((C.toSimpleGraph).edgeFinset.map f.sym2Map).card := by
            simp
      _ ≤ G.edgeFinset.card := Finset.card_le_card hsubset_map
  have hcard_vert :
      C.supp.toFinset.card ≤ (C.toSimpleGraph).edgeFinset.card + 1 := by
    have hverts := hconn.card_vert_le_card_edgeSet_add_one
    have hC :
        Nat.card C = C.supp.toFinset.card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_of_subtype C.supp.toFinset (by
        intro x
        rw [Set.mem_toFinset]
        show x ∈ C.supp ↔ x ∈ C
        rfl)
    have hedge :
        Nat.card ((C.toSimpleGraph).edgeSet) = (C.toSimpleGraph).edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    rw [hC, hedge] at hverts
    exact hverts
  calc
    σ.support.card - 1 ≤ C.supp.toFinset.card - 1 := by
      exact Nat.sub_le_sub_right hsupport_le 1
    _ ≤ (C.toSimpleGraph).edgeFinset.card := by
      omega
    _ ≤ G.edgeFinset.card := hcomponent_edges
    _ ≤ ts.length := by
      simpa [G] using card_edgeFinset_factorGraph_le ts hfactors

/-- Lemma 1(b): A minimal factorization of a cycle covers its entire support.
    Proof: When t = k−1, the graph G = H is connected. If V ⊊ W, then G
    would have ≥ k edges (k vertices in V plus ≥1 extra vertex, all connected).
    Since G has exactly k−1 edges, V = W. So all entries lie in σ.support. -/
theorem minimal_factorization_covers_support
    (σ : Perm α) (_hσ : σ.IsCycle)
    (ts : List (Perm α))
    (_hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = σ)
    (_hmin : ts.length = σ.support.card - 1) :
    ∀ a ∈ σ.support, ∃ t ∈ ts, a ∈ t.support := by
  intro a ha
  by_contra hnot
  push_neg at hnot
  have hfix_prod : ts.prod a = a := by
    apply listProd_apply_eq_of_forall_apply_eq
    intro t ht
    have htfix : a ∉ t.support := hnot t ht
    exact Equiv.Perm.notMem_support.mp htfix
  have hsigma_fix : σ a = a := by
    simpa [hprod] using hfix_prod
  exact (mem_support.mp ha) hsigma_fix

/-- In the minimal case `t = k - 1`, every endpoint appearing in every factor lies in
    `σ.support`. This is the stronger form of Lemma 1(b) used in the paper's proof.

    This pairs with
    `minimal_factorization_covers_support` (the trivial direction `V ⊆ W`), this theorem
    makes the paper's Lemma 1(b) equality `W = V` publicly representable. -/
theorem minimal_factorization_factorEndpoints_mem_support
    (σ : Perm α) (hσ : σ.IsCycle)
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = σ)
    (hmin : ts.length = σ.support.card - 1)
    {t : Perm α} (ht : t ∈ ts) :
    factorLeft ts hfactors t ht ∈ σ.support ∧
      factorRight ts hfactors t ht ∈ σ.support := by
  classical
  let G := factorGraph ts hfactors
  obtain ⟨a0, ha0⟩ := hσ.nonempty_support
  let C : G.ConnectedComponent := G.connectedComponentMk a0
  have hsubset : (↑σ.support : Set α) ⊆ C.supp := by
    simpa [G, C] using
      isCycle_support_subset_factorGraph_component σ hσ ts hfactors hprod ha0
  have hsupport_le : σ.support.card ≤ C.supp.toFinset.card := by
    exact Finset.card_le_card (by
      intro a ha
      simpa using hsubset ha)
  have hconn : C.toSimpleGraph.Connected := C.connected_toSimpleGraph
  let f : C ↪ α := ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
  have hsubset_map :
      ((C.toSimpleGraph).edgeFinset.map f.sym2Map) ⊆ G.edgeFinset := by
    intro e he
    rw [Finset.mem_map] at he
    rcases he with ⟨e', he', rfl⟩
    rw [SimpleGraph.mem_edgeFinset] at he'
    induction e' using Sym2.inductionOn with
    | hf u v =>
        rw [SimpleGraph.mem_edgeFinset]
        simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using he'
  have hcomponent_edges :
      (C.toSimpleGraph).edgeFinset.card ≤ G.edgeFinset.card := by
    calc
      (C.toSimpleGraph).edgeFinset.card
        = ((C.toSimpleGraph).edgeFinset.map f.sym2Map).card := by
            simp
      _ ≤ G.edgeFinset.card := Finset.card_le_card hsubset_map
  have hcard_vert :
      C.supp.toFinset.card ≤ (C.toSimpleGraph).edgeFinset.card + 1 := by
    have hverts := hconn.card_vert_le_card_edgeSet_add_one
    have hC :
        Nat.card C = C.supp.toFinset.card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_of_subtype C.supp.toFinset (by
        intro x
        rw [Set.mem_toFinset]
        show x ∈ C.supp ↔ x ∈ C
        rfl)
    have hedge :
        Nat.card ((C.toSimpleGraph).edgeSet) = (C.toSimpleGraph).edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    rw [hC, hedge] at hverts
    exact hverts
  have hcycle_le_component_edges :
      σ.support.card - 1 ≤ (C.toSimpleGraph).edgeFinset.card := by
    calc
      σ.support.card - 1 ≤ C.supp.toFinset.card - 1 := by
        exact Nat.sub_le_sub_right hsupport_le 1
      _ ≤ (C.toSimpleGraph).edgeFinset.card := by
        omega
  have hedge_le_cycle :
      G.edgeFinset.card ≤ σ.support.card - 1 := by
    calc
      G.edgeFinset.card ≤ ts.length := card_edgeFinset_factorGraph_le ts hfactors
      _ = σ.support.card - 1 := hmin
  have hcomponent_edges_eq :
      (C.toSimpleGraph).edgeFinset.card = G.edgeFinset.card := by
    omega
  have hcomponent_card_eq :
      C.supp.toFinset.card = σ.support.card := by
    have hcomponent_card_le : C.supp.toFinset.card ≤ σ.support.card := by
      calc
        C.supp.toFinset.card ≤ (C.toSimpleGraph).edgeFinset.card + 1 := hcard_vert
        _ = G.edgeFinset.card + 1 := by rw [hcomponent_edges_eq]
        _ ≤ (σ.support.card - 1) + 1 := Nat.succ_le_succ hedge_le_cycle
        _ = σ.support.card := by
              have hsupport_pos : 1 ≤ σ.support.card := by
                have htwo := hσ.two_le_card_support
                omega
              exact Nat.sub_add_cancel hsupport_pos
    exact Nat.le_antisymm hcomponent_card_le hsupport_le
  have hsupportC : σ.support = C.supp.toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      simpa using hsubset ha
    · rw [hcomponent_card_eq]
  have hedge_map_eq :
      ((C.toSimpleGraph).edgeFinset.map f.sym2Map) = G.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le hsubset_map
    rw [← hcomponent_edges_eq]
    simp
  have hfactorEdge :
      s(factorLeft ts hfactors t ht, factorRight ts hfactors t ht) ∈
        ((C.toSimpleGraph).edgeFinset.map f.sym2Map) := by
    rw [hedge_map_eq, SimpleGraph.mem_edgeFinset]
    exact factorGraph_edge_of_mem ts hfactors ht
  rw [Finset.mem_map] at hfactorEdge
  rcases hfactorEdge with ⟨e, he, heq⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
      have hu_eq : G.connectedComponentMk (u : α) = C := u.2
      have hv_eq : G.connectedComponentMk (v : α) = C := v.2
      rcases (Sym2.eq_iff).1 heq with hEq | hEq
      · constructor
        · rw [hsupportC, Set.mem_toFinset]
          exact hEq.1.symm ▸ hu_eq
        · rw [hsupportC, Set.mem_toFinset]
          exact hEq.2.symm ▸ hv_eq
      · constructor
        · rw [hsupportC, Set.mem_toFinset]
          exact hEq.2.symm ▸ hv_eq
        · rw [hsupportC, Set.mem_toFinset]
          exact hEq.1.symm ▸ hu_eq

/-- `Equiv.swap a b` reformulation of `minimal_factorization_factorEndpoints_mem_support`:
    if a minimal factor is presented as `Equiv.swap a b`, then `a, b ∈ σ.support`.

    Together with the previous theorem, both halves of
    the paper's Lemma 1(b) `W = V` are now public. -/
theorem minimal_factorization_factorEntries_mem_support
    (σ : Perm α) (hσ : σ.IsCycle)
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = σ)
    (hmin : ts.length = σ.support.card - 1)
    {t : Perm α} (ht : t ∈ ts) {a b : α}
    (htswap : t = Equiv.swap a b) :
    a ∈ σ.support ∧ b ∈ σ.support := by
  classical
  have hab : a ≠ b := by
    intro hab
    subst b
    have ht1 : t = (1 : Perm α) := by
      simpa [Equiv.swap_self] using htswap
    rcases hfactors t ht with ⟨u, v, huv, hswap⟩
    have : Equiv.swap u v = (1 : Perm α) := by simpa [ht1] using hswap.symm
    have huvu : v = u := by
      have := congrArg (fun f => f u) this
      simpa [Equiv.swap_apply_left] using this
    exact huv huvu.symm
  have hends :=
    minimal_factorization_factorEndpoints_mem_support σ hσ ts hfactors hprod hmin ht
  have hfactorEq :
      Equiv.swap a b =
        Equiv.swap (factorLeft ts hfactors t ht) (factorRight ts hfactors t ht) := by
    calc
      Equiv.swap a b = t := htswap.symm
      _ = Equiv.swap (factorLeft ts hfactors t ht) (factorRight ts hfactors t ht) :=
        factor_eq_swap_factorEndpoints ts hfactors t ht
  rcases (swap_eq_swap_iff hab).1 hfactorEq with
    hxy | hyx
  · constructor
    · simpa [hxy.1] using hends.1
    · simpa [hxy.2] using hends.2
  · constructor
    · simpa [hyx.1] using hends.2
    · simpa [hyx.2] using hends.1

private theorem support_mem_of_apply_mem_support
    {ρ : Perm α} {a : α} (ha : a ∈ ρ.support) :
    ρ a ∈ ρ.support := by
  rw [Equiv.Perm.mem_support] at ha ⊢
  intro hfix
  exact ha <| ρ.injective <| by simp [hfix]

private theorem support_mem_of_pow_apply_mem
    {ρ : Perm α} {a : α} (ha : a ∈ ρ.support) :
    ∀ n : ℕ, (ρ ^ n) a ∈ ρ.support := by
  intro n
  induction n with
  | zero =>
      simpa using ha
  | succ n ih =>
      simpa [pow_succ', Perm.mul_apply] using support_mem_of_apply_mem_support ih

private theorem disjoint_fix_of_mem_support_left
    {ρ κ : Perm α} (hdisj : Disjoint κ ρ) {a : α} (ha : a ∈ ρ.support) :
    κ a = a := by
  exact Equiv.Perm.notMem_support.mp
    ((Finset.disjoint_left.mp hdisj.disjoint_support.symm) ha)

private theorem isCycle_support_subset_factorGraph_component_of_disjoint_mul
    (ρ κ : Perm α) (hρ : ρ.IsCycle) (hdisj : Disjoint κ ρ)
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = κ * ρ)
    {a0 : α} (ha0 : a0 ∈ ρ.support) :
    (↑ρ.support : Set α) ⊆ (factorGraph ts hfactors).connectedComponentMk a0 := by
  have hpowpres :
      ∀ n : ℕ,
        (factorGraph ts hfactors).connectedComponentMk (((κ * ρ) ^ n) a0) =
          (factorGraph ts hfactors).connectedComponentMk a0 := by
    exact factorGraph_pow_preserves_component (κ * ρ) ts hfactors hprod a0
  have hpow_eq :
      ∀ n : ℕ, ((κ * ρ) ^ n) a0 = (ρ ^ n) a0 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hfixκ :
            κ ((ρ ^ (n + 1)) a0) = (ρ ^ (n + 1)) a0 :=
          disjoint_fix_of_mem_support_left hdisj
            (support_mem_of_pow_apply_mem ha0 (n + 1))
        simpa [pow_succ', Perm.mul_apply, ih] using hfixκ
  intro b hb
  obtain ⟨n, hn⟩ := hρ.exists_pow_eq (mem_support.mp ha0) (mem_support.mp hb)
  have hcomp :
      (factorGraph ts hfactors).connectedComponentMk b =
        (factorGraph ts hfactors).connectedComponentMk a0 := by
    calc
      (factorGraph ts hfactors).connectedComponentMk b
        = (factorGraph ts hfactors).connectedComponentMk ((ρ ^ n) a0) := by simp [hn]
      _ = (factorGraph ts hfactors).connectedComponentMk (((κ * ρ) ^ n) a0) := by
            simp [hpow_eq n]
      _ = (factorGraph ts hfactors).connectedComponentMk a0 := hpowpres n
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      ((factorGraph ts hfactors).connectedComponentMk a0) b).2 hcomp

private theorem no_cross_factor_of_disjoint_cycle_product
    (ρ κ : Perm α) (hρ : ρ.IsCycle) (hκ : κ.IsCycle) (hdisj : Disjoint κ ρ)
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = κ * ρ)
    (hlen : ts.length = ρ.support.card + κ.support.card - 2)
    {t : Perm α} (ht : t ∈ ts) {a b : α}
    (htswap : t = Equiv.swap a b)
    (ha : a ∈ ρ.support) :
    b ∉ κ.support := by
  classical
  intro hb
  let G := factorGraph ts hfactors
  let C : G.ConnectedComponent := G.connectedComponentMk a
  have hρsubset : (↑ρ.support : Set α) ⊆ C.supp := by
    simpa [G, C] using
      isCycle_support_subset_factorGraph_component_of_disjoint_mul
        ρ κ hρ hdisj ts hfactors hprod ha
  have hadj : G.Adj a b := by
    exact ⟨t, ht, htswap⟩
  have hab_comp :
      G.connectedComponentMk b = C := by
    simpa [C] using (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm
  have hκsubset : (↑κ.support : Set α) ⊆ C.supp := by
    have hprod' : ts.prod = ρ * κ := by
      calc
        ts.prod = κ * ρ := hprod
        _ = ρ * κ := hdisj.commute.eq
    have hsubset' :
        (↑κ.support : Set α) ⊆ G.connectedComponentMk b := by
      simpa [G] using
        isCycle_support_subset_factorGraph_component_of_disjoint_mul
          κ ρ hκ hdisj.symm ts hfactors hprod' hb
    intro x hx
    have hx' : x ∈ C.supp := by
      have hxb : x ∈ (G.connectedComponentMk b).supp := hsubset' hx
      simpa [C, hab_comp] using hxb
    simpa [C] using hx'
  have hdisj_fin : Disjoint ρ.support κ.support := hdisj.disjoint_support.symm
  have hsupport_le : ρ.support.card + κ.support.card ≤ C.supp.toFinset.card := by
    have hsubset_union : ρ.support ∪ κ.support ⊆ C.supp.toFinset := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxρ | hxκ
      · rw [Set.mem_toFinset]
        exact hρsubset hxρ
      · rw [Set.mem_toFinset]
        exact hκsubset hxκ
    calc
      ρ.support.card + κ.support.card = (ρ.support ∪ κ.support).card := by
        have hcard := Finset.card_union_add_card_inter ρ.support κ.support
        have hinter : ρ.support ∩ κ.support = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.mp hdisj_fin
        rw [hinter, Finset.card_empty, add_zero] at hcard
        exact hcard.symm
      _ ≤ C.supp.toFinset.card := Finset.card_le_card hsubset_union
  have hconn : C.toSimpleGraph.Connected := C.connected_toSimpleGraph
  have hcomponent_edges :
      (C.toSimpleGraph).edgeFinset.card ≤ G.edgeFinset.card := by
    let f : C ↪ α := ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
    have hsubset_map :
        ((C.toSimpleGraph).edgeFinset.map f.sym2Map) ⊆ G.edgeFinset := by
      intro e he
      rw [Finset.mem_map] at he
      rcases he with ⟨e', he', rfl⟩
      rw [SimpleGraph.mem_edgeFinset] at he'
      induction e' using Sym2.inductionOn with
      | hf u v =>
          rw [SimpleGraph.mem_edgeFinset]
          simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using he'
    calc
      (C.toSimpleGraph).edgeFinset.card
        = ((C.toSimpleGraph).edgeFinset.map f.sym2Map).card := by simp
      _ ≤ G.edgeFinset.card := Finset.card_le_card hsubset_map
  have hcard_vert :
      C.supp.toFinset.card ≤ (C.toSimpleGraph).edgeFinset.card + 1 := by
    have hverts := hconn.card_vert_le_card_edgeSet_add_one
    have hC :
        Nat.card C = C.supp.toFinset.card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_of_subtype C.supp.toFinset (by
        intro x
        rw [Set.mem_toFinset]
        show x ∈ C.supp ↔ x ∈ C
        rfl)
    have hedge :
        Nat.card ((C.toSimpleGraph).edgeSet) = (C.toSimpleGraph).edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    rw [hC, hedge] at hverts
    exact hverts
  have hedge_le :
      G.edgeFinset.card ≤ ρ.support.card + κ.support.card - 2 := by
    calc
      G.edgeFinset.card ≤ ts.length := card_edgeFinset_factorGraph_le ts hfactors
      _ = ρ.support.card + κ.support.card - 2 := hlen
  have hρcard : 2 ≤ ρ.support.card := hρ.two_le_card_support
  have hκcard : 2 ≤ κ.support.card := hκ.two_le_card_support
  omega

omit [DecidableEq α] [Fintype α] in
private theorem listProd_filter_apply_eq_of_mem
    (ts : List (Perm α))
    (p : Perm α → Prop) [DecidablePred p]
    (S : Finset α)
    (htrue : ∀ t ∈ ts, p t → ∀ z ∈ S, t z ∈ S)
    (hfalse : ∀ t ∈ ts, ¬ p t → ∀ z ∈ S, t z = z) :
    ∀ z ∈ S, (ts.filter p).prod z = ts.prod z := by
  intro z hz
  induction ts using List.reverseRecOn generalizing z with
  | nil =>
      simp
  | append_singleton ts t ih =>
      by_cases ht : p t
      · have htz : t z ∈ S := htrue t (by simp) ht z hz
        simp [List.filter_append, ht, List.prod_append, Perm.mul_apply]
        simpa using
          ih (fun u hu hu' a ha => htrue u (by simp [hu]) hu' a ha)
            (fun u hu hu' a ha => hfalse u (by simp [hu]) hu' a ha) (t z) htz
      · simp [List.filter_append, ht, List.prod_append, Perm.mul_apply, hfalse t (by simp) ht z hz]
        simpa using
          ih (fun u hu hu' a ha => htrue u (by simp [hu]) hu' a ha)
            (fun u hu hu' a ha => hfalse u (by simp [hu]) hu' a ha) z hz

private theorem support_card_formPerm_of_nodup
    (l : List α) (hl : l.Nodup) (hlen : 2 ≤ l.length) :
    (l.formPerm).support.card = l.length := by
  rw [List.support_formPerm_of_nodup _ hl]
  · simp [List.card_toFinset, hl.dedup]
  · intro x hx
    have := congrArg List.length hx
    simp at this
    omega

private noncomputable def cycleOrder (σ : Perm α) (hσ : σ.IsCycle) : List α :=
  (cycleFromPerm σ hσ).members.reverse

private theorem cycleOrder_nodup (σ : Perm α) (hσ : σ.IsCycle) :
    (cycleOrder σ hσ).Nodup := by
  unfold cycleOrder
  exact List.nodup_reverse.2 (cycleFromPerm σ hσ).nodup

private theorem mem_cycleOrder_iff_mem_support (σ : Perm α) (hσ : σ.IsCycle) {a : α} :
    a ∈ cycleOrder σ hσ ↔ a ∈ σ.support := by
  unfold cycleOrder
  rw [List.mem_reverse, mem_members_cycleFromPerm_iff_mem_support]

private theorem cycleOrder_length (σ : Perm α) (hσ : σ.IsCycle) :
    (cycleOrder σ hσ).length = σ.support.card := by
  unfold cycleOrder
  rw [List.length_reverse, members_length_cycleFromPerm]

private theorem sigma_eq_cycleOrder_formPerm (σ : Perm α) (hσ : σ.IsCycle) :
    (cycleOrder σ hσ).formPerm = σ := by
  unfold cycleOrder
  rw [members_cycleFromPerm]
  let x : α := cycleSeed σ hσ
  have hx_ne : σ x ≠ x := by
    simpa [x] using cycleSeed_ne_fixed σ hσ
  simpa [x, hσ.cycleOf_eq hx_ne] using (Equiv.Perm.formPerm_toList σ x)

private theorem sigma_apply_cycleOrder_eq_next
    (σ : Perm α) (hσ : σ.IsCycle) {a : α} (ha : a ∈ cycleOrder σ hσ) :
    σ a = (cycleOrder σ hσ).next a ha := by
  calc
    σ a = (cycleOrder σ hσ).formPerm a := by
      symm
      exact congrArg (fun π => π a) (sigma_eq_cycleOrder_formPerm σ hσ)
    _ = (cycleOrder σ hσ).next a ha := by
      exact List.formPerm_apply_mem_eq_next (cycleOrder_nodup σ hσ) a ha

omit [Fintype α] in
private theorem formPerm_append_singleton_eq
    (u : List α) (hu : u ≠ []) (a : α) :
    (u ++ [a]).formPerm = u.formPerm * swap (u.getLast hu) a := by
  have hsplit : u ++ [a] = (u.dropLast ++ [u.getLast hu]) ++ [a] := by
    rw [List.dropLast_append_getLast hu]
  calc
    (u ++ [a]).formPerm = ((u.dropLast ++ [u.getLast hu]) ++ [a]).formPerm := by
      rw [hsplit]
    _ = (u.dropLast ++ [u.getLast hu]).formPerm * swap (u.getLast hu) a := by
      simpa [List.append_assoc] using
        (List.formPerm_append_pair u.dropLast (u.getLast hu) a)
    _ = u.formPerm * swap (u.getLast hu) a := by
      rw [List.dropLast_append_getLast hu]

omit [DecidableEq α] [Fintype α] in
private theorem take_pair_drop_eq
    (l : List α) {n : ℕ} (hn : n + 1 < l.length) :
    l = l.take n ++ [l[n], l[n + 1]] ++ l.drop (n + 2) := by
  have hn0 : n < l.length := Nat.lt_of_succ_lt hn
  have hn1 : n + 1 < l.length := hn
  calc
    l = l.take n ++ l.drop n := by symm; exact List.take_append_drop n l
    _ = l.take n ++ (l[n] :: l.drop (n + 1)) := by
          rw [List.cons_getElem_drop_succ (h := hn0)]
    _ = l.take n ++ [l[n]] ++ l.drop (n + 1) := by simp
    _ = l.take n ++ [l[n]] ++ (l[n + 1] :: l.drop (n + 2)) := by
          rw [List.cons_getElem_drop_succ (l := l) (n := n + 1) (h := hn1)]
    _ = l.take n ++ [l[n], l[n + 1]] ++ l.drop (n + 2) := by simp [List.append_assoc]

omit [Fintype α] in
private theorem formPerm_append_mul_swap_getLast
    (r s : List α) (hr : r ≠ []) (hs : s ≠ [])
    (hdisj : r.Disjoint s) :
    (r ++ s).formPerm * swap (s.getLast hs) (r.getLast hr) = s.formPerm * r.formPerm := by
  classical
  induction s using List.reverseRecOn generalizing r with
  | nil =>
      contradiction
  | append_singleton s a ih =>
      by_cases hs0 : s = []
      · subst hs0
        calc
          (r ++ [a]).formPerm * swap a (r.getLast hr)
              = (r.formPerm * swap (r.getLast hr) a) * swap a (r.getLast hr) := by
                  rw [formPerm_append_singleton_eq r hr a]
          _ = r.formPerm := by
                simp [mul_assoc, Equiv.swap_comm]
      · have hsa : s ++ [a] ≠ [] := by simp
        have hdisj' : r.Disjoint s := by
          intro x hx hx'
          exact hdisj hx (by simp [hx'])
        have hnotin_r_a : a ∉ r := by
          intro ha
          exact hdisj ha (by simp)
        have hnotin_r_last : s.getLast hs0 ∉ r := by
          intro hmem
          exact hdisj hmem (by simp [List.getLast_mem _])
        have hform_append :
            (r ++ (s ++ [a])).formPerm = (r ++ s).formPerm * swap (s.getLast hs0) a := by
          have hrs : r ++ s ≠ [] := List.append_ne_nil_of_right_ne_nil r hs0
          simpa [List.append_assoc, List.getLast_append_of_right_ne_nil r s hs0] using
            (formPerm_append_singleton_eq (r ++ s) hrs a)
        have hbraid :
            swap (s.getLast hs0) a * swap a (r.getLast hr) =
              swap (s.getLast hs0) (r.getLast hr) * swap (s.getLast hs0) a := by
          have hneq1 : (r.getLast hr) ≠ s.getLast hs0 := by
            intro hEq
            exact hnotin_r_last (hEq ▸ List.getLast_mem _)
          have hneq2 : (r.getLast hr) ≠ a := by
            intro hEq
            exact hnotin_r_a (hEq ▸ List.getLast_mem _)
          have hfix :
              swap (s.getLast hs0) a (r.getLast hr) = r.getLast hr :=
            Equiv.swap_apply_of_ne_of_ne hneq1 hneq2
          simpa [hfix] using
            (mul_swap_eq_swap_mul (swap (s.getLast hs0) a) a (r.getLast hr))
        have hcomm :
            r.formPerm * swap (s.getLast hs0) a =
              swap (s.getLast hs0) a * r.formPerm := by
          have hfix_last : r.formPerm (s.getLast hs0) = s.getLast hs0 := by
            exact List.formPerm_apply_of_notMem hnotin_r_last
          have hfix_a : r.formPerm a = a := by
            exact List.formPerm_apply_of_notMem hnotin_r_a
          simpa [hfix_last, hfix_a] using
            (mul_swap_eq_swap_mul r.formPerm (s.getLast hs0) a)
        calc
          (r ++ (s ++ [a])).formPerm * swap ((s ++ [a]).getLast hsa) (r.getLast hr)
              = ((r ++ s).formPerm * swap (s.getLast hs0) a) *
                  swap a (r.getLast hr) := by
                    rw [hform_append]
                    simp
          _ = ((r ++ s).formPerm * swap (s.getLast hs0) (r.getLast hr)) *
                swap (s.getLast hs0) a := by
                  rw [mul_assoc, mul_assoc, hbraid]
          _ = (s.formPerm * r.formPerm) * swap (s.getLast hs0) a := by
                rw [ih r hr hs0 hdisj']
          _ = (s.formPerm * swap (s.getLast hs0) a) * r.formPerm := by
                rw [mul_assoc, hcomm, ← mul_assoc]
          _ = (s ++ [a]).formPerm * r.formPerm := by
                rw [formPerm_append_singleton_eq s hs0 a]

private theorem support_formPerm_eq_toFinset
    (l : List α) (hl : l.Nodup) (hlen : 2 ≤ l.length) :
    (l.formPerm).support = l.toFinset := by
  rw [List.support_formPerm_of_nodup _ hl]
  intro x hx
  have := congrArg List.length hx
  simp at this
  omega

omit [Fintype α] in
private theorem formPerm_apply_of_adjacent_split
    (l pre suf : List α) (a b : α)
    (hl : l = pre ++ [a, b] ++ suf)
    (hnodup : l.Nodup) :
    l.formPerm a = b := by
  subst hl
  have hlt : pre.length + 1 < (pre ++ [a, b] ++ suf).length := by
    simp
  calc
    (pre ++ [a, b] ++ suf).formPerm a
        = (pre ++ [a, b] ++ suf).formPerm ((pre ++ [a, b] ++ suf)[pre.length]) := by
            simp
    _ = (pre ++ [a, b] ++ suf)[pre.length + 1] := by
          simpa using
            (List.formPerm_apply_lt_getElem (pre ++ [a, b] ++ suf) hnodup pre.length hlt)
    _ = b := by simp

/-- A list-level strengthening of Lemma 1(c): for a minimal transposition
factorization of `l.formPerm`, one factor swaps two consecutive entries of `l`.

The proof is carried out on `formPerm` directly: peel off the rightmost factor,
split the cycle into `r` and `s`, filter the remaining factors into `Q / Qbar`,
and recurse on the smaller cycle `r` before pushing the result back to the
public cycle statement. -/
private theorem minimal_factorization_has_adjacent_formPerm
    (l : List α) (hl : l.Nodup) (hlen : 2 ≤ l.length)
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = l.formPerm)
    (hmin : ts.length = l.length - 1) :
    ∃ t ∈ ts, ∃ pre a b suf, l = pre ++ [a, b] ++ suf ∧ t = swap a b := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ l : List α, l.length = n → l.Nodup → 2 ≤ l.length →
      ∀ ts : List (Perm α),
        (∀ t ∈ ts, t.IsSwap) →
        ts.prod = l.formPerm →
        ts.length = l.length - 1 →
        ∃ t ∈ ts, ∃ pre a b suf, l = pre ++ [a, b] ++ suf ∧ t = swap a b
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih l hln hl hlen ts hfactors hprod hmin
    have hcycle : l.formPerm.IsCycle := List.isCycle_formPerm hl (by simpa [hln] using hlen)
    have hsupp : (l.formPerm).support = l.toFinset := support_formPerm_eq_toFinset l hl hlen
    have hsupp_card : (l.formPerm).support.card = l.length := by
      simpa using support_card_formPerm_of_nodup l hl hlen
    have hts_pos : 0 < ts.length := by
      rw [hmin]
      omega
    have hts_ne : ts ≠ [] := List.length_pos_iff_ne_nil.mp hts_pos
    induction ts using List.reverseRecOn with
    | nil =>
        contradiction
    | append_singleton ts0 t =>
        have hfactors0 : ∀ t' ∈ ts0, t'.IsSwap := by
          intro t' ht'
          exact hfactors t' (by simp [ht'])
        have hts0len : ts0.length = l.length - 2 := by
          have := hmin
          simp at this
          omega
        rcases hfactors t (by simp) with ⟨x, y, hxy, hswap0⟩
        have hmin_cycle : (ts0 ++ [t]).length = (l.formPerm).support.card - 1 := by
          simpa [hsupp_card] using hmin
        have hends_support :
            x ∈ (l.formPerm).support ∧ y ∈ (l.formPerm).support := by
          exact minimal_factorization_factorEntries_mem_support
            (σ := l.formPerm) hcycle (ts0 ++ [t]) hfactors hprod hmin_cycle
            (ht := by simp) hswap0
        have hx_mem : x ∈ l := by
          rw [← List.mem_toFinset, ← hsupp]
          exact hends_support.1
        have hy_mem : y ∈ l := by
          rw [← List.mem_toFinset, ← hsupp]
          exact hends_support.2
        let u := l.idxOf x
        let v := l.idxOf y
        have hu : u < l.length := by
          simpa [u] using (List.idxOf_lt_length_iff.2 hx_mem)
        have hv : v < l.length := by
          simpa [v] using (List.idxOf_lt_length_iff.2 hy_mem)
        have hxu : l[u] = x := by
          show l[List.idxOf x l] = x
          exact List.getElem_idxOf (l := l) hu
        have hyv : l[v] = y := by
          show l[List.idxOf y l] = y
          exact List.getElem_idxOf (l := l) hv
        have huv_ne : u ≠ v := by
          intro huv_eq
          have : x = y := by
            calc
              x = l[u] := hxu.symm
              _ = l[v] := by simp [huv_eq]
              _ = y := hyv
          exact hxy this
        have horient :
            ∃ a b u v, ∃ hu : u < l.length, ∃ hv : v < l.length,
              t = swap a b ∧ a ∈ l ∧ b ∈ l ∧ u < v ∧ l[u]'hu = a ∧ l[v]'hv = b := by
          rcases lt_or_gt_of_ne huv_ne with huv | hvu
          · exact ⟨x, y, u, v, hu, hv, hswap0, hx_mem, hy_mem, huv, by simpa using hxu, by simpa using hyv⟩
          · exact ⟨y, x, v, u, hv, hu, by simpa [Equiv.swap_comm] using hswap0,
              hy_mem, hx_mem, hvu, by simpa using hyv, by simpa using hxu⟩
        rcases horient with ⟨a, b, u, v, hu, hv, hswap, ha_mem, hb_mem, huv, hlu, hlv⟩
        by_cases hadj : v = u + 1
        · refine ⟨t, by simp, l.take u, a, b, l.drop (u + 2), ?_, hswap⟩
          have hlu1 : l[u + 1] = b := by
            simpa [hadj] using hlv
          calc
            l = l.take u ++ [l[u], l[u + 1]] ++ l.drop (u + 2) := by
                  exact take_pair_drop_eq l (by simpa [hadj] using hv)
            _ = l.take u ++ [a, b] ++ l.drop (u + 2) := by
                  simp [hlu, hlu1]
        · have huv1 : u + 1 < v := by omega
          let r : List α := (l.drop (u + 1)).take (v - u)
          let s : List α := l.drop (v + 1) ++ l.take (u + 1)
          have hrot_eq : l.rotate (u + 1) = r ++ s := by
            have hdrop_eq : (l.drop (u + 1)).drop (v - u) = l.drop (v + 1) := by
              rw [List.drop_drop]
              have huv_le : u ≤ v := Nat.le_of_lt huv
              have hsum : (u + 1) + (v - u) = v + 1 := by
                calc
                  (u + 1) + (v - u) = (u + (v - u)) + 1 := by omega
                  _ = v + 1 := by rw [Nat.add_sub_of_le huv_le]
              simp [hsum]
            have hsplit_drop :
                l.drop (u + 1) = (l.drop (u + 1)).take (v - u) ++ l.drop (v + 1) := by
              calc
                l.drop (u + 1)
                    = (l.drop (u + 1)).take (v - u) ++ (l.drop (u + 1)).drop (v - u) := by
                        symm
                        exact List.take_append_drop (v - u) (l.drop (u + 1))
                _ = (l.drop (u + 1)).take (v - u) ++ l.drop (v + 1) := by
                      rw [hdrop_eq]
            dsimp [r, s]
            rw [List.rotate_eq_drop_append_take (n := u + 1) (Nat.succ_le_of_lt hu)]
            conv_lhs => rw [hsplit_drop]
            simp [List.append_assoc]
          have hnodup_rot : (l.rotate (u + 1)).Nodup := by
            simpa using (List.nodup_rotate (l := l) (n := u + 1)).2 hl
          have hnodup_rs : (r ++ s).Nodup := by
            simpa [hrot_eq] using hnodup_rot
          have hr_nodup : r.Nodup := (List.nodup_append'.1 hnodup_rs).1
          have hs_nodup : s.Nodup := (List.nodup_append'.1 hnodup_rs).2.1
          have hrs_disj : r.Disjoint s := (List.nodup_append'.1 hnodup_rs).2.2
          have hr_len : r.length = v - u := by
            dsimp [r]
            rw [List.length_take]
            have hvu_bound : v - u ≤ (l.drop (u + 1)).length := by
              rw [List.length_drop]
              have hsub : v - u = (v - (u + 1)) + 1 := by omega
              rw [hsub]
              exact Nat.succ_le_of_lt (Nat.sub_lt_sub_right (Nat.le_of_lt huv1) hv)
            rw [Nat.min_eq_left hvu_bound]
          have hr_two : 2 ≤ r.length := by
            rw [hr_len]
            omega
          have hr_ne : r ≠ [] := by
            intro hr_nil
            have : r.length = 0 := by simp [hr_nil]
            omega
          have htake_ne : l.take (u + 1) ≠ [] := by
            intro hnil
            have hlen_take : (l.take (u + 1)).length = u + 1 := by
              rw [List.length_take, Nat.min_eq_left]
              omega
            rw [hnil] at hlen_take
            simp at hlen_take
          have hs_ne : s ≠ [] := by
            dsimp [s]
            exact List.append_ne_nil_of_right_ne_nil _ htake_ne
          have htake_eq : l.take (u + 1) = l.take u ++ [a] := by
            simpa [hlu] using (List.take_concat_get' l u hu).symm
          have hs_last : s.getLast hs_ne = a := by
            have htake_last' : (l.take u ++ [a]).getLast (by simp) = a := by
              simp
            have htake_last : (l.take (u + 1)).getLast htake_ne = a := by
              convert htake_last' using 1
              simp [htake_eq]
            dsimp [s]
            rw [List.getLast_append_of_right_ne_nil _ _ htake_ne]
            exact htake_last
          have hwlt : v - (u + 1) < (l.drop (u + 1)).length := by
            rw [List.length_drop]
            exact Nat.sub_lt_sub_right (Nat.le_of_lt huv1) hv
          have hdrop_get : (l.drop (u + 1))[v - (u + 1)] = b := by
            rw [List.getElem_drop]
            have hindex : u + 1 + (v - (u + 1)) = v := Nat.add_sub_of_le (Nat.le_of_lt huv1)
            simpa [hindex] using hlv
          have hr_eq : r = (l.drop (u + 1)).take (v - (u + 1)) ++ [b] := by
            dsimp [r]
            calc
              (l.drop (u + 1)).take (v - u)
                  = (l.drop (u + 1)).take ((v - (u + 1)) + 1) := by
                      congr
                      omega
              _ = (l.drop (u + 1)).take (v - (u + 1)) ++ [(l.drop (u + 1))[v - (u + 1)]] := by
                    symm
                    exact List.take_concat_get' (l.drop (u + 1)) (v - (u + 1)) hwlt
              _ = (l.drop (u + 1)).take (v - (u + 1)) ++ [b] := by
                    simp [hdrop_get]
          have hr_last : r.getLast hr_ne = b := by
            have hlast :
                ((l.drop (u + 1)).take (v - (u + 1)) ++ [b]).getLast
                    (by simp) = b := by
              simp
            convert hlast using 1
            simp [hr_eq]
          have hform_rot : l.formPerm = (r ++ s).formPerm := by
            have hrot : l ~r r ++ s := ⟨u + 1, hrot_eq⟩
            exact List.formPerm_eq_of_isRotated hl hrot
          have hprod_last : ts0.prod * swap a b = l.formPerm := by
            simpa [List.prod_append, hswap] using hprod
          have hprod0 : ts0.prod = s.formPerm * r.formPerm := by
            calc
              ts0.prod = (ts0.prod * swap a b) * swap a b := by
                simp [mul_assoc]
              _ = l.formPerm * swap a b := by rw [hprod_last]
              _ = (r ++ s).formPerm * swap (s.getLast hs_ne) (r.getLast hr_ne) := by
                    simp [hform_rot, hs_last, hr_last]
              _ = s.formPerm * r.formPerm := by
                    exact formPerm_append_mul_swap_getLast r s hr_ne hs_ne hrs_disj
          have hlen_rs : r.length + s.length = l.length := by
            have := congrArg List.length hrot_eq
            simpa using this.symm
          have hmem_r_or_s : ∀ {z : α}, z ∈ l ↔ z ∈ r ∨ z ∈ s := by
            intro z
            calc
              z ∈ l ↔ z ∈ l.rotate (u + 1) := by
                    exact (List.mem_rotate (l := l) (a := z) (n := u + 1)).symm
              _ ↔ z ∈ r ∨ z ∈ s := by
                    rw [hrot_eq, List.mem_append]
          have hfactorEnds_mem_l :
              ∀ {c d : α}, (swap c d : Perm α) ∈ ts0 → c ∈ l ∧ d ∈ l := by
            intro c d hτ
            have hends := minimal_factorization_factorEntries_mem_support
              (σ := l.formPerm) hcycle (ts0 ++ [t]) hfactors hprod hmin_cycle
              (t := (swap c d : Perm α)) (ht := by simp [hτ]) (a := c) (b := d) (htswap := rfl)
            have hc : c ∈ l := by
              rw [← List.mem_toFinset, ← hsupp]
              exact hends.1
            have hd : d ∈ l := by
              rw [← List.mem_toFinset, ← hsupp]
              exact hends.2
            exact ⟨hc, hd⟩
          have hr_support : (r.formPerm).support = r.toFinset := support_formPerm_eq_toFinset r hr_nodup hr_two
          by_cases hs_two : 2 ≤ s.length
          · have hs_support : (s.formPerm).support = s.toFinset := support_formPerm_eq_toFinset s hs_nodup hs_two
            have hrs_perm_disj : Disjoint s.formPerm r.formPerm := by
              rw [List.formPerm_disjoint_iff hs_nodup hr_nodup hs_two hr_two]
              exact hrs_disj.symm
            let inR : Perm α → Prop :=
              fun τ => ∃ c d, τ = swap c d ∧ c ∈ (r.formPerm).support ∧ d ∈ (r.formPerm).support
            let Q : List (Perm α) := ts0.filter inR
            let Qbar : List (Perm α) := ts0.filter fun τ => ¬ inR τ
            have hlen0' :
                ts0.length = (r.formPerm).support.card + (s.formPerm).support.card - 2 := by
              rw [hr_support, hs_support]
              simp [List.card_toFinset, hr_nodup.dedup, hs_nodup.dedup]
              omega
            have hQ_factors : ∀ τ ∈ Q, τ.IsSwap := by
              intro τ hτ
              exact hfactors0 τ (List.mem_of_mem_filter hτ)
            have hQbar_factors : ∀ τ ∈ Qbar, τ.IsSwap := by
              intro τ hτ
              exact hfactors0 τ (List.mem_of_mem_filter hτ)
            have hQ_pres :
                ∀ τ ∈ ts0, inR τ → ∀ z ∈ (r.formPerm).support, τ z ∈ (r.formPerm).support := by
              intro τ hτ hτR z hz
              rcases hτR with ⟨c, d, rfl, hc, hd⟩
              by_cases hzc : z = c
              · subst hzc
                simpa [Equiv.swap_apply_left] using hd
              by_cases hzd : z = d
              · subst hzd
                simpa [Equiv.swap_apply_right, hzc] using hc
              · simpa [Equiv.swap_apply_of_ne_of_ne hzc hzd] using hz
            -- A non-`inR` factor cannot cross between the two cycle supports,
            -- so both of its endpoints must lie on the `s` side.
            have hfactorEnds_mem_s_of_notinR :
                ∀ {c d : α}, (swap c d : Perm α) ∈ ts0 → ¬ inR (swap c d) →
                  c ∈ (s.formPerm).support ∧ d ∈ (s.formPerm).support := by
              intro c d hτ hτR
              have hc_mem_l : c ∈ l := (hfactorEnds_mem_l hτ).1
              have hd_mem_l : d ∈ l := (hfactorEnds_mem_l hτ).2
              have hc_s : c ∈ (s.formPerm).support := by
                rcases (hmem_r_or_s.1 hc_mem_l) with hcR | hcS
                · rw [← List.mem_toFinset, ← hr_support] at hcR
                  have hd_r : d ∈ (r.formPerm).support := by
                    rcases (hmem_r_or_s.1 hd_mem_l) with hdR | hdS
                    · rw [← List.mem_toFinset, ← hr_support] at hdR
                      exact hdR
                    · rw [← List.mem_toFinset, ← hs_support] at hdS
                      have hno := no_cross_factor_of_disjoint_cycle_product
                        (ρ := r.formPerm) (κ := s.formPerm)
                        (hρ := List.isCycle_formPerm hr_nodup hr_two)
                        (hκ := List.isCycle_formPerm hs_nodup hs_two)
                        hrs_perm_disj ts0 hfactors0 hprod0 hlen0'
                        (ht := hτ) (htswap := rfl) hcR
                      exact False.elim (hno hdS)
                  exact False.elim (hτR ⟨c, d, rfl, hcR, hd_r⟩)
                · rw [← List.mem_toFinset, ← hs_support] at hcS
                  exact hcS
              have hd_s : d ∈ (s.formPerm).support := by
                rcases (hmem_r_or_s.1 hd_mem_l) with hdR | hdS
                · rw [← List.mem_toFinset, ← hr_support] at hdR
                  have hc_r : c ∈ (r.formPerm).support := by
                    rcases (hmem_r_or_s.1 hc_mem_l) with hcR | hcS
                    · rw [← List.mem_toFinset, ← hr_support] at hcR
                      exact hcR
                    · rw [← List.mem_toFinset, ← hs_support] at hcS
                      have hno := no_cross_factor_of_disjoint_cycle_product
                        (ρ := r.formPerm) (κ := s.formPerm)
                        (hρ := List.isCycle_formPerm hr_nodup hr_two)
                        (hκ := List.isCycle_formPerm hs_nodup hs_two)
                        hrs_perm_disj ts0 hfactors0 hprod0 hlen0'
                        (ht := hτ)
                        (a := d) (b := c)
                        (htswap := by
                          simp [Equiv.swap_comm])
                        hdR
                      exact False.elim (hno hcS)
                  exact False.elim (hτR ⟨c, d, rfl, hc_r, hdR⟩)
                · rw [← List.mem_toFinset, ← hs_support] at hdS
                  exact hdS
              exact ⟨hc_s, hd_s⟩
            -- Once the endpoints are known to lie in `s.support`, the factor
            -- preserves `s.support` pointwise.
            have hQbar_pres :
                ∀ τ ∈ ts0, ¬ inR τ → ∀ z ∈ (s.formPerm).support, τ z ∈ (s.formPerm).support := by
              intro τ hτ hτR z hz
              rcases hfactors0 τ hτ with ⟨c, d, hcd, rfl⟩
              have hends_s : c ∈ (s.formPerm).support ∧ d ∈ (s.formPerm).support :=
                hfactorEnds_mem_s_of_notinR hτ hτR
              by_cases hzc : z = c
              · subst z
                simpa [Equiv.swap_apply_left] using hends_s.2
              by_cases hzd : z = d
              · subst z
                simpa [Equiv.swap_apply_right, hcd] using hends_s.1
              · simpa [Equiv.swap_apply_of_ne_of_ne hzc hzd] using hz
            -- The same `Qbar` factors fix every point in `r.support`, which is
            -- the hypothesis needed by `listProd_filter_apply_eq_of_mem`.
            have hQbar_fix_r :
                ∀ τ ∈ ts0, ¬ inR τ → ∀ z ∈ (r.formPerm).support, τ z = z := by
              intro τ hτ hτR z hz
              rcases hfactors0 τ hτ with ⟨c, d, hcd, rfl⟩
              have hends_s : c ∈ (s.formPerm).support ∧ d ∈ (s.formPerm).support :=
                hfactorEnds_mem_s_of_notinR hτ hτR
              have hzc : z ≠ c := by
                intro hEq
                subst z
                have hz_ne : r.formPerm c ≠ c := by
                  simpa [Equiv.Perm.mem_support] using hz
                exact hz_ne (disjoint_fix_of_mem_support_left hrs_perm_disj.symm hends_s.1)
              have hzd : z ≠ d := by
                intro hEq
                subst z
                have hz_ne : r.formPerm d ≠ d := by
                  simpa [Equiv.Perm.mem_support] using hz
                exact hz_ne (disjoint_fix_of_mem_support_left hrs_perm_disj.symm hends_s.2)
              simp [Equiv.swap_apply_of_ne_of_ne hzc hzd]
            have hQ_prod_apply :
                ∀ z ∈ (r.formPerm).support, Q.prod z = ts0.prod z := by
              intro z hz
              exact listProd_filter_apply_eq_of_mem ts0 inR (r.formPerm).support
                hQ_pres hQbar_fix_r z hz
            have hQbar_fix_s :
                ∀ τ ∈ ts0, inR τ → ∀ z ∈ (s.formPerm).support, τ z = z := by
              intro τ hτ hτR z hz
              rcases hτR with ⟨c, d, rfl, hc, hd⟩
              have hzc : z ≠ c := by
                intro hEq
                subst z
                have hz_ne : s.formPerm c ≠ c := by
                  simpa [Equiv.Perm.mem_support] using hz
                exact hz_ne (disjoint_fix_of_mem_support_left hrs_perm_disj hc)
              have hzd : z ≠ d := by
                intro hEq
                subst z
                have hz_ne : s.formPerm d ≠ d := by
                  simpa [Equiv.Perm.mem_support] using hz
                exact hz_ne (disjoint_fix_of_mem_support_left hrs_perm_disj hd)
              simp [Equiv.swap_apply_of_ne_of_ne hzc hzd]
            have hQbar_prod_apply :
                ∀ z ∈ (s.formPerm).support, Qbar.prod z = ts0.prod z := by
              intro z hz
              exact listProd_filter_apply_eq_of_mem ts0 (fun τ => ¬ inR τ) (s.formPerm).support
                hQbar_pres
                (by
                  intro τ hτ hτR z hz
                  exact hQbar_fix_s τ hτ (not_not.mp hτR) z hz)
                z hz
            have hQ_fix_out :
                ∀ z ∉ (r.formPerm).support, Q.prod z = z := by
              intro z hz
              apply listProd_apply_eq_of_forall_apply_eq
              intro τ hτ
              rcases List.mem_filter.1 hτ with ⟨hτ0, hτR⟩
              have hτR' : inR τ := by
                simpa using hτR
              rcases hτR' with ⟨c, d, rfl, hc, hd⟩
              have hzc : z ≠ c := by
                intro hEq; exact hz (hEq ▸ hc)
              have hzd : z ≠ d := by
                intro hEq; exact hz (hEq ▸ hd)
              simp [Equiv.swap_apply_of_ne_of_ne hzc hzd]
            have hQbar_fix_out :
                ∀ z ∉ (s.formPerm).support, Qbar.prod z = z := by
              intro z hz
              apply listProd_apply_eq_of_forall_apply_eq
              intro τ hτ
              rcases List.mem_filter.1 hτ with ⟨hτ0, hτR⟩
              have hτR' : ¬ inR τ := by
                simpa using hτR
              rcases hfactors0 τ hτ0 with ⟨c, d, hcd, rfl⟩
              have hends_s : c ∈ (s.formPerm).support ∧ d ∈ (s.formPerm).support :=
                hfactorEnds_mem_s_of_notinR hτ0 hτR'
              have hzc : z ≠ c := by intro hEq; exact hz (hEq ▸ hends_s.1)
              have hzd : z ≠ d := by intro hEq; exact hz (hEq ▸ hends_s.2)
              simp [Equiv.swap_apply_of_ne_of_ne hzc hzd]
            have hQ_prod : Q.prod = r.formPerm := by
              ext z
              by_cases hz : z ∈ (r.formPerm).support
              · have hz' : r.formPerm z ∈ (r.formPerm).support := support_mem_of_apply_mem_support hz
                rw [hQ_prod_apply z hz, hprod0, Perm.mul_apply, disjoint_fix_of_mem_support_left hrs_perm_disj hz']
              · rw [hQ_fix_out z hz, List.formPerm_apply_of_notMem]
                intro hz_mem
                apply hz
                have : z ∈ r.toFinset := List.mem_toFinset.mpr hz_mem
                simpa [hr_support] using this
            have hQbar_prod : Qbar.prod = s.formPerm := by
              ext z
              by_cases hz : z ∈ (s.formPerm).support
              · rw [hQbar_prod_apply z hz, hprod0, Perm.mul_apply,
                  disjoint_fix_of_mem_support_left hrs_perm_disj.symm hz]
              · rw [hQbar_fix_out z hz, List.formPerm_apply_of_notMem]
                intro hz_mem
                apply hz
                have : z ∈ s.toFinset := List.mem_toFinset.mpr hz_mem
                simpa [hs_support] using this
            have hlen_split :
                ts0.length = Q.length + Qbar.length := by
              simpa [Q, Qbar] using (ts0.length_eq_length_filter_add fun τ => decide (inR τ))
            have hQ_min :
                (r.formPerm).support.card - 1 ≤ Q.length := by
              exact transposition_count_ge_cycle_length
                (σ := r.formPerm) (List.isCycle_formPerm hr_nodup hr_two)
                Q hQ_factors hQ_prod
            have hQbar_min :
                (s.formPerm).support.card - 1 ≤ Qbar.length := by
              exact transposition_count_ge_cycle_length
                (σ := s.formPerm) (List.isCycle_formPerm hs_nodup hs_two)
                Qbar hQbar_factors hQbar_prod
            have hQ_len :
                Q.length = r.length - 1 := by
              rw [hr_support] at hQ_min
              rw [hs_support] at hQbar_min
              simp [List.card_toFinset, hr_nodup.dedup, hs_nodup.dedup] at hQ_min hQbar_min
              omega
            have hlt_r : r.length < n := by
              rw [← hln]
              omega
            rcases ih r.length hlt_r r rfl hr_nodup hr_two Q hQ_factors hQ_prod hQ_len with
              ⟨t', ht', pre, c, d, suf, hr_split, hteq⟩
            have hsplit_l :
                l = l.take (u + 1) ++ r ++ l.drop (v + 1) := by
              have hsplit_drop' :
                  l.drop (u + 1) = (l.drop (u + 1)).take (v - u) ++ l.drop (v + 1) := by
                calc
                  l.drop (u + 1)
                      = (l.drop (u + 1)).take (v - u) ++ (l.drop (u + 1)).drop (v - u) := by
                          symm
                          exact List.take_append_drop (v - u) (l.drop (u + 1))
                  _ = (l.drop (u + 1)).take (v - u) ++ l.drop (v + 1) := by
                        rw [List.drop_drop]
                        have hsum : (u + 1) + (v - u) = v + 1 := by
                          omega
                        simp [hsum]
              calc
                l = l.take (u + 1) ++ l.drop (u + 1) := by
                      symm
                      exact List.take_append_drop (u + 1) l
                _ = l.take (u + 1) ++ ((l.drop (u + 1)).take (v - u) ++ l.drop (v + 1)) := by
                      conv_lhs => rw [hsplit_drop']
                _ = l.take (u + 1) ++ r ++ l.drop (v + 1) := by
                      simp [r, List.append_assoc]
            refine ⟨t', ?_, l.take (u + 1) ++ pre, c, d, suf ++ l.drop (v + 1), ?_, hteq⟩
            · exact List.mem_append.2 <| Or.inl <| List.mem_of_mem_filter ht'
            calc
              l = l.take (u + 1) ++ r ++ l.drop (v + 1) := hsplit_l
              _ = l.take (u + 1) ++ (pre ++ [c, d] ++ suf) ++ l.drop (v + 1) := by rw [hr_split]
              _ = (l.take (u + 1) ++ pre) ++ [c, d] ++ (suf ++ l.drop (v + 1)) := by
                    simp [List.append_assoc]
          · have hs_len1 : s.length = 1 := by omega
            have hs_one : s.formPerm = (1 : Perm α) := by
              rw [List.formPerm_eq_one_iff (l := s) hs_nodup]
              omega
            have hprod_r : ts0.prod = r.formPerm := by
              simpa [hs_one] using hprod0
            have hQ_len : ts0.length = r.length - 1 := by
              omega
            have hlt_r : r.length < n := by
              rw [← hln]
              omega
            rcases ih r.length hlt_r r rfl hr_nodup hr_two ts0 hfactors0 hprod_r hQ_len with
              ⟨t', ht', pre, c, d, suf, hr_split, hteq⟩
            have hsplit_l :
                l = l.take (u + 1) ++ r ++ l.drop (v + 1) := by
              have hsplit_drop' :
                  l.drop (u + 1) = (l.drop (u + 1)).take (v - u) ++ l.drop (v + 1) := by
                calc
                  l.drop (u + 1)
                      = (l.drop (u + 1)).take (v - u) ++ (l.drop (u + 1)).drop (v - u) := by
                          symm
                          exact List.take_append_drop (v - u) (l.drop (u + 1))
                  _ = (l.drop (u + 1)).take (v - u) ++ l.drop (v + 1) := by
                        rw [List.drop_drop]
                        have hsum : (u + 1) + (v - u) = v + 1 := by
                          omega
                        simp [hsum]
              calc
                l = l.take (u + 1) ++ l.drop (u + 1) := by
                      symm
                      exact List.take_append_drop (u + 1) l
                _ = l.take (u + 1) ++ ((l.drop (u + 1)).take (v - u) ++ l.drop (v + 1)) := by
                      conv_lhs => rw [hsplit_drop']
                _ = l.take (u + 1) ++ r ++ l.drop (v + 1) := by
                      simp [r, List.append_assoc]
            refine ⟨t', by simp [ht'], l.take (u + 1) ++ pre, c, d, suf ++ l.drop (v + 1), ?_, hteq⟩
            calc
              l = l.take (u + 1) ++ r ++ l.drop (v + 1) := hsplit_l
              _ = l.take (u + 1) ++ (pre ++ [c, d] ++ suf) ++ l.drop (v + 1) := by rw [hr_split]
              _ = (l.take (u + 1) ++ pre) ++ [c, d] ++ (suf ++ l.drop (v + 1)) := by
                    simp [List.append_assoc]
  exact hP l.length l rfl hl hlen ts hfactors hprod hmin

/-- Lemma 1(c): A minimal factorization contains an adjacent transposition.
    Proof (Isaacs/Verstraete): G is a tree. Take the rightmost factor (aᵤaᵥ)
    with u < v. If v−u = 1, done. Otherwise, removing edge [aᵤ,aᵥ] splits G
    into trees R (on {aᵤ₊₁,...,aᵥ}) and S. The w-cycle r = (aᵤ₊₁...aᵥ) equals
    the product of w−1 factors from R. By induction, one has the required form. -/
theorem minimal_factorization_has_adjacent
    (σ : Perm α) (hσ : σ.IsCycle)
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = σ)
    (hmin : ts.length = σ.support.card - 1) :
    ∃ t ∈ ts, ∃ a ∈ σ.support, t = swap a (σ a) := by
  classical
  let l := cycleOrder σ hσ
  have hl : l.Nodup := cycleOrder_nodup σ hσ
  have hlen : 2 ≤ l.length := by
    simp [l, cycleOrder_length]
    exact hσ.two_le_card_support
  have hform : ts.prod = l.formPerm := by
    simpa [l, sigma_eq_cycleOrder_formPerm σ hσ] using hprod
  have hmin' : ts.length = l.length - 1 := by
    simpa [l, cycleOrder_length σ hσ] using hmin
  rcases minimal_factorization_has_adjacent_formPerm l hl hlen ts hfactors hform hmin' with
    ⟨t, ht, pre, a, b, suf, hl_split, hteq⟩
  refine ⟨t, ht, a, ?_, ?_⟩
  · rw [← mem_cycleOrder_iff_mem_support σ hσ]
    simp [l, hl_split]
  · have hsigma : σ a = b := by
      have hfa : l.formPerm a = b := formPerm_apply_of_adjacent_split l pre suf a b hl_split hl
      calc
        σ a = l.formPerm a := by
          simpa [l] using congrArg (fun π => π a) (sigma_eq_cycleOrder_formPerm σ hσ).symm
        _ = b := hfa
    calc
      t = swap a b := hteq
      _ = swap a (σ a) := by rw [hsigma]

/-- Paper-strong Lemma 1(c): the wrap-around exclusion `1 ≤ i < k` is preserved.

    Stronger than `minimal_factorization_has_adjacent` (which permits the
    wrap-around `swap a_k a_1`). The conclusion exposes the underlying
    `pre ++ [a, b] ++ suf` split structure of the cycle-order list, witnessing
    that `a` and `b` are *interior* consecutive elements of some
    `formPerm`-presentation of `σ`. The wrap-around case `a = a_k` is
    automatically excluded because a single `[a, b]` adjacency cannot span
    the end and start of `l`.

    The list `l` returned in the existential is `cycleOrder σ hσ` internally,
    but the public conclusion abstracts away the implementation by quantifying
    over arbitrary `l` with the required `formPerm`-and-Nodup contract.
    paper-strong upgrade of Lemma 1(c). -/
theorem minimal_factorization_has_adjacent_paper
    (σ : Perm α) (hσ : σ.IsCycle)
    (ts : List (Perm α))
    (hfactors : ∀ t ∈ ts, t.IsSwap)
    (hprod : ts.prod = σ)
    (hmin : ts.length = σ.support.card - 1) :
    ∃ t ∈ ts, ∃ l : List α, ∃ pre suf : List α, ∃ a b : α,
      l.Nodup ∧ l.formPerm = σ ∧ l = pre ++ [a, b] ++ suf ∧ t = swap a b := by
  classical
  let l := cycleOrder σ hσ
  have hl : l.Nodup := cycleOrder_nodup σ hσ
  have hlen : 2 ≤ l.length := by
    simp [l, cycleOrder_length]
    exact hσ.two_le_card_support
  have hform : ts.prod = l.formPerm := by
    simpa [l, sigma_eq_cycleOrder_formPerm σ hσ] using hprod
  have hmin' : ts.length = l.length - 1 := by
    simpa [l, cycleOrder_length σ hσ] using hmin
  rcases minimal_factorization_has_adjacent_formPerm l hl hlen ts hfactors hform hmin' with
    ⟨t, ht, pre, a, b, suf, hl_split, hteq⟩
  exact ⟨t, ht, l, pre, suf, a, b, hl,
    sigma_eq_cycleOrder_formPerm σ hσ, hl_split, hteq⟩


end Futurama
end Project
