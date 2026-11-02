/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import CliqueMinorsLib.Minors

/-!
# Reduction to a minor-minimal graph

The first step of Alon–Krivelevich–Sudakov: a graph with at least `d · |S|` edges on a support `S`
has a minor in which some vertex `x` has at most `2d` neighbours, every one of which has at least
`d` neighbours among the neighbours of `x`. We prove it in the form "to find a `K_t` minor of `G`
it suffices to find one in every graph with such a vertex", by contracting edges that lie in fewer
than `d` triangles, deleting surplus edges and removing isolated vertices.
-/

@[expose] public section

open SimpleGraph CliqueMinors

namespace KostochkaThomason

variable {V : Type*}

section Reduce

open scoped Classical

variable [Fintype V]

theorem degree_eq_zero_of_not_mem {G : SimpleGraph V} {S : Finset V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) {v : V} (hv : v ∉ S) : G.degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  exact hv (hsupp _ _ ((mem_neighborFinset _ _ _).1 hw))

theorem sum_degree_support {G : SimpleGraph V} {S : Finset V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    ∑ v ∈ S, G.degree v = 2 * G.edgeFinset.card := by
  rw [← sum_degrees_eq_twice_card_edges]
  refine Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_
  exact degree_eq_zero_of_not_mem hsupp hv

theorem two_le_card_of_adj {G : SimpleGraph V} {S : Finset V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) {a b : V} (hab : G.Adj a b) : 2 ≤ S.card := by
  have h : ({a, b} : Finset V) ⊆ S := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact hsupp _ _ hab
    · rw [Finset.mem_singleton.1 hv]; exact hsupp _ _ hab.symm
  have := Finset.card_le_card h
  rwa [Finset.card_pair hab.ne] at this

theorem card_edgeFinset_deleteEdge {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    (G.deleteEdges {e}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have h : (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
    ext f
    simp only [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff,
      Finset.mem_erase]
    tauto
  rw [h, Finset.card_erase_of_mem he]
  have := Finset.card_pos.2 ⟨e, he⟩
  omega

/-- **Reduction to a minor-minimal graph.** If every graph with a vertex `x` whose (nonempty)
neighbourhood has at most `2d` vertices, each with at least `d` neighbours inside it, has a `K_t`
minor, then so does every graph with at least `d · |S|` edges supported on `S`. -/
theorem reduce {d t : ℕ} (hd : 1 ≤ d) (ht : 2 ≤ t)
    (core : ∀ (G : SimpleGraph V) (x : V), (G.neighborFinset x).Nonempty →
      (G.neighborFinset x).card ≤ 2 * d →
      (∀ y ∈ G.neighborFinset x, d ≤ (G.neighborFinset x ∩ G.neighborFinset y).card) →
      IsMinor (⊤ : SimpleGraph (Fin t)) G) :
    ∀ (G : SimpleGraph V) (S : Finset V), (∀ a b, G.Adj a b → a ∈ S) →
      d * S.card ≤ G.edgeFinset.card → 0 < G.edgeFinset.card →
      IsMinor (⊤ : SimpleGraph (Fin t)) G := by
  suffices ∀ n (G : SimpleGraph V) (S : Finset V), S.card = n → (∀ a b, G.Adj a b → a ∈ S) →
      d * S.card ≤ G.edgeFinset.card → 0 < G.edgeFinset.card →
      IsMinor (⊤ : SimpleGraph (Fin t)) G from fun G S => this _ G S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  suffices ∀ m (G : SimpleGraph V) (S : Finset V), G.edgeFinset.card = m → S.card = n →
      (∀ a b, G.Adj a b → a ∈ S) → d * S.card ≤ G.edgeFinset.card → 0 < G.edgeFinset.card →
      IsMinor (⊤ : SimpleGraph (Fin t)) G from fun G S => this _ G S rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro G S hm hn hsupp hE hE0
  obtain ⟨a₀, b₀, hab₀⟩ := CliqueMinors.exists_adj_of_card_pos hE0
  have hS2 := two_le_card_of_adj hsupp hab₀
  -- Case A: an edge whose contraction keeps the density.
  by_cases hc : ∃ x y, G.Adj x y ∧ d * (S.card - 1) ≤ (contractG G x y).edgeFinset.card
  · obtain ⟨x, y, hxy, hc⟩ := hc
    refine isMinor_lift_contract (G' := contractG G x y) hxy
      (fun u v h => (contractG_adj.1 h).2) ht ?_
    have hyS : y ∈ S := hsupp _ _ hxy.symm
    have hcard := Finset.card_erase_of_mem hyS
    refine ihn (S.card - 1) (by omega) (contractG G x y) (S.erase y) hcard
      (contract_support hxy hsupp) (by rw [hcard]; exact hc) ?_
    have : 1 ≤ d * (S.card - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  simp only [not_exists, not_and, not_le] at hc
  -- Case B: surplus edges.
  by_cases hsur : d * S.card < G.edgeFinset.card
  · obtain ⟨e, he⟩ := Finset.card_pos.1 hE0
    have hdel := card_edgeFinset_deleteEdge he
    refine isMinor_mono (G' := G.deleteEdges {e}) (deleteEdges_le _) ?_
    have h1 : 1 ≤ d * S.card := Nat.mul_pos (by omega) (by omega)
    have key : ∀ H : SimpleGraph V, H = G.deleteEdges {e} →
        H.edgeFinset.card + 1 = G.edgeFinset.card := by
      rintro H rfl; convert hdel
    have h' := key _ rfl
    refine ihm _ ?_ (G.deleteEdges {e}) S rfl hn
      (fun a b h => hsupp a b (deleteEdges_le _ h)) ?_ ?_
    all_goals omega
  have hEq : G.edgeFinset.card = d * S.card := by omega
  -- Case C: an isolated vertex of the support.
  by_cases hiso : ∃ x ∈ S, G.degree x = 0
  · obtain ⟨x, hxS, hx0⟩ := hiso
    have hcard := Finset.card_erase_of_mem hxS
    refine ihn (S.card - 1) (by omega) G (S.erase x) hcard (fun a b h => ?_) ?_ hE0
    · refine Finset.mem_erase.2 ⟨fun hax => ?_, hsupp a b h⟩
      subst hax
      have : b ∈ G.neighborFinset a := (mem_neighborFinset _ _ _).2 h
      rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero] at hx0
      simp [hx0] at this
    · rw [hcard]
      have : d * (S.card - 1) ≤ d * S.card := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      omega
  simp only [not_exists, not_and] at hiso
  -- Case D: a vertex of degree at most `2d` is the required vertex.
  have hsum := sum_degree_support hsupp
  obtain ⟨x, hxS, hx⟩ : ∃ x ∈ S, G.degree x ≤ 2 * d := by
    by_contra hno
    push_neg at hno
    have : ∑ v ∈ S, (2 * d + 1) ≤ ∑ v ∈ S, G.degree v := Finset.sum_le_sum fun v hv => hno v hv
    rw [Finset.sum_const, smul_eq_mul] at this
    have hpos : 0 < S.card := by omega
    nlinarith
  refine core G x ?_ (by rwa [card_neighborFinset_eq_degree]) fun y hy => ?_
  · rw [← Finset.card_pos, card_neighborFinset_eq_degree]
    exact Nat.pos_of_ne_zero (hiso x hxS)
  · have hxy : G.Adj x y := (mem_neighborFinset _ _ _).1 hy
    have h1 := card_edge_contract hxy
    have h2 := hc x y hxy
    have : d * (S.card - 1) + d = d * S.card := by
      rw [Nat.mul_sub_one]; have : d ≤ d * S.card := Nat.le_mul_of_pos_right _ (by omega)
      omega
    omega

end Reduce

end KostochkaThomason
