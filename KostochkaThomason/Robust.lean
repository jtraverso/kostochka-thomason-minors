/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# A robustly connected dense piece

Second step of Alon–Krivelevich–Sudakov. If `N` has at most `2d` vertices and every vertex of `N`
has at least `d` neighbours in `N`, then some `W ⊆ N` has every vertex with at least `2d/3`
neighbours in `W` and stays connected after the removal of any fewer than `d/3` vertices.
-/

@[expose] public section

open SimpleGraph

namespace KostochkaThomason

variable {V : Type*}

section Robust

open scoped Classical

variable [Fintype V]

/-- The number of neighbours of `v` in `U`. -/
noncomputable def degIn (G : SimpleGraph V) (U : Finset V) (v : V) : ℕ :=
  (G.neighborFinset v ∩ U).card

/-- `G` restricted to `W` stays connected after the removal of any fewer than `k / 3` vertices
(precisely: of any `R` with `3 |R| < k`). -/
def RobustlyConnected (G : SimpleGraph V) (W : Finset V) (k : ℕ) : Prop :=
  ∀ R : Finset V, 3 * R.card < k → (G.induce (↑(W \ R) : Set V)).Connected

theorem degIn_mono (G : SimpleGraph V) {U U' : Finset V} (h : U ⊆ U') (v : V) :
    degIn G U v ≤ degIn G U' v :=
  Finset.card_le_card (Finset.inter_subset_inter_left h)

theorem degIn_sdiff (G : SimpleGraph V) (U R : Finset V) (v : V) :
    degIn G U v ≤ degIn G (U \ R) v + R.card := by
  unfold degIn
  calc (G.neighborFinset v ∩ U).card
      ≤ (G.neighborFinset v ∩ (U \ R) ∪ R).card := by
        refine Finset.card_le_card fun w hw => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hw
        by_cases hR : w ∈ R
        · exact Finset.mem_union_right _ hR
        · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨h1, Finset.mem_sdiff.2 ⟨h2, hR⟩⟩)
    _ ≤ _ := Finset.card_union_le _ _

/-- A set in which every two vertices have a common neighbour outside any removed `R` is
connected after the removal of `R`. -/
theorem induce_connected_of_common {G : SimpleGraph V} {W : Finset V}
    (hne : W.Nonempty)
    (hcom : ∀ u ∈ W, ∀ w ∈ W, u ≠ w → G.Adj u w ∨ ∃ z ∈ W, G.Adj u z ∧ G.Adj z w) :
    (G.induce (↑W : Set V)).Connected := by
  obtain ⟨r, hr⟩ := hne
  have : Nonempty (↑(↑W : Set V)) := ⟨⟨r, hr⟩⟩
  refine Connected.mk fun a b => ?_
  by_cases hab : a = b
  · rw [hab]
  rcases hcom a.1 a.2 b.1 b.2 (fun h => hab (Subtype.ext h)) with h | ⟨z, hz, h1, h2⟩
  · exact (Adj.reachable (by simpa using h))
  · refine (Adj.reachable (G := G.induce (↑W : Set V)) (v := ⟨z, hz⟩) ?_).trans ?_
    · simpa using h1
    · exact Adj.reachable (by simpa using h2)

/-- **The robust piece.** -/
theorem exists_robust {G : SimpleGraph V} {d : ℕ} {N : Finset V} (hd : 1 ≤ d)
    (hN : N.card ≤ 2 * d) (hdeg : ∀ v ∈ N, d ≤ degIn G N v) (hne : N.Nonempty) :
    ∃ W ⊆ N, W.Nonempty ∧ (∀ v ∈ W, 2 * d ≤ 3 * degIn G W v) ∧ RobustlyConnected G W d := by
  by_cases hrob : RobustlyConnected G N d
  · exact ⟨N, le_rfl, hne, fun v hv => by have := hdeg v hv; omega, hrob⟩
  unfold RobustlyConnected at hrob
  push_neg at hrob
  obtain ⟨R, hR, hdis⟩ := hrob
  -- `N \ R` is nonempty: a vertex of `N` has at least `d > |R|` neighbours in `N`.
  obtain ⟨v₀, hv₀⟩ := hne
  have hNR : (N \ R).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
    have h1 := hdeg v₀ hv₀
    have h2 : degIn G N v₀ ≤ N.card := Finset.card_le_card Finset.inter_subset_right
    have h3 := Finset.card_le_card hemp
    omega
  obtain ⟨u, hu⟩ := hNR
  set X : Set V := ↑(N \ R)
  have : Nonempty X := ⟨⟨u, hu⟩⟩
  -- `A` is the component of `u` in `N \ R`, and `B` is the rest.
  let reach : V → Prop := fun w =>
    ∃ hw : w ∈ N \ R, (G.induce X).Reachable ⟨u, hu⟩ ⟨w, hw⟩
  set A := (N \ R).filter reach
  set B := (N \ R).filter (fun w => ¬ reach w)
  have hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
    intro a ha b hb hab
    obtain ⟨-, ha'⟩ := Finset.mem_filter.1 ha
    obtain ⟨hbN, hb'⟩ := Finset.mem_filter.1 hb
    obtain ⟨haN, hra⟩ := ha'
    exact hb' ⟨hbN, hra.trans (Adj.reachable (by simpa using hab))⟩
  have hBne : B.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
    refine hdis (Connected.mk fun a b => ?_)
    have ha := hemp a.2
    have hb := hemp b.2
    push_neg at ha hb
    obtain ⟨_, ha⟩ := ha
    obtain ⟨_, hb⟩ := hb
    exact ha.symm.trans hb
  have hAne : A.Nonempty := ⟨u, Finset.mem_filter.2 ⟨hu, hu, Reachable.refl _⟩⟩
  have hAB : A.card + B.card = (N \ R).card := Finset.card_filter_add_card_filter_not _
  have hNRc : (N \ R).card ≤ N.card := Finset.card_le_card Finset.sdiff_subset
  -- The smaller side `W` of the cut.
  obtain ⟨W, Y, hW, hY, hWY, hWsub, hYsub, hWc⟩ : ∃ W Y : Finset V, W.Nonempty ∧ Y.Nonempty ∧
      (∀ a ∈ W, ∀ b ∈ Y, ¬ G.Adj a b) ∧ W ⊆ N \ R ∧ (∀ w ∈ N \ R, w ∉ W → w ∈ Y) ∧
      W.card ≤ d := by
    by_cases hc : A.card ≤ B.card
    · refine ⟨A, B, hAne, hBne, hnoAB, Finset.filter_subset _ _, fun w hw hwA =>
        Finset.mem_filter.2 ⟨hw, fun h => hwA (Finset.mem_filter.2 ⟨hw, h⟩)⟩, by omega⟩
    · refine ⟨B, A, hBne, hAne, fun b hb a ha hba => hnoAB a ha b hb hba.symm,
        Finset.filter_subset _ _, fun w hw hwB => ?_, by omega⟩
      by_contra hwA
      exact hwB (Finset.mem_filter.2 ⟨hw, fun h => hwA (Finset.mem_filter.2 ⟨hw, h⟩)⟩)
  have hWN : W ⊆ N := hWsub.trans Finset.sdiff_subset
  -- Every vertex of `W` has more than `2d/3` neighbours in `W`.
  have hdegW : ∀ v ∈ W, d ≤ degIn G W v + R.card := by
    intro v hv
    have h1 := hdeg v (hWN hv)
    refine h1.trans ?_
    unfold degIn
    calc (G.neighborFinset v ∩ N).card ≤ (G.neighborFinset v ∩ W ∪ R).card := by
          refine Finset.card_le_card fun w hw => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hw
          by_cases hR : w ∈ R
          · exact Finset.mem_union_right _ hR
          · refine Finset.mem_union_left _ (Finset.mem_inter.2 ⟨h1, ?_⟩)
            by_contra hwW
            exact hWY v hv w (hYsub w (Finset.mem_sdiff.2 ⟨h2, hR⟩) hwW)
              ((mem_neighborFinset _ _ _).1 h1)
      _ ≤ _ := Finset.card_union_le _ _
  refine ⟨W, hWN, hW, fun v hv => by have := hdegW v hv; omega, fun R' hR' => ?_⟩
  -- Two vertices of `W` have more than `d/3` common neighbours in `W`.
  have hcommon : ∀ a ∈ W, ∀ b ∈ W,
      d < 3 * (G.neighborFinset a ∩ W ∩ (G.neighborFinset b ∩ W)).card := by
    intro a ha b hb
    have h1 := hdegW a ha
    have h2 := hdegW b hb
    have h3 := Finset.card_union_add_card_inter (G.neighborFinset a ∩ W) (G.neighborFinset b ∩ W)
    have h4 : (G.neighborFinset a ∩ W ∪ G.neighborFinset b ∩ W).card ≤ W.card :=
      Finset.card_le_card (Finset.union_subset Finset.inter_subset_right
        Finset.inter_subset_right)
    unfold degIn at h1 h2
    omega
  have hWR : (W \ R').Nonempty := by
    obtain ⟨a, ha⟩ := hW
    have h := hcommon a ha a ha
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
    have : (G.neighborFinset a ∩ W ∩ (G.neighborFinset a ∩ W)).card ≤ R'.card :=
      Finset.card_le_card ((Finset.inter_subset_right.trans Finset.inter_subset_right).trans hemp)
    omega
  refine induce_connected_of_common hWR fun a ha b hb _ => Or.inr ?_
  obtain ⟨haW, -⟩ := Finset.mem_sdiff.1 ha
  obtain ⟨hbW, -⟩ := Finset.mem_sdiff.1 hb
  have h := hcommon a haW b hbW
  obtain ⟨z, hz, hzR⟩ : ∃ z ∈ G.neighborFinset a ∩ W ∩ (G.neighborFinset b ∩ W), z ∉ R' := by
    by_contra hno
    push_neg at hno
    have : (G.neighborFinset a ∩ W ∩ (G.neighborFinset b ∩ W)).card ≤ R'.card :=
      Finset.card_le_card hno
    omega
  simp only [Finset.mem_inter, mem_neighborFinset] at hz
  exact ⟨z, Finset.mem_sdiff.2 ⟨hz.1.2, hzR⟩, hz.1.1, hz.2.1.symm⟩

end Robust

end KostochkaThomason
