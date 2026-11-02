/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import CliqueMinorsLib.Minors
public import KostochkaThomason.Connect
public import KostochkaThomason.Sampling

/-!
# Growing the branch sets

The iteration of Alon–Krivelevich–Sudakov. Inside a robustly connected dense piece `W`, branch
sets `B 0, B 1, …` are built one at a time: the next one is a good sample of the remaining vertices
(Lemma 2), made connected by short paths. It meets every earlier branch set and leaves at most `ε`
remaining vertices without a neighbour in it; as long as fewer than `d / 3` vertices have been
used, the remaining graph stays connected and dense, so the iteration can go on.
-/

@[expose] public section

open SimpleGraph CliqueMinors Finset

namespace KostochkaThomason

variable {V : Type*}

section Iterate

open scoped Classical

variable [Fintype V] {G : SimpleGraph V}

/-- The invariant after `i` branch sets have been chosen. -/
def BranchInv (G : SimpleGraph V) (W : Finset V) (m : ℕ) (ε : ℝ) (i : ℕ) (B : ℕ → Finset V) :
    Prop :=
  (∀ j < i, B j ⊆ W ∧ (B j).Nonempty ∧ (G.induce (↑(B j) : Set V)).Connected ∧
    (B j).card ≤ m) ∧
  (∀ j < i, ∀ j' < i, j ≠ j' → Disjoint (B j) (B j')) ∧
  (∀ j < i, ∀ j' < i, j ≠ j' → ∃ u ∈ B j, ∃ v ∈ B j', G.Adj u v) ∧
  (∀ j < i, (((W \ (range i).biUnion B).filter fun v => ∀ b ∈ B j, ¬ G.Adj v b).card : ℝ) ≤ ε)

theorem card_used_le {W : Finset V} {m i : ℕ} {ε : ℝ} {B : ℕ → Finset V}
    (h : BranchInv G W m ε i B) : ((range i).biUnion B).card ≤ i * m := by
  calc ((range i).biUnion B).card ≤ ∑ j ∈ range i, (B j).card := card_biUnion_le
    _ ≤ ∑ j ∈ range i, m := sum_le_sum fun j hj => (h.1 j (mem_range.1 hj)).2.2.2
    _ = i * m := by rw [sum_const, card_range, smul_eq_mul]

/-- **One step of the iteration.** -/
theorem branchInv_step {d s a K T : ℕ} {ε : ℝ} (hε : 0 < ε) {W : Finset V}
    (hW : W.card ≤ 2 * d) (hdegW : ∀ v ∈ W, 2 * d ≤ 3 * degIn G W v)
    (hrob : RobustlyConnected G W d) (hs : 0 < s) (hK : s < (a + 1) * (K + 1))
    (hT : 3 * T * (s + 15 * K) < d) (h1 : 3 * (2 * d : ℝ) * (5 / 6 : ℝ) ^ s ≤ ε)
    (h2 : 3 * (T : ℝ) * ε ^ s < ((d : ℝ) / 3) ^ s)
    (h3 : 3 * (s : ℝ) * Real.exp a * chernoffQ ^ (s - 1) ≤ 1)
    {i : ℕ} (hi : i < T) {B : ℕ → Finset V} (hB : BranchInv G W (s + 15 * K) ε i B) :
    ∃ B' : ℕ → Finset V, BranchInv G W (s + 15 * K) ε (i + 1) B' := by
  set m := s + 15 * K
  set R := (range i).biUnion B
  set U := W \ R
  have hR : 3 * R.card < d := by
    have : R.card ≤ i * m := by convert card_used_le hB
    have : i * m ≤ T * m := Nat.mul_le_mul_right _ hi.le
    have : 3 * (T * m) = 3 * T * m := by ring
    omega
  -- The remaining graph is dense and connected.
  have hdegU : ∀ v ∈ U, U.card < 6 * degIn G U v := by
    intro v hv
    have hvW : v ∈ W := (mem_sdiff.1 hv).1
    have h1 : degIn G W v ≤ degIn G U v + R.card := degIn_sdiff G W R v
    have h2 := hdegW v hvW
    have h3 : U.card ≤ W.card := card_le_card sdiff_subset
    omega
  have hconn : (G.induce (↑U : Set V)).Connected := hrob R hR
  have hUcard : (d : ℝ) / 3 ≤ U.card := by
    obtain ⟨⟨v, hv'⟩⟩ := hconn.nonempty
    have hv' : v ∈ U := hv'
    have h2 : degIn G U v + 1 ≤ U.card := by
      have hsub : insert v (G.neighborFinset v ∩ U) ⊆ U :=
        insert_subset hv' inter_subset_right
      have := card_le_card hsub
      rwa [card_insert_of_notMem (by simp)] at this
    have h3 : degIn G W v ≤ degIn G U v + R.card := degIn_sdiff G W R v
    have h4 := hdegW v (mem_sdiff.1 hv').1
    have : d ≤ 3 * U.card := by omega
    have : (d : ℝ) ≤ 3 * U.card := by exact_mod_cast this
    linarith
  -- A good sample of `U`.
  set A : ℕ → Finset V := fun j => W.filter fun v => ∀ b ∈ B j, ¬ G.Adj v b
  have hA : ∀ j < i, ((A j ∩ U).card : ℝ) ≤ ε := by
    intro j hj
    refine le_trans ?_ (hB.2.2.2 j hj)
    exact_mod_cast card_le_card fun v hv => by
      simp only [A, mem_inter, mem_filter] at hv
      exact mem_filter.2 ⟨hv.2, hv.1.2⟩
  have hd : (0 : ℝ) ≤ d / 3 := by positivity
  have hs1 : 3 * (U.card : ℝ) * (5 / 6 : ℝ) ^ s ≤ ε := by
    refine le_trans ?_ h1
    have : (U.card : ℝ) ≤ 2 * d := by exact_mod_cast (card_le_card sdiff_subset).trans hW
    have : (0 : ℝ) ≤ (5 / 6 : ℝ) ^ s := by positivity
    nlinarith
  have hs2 : 3 * (i : ℝ) * ε ^ s < (U.card : ℝ) ^ s := by
    have : (i : ℝ) ≤ T := by exact_mod_cast hi.le
    have : 3 * (i : ℝ) * ε ^ s ≤ 3 * (T : ℝ) * ε ^ s := by
      have := pow_pos hε s; nlinarith
    exact lt_of_le_of_lt this (h2.trans_le (pow_le_pow_left₀ hd hUcard _))
  obtain ⟨f, hfU, hdom, havoid, hspread⟩ :=
    exists_good_sample (G := G) hdegU (a := a) hε A hA hs1 hs2 h3
  -- Make it connected.
  obtain ⟨C, hCU, hfC, hCcard, hCconn⟩ :=
    exists_connected_superset hconn hdegU hs f hfU hspread hK
  refine ⟨fun j => if j = i then C else B j, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · dsimp only; rw [if_pos hji]
      exact ⟨hCU.trans sdiff_subset, ⟨f ⟨0, hs⟩, hfC _⟩, hCconn, hCcard⟩
    · dsimp only; rw [if_neg hji]
      exact hB.1 j (by omega)
  · intro j hj j' hj' hjj'
    have hdisjC : ∀ j < i, Disjoint C (B j) := fun j hj => by
      refine disjoint_left.2 fun v hvC hvB => ?_
      exact (mem_sdiff.1 (hCU hvC)).2 (mem_biUnion.2 ⟨j, mem_range.2 hj, hvB⟩)
    by_cases hji : j = i <;> by_cases hj'i : j' = i <;> simp only [hji, hj'i, ite_true, ite_false]
    · omega
    · exact hdisjC j' (by omega)
    · exact (hdisjC j (by omega)).symm
    · exact hB.2.1 j (by omega) j' (by omega) hjj'
  · intro j hj j' hj' hjj'
    have hadjC : ∀ j < i, ∃ u ∈ C, ∃ v ∈ B j, G.Adj u v := fun j hj => by
      obtain ⟨k, hk⟩ := havoid j hj
      have hkW : f k ∈ W := (mem_sdiff.1 (hfU k)).1
      simp only [A, mem_filter, not_and, not_forall, not_not] at hk
      obtain ⟨b, hb, hadj⟩ := hk hkW
      exact ⟨f k, hfC k, b, hb, hadj⟩
    by_cases hji : j = i <;> by_cases hj'i : j' = i <;> simp only [hji, hj'i, ite_true, ite_false]
    · omega
    · exact hadjC j' (by omega)
    · obtain ⟨u, hu, v, hv, h⟩ := hadjC j (by omega)
      exact ⟨v, hv, u, hu, h.symm⟩
    · exact hB.2.2.1 j (by omega) j' (by omega) hjj'
  · intro j hj
    have hsub : W \ (range (i + 1)).biUnion (fun j => if j = i then C else B j) ⊆ U \ C := by
      intro v hv
      obtain ⟨hvW, hvR⟩ := mem_sdiff.1 hv
      refine mem_sdiff.2 ⟨mem_sdiff.2 ⟨hvW, fun hvR' => hvR ?_⟩, fun hvC => hvR ?_⟩
      · obtain ⟨j', hj', hvB⟩ := mem_biUnion.1 hvR'
        have : j' ≠ i := by have := mem_range.1 hj'; omega
        exact mem_biUnion.2 ⟨j', mem_range.2 (by have := mem_range.1 hj'; omega),
          by simp only [this, ite_false]; exact hvB⟩
      · exact mem_biUnion.2 ⟨i, mem_range.2 (by omega), by simp only [ite_true]; exact hvC⟩
    by_cases hji : j = i
    · simp only [hji, ite_true]
      refine le_trans ?_ hdom
      exact_mod_cast card_le_card fun v hv => by
        obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
        have hv3 := hsub hv1
        exact mem_filter.2 ⟨(mem_sdiff.1 hv3).1, fun k => hv2 (f k) (hfC k)⟩
    · simp only [hji, ite_false]
      refine le_trans ?_ (hB.2.2.2 j (by omega))
      exact_mod_cast card_le_card fun v hv => by
        obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
        exact mem_filter.2 ⟨(mem_sdiff.1 (hsub hv1)).1, hv2⟩

/-- **The iteration.** `T` branch sets forming a `K_T` minor. -/
theorem isMinor_of_robust {d s a K T : ℕ} {ε : ℝ} (hε : 0 < ε) {W : Finset V}
    (hW : W.card ≤ 2 * d) (hdegW : ∀ v ∈ W, 2 * d ≤ 3 * degIn G W v)
    (hrob : RobustlyConnected G W d) (hs : 0 < s) (hK : s < (a + 1) * (K + 1))
    (hT : 3 * T * (s + 15 * K) < d) (h1 : 3 * (2 * d : ℝ) * (5 / 6 : ℝ) ^ s ≤ ε)
    (h2 : 3 * (T : ℝ) * ε ^ s < ((d : ℝ) / 3) ^ s)
    (h3 : 3 * (s : ℝ) * Real.exp a * chernoffQ ^ (s - 1) ≤ 1) :
    IsMinor (⊤ : SimpleGraph (Fin T)) G := by
  have key : ∀ i ≤ T, ∃ B, BranchInv G W (s + 15 * K) ε i B := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨fun _ => ∅, fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ i ih =>
      intro hi
      obtain ⟨B, hB⟩ := ih (by omega)
      exact branchInv_step hε hW hdegW hrob hs hK hT h1 h2 h3 (by omega) hB
  obtain ⟨B, hB⟩ := key T le_rfl
  refine ⟨⟨fun w => B w.1, fun w => (hB.1 w.1 w.2).2.1, fun w => (hB.1 w.1 w.2).2.2.1,
    fun w w' hww' => hB.2.1 w.1 w.2 w'.1 w'.2 (fun h => hww' (Fin.ext h)),
    fun w w' hww' => hB.2.2.1 w.1 w.2 w'.1 w'.2 (fun h => hww'.ne (Fin.ext h))⟩⟩

end Iterate

end KostochkaThomason
