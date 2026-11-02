/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import KostochkaThomason.Robust

/-!
# The sampling lemma (Lemma 2 of Alon–Krivelevich–Sudakov)

Let every vertex of `U` have more than `|U| / 6` neighbours in `U`. Among the `|U|^s` sequences
`f : Fin s → U` we count those that fail one of three requirements:

* more than `ε` vertices of `U` have no neighbour in the sample (Markov's inequality: the expected
  number of such vertices is at most `|U| (5/6)^s`);
* the sample lies inside one of `t` given sets `A j` of size at most `ε` (at most `t ε^s`);
* some sample point has fewer than `a` sample neighbours (a Chernoff bound with the exponential
  moment `e^{-1}`: at most `s e^a q^{s-1} |U|^s` with `q = 1 - (1 - e^{-1}) / 6`).

If each of these is below a third of all sequences, a good sample exists. This is the probabilistic
argument of the lemma written as a count over the uniform product space.
-/

@[expose] public section

open SimpleGraph Finset

namespace KostochkaThomason

variable {V : Type*}

section Sampling

open scoped Classical

variable [Fintype V] {G : SimpleGraph V}

/-- The number of sample points adjacent to the `k`-th one. -/
noncomputable def sampleDeg (G : SimpleGraph V) {s : ℕ} (f : Fin s → V) (k : Fin s) : ℕ :=
  (univ.filter fun l => G.Adj (f k) (f l)).card

/-- The vertices of `U` with no neighbour in the sample. -/
noncomputable def undominated (G : SimpleGraph V) (U : Finset V) {s : ℕ} (f : Fin s → V) :
    Finset V :=
  U.filter fun v => ∀ k, ¬ G.Adj v (f k)

/-- The Chernoff ratio. -/
noncomputable def chernoffQ : ℝ := 1 - (1 - Real.exp (-1)) / 6

theorem chernoffQ_nonneg : 0 ≤ chernoffQ := by
  unfold chernoffQ
  have : 0 < Real.exp (-1) := Real.exp_pos _
  linarith

theorem card_piFinset_const (U : Finset V) (s : ℕ) :
    (Fintype.piFinset fun _ : Fin s => U).card = U.card ^ s := by
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]

theorem filter_forall_piFinset (U : Finset V) (s : ℕ) (P : V → Prop) :
    (Fintype.piFinset fun _ : Fin s => U).filter (fun f => ∀ k, P (f k)) =
      Fintype.piFinset fun _ : Fin s => U.filter P := by
  ext f
  simp [Fintype.mem_piFinset, forall_and]

theorem card_filter_adj (U : Finset V) (u : V) :
    (U.filter fun w => G.Adj u w).card = degIn G U u := by
  unfold degIn
  congr 1
  ext w
  simp [and_comm]

/-! ### Domination (Markov) -/

theorem sum_card_undominated (U : Finset V) (s : ℕ) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin s => U), (undominated G U f).card =
      ∑ v ∈ U, (U.filter fun w => ¬ G.Adj v w).card ^ s := by
  unfold undominated
  rw [show (∑ f ∈ Fintype.piFinset (fun _ : Fin s => U),
      (U.filter fun v => ∀ k, ¬ G.Adj v (f k)).card) =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin s => U), ∑ v ∈ U,
        if (∀ k, ¬ G.Adj v (f k)) then 1 else 0 from sum_congr rfl fun f _ => card_filter _ _]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← card_filter, ← card_piFinset_const]
  congr 1
  ext f
  simp [Fintype.mem_piFinset, forall_and]

theorem card_bad_domination {U : Finset V} (hdeg : ∀ v ∈ U, U.card < 6 * degIn G U v)
    {s : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (((Fintype.piFinset fun _ : Fin s => U).filter
        fun f => ε < (undominated G U f).card).card : ℝ) * ε ≤
      U.card * ((5 / 6 : ℝ) * U.card) ^ s := by
  set Ω := Fintype.piFinset fun _ : Fin s => U
  calc ((Ω.filter fun f => ε < (undominated G U f).card).card : ℝ) * ε
      = ∑ f ∈ Ω.filter (fun f => ε < (undominated G U f).card), ε := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ f ∈ Ω.filter (fun f => ε < (undominated G U f).card), ((undominated G U f).card : ℝ) :=
        sum_le_sum fun f hf => (mem_filter.1 hf).2.le
    _ ≤ ∑ f ∈ Ω, ((undominated G U f).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
    _ = ∑ v ∈ U, ((U.filter fun w => ¬ G.Adj v w).card : ℝ) ^ s := by
        rw [← Nat.cast_sum, sum_card_undominated]; push_cast; rfl
    _ ≤ ∑ v ∈ U, ((5 / 6 : ℝ) * U.card) ^ s := by
        refine sum_le_sum fun v hv => pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
        have h1 := card_filter_add_card_filter_not (s := U) (fun w => G.Adj v w)
        rw [card_filter_adj] at h1
        have h3 : (degIn G U v : ℝ) + (U.filter fun w => ¬ G.Adj v w).card = U.card := by
          exact_mod_cast h1
        have h4 : (U.card : ℝ) < 6 * degIn G U v := by exact_mod_cast hdeg v hv
        linarith
    _ = U.card * ((5 / 6 : ℝ) * U.card) ^ s := by rw [sum_const, nsmul_eq_mul]

/-! ### Avoidance -/

theorem card_bad_avoid {U A : Finset V} {s : ℕ} {ε : ℝ} (hA : ((A ∩ U).card : ℝ) ≤ ε) :
    (((Fintype.piFinset fun _ : Fin s => U).filter fun f => ∀ k, f k ∈ A).card : ℝ) ≤ ε ^ s := by
  have hf : ((Fintype.piFinset fun _ : Fin s => U).filter fun f => ∀ k, f k ∈ A) =
      Fintype.piFinset fun _ : Fin s => U.filter (· ∈ A) := by
    ext f
    simp [Fintype.mem_piFinset, forall_and]
  rw [hf, card_piFinset_const]
  push_cast
  refine pow_le_pow_left₀ (Nat.cast_nonneg _) (le_trans ?_ hA) _
  exact_mod_cast card_le_card fun v hv => by
    rw [mem_filter] at hv; exact mem_inter.2 ⟨hv.2, hv.1⟩

/-! ### Spread (Chernoff) -/

theorem cast_sampleDeg {s : ℕ} (f : Fin s → V) (k : Fin s) :
    (sampleDeg G f k : ℝ) = ∑ l, if G.Adj (f k) (f l) then (1 : ℝ) else 0 := by
  unfold sampleDeg
  rw [card_filter]
  push_cast
  rfl

theorem exp_neg_sampleDeg {s : ℕ} (f : Fin s → V) (k : Fin s) :
    Real.exp (-(sampleDeg G f k : ℝ)) =
      ∏ l, if G.Adj (f k) (f l) then Real.exp (-1) else 1 := by
  rw [cast_sampleDeg, ← sum_neg_distrib, Real.exp_sum]
  refine prod_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem sum_weight_le {U : Finset V} (hdeg : ∀ v ∈ U, U.card < 6 * degIn G U v) {u : V}
    (hu : u ∈ U) :
    ∑ w ∈ U, (if G.Adj u w then Real.exp (-1) else 1) ≤ chernoffQ * U.card := by
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, card_filter_adj]
  have h1 := card_filter_add_card_filter_not (s := U) (fun w => G.Adj u w)
  rw [card_filter_adj] at h1
  have h3 : (degIn G U u : ℝ) + (U.filter fun w => ¬ G.Adj u w).card = U.card := by
    exact_mod_cast h1
  have h4 : (U.card : ℝ) < 6 * degIn G U u := by exact_mod_cast hdeg u hu
  have h5 : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
    simpa using this
  have h6 : 0 < (6 * (degIn G U u : ℝ) - U.card) * (1 - Real.exp (-1)) :=
    mul_pos (by linarith) (by linarith)
  unfold chernoffQ
  nlinarith

theorem filter_eq_piFinset {U : Finset V} {s : ℕ} (k : Fin s) {u : V} (hu : u ∈ U) :
    (Fintype.piFinset fun _ : Fin s => U).filter (fun f => f k = u) =
      Fintype.piFinset fun l => if l = k then ({u} : Finset V) else U := by
  ext f
  simp only [mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩ l
    split_ifs with hl
    · subst hl; exact mem_singleton.2 h2
    · exact h1 l
  · intro h
    refine ⟨fun l => ?_, ?_⟩
    · have := h l
      split_ifs at this with hl
      · rw [mem_singleton.1 this]; exact hu
      · exact this
    · have := h k
      rw [if_pos rfl] at this
      exact mem_singleton.1 this

theorem card_bad_spread {U : Finset V} (hdeg : ∀ v ∈ U, U.card < 6 * degIn G U v) {s : ℕ}
    (k : Fin s) (a : ℕ) :
    (((Fintype.piFinset fun _ : Fin s => U).filter fun f => sampleDeg G f k < a).card : ℝ) ≤
      Real.exp a * chernoffQ ^ (s - 1) * (U.card : ℝ) ^ s := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by have := k.2; omega⟩
  set Ω := Fintype.piFinset fun _ : Fin (m + 1) => U
  set φ : V → V → ℝ := fun u w => if G.Adj u w then Real.exp (-1) else 1
  have hφ0 : ∀ u w, 0 ≤ φ u w := fun u w => by
    simp only [φ]; split_ifs <;> positivity
  calc ((Ω.filter fun f => sampleDeg G f k < a).card : ℝ)
      = ∑ f ∈ Ω.filter (fun f => sampleDeg G f k < a), (1 : ℝ) := by
        rw [sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ f ∈ Ω.filter (fun f => sampleDeg G f k < a),
          Real.exp ((a : ℝ) - sampleDeg G f k) := by
        refine sum_le_sum fun f hf => Real.one_le_exp ?_
        have : sampleDeg G f k < a := (mem_filter.1 hf).2
        have : (sampleDeg G f k : ℝ) < a := by exact_mod_cast this
        linarith
    _ ≤ ∑ f ∈ Ω, Real.exp ((a : ℝ) - sampleDeg G f k) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => (Real.exp_pos _).le
    _ = Real.exp a * ∑ f ∈ Ω, ∏ l, φ (f k) (f l) := by
        rw [mul_sum]
        refine sum_congr rfl fun f _ => ?_
        rw [sub_eq_add_neg, Real.exp_add, exp_neg_sampleDeg]
    _ = Real.exp a * ∑ u ∈ U, ∑ f ∈ Ω.filter (fun f => f k = u), ∏ l, φ u (f l) := by
        congr 1
        rw [← sum_fiberwise_of_maps_to (g := fun f => f k) (t := U)
          fun f hf => (Fintype.mem_piFinset.1 hf) k]
        refine sum_congr rfl fun u _ => sum_congr rfl fun f hf => ?_
        rw [(mem_filter.1 hf).2]
    _ = Real.exp a * ∑ u ∈ U, (∑ w ∈ U, φ u w) ^ (m + 1 - 1) := by
        congr 1
        refine sum_congr rfl fun u hu => ?_
        rw [filter_eq_piFinset k hu, ← prod_univ_sum]
        have : ∀ l, (∑ w ∈ (if l = k then ({u} : Finset V) else U), φ u w) =
            if l = k then 1 else ∑ w ∈ U, φ u w := by
          intro l
          split_ifs
          · simp [φ]
          · rfl
        simp_rw [this]
        rw [prod_ite, prod_const_one, one_mul, prod_const]
        congr 1
        rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    _ ≤ Real.exp a * ∑ u ∈ U, (chernoffQ * U.card) ^ (m + 1 - 1) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun u hu => ?_) (Real.exp_pos _).le
        exact pow_le_pow_left₀ (sum_nonneg fun w _ => hφ0 u w) (sum_weight_le hdeg hu) _
    _ = Real.exp a * chernoffQ ^ (m + 1 - 1) * (U.card : ℝ) ^ (m + 1) := by
        rw [sum_const, nsmul_eq_mul, mul_pow, Nat.add_sub_cancel, pow_succ]
        ring

/-! ### The lemma -/

/-- **Lemma 2 of Alon–Krivelevich–Sudakov, as a count.** -/
theorem exists_good_sample {U : Finset V} (hdeg : ∀ v ∈ U, U.card < 6 * degIn G U v)
    {s a t : ℕ} {ε : ℝ} (hε : 0 < ε) (A : ℕ → Finset V)
    (hA : ∀ j < t, ((A j ∩ U).card : ℝ) ≤ ε)
    (h1 : 3 * (U.card : ℝ) * (5 / 6 : ℝ) ^ s ≤ ε)
    (h2 : 3 * (t : ℝ) * ε ^ s < (U.card : ℝ) ^ s)
    (h3 : 3 * (s : ℝ) * Real.exp a * chernoffQ ^ (s - 1) ≤ 1) :
    ∃ f : Fin s → V, (∀ k, f k ∈ U) ∧ ((undominated G U f).card : ℝ) ≤ ε ∧
      (∀ j < t, ∃ k, f k ∉ A j) ∧ ∀ k, a ≤ sampleDeg G f k := by
  set Ω := Fintype.piFinset fun _ : Fin s => U
  set B1 := Ω.filter fun f => ε < (undominated G U f).card
  set B2 := (range t).biUnion fun j => Ω.filter fun f => ∀ k, f k ∈ A j
  set B3 := univ.biUnion fun k : Fin s => Ω.filter fun f => sampleDeg G f k < a
  have hN : (Ω.card : ℝ) = (U.card : ℝ) ^ s := by rw [card_piFinset_const]; push_cast; rfl
  have hb1 : (B1.card : ℝ) * 3 ≤ (U.card : ℝ) ^ s := by
    have := card_bad_domination hdeg (s := s) hε
    rw [mul_pow, ← mul_assoc] at this
    have h1' : (U.card : ℝ) * (5 / 6 : ℝ) ^ s * 3 ≤ ε := by linarith
    have hNs : 0 ≤ (U.card : ℝ) ^ s := by positivity
    nlinarith
  have hb2 : (B2.card : ℝ) * 3 < (U.card : ℝ) ^ s := by
    have : (B2.card : ℝ) ≤ t * ε ^ s := by
      calc (B2.card : ℝ) ≤ ∑ j ∈ range t, ((Ω.filter fun f => ∀ k, f k ∈ A j).card : ℝ) := by
            exact_mod_cast card_biUnion_le
        _ ≤ ∑ j ∈ range t, ε ^ s :=
            sum_le_sum fun j hj => card_bad_avoid (hA j (mem_range.1 hj))
        _ = t * ε ^ s := by rw [sum_const, card_range, nsmul_eq_mul]
    linarith
  have hb3 : (B3.card : ℝ) * 3 ≤ (U.card : ℝ) ^ s := by
    have : (B3.card : ℝ) ≤ s * (Real.exp a * chernoffQ ^ (s - 1) * (U.card : ℝ) ^ s) := by
      calc (B3.card : ℝ) ≤ ∑ k : Fin s,
            ((Ω.filter fun f => sampleDeg G f k < a).card : ℝ) := by
            exact_mod_cast card_biUnion_le
        _ ≤ ∑ k : Fin s, Real.exp a * chernoffQ ^ (s - 1) * (U.card : ℝ) ^ s :=
            sum_le_sum fun k _ => card_bad_spread hdeg k a
        _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNs : 0 ≤ (U.card : ℝ) ^ s := by positivity
    nlinarith
  have hlt : ((B1 ∪ B2 ∪ B3).card : ℝ) < Ω.card := by
    have : ((B1 ∪ B2 ∪ B3).card : ℝ) ≤ B1.card + B2.card + B3.card := by
      exact_mod_cast (card_union_le _ _).trans (by
        have := card_union_le B1 B2; omega)
    rw [hN]; linarith
  obtain ⟨f, hfΩ, hfB⟩ : ∃ f ∈ Ω, f ∉ B1 ∪ B2 ∪ B3 := by
    by_contra hno
    push_neg at hno
    have : Ω.card ≤ (B1 ∪ B2 ∪ B3).card := card_le_card fun f hf => hno f hf
    have : (Ω.card : ℝ) ≤ (B1 ∪ B2 ∪ B3).card := by exact_mod_cast this
    linarith
  simp only [mem_union, not_or] at hfB
  obtain ⟨⟨n1, n2⟩, n3⟩ := hfB
  refine ⟨f, Fintype.mem_piFinset.1 hfΩ, ?_, fun j hj => ?_, fun k => ?_⟩
  · by_contra h
    exact n1 (mem_filter.2 ⟨hfΩ, lt_of_not_ge h⟩)
  · by_contra h
    push_neg at h
    exact n2 (mem_biUnion.2 ⟨j, mem_range.2 hj, mem_filter.2 ⟨hfΩ, h⟩⟩)
  · by_contra h
    exact n3 (mem_biUnion.2 ⟨k, mem_univ _, mem_filter.2 ⟨hfΩ, lt_of_not_ge h⟩⟩)

end Sampling

end KostochkaThomason
