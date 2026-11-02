/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import CliqueMinorsLib.Minors
public import KostochkaThomason.Reduce
public import KostochkaThomason.Iterate
public import KostochkaThomason.Numeric

/-!
# Complete minors and average degree

The theorem of Kostochka (1982) and Thomason (1984), in the form of Theorem 1 of
Alon–Krivelevich–Sudakov: for every sufficiently large integer `d`, a graph with at least `d · |V|`
edges has a `K_t` minor for every `t ≤ d / (10 √(ln d))`.
-/

@[expose] public section

open SimpleGraph CliqueMinors Real

namespace KostochkaThomason

universe u

/-- **Alon–Krivelevich–Sudakov (2023), Theorem 1.** -/
theorem complete_minor_of_edges :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ (V : Type u) [Fintype V] [Nonempty V] (G : SimpleGraph V)
      [DecidableRel G.Adj], d * Fintype.card V ≤ G.edgeFinset.card →
      ∀ t : ℕ, (t : ℝ) ≤ d / (10 * Real.sqrt (Real.log d)) →
        IsMinor (⊤ : SimpleGraph (Fin t)) G := by
  obtain ⟨S₀, hS₀⟩ := eventually_spread
  set R₀ : ℝ := max 1400 S₀
  have hR₀ : 0 ≤ R₀ := le_max_of_le_left (by norm_num)
  refine ⟨⌈exp (R₀ ^ 2)⌉₊ + 1, fun d hd V _ _ G _ hE t ht => ?_⟩
  have hdpos : 0 < d := by omega
  set r := sqrt (log d) with hr
  have hr0 : R₀ ≤ r := by
    have h1 : exp (R₀ ^ 2) < d := by
      have := Nat.le_ceil (exp (R₀ ^ 2))
      have : (⌈exp (R₀ ^ 2)⌉₊ + 1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have h2 : R₀ ^ 2 < log d := by
      rw [lt_log_iff_exp_lt (by exact_mod_cast hdpos)]; exact h1
    calc R₀ = sqrt (R₀ ^ 2) := (sqrt_sq hR₀).symm
      _ ≤ r := sqrt_le_sqrt h2.le
  have h1400 : 1400 ≤ r := le_trans (le_max_left _ _) hr0
  have hS : (S₀ : ℝ) ≤ r := le_trans (le_max_right _ _) hr0
  set s := ⌈3.2 * r⌉₊
  have hs1 : 3.2 * r ≤ s := Nat.le_ceil _
  have hs2 : (s : ℝ) < 3.2 * r + 1 := Nat.ceil_lt_add_one (by positivity)
  have hsS : S₀ ≤ s := by exact_mod_cast (show (S₀ : ℝ) ≤ s by linarith)
  have hs0 : 0 < s := by exact_mod_cast (show (0 : ℝ) < s by linarith)
  rcases lt_or_ge t 2 with ht2 | ht2
  · interval_cases t
    · exact isMinor_of_clique Fin.elim0 (fun i => i.elim0)
    · obtain ⟨v⟩ := ‹Nonempty V›
      exact isMinor_of_clique (fun _ => v) (fun i j h => absurd (Subsingleton.elim i j) h)
  have ht' : (t : ℝ) ≤ d / (10 * r) := ht
  have htd : (t : ℝ) ≤ d := by
    refine ht'.trans (div_le_self (by positivity) ?_)
    linarith
  have hEpos : 0 < G.edgeFinset.card :=
    lt_of_lt_of_le (Nat.mul_pos hdpos Fintype.card_pos) hE
  refine reduce (d := d) (t := t) (by omega) ht2 ?_ G Finset.univ
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_
  · intro G' x hne hcard hcom
    classical
    have hdeg : ∀ v ∈ G'.neighborFinset x, d ≤ degIn G' (G'.neighborFinset x) v := by
      intro v hv
      unfold degIn
      rw [Finset.inter_comm]
      exact hcom v hv
    obtain ⟨W, hWN, -, hWdeg, hWrob⟩ := exists_robust (by omega) hcard hdeg hne
    exact isMinor_of_robust (s := s) (a := s / 12) (K := 12) (T := t)
      (ε := 2 * d * exp (-r / 3)) (by positivity) ((Finset.card_le_card hWN).trans hcard) hWdeg
      hWrob hs0 (by omega) (param_used hdpos h1400 hs2 ht') (param_domination h1400 hs1)
      (param_avoid hdpos hr h1400 hs1 htd) (hS₀ s hsS)
  · convert hE using 2 <;> simp
  · convert hEpos using 2
    ext e; simp

/-- **Kostochka (1982), Thomason (1984).** -/
theorem kostochka_thomason :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ (V : Type u) [Fintype V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj], d * Fintype.card V ≤ G.edgeFinset.card →
      ∀ t : ℕ, (t : ℝ) ≤ c * d / Real.sqrt (Real.log d) →
        IsMinor (⊤ : SimpleGraph (Fin t)) G := by
  obtain ⟨d₀, hd₀⟩ := complete_minor_of_edges.{u}
  refine ⟨1 / (10 * (d₀ + 1)), by positivity, fun d hd V _ _ G _ hE t ht => ?_⟩
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : log 2 ≤ log d := log_le_log (by norm_num) hd2
  have hlog2 : 1 / 4 < log 2 := by
    have := log_two_gt_d9; linarith
  have hsq : 1 / 2 < sqrt (log d) := by
    rw [show (1 / 2 : ℝ) = sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt (by norm_num) (by linarith)
  have hsq0 : 0 < sqrt (log d) := by linarith
  rcases lt_or_ge d d₀ with hlt | hge
  · -- Below the threshold the bound forces `t = 0`.
    have ht0 : t = 0 := by
      have hdlt : (d : ℝ) < d₀ + 1 := by exact_mod_cast (by omega : d < d₀ + 1)
      have : (t : ℝ) < 1 := by
        refine ht.trans_lt ?_
        rw [div_lt_one hsq0]
        calc 1 / (10 * ((d₀ : ℝ) + 1)) * d ≤ 1 / (10 * ((d₀ : ℝ) + 1)) * (d₀ + 1) := by
              gcongr
          _ = 1 / 10 := by field_simp
          _ < sqrt (log d) := by linarith
      exact_mod_cast (show t < 1 by exact_mod_cast this) |> Nat.lt_one_iff.1
    subst ht0
    exact isMinor_of_clique Fin.elim0 (fun i => i.elim0)
  · refine hd₀ d hge V G hE t (ht.trans ?_)
    have h0 : (0 : ℝ) ≤ d₀ := Nat.cast_nonneg _
    calc 1 / (10 * ((d₀ : ℝ) + 1)) * d / sqrt (log d) ≤ 1 / 10 * d / sqrt (log d) := by
          gcongr
          linarith
      _ = d / (10 * sqrt (log d)) := by field_simp

end KostochkaThomason
