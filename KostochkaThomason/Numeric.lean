/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import KostochkaThomason.Sampling

/-!
# The numerical conditions

With `r = √(ln d) ≥ 1400`, a sample size `s = ⌈3.2 r⌉`, the domination slack `ε = 2d e^{-r/3}`,
spread `a = ⌊s/12⌋` (so a sample has at most `12` components) and `t ≤ d / (10 r)` branch sets of at
most `s + 180` vertices, all requirements of the iteration hold:

* `3 · 2d · (5/6)^s ≤ ε` (domination),
* `3 t ε^s < (d/3)^s` (every earlier branch set is met),
* `3 t (s + 180) < d` (fewer than `d / 3` vertices are used),
* `3 s e^a q^{s-1} ≤ 1` once `s` is large (spread).
-/

@[expose] public section

open Real

namespace KostochkaThomason

/-- The Chernoff ratio times `e^{1/12}` is below one. -/
theorem chernoff_ratio_lt_one : exp (1 / 12) * chernoffQ < 1 := by
  have h1 : exp (-1) < 0.3678794412 := exp_neg_one_lt_d9
  have h2 : exp (1 / 12) ≤ 12 / 11 := by
    have h := add_one_le_exp (-(1 / 12 : ℝ))
    have hpos := exp_pos (-(1 / 12 : ℝ))
    have : exp (1 / 12) * exp (-(1 / 12)) = 1 := by rw [← exp_add]; norm_num
    nlinarith
  have hq : chernoffQ ≤ 1 - (1 - 0.3678794412) / 6 := by unfold chernoffQ; linarith
  have hq0 := chernoffQ_nonneg
  nlinarith [exp_pos (1 / 12 : ℝ)]

theorem chernoffQ_pos : 0 < chernoffQ := by
  unfold chernoffQ
  have : exp (-1) < 1 := by
    have := exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num); simpa using this
  have := exp_pos (-1 : ℝ)
  linarith

/-- **Spread.** For all large `s`, `3 s e^{⌊s/12⌋} q^{s-1} ≤ 1`. -/
theorem eventually_spread :
    ∃ S₀ : ℕ, ∀ s : ℕ, S₀ ≤ s → 3 * (s : ℝ) * exp ((s / 12 : ℕ) : ℝ) * chernoffQ ^ (s - 1) ≤ 1 := by
  set ρ := exp (1 / 12) * chernoffQ
  have hρ0 : 0 ≤ ρ := mul_nonneg (exp_pos _).le chernoffQ_nonneg
  have hρ1 : |ρ| < 1 := by rw [abs_of_nonneg hρ0]; exact chernoff_ratio_lt_one
  have hq := chernoffQ_pos
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hρ1
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < chernoffQ / 3 by positivity)))
  obtain ⟨S₀, hS₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨S₀ + 1, fun s hs => ?_⟩
  have h := hS₀ s (by omega)
  rw [pow_one] at h
  have hs1 : 1 ≤ s := by omega
  have e1 : exp ((s / 12 : ℕ) : ℝ) ≤ exp (1 / 12) ^ s := by
    rw [← exp_nat_mul]
    refine exp_le_exp.2 ?_
    have : ((s / 12 : ℕ) : ℝ) ≤ (s : ℝ) / 12 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast Nat.div_mul_le_self s 12
    linarith
  have e2 : chernoffQ ^ (s - 1) * chernoffQ = chernoffQ ^ s := by
    rw [← pow_succ]; congr 1; omega
  have e3 : (s : ℝ) * ρ ^ s = (s : ℝ) * exp (1 / 12) ^ s * chernoffQ ^ s := by
    simp only [ρ, mul_pow]; ring
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hp := pow_nonneg chernoffQ_nonneg (s - 1)
  have hE := pow_nonneg (exp_pos (1 / 12 : ℝ)).le s
  calc 3 * (s : ℝ) * exp ((s / 12 : ℕ) : ℝ) * chernoffQ ^ (s - 1)
      ≤ 3 * (s : ℝ) * exp (1 / 12) ^ s * chernoffQ ^ (s - 1) := by gcongr
    _ = 3 / chernoffQ * ((s : ℝ) * ρ ^ s) := by
        rw [e3, ← e2]; field_simp
    _ ≤ 3 / chernoffQ * (chernoffQ / 3) := by gcongr
    _ = 1 := by field_simp

section Params

variable {d : ℕ} {r : ℝ}

theorem sq_r (hd : 0 < d) (hr : r = sqrt (log d)) : r ^ 2 = log d := by
  rw [hr, sq_sqrt (log_nonneg (by exact_mod_cast hd))]

theorem exp_r_sq (hd : 0 < d) (hr : r = sqrt (log d)) : exp (r ^ 2) = d := by
  rw [sq_r hd hr, exp_log (by exact_mod_cast hd)]

/-- **Domination.** -/
theorem param_domination (hr0 : 1400 ≤ r) {s : ℕ} (hs : 3.2 * r ≤ s) :
    3 * (2 * d : ℝ) * (5 / 6 : ℝ) ^ s ≤ 2 * d * exp (-r / 3) := by
  have h56 : (5 / 6 : ℝ) ≤ exp (-1 / 6) := by have := add_one_le_exp (-1 / 6 : ℝ); linarith
  have hpow : (5 / 6 : ℝ) ^ s ≤ exp (-1 / 6) ^ s := pow_le_pow_left₀ (by norm_num) h56 s
  rw [← exp_nat_mul] at hpow
  have h2 : exp (s * (-1 / 6)) ≤ exp (-(3.2 * r) / 6) := exp_le_exp.2 (by linarith)
  have h3 : 3 * exp (-(3.2 * r) / 6) ≤ exp (-r / 3) := by
    have e : exp (-r / 3) = exp (-(3.2 * r) / 6) * exp (0.2 * r) := by
      rw [← exp_add]; ring_nf
    have : 3 ≤ exp (0.2 * r) := by have := add_one_le_exp (0.2 * r); linarith
    rw [e]
    nlinarith [exp_pos (-(3.2 * r) / 6)]
  have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
  calc 3 * (2 * d : ℝ) * (5 / 6 : ℝ) ^ s ≤ 2 * d * (3 * exp (-(3.2 * r) / 6)) := by
        nlinarith
    _ ≤ 2 * d * exp (-r / 3) := by gcongr

/-- **Avoidance.** -/
theorem param_avoid (hd : 0 < d) (hr : r = sqrt (log d)) (hr0 : 1400 ≤ r) {s t : ℕ}
    (hs : 3.2 * r ≤ s) (ht : (t : ℝ) ≤ d) :
    3 * (t : ℝ) * (2 * d * exp (-r / 3)) ^ s < ((d : ℝ) / 3) ^ s := by
  set β := 6 * exp (-r / 3)
  have hβ : 2 * d * exp (-r / 3) = (d : ℝ) / 3 * β := by simp only [β]; ring
  have hβ' : β = exp (log 6 - r / 3) := by
    simp only [β]
    rw [exp_sub, exp_log (by norm_num : (0 : ℝ) < 6), neg_div, exp_neg, div_eq_mul_inv]
    ring
  have hlog6 : log 6 ≤ 5 := by
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num); linarith
  have hβs : β ^ s ≤ exp (3.2 * r * (5 - r / 3)) := by
    rw [hβ', ← exp_nat_mul]
    refine exp_le_exp.2 ?_
    have hneg : log 6 - r / 3 ≤ 5 - r / 3 := by linarith
    have hneg' : 5 - r / 3 < 0 := by linarith
    nlinarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdr : (d : ℝ) = exp (r ^ 2) := (exp_r_sq hd hr).symm
  have key : 3 * (t : ℝ) * β ^ s < 1 := by
    have hβ0 : 0 ≤ β ^ s := pow_nonneg (by positivity) s
    calc 3 * (t : ℝ) * β ^ s ≤ 3 * exp (r ^ 2) * exp (3.2 * r * (5 - r / 3)) := by
          rw [← hdr]; gcongr
      _ = 3 * exp (r ^ 2 + 3.2 * r * (5 - r / 3)) := by rw [exp_add]; ring
      _ ≤ 3 * exp (-3) := by
          gcongr
          nlinarith
      _ < 1 := by
          have : 4 ≤ exp 3 := by have := add_one_le_exp (3 : ℝ); linarith
          have h := exp_pos (3 : ℝ)
          have : exp (-3) = (exp 3)⁻¹ := exp_neg 3
          rw [this]
          rw [← div_eq_mul_inv, div_lt_one h]
          linarith
  rw [hβ, mul_pow]
  have hD : 0 < ((d : ℝ) / 3) ^ s := by positivity
  nlinarith

/-- **Few vertices used.** -/
theorem param_used (hd : 0 < d) (hr0 : 1400 ≤ r) {s t : ℕ} (hs : (s : ℝ) < 3.2 * r + 1)
    (ht : (t : ℝ) ≤ d / (10 * r)) : 3 * t * (s + 15 * 12) < d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : 0 < r := by linarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  suffices h : (3 * t * (s + 180) : ℝ) < d by exact_mod_cast h
  calc (3 * t * (s + 180) : ℝ) ≤ 3 * (d / (10 * r)) * (3.2 * r + 181) := by
        have : (s : ℝ) + 180 ≤ 3.2 * r + 181 := by linarith
        gcongr
    _ = d * ((9.6 * r + 543) / (10 * r)) := by field_simp; ring
    _ < d * 1 := by
        gcongr
        rw [div_lt_one (by positivity)]
        linarith
    _ = d := mul_one _

end Params

end KostochkaThomason
