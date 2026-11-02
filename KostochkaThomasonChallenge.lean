/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Complete minors and average degree (Kostochka 1982, Thomason 1984)

For finite simple graphs, with minors given by branch-set models (`CliqueMinors.MinorModel`,
copied verbatim from `CliqueMinorsLib/Minors.lean` of the registered entry
PALOMAR-2026-10-16-000001, jtraverso/hadwiger-mader):

* `KostochkaThomason.complete_minor_of_edges`: **Theorem 1 of Alon–Krivelevich–Sudakov,
  *Complete minors and average degree – a short proof* (J. Graph Theory 103 (2023)).** If `d` is
  a sufficiently large integer and `G` has at least `d · |V|` edges, then `G` has the complete
  graph on `t` vertices as a minor for every `t ≤ d / (10 √(ln d))`.
* `KostochkaThomason.kostochka_thomason`: **the Kostochka–Thomason bound.** There is `c > 0` such
  that for every integer `d ≥ 2`, every finite graph with at least `d · |V|` edges has a `K_t`
  minor for every `t ≤ c · d / √(ln d)`.
-/

@[expose] public section

open SimpleGraph

namespace CliqueMinors

variable {V W : Type*}

/-- A branch-set model of `H` as a minor of `G`: disjoint, nonempty, connected branch sets, one
for every vertex of `H`, with an edge of `G` between the branch sets of adjacent vertices. -/
structure MinorModel (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Finset V
  branch_nonempty : ∀ w, (branch w).Nonempty
  branch_connected : ∀ w, (G.induce (↑(branch w) : Set V)).Connected
  branch_disjoint : ∀ w w', w ≠ w' → Disjoint (branch w) (branch w')
  branch_adjacent : ∀ w w', H.Adj w w' → ∃ u ∈ branch w, ∃ v ∈ branch w', G.Adj u v

/-- `H` is a minor of `G`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (MinorModel G H)

end CliqueMinors

namespace KostochkaThomason

open CliqueMinors

universe u

/-- **Alon–Krivelevich–Sudakov (2023), Theorem 1.** For every sufficiently large integer `d`, a
nonempty finite graph with at least `d · |V|` edges has a `K_t` minor for every
`t ≤ d / (10 √(ln d))`. -/
theorem complete_minor_of_edges :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ (V : Type u) [Fintype V] [Nonempty V] (G : SimpleGraph V)
      [DecidableRel G.Adj], d * Fintype.card V ≤ G.edgeFinset.card →
      ∀ t : ℕ, (t : ℝ) ≤ d / (10 * Real.sqrt (Real.log d)) →
        IsMinor (⊤ : SimpleGraph (Fin t)) G := by
  sorry

/-- **Kostochka (1982), Thomason (1984).** There is a constant `c > 0` such that for every integer
`d ≥ 2`, every nonempty finite graph with at least `d · |V|` edges (average degree at least `2d`)
has a `K_t` minor for every `t ≤ c · d / √(ln d)`. -/
theorem kostochka_thomason :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ (V : Type u) [Fintype V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj], d * Fintype.card V ≤ G.edgeFinset.card →
      ∀ t : ℕ, (t : ℝ) ≤ c * d / Real.sqrt (Real.log d) →
        IsMinor (⊤ : SimpleGraph (Fin t)) G := by
  sorry

end KostochkaThomason
