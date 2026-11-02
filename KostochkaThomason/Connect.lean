/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import CliqueMinorsLib.Minors
public import KostochkaThomason.Robust

/-!
# Short paths and connected branch sets

* `exists_short_path`: in a connected induced subgraph on `U` in which every vertex has more than
  `|U| / 6` neighbours, any two vertices lie on a connected set of at most `15` vertices (the
  diameter is at most `14`: on a shortest path the vertices at distance `0, 3, …, 15` from the
  start would have pairwise disjoint neighbourhoods).
* `exists_connected_superset`: a sample `f : Fin s → U` in which every point has at least `a`
  neighbours among the sample points splits into at most `s / (a + 1)` components, and joining
  them by short paths gives a connected set of at most `s + 15 · s / (a + 1)` vertices.
-/

@[expose] public section

open SimpleGraph CliqueMinors Relation

namespace KostochkaThomason

variable {V : Type*}

section Connect

open scoped Classical

variable [Fintype V] {G : SimpleGraph V}

theorem rtg_mono {B B' : Finset V} (h : B ⊆ B') {u v : V}
    (huv : ReflTransGen (InAdj G B) u v) : ReflTransGen (InAdj G B') u v :=
  reflTransGen_of_step (fun _ _ hab => ReflTransGen.single ⟨h hab.1, h hab.2.1, hab.2.2⟩) huv

theorem rtg_symm {B : Finset V} {u v : V} (huv : ReflTransGen (InAdj G B) u v) :
    ReflTransGen (InAdj G B) v u := by
  induction huv with
  | refl => rfl
  | tail _ hbc ih => exact ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih

/-- Two connected sets with a common vertex have a connected union. -/
theorem connected_union {B₁ B₂ : Finset V} (h₁ : (G.induce (↑B₁ : Set V)).Connected)
    (h₂ : (G.induce (↑B₂ : Set V)).Connected) {x : V} (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂) :
    (G.induce (↑(B₁ ∪ B₂) : Set V)).Connected := by
  refine induce_connected_of_root G _ x (Finset.mem_union_left _ hx₁) fun v hv => ?_
  rcases Finset.mem_union.1 hv with hv | hv
  · exact rtg_mono Finset.subset_union_left (reflTransGen_of_connected h₁ hx₁ hv)
  · exact rtg_mono Finset.subset_union_right (reflTransGen_of_connected h₂ hx₂ hv)

/-- The vertex set of a walk in `G.induce U`, as a finset of `V`. -/
noncomputable def walkSet {U : Set V} {x y : U} (p : (G.induce U).Walk x y) : Finset V :=
  (p.support.map Subtype.val).toFinset

theorem mem_walkSet {U : Set V} {x y : U} (p : (G.induce U).Walk x y) {v : U} :
    v ∈ p.support → v.1 ∈ walkSet p := by
  intro hv
  simp only [walkSet, List.mem_toFinset, List.mem_map]
  exact ⟨v, hv, rfl⟩

theorem walk_rtg {U : Set V} {x y : U} (p : (G.induce U).Walk x y) (P : Finset V)
    (hP : ∀ w ∈ p.support, w.1 ∈ P) : ∀ v ∈ p.support, ReflTransGen (InAdj G P) x.1 v.1 := by
  induction p with
  | nil => intro v hv; rw [Walk.support_nil, List.mem_singleton] at hv; rw [hv]
  | @cons a b c h q ih =>
    intro v hv
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · rfl
    · have hq : ∀ w ∈ q.support, w.1 ∈ P := fun w hw => hP w (by simp [hw])
      refine ReflTransGen.head ⟨hP a (by simp), hP b (by simp [Walk.start_mem_support]), ?_⟩
        (ih hq v hv)
      simpa using h

theorem walkSet_connected {U : Set V} {x y : U} (p : (G.induce U).Walk x y) :
    (G.induce (↑(walkSet p) : Set V)).Connected := by
  refine induce_connected_of_root G _ x.1 (mem_walkSet p p.start_mem_support) fun v hv => ?_
  simp only [walkSet, List.mem_toFinset, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  exact walk_rtg p _ (fun w hw => mem_walkSet p hw) w hw

theorem walkSet_subset {U : Finset V} {x y : (↑U : Set V)} (p : (G.induce (↑U : Set V)).Walk x y) :
    walkSet p ⊆ U := by
  intro v hv
  simp only [walkSet, List.mem_toFinset, List.mem_map] at hv
  obtain ⟨w, -, rfl⟩ := hv
  exact w.2

theorem card_walkSet_le {U : Set V} {x y : U} (p : (G.induce U).Walk x y) :
    (walkSet p).card ≤ p.length + 1 := by
  unfold walkSet
  refine (List.toFinset_card_le _).trans ?_
  simp

/-- Every distance up to `dist a c` is attained from `a`. -/
theorem exists_dist_eq {W : Type*} {H : SimpleGraph W} (hconn : H.Connected) (a : W) :
    ∀ c : W, ∀ j ≤ H.dist a c, ∃ c', H.dist a c' = j := by
  intro c
  induction hk : H.dist a c using Nat.strong_induction_on generalizing c with
  | _ k ih =>
  intro j hj
  rcases hj.lt_or_eq with hj | hj
  · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist c a
    cases p with
    | nil => rw [Walk.length_nil, SimpleGraph.dist_comm] at hp; omega
    | @cons _ c₁ _ h q =>
      rw [Walk.length_cons, SimpleGraph.dist_comm] at hp
      have h1 : H.dist a c₁ ≤ q.length := by rw [SimpleGraph.dist_comm]; exact dist_le q
      have h2 : H.dist a c ≤ H.dist a c₁ + H.dist c₁ c := hconn.dist_triangle
      have h3 : H.dist c₁ c = 1 := dist_eq_one_iff_adj.2 h.symm
      exact ih (H.dist a c₁) (by omega) c₁ rfl j (by omega)
  · exact ⟨c, by omega⟩

/-- **Diameter at most `14`.** -/
theorem dist_le_fourteen {U : Finset V} (hconn : (G.induce (↑U : Set V)).Connected)
    (hdeg : ∀ v ∈ U, U.card < 6 * degIn G U v) (a b : (↑U : Set V)) :
    (G.induce (↑U : Set V)).dist a b ≤ 14 := by
  set H := G.induce (↑U : Set V)
  by_contra hlt
  push_neg at hlt
  have hc : ∀ m : Fin 6, ∃ c, H.dist a c = 3 * m.1 := fun m =>
    exists_dist_eq hconn a b _ (by have := m.2; omega)
  choose c hc using hc
  let N : Fin 6 → Finset V := fun m => G.neighborFinset (c m).1 ∩ U
  have hdisj : (Set.univ : Set (Fin 6)).PairwiseDisjoint N := by
    intro m _ m' _ hmm'
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz hz'
    simp only [N, Finset.mem_inter, mem_neighborFinset] at hz hz'
    have hzU : z ∈ U := hz.2
    set z' : (↑U : Set V) := ⟨z, hzU⟩
    have e1 : H.dist (c m) z' = 1 := dist_eq_one_iff_adj.2 (by simpa [H, z'] using hz.1)
    have e2 : H.dist (c m') z' = 1 := dist_eq_one_iff_adj.2 (by simpa [H, z'] using hz'.1)
    have e1' : H.dist z' (c m) = 1 := by rw [SimpleGraph.dist_comm]; exact e1
    have e2' : H.dist z' (c m') = 1 := by rw [SimpleGraph.dist_comm]; exact e2
    have t1 : H.dist a (c m') ≤ H.dist a z' + H.dist z' (c m') := hconn.dist_triangle
    have t1' : H.dist a z' ≤ H.dist a (c m) + H.dist (c m) z' := hconn.dist_triangle
    have t2 : H.dist a (c m) ≤ H.dist a z' + H.dist z' (c m) := hconn.dist_triangle
    have t2' : H.dist a z' ≤ H.dist a (c m') + H.dist (c m') z' := hconn.dist_triangle
    have hm := hc m
    have hm' := hc m'
    have : m.1 ≠ m'.1 := fun h => hmm' (Fin.ext h)
    omega
  have hsub : (Finset.univ.biUnion N) ⊆ U :=
    Finset.biUnion_subset.2 fun m _ => Finset.inter_subset_right
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion (fun m _ m' _ h => hdisj (Set.mem_univ m) (Set.mem_univ m') h)]
    at hcard
  have hbig : ∀ m, U.card < 6 * (N m).card := fun m => hdeg _ (c m).2
  have : ∑ m : Fin 6, U.card < ∑ m : Fin 6, 6 * (N m).card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun m _ => hbig m
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum] at this
  omega

/-- **Short connecting sets.** -/
theorem exists_short_path {U : Finset V} (hconn : (G.induce (↑U : Set V)).Connected)
    (hdeg : ∀ v ∈ U, U.card < 6 * degIn G U v) {a b : V} (ha : a ∈ U) (hb : b ∈ U) :
    ∃ P ⊆ U, a ∈ P ∧ b ∈ P ∧ P.card ≤ 15 ∧ (G.induce (↑P : Set V)).Connected := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist ⟨a, ha⟩ ⟨b, hb⟩
  have h14 := dist_le_fourteen hconn hdeg ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨walkSet p, walkSet_subset p, mem_walkSet p p.start_mem_support,
    mem_walkSet p p.end_mem_support, ?_, walkSet_connected p⟩
  have := card_walkSet_le p
  omega

/-- The component of `v` in the subgraph induced by `B`, as a finset. -/
noncomputable def compOf (G : SimpleGraph V) (B : Finset V) (v : V) : Finset V :=
  B.filter fun w => ReflTransGen (InAdj G B) v w

theorem compOf_eq {B : Finset V} {u v w : V} (hu : w ∈ compOf G B u) (hv : w ∈ compOf G B v) :
    compOf G B u = compOf G B v := by
  simp only [compOf, Finset.mem_filter] at hu hv
  have huv : ReflTransGen (InAdj G B) u v := hu.2.trans (rtg_symm hv.2)
  ext x
  simp only [compOf, Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, (rtg_symm huv).trans h.2⟩, fun h => ⟨h.1, huv.trans h.2⟩⟩

/-- **Connecting a well-spread sample.** If every point of a sample `f : Fin s → U` has at least
`a` sample neighbours, then the sample lies in a connected subset of `U` with at most
`s + 15 · K` vertices, whenever `s < (a + 1) · (K + 1)`. -/
theorem exists_connected_superset {U : Finset V} (hconn : (G.induce (↑U : Set V)).Connected)
    (hdeg : ∀ v ∈ U, U.card < 6 * degIn G U v) {s a K : ℕ} (hs : 0 < s) (f : Fin s → V)
    (hfU : ∀ k, f k ∈ U)
    (hspread : ∀ k, a ≤ (Finset.univ.filter fun l => G.Adj (f k) (f l)).card)
    (hK : s < (a + 1) * (K + 1)) :
    ∃ B ⊆ U, (∀ k, f k ∈ B) ∧ B.card ≤ s + 15 * K ∧ (G.induce (↑B : Set V)).Connected := by
  set S : Finset V := Finset.univ.image f
  have hSU : S ⊆ U := Finset.image_subset_iff.2 fun k _ => hfU k
  set C : Finset (Finset V) := Finset.univ.image fun k => compOf G S (f k)
  have hfS : ∀ k, f k ∈ S := fun k => Finset.mem_image_of_mem f (Finset.mem_univ k)
  have hself : ∀ k, f k ∈ compOf G S (f k) := fun k =>
    Finset.mem_filter.2 ⟨hfS k, ReflTransGen.refl⟩
  -- Every component carries at least `a + 1` sample indices.
  have hfib : ∀ X ∈ C, a + 1 ≤ (Finset.univ.filter fun l => compOf G S (f l) = X).card := by
    intro X hX
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hX
    have hsub : insert k (Finset.univ.filter fun l => G.Adj (f k) (f l)) ⊆
        Finset.univ.filter fun l => compOf G S (f l) = compOf G S (f k) := by
      intro l hl
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.1 hl with rfl | hl
      · rfl
      · have hadj := (Finset.mem_filter.1 hl).2
        refine (compOf_eq (w := f l) (hself l) ?_)
        exact Finset.mem_filter.2 ⟨hfS l, ReflTransGen.single ⟨hfS k, hfS l, hadj⟩⟩
    have hk : k ∉ Finset.univ.filter fun l => G.Adj (f k) (f l) := by
      simp
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hk] at this
    have := hspread k
    omega
  have hCcard : C.card ≤ K := by
    have hsum : ∑ X ∈ C, (Finset.univ.filter fun l => compOf G S (f l) = X).card = s := by
      rw [← Finset.card_eq_sum_card_fiberwise (fun l _ => Finset.mem_image_of_mem _
        (Finset.mem_univ l)), Finset.card_univ, Fintype.card_fin]
    have : ∑ X ∈ C, (a + 1) ≤ s := hsum ▸ Finset.sum_le_sum hfib
    rw [Finset.sum_const, smul_eq_mul] at this
    by_contra hlt
    push_neg at hlt
    have : (K + 1) * (a + 1) ≤ C.card * (a + 1) := Nat.mul_le_mul_right _ hlt
    nlinarith
  -- A short path from `f 0` to each component.
  have hpath : ∀ X ∈ C, ∃ P ⊆ U, f ⟨0, hs⟩ ∈ P ∧ (∃ w ∈ P, w ∈ X) ∧ P.card ≤ 15 ∧
      (G.induce (↑P : Set V)).Connected := by
    intro X hX
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hX
    obtain ⟨P, hPU, h0, hk, hPc, hPconn⟩ := exists_short_path hconn hdeg (hfU ⟨0, hs⟩) (hfU k)
    exact ⟨P, hPU, h0, ⟨f k, hk, hself k⟩, hPc, hPconn⟩
  choose! P hPU hP0 hPX hPc hPconn using hpath
  refine ⟨S ∪ C.biUnion P, Finset.union_subset hSU (Finset.biUnion_subset.2 hPU),
    fun k => Finset.mem_union_left _ (hfS k), ?_, ?_⟩
  · calc (S ∪ C.biUnion P).card ≤ S.card + (C.biUnion P).card := Finset.card_union_le _ _
      _ ≤ s + 15 * K := by
        have h1 : S.card ≤ s := Finset.card_image_le.trans (by simp)
        have h2 : (C.biUnion P).card ≤ ∑ X ∈ C, (P X).card := Finset.card_biUnion_le
        have h3 : ∑ X ∈ C, (P X).card ≤ ∑ X ∈ C, 15 := Finset.sum_le_sum fun X hX => hPc X hX
        rw [Finset.sum_const, smul_eq_mul] at h3
        nlinarith
  · set r := f ⟨0, hs⟩
    set T := S ∪ C.biUnion P
    have hPT : ∀ X ∈ C, P X ⊆ T := fun X hX =>
      (Finset.subset_biUnion_of_mem P hX).trans Finset.subset_union_right
    have hreachP : ∀ X ∈ C, ∀ v ∈ P X, ReflTransGen (InAdj G T) r v := fun X hX v hv =>
      rtg_mono (hPT X hX) (reflTransGen_of_connected (hPconn X hX) (hP0 X hX) hv)
    refine induce_connected_of_root G T r (Finset.mem_union_left _ (hfS _)) fun v hv => ?_
    rcases Finset.mem_union.1 hv with hv | hv
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      have hX : compOf G S (f l) ∈ C := Finset.mem_image_of_mem _ (Finset.mem_univ l)
      obtain ⟨w, hwP, hwX⟩ := hPX _ hX
      have h1 := hreachP _ hX w hwP
      have h2 : ReflTransGen (InAdj G S) w (f l) := rtg_symm (Finset.mem_filter.1 hwX).2
      exact h1.trans (rtg_mono Finset.subset_union_left h2)
    · obtain ⟨X, hX, hvX⟩ := Finset.mem_biUnion.1 hv
      exact hreachP X hX v hvX

end Connect

end KostochkaThomason
