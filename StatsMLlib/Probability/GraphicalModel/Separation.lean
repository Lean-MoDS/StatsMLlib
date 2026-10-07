/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Vertex separation in undirected graphs

Separation of vertex sets by a third vertex set in a simple graph, the graph-side input to the
Markov properties of undirected graphical models. This module is purely combinatorial: it uses no
probability.

## Main definitions

* `SimpleGraph.Separates G S A B`: every walk from a vertex of `A` to a vertex of `B` visits `S`.
* `SimpleGraph.closedNeighborFinset G v`: the closed neighbourhood `insert v (G.neighborFinset v)`.
* `SimpleGraph.reachFinset G S A`: the vertices outside `S` reachable from `A` by walks avoiding
  `S`.

## Main results

* `SimpleGraph.Separates.symm`, `SimpleGraph.Separates.mono`: symmetry and monotonicity.
* `SimpleGraph.Separates.insert_or_insert`: if `S` separates `A` and `B`, then any vertex `c` is
  separated from `B` by `S ∪ A` or from `A` by `S ∪ B`.
* `SimpleGraph.separates_neighborFinset`: the neighbours of `v` separate `v` from the vertices
  outside its closed neighbourhood.
* `SimpleGraph.separates_compl_pair`: two distinct non-adjacent vertices are separated by all other
  vertices.
* `SimpleGraph.IsClique.subset_reachFinset_union_or_disjoint`: a clique lies inside
  `reachFinset G S A ∪ S` or is disjoint from `reachFinset G S A`.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- `G.Separates S A B`: every walk from a vertex of `A` to a vertex of `B` visits `S`. -/
def Separates (S A B : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ w : G.Walk a b, ∃ v ∈ w.support, v ∈ S

variable {G}

namespace Separates

variable {S S' A A' B B' : Finset V}

theorem symm (h : G.Separates S A B) : G.Separates S B A := by
  intro b hb a ha w
  obtain ⟨v, hv, hvS⟩ := h a ha b hb w.reverse
  exact ⟨v, by simpa using hv, hvS⟩

theorem mono (h : G.Separates S A B) (hS : S ⊆ S') (hA : A' ⊆ A) (hB : B' ⊆ B) :
    G.Separates S' A' B' := by
  intro a ha b hb w
  obtain ⟨v, hv, hvS⟩ := h a (hA ha) b (hB hb) w
  exact ⟨v, hv, hS hvS⟩

/-- If `S` separates `A` and `B`, then any vertex `c` is separated from `B` by `S ∪ A`, or from
`A` by `S ∪ B`: otherwise the two walks out of `c` would join to a walk from `A` to `B` avoiding
`S`. -/
theorem insert_or_insert [DecidableEq V] (h : G.Separates S A B) (c : V) :
    G.Separates (S ∪ A) {c} B ∨ G.Separates (S ∪ B) {c} A := by
  by_contra hcon
  simp only [not_or, Separates, Finset.mem_singleton, forall_eq, not_forall, not_exists,
    not_and] at hcon
  obtain ⟨⟨b, hb, wb, hwb⟩, ⟨a, ha, wa, hwa⟩⟩ := hcon
  obtain ⟨v, hv, hvS⟩ := h a ha b hb (wa.reverse.append wb)
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hv
  rcases hv with hv | hv
  · exact hwa v hv (Finset.mem_union_left _ hvS)
  · exact hwb v hv (Finset.mem_union_left _ hvS)

end Separates

section Fintype

variable [Fintype V]

section DecidableEq

variable [DecidableEq V]

section DecidableRel

variable [DecidableRel G.Adj]

variable (G) in
/-- The closed neighbourhood of `v`: `v` together with its neighbours. -/
def closedNeighborFinset (v : V) : Finset V :=
  insert v (G.neighborFinset v)

/-- The neighbours of `v` separate `v` from every vertex outside its closed neighbourhood: the first
step of a walk out of `v` lands on a neighbour. -/
theorem separates_neighborFinset (v : V) :
    G.Separates (G.neighborFinset v) {v} (Finset.univ \ G.closedNeighborFinset v) := by
  intro a ha b hb w
  rw [Finset.mem_singleton] at ha
  subst ha
  cases w with
  | nil => simp [closedNeighborFinset] at hb
  | @cons _ u _ hadj w => exact ⟨u, by simp, by simpa using hadj⟩

end DecidableRel

/-- Two distinct non-adjacent vertices are separated by all the other vertices. -/
theorem separates_compl_pair {u v : V} (huv : u ≠ v) (hadj : ¬ G.Adj u v) :
    G.Separates (Finset.univ \ {u, v}) {u} {v} := by
  intro a ha b hb w
  rw [Finset.mem_singleton] at ha hb
  subst ha hb
  cases w with
  | nil => exact absurd rfl huv
  | @cons _ x _ hx w =>
    refine ⟨x, by simp, ?_⟩
    have hxa : x ≠ a := (G.ne_of_adj hx).symm
    have hxb : x ≠ b := fun h ↦ hadj (h ▸ hx)
    simp [hxa, hxb]

end DecidableEq

variable (G) in
open Classical in
/-- The vertices outside `S` that a vertex of `A` reaches by a walk avoiding `S`. -/
noncomputable def reachFinset (S A : Finset V) : Finset V :=
  Finset.univ.filter fun w ↦ ∃ a ∈ A, ∃ p : G.Walk a w, ∀ x ∈ p.support, x ∉ S

theorem mem_reachFinset {S A : Finset V} {w : V} :
    w ∈ G.reachFinset S A ↔ ∃ a ∈ A, ∃ p : G.Walk a w, ∀ x ∈ p.support, x ∉ S := by
  classical
  simp [reachFinset]

theorem reachFinset_disjoint {S A : Finset V} : Disjoint (G.reachFinset S A) S := by
  rw [Finset.disjoint_left]
  intro w hw
  obtain ⟨_, _, p, hp⟩ := mem_reachFinset.1 hw
  exact hp w p.end_mem_support

theorem subset_reachFinset {S A : Finset V} (hSA : Disjoint S A) : A ⊆ G.reachFinset S A := by
  intro a ha
  refine mem_reachFinset.2 ⟨a, ha, Walk.nil, ?_⟩
  intro x hx
  rw [Walk.mem_support_nil_iff] at hx
  subst hx
  exact Finset.disjoint_right.1 hSA ha

theorem Separates.disjoint_reachFinset {S A B : Finset V} (h : G.Separates S A B) :
    Disjoint (G.reachFinset S A) B := by
  rw [Finset.disjoint_left]
  intro b hbA hb
  obtain ⟨a, ha, p, hp⟩ := mem_reachFinset.1 hbA
  obtain ⟨v, hv, hvS⟩ := h a ha b hb p
  exact hp v hv hvS

/-- A clique lies inside `reachFinset G S A ∪ S` or is disjoint from `reachFinset G S A`: an edge
from a reachable vertex to a vertex outside `S` extends the walk. -/
theorem IsClique.subset_reachFinset_union_or_disjoint [DecidableEq V] {S A C : Finset V}
    (hC : G.IsClique (C : Set V)) :
    C ⊆ G.reachFinset S A ∪ S ∨ Disjoint C (G.reachFinset S A) := by
  by_contra hcon
  simp only [not_or, Finset.not_subset, Finset.not_disjoint_iff, Finset.mem_union, not_or] at hcon
  obtain ⟨⟨u, huC, huR, huS⟩, ⟨w, hwC, hwR⟩⟩ := hcon
  have huw : w ≠ u := fun h ↦ huR (h ▸ hwR)
  obtain ⟨a, ha, p, hp⟩ := mem_reachFinset.1 hwR
  refine huR (mem_reachFinset.2 ⟨a, ha, p.concat (hC hwC huC huw), ?_⟩)
  intro x hx
  rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx
  · exact hp x hx
  · exact hx ▸ huS

end Fintype

end SimpleGraph
