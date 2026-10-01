/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.GraphicalModel.Graphoid
import StatsMLlib.Probability.GraphicalModel.Separation

/-!
# Markov properties of undirected graphs

The global, local and pairwise Markov properties of an independence model with respect to a simple
graph, and their equivalence for graphoids. The proofs use only the graphoid axioms, not
probability.

## Main definitions

* `GraphicalModel.IsGlobalMarkov G I`: every separation in `G` is an independence in `I`.
* `GraphicalModel.IsLocalMarkov G I`: every vertex is independent of the vertices outside its closed
  neighbourhood, given its neighbours.
* `GraphicalModel.IsPairwiseMarkov G I`: two distinct non-adjacent vertices are independent given
  all the other vertices.

## Main results

* `GraphicalModel.IsGlobalMarkov.isLocalMarkov`: global implies local, for any independence model.
* `GraphicalModel.IsLocalMarkov.isPairwiseMarkov`: local implies pairwise, for semigraphoids.
* `GraphicalModel.IsPairwiseMarkov.isGlobalMarkov`: pairwise implies global, for graphoids.
* `GraphicalModel.Graphoid.markov_tfae`: the three properties are equivalent for graphoids.
-/

namespace GraphicalModel

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  (I : Finset V → Finset V → Finset V → Prop)

/-- The global Markov property: if `S` separates `A` and `B` in `G`, then `A ⫫ B | S`. -/
def IsGlobalMarkov : Prop :=
  ∀ S A B : Finset V, Disjoint S A → Disjoint S B → Disjoint A B → G.Separates S A B → I A B S

/-- The pairwise Markov property: distinct non-adjacent `u` and `v` satisfy
`u ⫫ v | V \ {u, v}`. -/
def IsPairwiseMarkov : Prop :=
  ∀ u v : V, u ≠ v → ¬ G.Adj u v → I {u} {v} (univ \ {u, v})

section DecidableRel

variable [DecidableRel G.Adj]

/-- The local Markov property: every vertex `v` satisfies `v ⫫ V \ cl(v) | N(v)`. -/
def IsLocalMarkov : Prop :=
  ∀ v : V, I {v} (univ \ G.closedNeighborFinset v) (G.neighborFinset v)

variable {G I}

/-- The global Markov property implies the local one: the neighbours of `v` separate `v` from the
vertices outside its closed neighbourhood. -/
theorem IsGlobalMarkov.isLocalMarkov (h : IsGlobalMarkov G I) : IsLocalMarkov G I := by
  intro v
  refine h _ _ _ ?_ ?_ ?_ (SimpleGraph.separates_neighborFinset v) <;>
    grind [Finset.disjoint_left, SimpleGraph.closedNeighborFinset, SimpleGraph.mem_neighborFinset,
      SimpleGraph.irrefl]

/-- For a semigraphoid, the local Markov property implies the pairwise one, by weak union. -/
theorem IsLocalMarkov.isPairwiseMarkov (hI : Semigraphoid I) (h : IsLocalMarkov G I) :
    IsPairwiseMarkov G I := by
  intro u v huv hadj
  have hvu : ¬ G.Adj v u := fun h' ↦ hadj h'.symm
  set N := G.neighborFinset v
  set D := univ \ insert u (G.closedNeighborFinset v)
  have hsplit : univ \ G.closedNeighborFinset v = {u} ∪ D := by
    ext x
    grind [SimpleGraph.closedNeighborFinset, SimpleGraph.mem_neighborFinset]
  have hcond : N ∪ D = univ \ {u, v} := by
    ext x
    grind [SimpleGraph.closedNeighborFinset, SimpleGraph.mem_neighborFinset, SimpleGraph.irrefl]
  have hloc : I {v} ({u} ∪ D) N := hsplit ▸ h v
  have hwu : I {v} {u} (N ∪ D) := by
    refine hI.weakUnion ?_ ?_ ?_ ?_ ?_ ?_ hloc <;>
      grind [Finset.disjoint_left, SimpleGraph.closedNeighborFinset, SimpleGraph.mem_neighborFinset,
        SimpleGraph.irrefl]
  rw [hcond] at hwu
  exact hI.symm (by grind [Finset.disjoint_left]) (by grind [Finset.disjoint_left])
    (by grind [Finset.disjoint_left]) hwu

end DecidableRel

variable {G I}

omit [Fintype V] in
private theorem ssubset_union_of_disjoint {S T : Finset V} (hST : Disjoint S T) (hT : T.Nonempty) :
    S ⊂ S ∪ T := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨subset_union_left, fun h ↦ ?_⟩
  obtain ⟨t, ht⟩ := hT
  have htS : t ∈ S := h ▸ mem_union_right S ht
  exact Finset.disjoint_left.1 hST htS ht

omit [Fintype V] in
/-- The inductive step for a separated pair `A`, `B` with `|B| ≥ 2`: split off `b ∈ B`, use the
claim for the two strictly larger separating sets `S ∪ {b}` and `S ∪ (B \ {b})`, and recombine by
intersection. -/
private theorem split_right (hI : Graphoid I) {S A B : Finset V}
    (IH : ∀ S', S ⊂ S' → ∀ A B : Finset V, Disjoint S' A → Disjoint S' B → Disjoint A B →
      G.Separates S' A B → I A B S')
    (hSA : Disjoint S A) (hSB : Disjoint S B) (hAB : Disjoint A B) (hsep : G.Separates S A B)
    {b : V} (hb : b ∈ B) (hB' : (B.erase b).Nonempty) : I A B S := by
  have hbS : b ∉ S := Finset.disjoint_right.1 hSB hb
  have h1 : I A (B.erase b) (S ∪ {b}) :=
    IH _ (ssubset_union_of_disjoint (by grind [Finset.disjoint_left]) (singleton_nonempty b)) _ _
      (by grind [Finset.disjoint_left]) (by grind [Finset.disjoint_left])
      (by grind [Finset.disjoint_left])
      (hsep.mono subset_union_left subset_rfl (erase_subset b B))
  have h2 : I A {b} (S ∪ B.erase b) :=
    IH _ (ssubset_union_of_disjoint (by grind [Finset.disjoint_left]) hB') _ _
      (by grind [Finset.disjoint_left]) (by grind [Finset.disjoint_left])
      (by grind [Finset.disjoint_left])
      (hsep.mono subset_union_left subset_rfl (singleton_subset_iff.2 hb))
  have h3 : I A (B.erase b ∪ {b}) S := by
    refine hI.intersection ?_ ?_ ?_ ?_ ?_ ?_ h1 h2 <;> grind [Finset.disjoint_left]
  have hB : B.erase b ∪ {b} = B := by
    ext x
    grind
  rwa [hB] at h3

/-- For a graphoid, the pairwise Markov property implies the global one. The proof is by strong
induction on the number of vertices outside the separating set. -/
theorem IsPairwiseMarkov.isGlobalMarkov (hI : Graphoid I) (h : IsPairwiseMarkov G I) :
    IsGlobalMarkov G I := by
  intro S
  induction hn : Fintype.card V - S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  intro A B hSA hSB hAB hsep
  have IH : ∀ S', S ⊂ S' → ∀ A B : Finset V, Disjoint S' A → Disjoint S' B → Disjoint A B →
      G.Separates S' A B → I A B S' := by
    intro S' hS'
    have hlt := card_lt_card hS'
    have hle := card_le_univ S'
    exact ih _ (by omega) S' rfl
  -- empty `A` or `B`: triviality
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact hI.symm (disjoint_empty_right B) hSB.symm (disjoint_empty_left S)
      (hI.trivial hSB.symm)
  rcases B.eq_empty_or_nonempty with rfl | hB
  · exact hI.trivial hSA.symm
  -- `|B| ≥ 2` or `|A| ≥ 2`: split off one vertex
  by_cases hB2 : 1 < B.card
  · obtain ⟨b, hb⟩ := hB
    have hB' : (B.erase b).Nonempty := by
      rw [← card_pos, card_erase_of_mem hb]
      omega
    exact split_right hI IH hSA hSB hAB hsep hb hB'
  by_cases hA2 : 1 < A.card
  · obtain ⟨a, ha⟩ := hA
    have hA' : (A.erase a).Nonempty := by
      rw [← card_pos, card_erase_of_mem ha]
      omega
    exact hI.symm hAB.symm hSB.symm hSA.symm
      (split_right hI IH hSB hSA hAB.symm hsep.symm ha hA')
  -- `A = {u}` and `B = {v}`
  have hA1 : A.card = 1 := by
    have := hA.card_pos
    omega
  have hB1 : B.card = 1 := by
    have := hB.card_pos
    omega
  obtain ⟨u, rfl⟩ := card_eq_one.1 hA1
  obtain ⟨v, rfl⟩ := card_eq_one.1 hB1
  have huS : u ∉ S := Finset.disjoint_right.1 hSA (mem_singleton_self u)
  have hvS : v ∉ S := Finset.disjoint_right.1 hSB (mem_singleton_self v)
  by_cases hcov : ∀ c, c ∈ S ∨ c = u ∨ c = v
  · -- `S = V \ {u, v}`: the pairwise Markov property
    have huv : u ≠ v := by grind [Finset.disjoint_left]
    have hadj : ¬ G.Adj u v := by
      intro hadj
      obtain ⟨x, hx, hxS⟩ := hsep u (mem_singleton_self u) v (mem_singleton_self v) hadj.toWalk
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact huS hxS
      · exact hvS hxS
    have hS : S = univ \ {u, v} := by
      ext x
      grind
    exact hS ▸ h u v huv hadj
  -- a vertex `c` outside `S ∪ {u, v}`: intersection with `c`, then decomposition
  push Not at hcov
  obtain ⟨c, hcS, hcu, hcv⟩ := hcov
  have hcS' : Disjoint S {c} := disjoint_singleton_right.2 hcS
  have h1 : I {u} {v} (S ∪ {c}) :=
    IH _ (ssubset_union_of_disjoint hcS' (singleton_nonempty c)) _ _
      (by grind [Finset.disjoint_left]) (by grind [Finset.disjoint_left]) hAB
      (hsep.mono subset_union_left subset_rfl subset_rfl)
  rcases hsep.insert_or_insert c with hc | hc
  · have h2 : I {c} {v} (S ∪ {u}) :=
      IH _ (ssubset_union_of_disjoint hSA (singleton_nonempty u)) _ _
        (by grind [Finset.disjoint_left]) (by grind [Finset.disjoint_left])
        (by grind [Finset.disjoint_left]) hc
    have h3 : I {v} ({u} ∪ {c}) S := by
      refine hI.intersection ?_ ?_ ?_ ?_ ?_ ?_
        (hI.symm (by grind [Finset.disjoint_left]) (by grind [Finset.disjoint_left])
          (by grind [Finset.disjoint_left]) h1)
        (hI.symm (by grind [Finset.disjoint_left]) (by grind [Finset.disjoint_left])
          (by grind [Finset.disjoint_left]) h2) <;>
        grind [Finset.disjoint_left]
    have h4 : I {v} {u} S := by
      refine hI.decomp ?_ ?_ ?_ ?_ ?_ ?_ h3 <;> grind [Finset.disjoint_left]
    exact hI.symm (by grind [Finset.disjoint_left]) (by grind [Finset.disjoint_left])
      (by grind [Finset.disjoint_left]) h4
  · have h2 : I {c} {u} (S ∪ {v}) :=
      IH _ (ssubset_union_of_disjoint hSB (singleton_nonempty v)) _ _
        (by grind [Finset.disjoint_left]) (by grind [Finset.disjoint_left])
        (by grind [Finset.disjoint_left]) hc
    have h3 : I {u} ({v} ∪ {c}) S := by
      refine hI.intersection ?_ ?_ ?_ ?_ ?_ ?_ h1
        (hI.symm (by grind [Finset.disjoint_left]) (by grind [Finset.disjoint_left])
          (by grind [Finset.disjoint_left]) h2) <;>
        grind [Finset.disjoint_left]
    refine hI.decomp ?_ ?_ ?_ ?_ ?_ ?_ h3 <;> grind [Finset.disjoint_left]

/-- For a graphoid, the global, local and pairwise Markov properties are equivalent. -/
theorem Graphoid.markov_tfae [DecidableRel G.Adj] (hI : Graphoid I) :
    [IsGlobalMarkov G I, IsLocalMarkov G I, IsPairwiseMarkov G I].TFAE := by
  tfae_have 1 → 2 := IsGlobalMarkov.isLocalMarkov
  tfae_have 2 → 3 := IsLocalMarkov.isPairwiseMarkov hI.toSemigraphoid
  tfae_have 3 → 1 := IsPairwiseMarkov.isGlobalMarkov hI
  tfae_finish

end GraphicalModel
