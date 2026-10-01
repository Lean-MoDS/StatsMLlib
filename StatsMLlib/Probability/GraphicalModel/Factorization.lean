/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.GraphicalModel.DiscreteCondIndep

/-!
# Clique factorisation implies the global Markov property

A function `p` on configurations *factorises* over a simple graph `G` if it is a product of
nonnegative potentials, one for each complete vertex set `C`, each depending only on `x_C`. Every
factorising `p` satisfies the global Markov property for `DiscreteCondIndep p`; no positivity is
needed.

## Main definitions

* `GraphicalModel.Factorizes G p`: `p` is a product of clique potentials.

## Main results

* `GraphicalModel.DiscreteCondIndep.of_mul`: if `A ∪ B ∪ S` is everything and `p = h · k` with `h`
  depending on `A ∪ S` and `k` on `B ∪ S`, then `A ⫫ B | S`.
* `GraphicalModel.Factorizes.isGlobalMarkov`: factorisation implies the global Markov property.
-/

namespace GraphicalModel

open Finset Function

variable {V : Type*} [Fintype V] [DecidableEq V] {Ω : V → Type*} [∀ v, Fintype (Ω v)]
  [∀ v, DecidableEq (Ω v)] {p : (∀ v, Ω v) → ℝ}

/-- `p` factorises over `G`: it is a product, over the complete vertex sets `C` of `G`, of
nonnegative potentials `ψ C` depending only on `x_C`. -/
def Factorizes (G : SimpleGraph V) [DecidableRel G.Adj] (p : (∀ v, Ω v) → ℝ) : Prop :=
  ∃ ψ : Finset V → (∀ v, Ω v) → ℝ, (∀ C x, 0 ≤ ψ C x) ∧ (∀ C, DependsOn (ψ C) (C : Set V)) ∧
    ∀ x, p x = ∏ C ∈ univ.filter (fun C : Finset V ↦ G.IsClique (C : Set V)), ψ C x

/-- A product `h · k` with `h` depending on `A ∪ S` and `k` on `B ∪ S`, where `A ∪ B ∪ S` covers all
vertices, makes `A` and `B` independent given `S`. -/
theorem DiscreteCondIndep.of_mul {A B S : Finset V} (hAB : Disjoint A B) (hAS : Disjoint A S)
    (hcover : A ∪ B ∪ S = univ) {h k : (∀ v, Ω v) → ℝ} (hh : DependsOn h ((A ∪ S : Finset V) : Set V))
    (hk : DependsOn k ((B ∪ S : Finset V) : Set V)) (hp : ∀ x, p x = h x * k x) :
    DiscreteCondIndep p A B S := by
  have hmem : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ S := fun v ↦ by
    have hv := mem_univ v
    rw [← hcover] at hv
    simpa [or_assoc] using hv
  intro x
  have hAS' : marginal p (A ∪ S) x = h x * ∑ y ∈ agree (A ∪ S) x, k y := by
    rw [marginal, mul_sum]
    refine sum_congr rfl fun y hy ↦ ?_
    rw [hp, hh fun v hv ↦ mem_agree.1 hy v (mem_coe.1 hv)]
  have hBS' : marginal p (B ∪ S) x = k x * ∑ y ∈ agree (B ∪ S) x, h y := by
    rw [marginal, mul_sum]
    refine sum_congr rfl fun y hy ↦ ?_
    rw [hp, hk fun v hv ↦ mem_agree.1 hy v (mem_coe.1 hv), mul_comm]
  -- `p_S` splits into the sum over the `A`-coordinates times the sum over the `B`-coordinates
  have hS' : marginal p S x =
      (∑ y ∈ agree (B ∪ S) x, h y) * ∑ y ∈ agree (A ∪ S) x, k y := by
    rw [sum_mul_sum, ← sum_product', marginal]
    symm
    refine sum_nbij' (fun ab v ↦ if v ∈ A then ab.1 v else ab.2 v)
      (fun y ↦ (fun v ↦ if v ∈ A then y v else x v, fun v ↦ if v ∈ A then x v else y v))
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hab
      simp only [mem_product, mem_agree] at hab ⊢
      intro v hv
      by_cases hvA : v ∈ A
      · simpa [hvA] using hab.1 v (mem_union_right B hv)
      · simpa [hvA] using hab.2 v (mem_union_right A hv)
    · intro y hy
      simp only [mem_product, mem_agree] at hy ⊢
      refine ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩
      · have : v ∉ A := by grind [disjoint_left]
        simp [this]
      · by_cases hvA : v ∈ A
        · simp [hvA]
        · simpa [hvA] using hy v (by grind)
    · rintro ⟨a, b⟩ hab
      simp only [mem_product, mem_agree] at hab
      refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
      · by_cases hvA : v ∈ A
        · simp [hvA]
        · simpa [hvA] using (hab.1 v (by grind [hmem v])).symm
      · by_cases hvA : v ∈ A
        · simpa [hvA] using (hab.2 v (mem_union_left S hvA)).symm
        · simp [hvA]
    · intro y _
      funext v
      by_cases hvA : v ∈ A <;> simp [hvA]
    · rintro ⟨a, b⟩ hab
      simp only [mem_product, mem_agree] at hab
      rw [hp]
      congr 1
      · refine hh fun v hv ↦ ?_
        by_cases hvA : v ∈ A
        · simp [hvA]
        · have hvS : v ∈ S := by grind
          simp only [hvA, ite_false]
          rw [hab.1 v (mem_union_right B hvS), hab.2 v (mem_union_right A hvS)]
      · refine hk fun v hv ↦ ?_
        have hvA : v ∉ A := by grind [disjoint_left]
        simp [hvA]
  rw [hcover, marginal_univ, hp, hAS', hBS', hS']
  ring

variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (Ω v)] [∀ v, DecidableEq (Ω v)] in
/-- A finite product of functions each depending only on a subset of `T` depends only on `T`. -/
private theorem dependsOn_prod {ι : Type*} {s : Finset ι} {f : ι → (∀ v, Ω v) → ℝ}
    {S : ι → Set V} {T : Set V} (hf : ∀ i ∈ s, DependsOn (f i) (S i)) (hST : ∀ i ∈ s, S i ⊆ T) :
    DependsOn (fun x ↦ ∏ i ∈ s, f i x) T :=
  fun _ _ hxy ↦ prod_congr rfl fun i hi ↦ hf i hi fun v hv ↦ hxy v (hST i hi hv)

/-- A function that factorises over `G` satisfies the global Markov property. Split the clique
potentials into those inside `Ã ∪ S`, where `Ã` is the set reachable from `A` avoiding `S`, and the
rest, which avoid `Ã`. -/
theorem Factorizes.isGlobalMarkov (hF : Factorizes G p) : IsGlobalMarkov G (DiscreteCondIndep p) := by
  obtain ⟨ψ, -, hψ, hp⟩ := hF
  intro S A B hSA hSB hAB hsep
  set R := G.reachFinset S A
  set cliques := univ.filter fun C : Finset V ↦ G.IsClique (C : Set V)
  let h : (∀ v, Ω v) → ℝ := fun x ↦ ∏ C ∈ cliques with C ⊆ R ∪ S, ψ C x
  let k : (∀ v, Ω v) → ℝ := fun x ↦ ∏ C ∈ cliques with ¬ C ⊆ R ∪ S, ψ C x
  have hRS : Disjoint R S := SimpleGraph.reachFinset_disjoint
  have hAR : A ⊆ R := SimpleGraph.subset_reachFinset hSA
  have hBR : Disjoint R B := hsep.disjoint_reachFinset
  have hh : DependsOn h ((R ∪ S : Finset V) : Set V) :=
    dependsOn_prod (fun C _ ↦ hψ C) fun C hC ↦ by
      rw [coe_subset]
      exact (mem_filter.1 hC).2
  have hk : DependsOn k ((univ \ (R ∪ S) ∪ S : Finset V) : Set V) := by
    refine dependsOn_prod (fun C _ ↦ hψ C) fun C hC ↦ ?_
    obtain ⟨hCcl, hCRS⟩ := mem_filter.1 hC
    have hCcl' := (mem_filter.1 hCcl).2
    rcases hCcl'.subset_reachFinset_union_or_disjoint (S := S) (A := A) with hsub | hdisj
    · exact absurd hsub hCRS
    · intro v hv
      simp only [coe_union, coe_sdiff, coe_univ, Set.mem_union, Set.mem_sdiff, Set.mem_univ,
        true_and, mem_coe] at hv ⊢
      grind [disjoint_left]
  have hpk : ∀ x, p x = h x * k x := fun x ↦ by
    rw [hp x]
    exact (prod_filter_mul_prod_filter_not cliques (· ⊆ R ∪ S) (fun C ↦ ψ C x)).symm
  have hRB : DiscreteCondIndep p R (univ \ (R ∪ S)) S :=
    DiscreteCondIndep.of_mul (by grind [disjoint_left]) hRS (by grind) hh hk hpk
  -- shrink `univ \ (R ∪ S)` to `B` and `R` to `A`
  have hB : DiscreteCondIndep p R B S := by
    have hsplit : univ \ (R ∪ S) = B ∪ ((univ \ (R ∪ S)) \ B) := by grind [disjoint_left]
    rw [hsplit] at hRB
    exact DiscreteCondIndep.decomp (by grind [disjoint_left]) (by grind [disjoint_left])
      (by grind [disjoint_left]) hRB
  have hsplit : R = A ∪ (R \ A) := by grind
  rw [hsplit] at hB
  exact (DiscreteCondIndep.decomp (by grind [disjoint_left]) (by grind [disjoint_left])
    (by grind [disjoint_left]) hB.symm).symm

end GraphicalModel
