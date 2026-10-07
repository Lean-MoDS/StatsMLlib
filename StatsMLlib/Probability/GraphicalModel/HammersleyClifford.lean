/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import StatsMLlib.Probability.GraphicalModel.Factorization

/-!
# The Hammersley–Clifford theorem

A strictly positive finite discrete `p` whose product-form conditional independence satisfies the
pairwise Markov property with respect to `G` factorises over the cliques of `G`. Together with
the converse direction and the graphoid equivalences, factorisation and the global, local and
pairwise Markov properties are all equivalent for positive `p`.

The clique potentials are the exponentials of the Möbius components of `log p` with respect to a
fixed reference configuration `x⋆`: `f_A(x) = f(x on A, x⋆ elsewhere)`. A Möbius component on a set
`A` vanishes as soon as `f` does not depend on one coordinate of `A`.

## Main definitions

* `GraphicalModel.mobius F A`: the Möbius transform `∑ C ⊆ A, (-1) ^ |A \ C| * F C`.
* `GraphicalModel.glue xstar A x`: the configuration equal to `x` on `A` and to `xstar` elsewhere.
* `GraphicalModel.interaction xstar f A`: the Möbius component of `f` on `A`.

## Main results

* `GraphicalModel.sum_powerset_mobius`: Möbius inversion over subsets.
* `GraphicalModel.mobius_eq_zero`: the transform vanishes when `F` ignores a vertex of `A`.
* `GraphicalModel.IsPairwiseMarkov.factorizes`: the Hammersley–Clifford theorem.
* `GraphicalModel.DiscreteCondIndep.factorizes_tfae`: for `p > 0`, factorisation and the three
  Markov properties are equivalent.
-/

namespace GraphicalModel

open Finset Function

section Mobius

variable {V : Type*} [DecidableEq V]

/-- The Möbius transform of `F` over the subsets of `A`. -/
def mobius (F : Finset V → ℝ) (A : Finset V) : ℝ :=
  ∑ C ∈ A.powerset, (-1 : ℝ) ^ #(A \ C) * F C

/-- Splitting the subsets of `insert i A` by whether they contain `i`. -/
theorem mobius_insert (F : Finset V → ℝ) {i : V} {A : Finset V} (hi : i ∉ A) :
    mobius F (insert i A) = mobius (fun C ↦ F (insert i C)) A - mobius F A := by
  rw [mobius, sum_powerset_insert hi, mobius, mobius, sub_eq_neg_add, ← sum_neg_distrib]
  congr 1
  · refine sum_congr rfl fun C hC ↦ ?_
    have hCA := mem_powerset.1 hC
    have hcard : #(insert i A \ C) = #(A \ C) + 1 := by
      have heq : insert i A \ C = insert i (A \ C) := by
        ext x
        grind
      rw [heq, card_insert_of_notMem (by grind)]
    rw [hcard, pow_succ]
    ring
  · refine sum_congr rfl fun C _ ↦ ?_
    have heq : insert i A \ insert i C = A \ C := by
      ext x
      grind
    rw [heq]

/-- Möbius inversion: summing the Möbius transform over the subsets of `U` recovers `F U`. -/
theorem sum_powerset_mobius (F : Finset V → ℝ) (U : Finset V) :
    ∑ A ∈ U.powerset, mobius F A = F U := by
  induction U using Finset.induction_on generalizing F with
  | empty => simp [mobius]
  | insert i U hi ih =>
    rw [sum_powerset_insert hi]
    have hsum : ∑ A ∈ U.powerset, mobius F (insert i A) =
        ∑ A ∈ U.powerset, mobius (fun C ↦ F (insert i C)) A - ∑ A ∈ U.powerset, mobius F A := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun A hA ↦
        mobius_insert F fun h ↦ hi (mem_powerset.1 hA h)
    rw [hsum, ih (fun C ↦ F (insert i C))]
    ring

/-- The Möbius transform on `A` vanishes when `F` ignores a vertex `i ∈ A`. -/
theorem mobius_eq_zero {F : Finset V → ℝ} {i : V} (hF : ∀ C, F (insert i C) = F C)
    {A : Finset V} (hi : i ∈ A) : mobius F A = 0 := by
  rw [← insert_erase hi, mobius_insert F (notMem_erase i A)]
  have : (fun C ↦ F (insert i C)) = F := funext hF
  rw [this, sub_self]

theorem mobius_add (F G : Finset V → ℝ) (A : Finset V) :
    mobius (fun C ↦ F C + G C) A = mobius F A + mobius G A := by
  simp only [mobius, mul_add, sum_add_distrib]

end Mobius

section Interaction

variable {V : Type*} [DecidableEq V] {Ω : V → Type*}

/-- The configuration equal to `x` on `A` and to the reference configuration `xstar` elsewhere. -/
def glue (xstar : ∀ v, Ω v) (A : Finset V) (x : ∀ v, Ω v) : ∀ v, Ω v :=
  fun v ↦ if v ∈ A then x v else xstar v

/-- The Möbius component on `A` of `f`, relative to the reference configuration `xstar`. -/
def interaction (xstar : ∀ v, Ω v) (f : (∀ v, Ω v) → ℝ) (A : Finset V) (x : ∀ v, Ω v) : ℝ :=
  mobius (fun C ↦ f (glue xstar C x)) A

theorem interaction_dependsOn (xstar : ∀ v, Ω v) (f : (∀ v, Ω v) → ℝ) (A : Finset V) :
    DependsOn (interaction xstar f A) (A : Set V) := by
  intro x y hxy
  refine sum_congr rfl fun C hC ↦ ?_
  have hglue : glue xstar C x = glue xstar C y := by
    funext v
    by_cases hv : v ∈ C
    · simp [glue, hv, hxy v (mem_coe.2 (mem_powerset.1 hC hv))]
    · simp [glue, hv]
  simp only [hglue]

theorem sum_interaction [Fintype V] (xstar : ∀ v, Ω v) (f : (∀ v, Ω v) → ℝ) (x : ∀ v, Ω v) :
    ∑ A, interaction xstar f A x = f x := by
  rw [← powerset_univ]
  simp only [interaction]
  rw [sum_powerset_mobius]
  congr 1
  funext v
  simp [glue]

/-- The Möbius component on `A` vanishes when `f` does not depend on a coordinate `i ∈ A`. -/
theorem interaction_eq_zero (xstar : ∀ v, Ω v) {f : (∀ v, Ω v) → ℝ} {i : V}
    (hf : DependsOn f ({i}ᶜ : Set V)) {A : Finset V} (hi : i ∈ A) (x : ∀ v, Ω v) :
    interaction xstar f A x = 0 := by
  refine mobius_eq_zero (fun C ↦ hf fun v hv ↦ ?_) hi
  have hvi : v ≠ i := hv
  simp [glue, hvi]

theorem interaction_add (xstar : ∀ v, Ω v) (f g : (∀ v, Ω v) → ℝ) (A : Finset V)
    (x : ∀ v, Ω v) :
    interaction xstar (fun y ↦ f y + g y) A x = interaction xstar f A x + interaction xstar g A x :=
  mobius_add _ _ A

end Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {Ω : V → Type*} [∀ v, Fintype (Ω v)]
  [∀ v, DecidableEq (Ω v)] {p : (∀ v, Ω v) → ℝ}

/-- For `p > 0`, `u ⫫ v | V \ {u, v}` splits `log p` into a part not depending on `u` and a part
not depending on `v`. -/
theorem DiscreteCondIndep.exists_log_eq_add (hp : ∀ x, 0 < p x) {u v : V} (huv : u ≠ v)
    (h : DiscreteCondIndep p {u} {v} (univ \ {u, v})) :
    ∃ h₁ h₂ : (∀ w, Ω w) → ℝ, DependsOn h₁ ({u}ᶜ : Set V) ∧ DependsOn h₂ ({v}ᶜ : Set V) ∧
      ∀ x, Real.log (p x) = h₁ x + h₂ x := by
  set R := univ \ {u, v}
  have hne : ∀ S y, marginal p S y ≠ 0 := fun S y ↦ (marginal_pos hp S y).ne'
  have hlog : ∀ (S : Finset V) (T : Set V), (S : Set V) ⊆ T →
      DependsOn (fun x ↦ Real.log (marginal p S x)) T := fun S T hST x y hxy ↦ by
    simp only
    rw [marginal_dependsOn p S fun w hw ↦ hxy w (hST hw)]
  refine ⟨fun x ↦ Real.log (marginal p ({v} ∪ R) x) - Real.log (marginal p R x),
    fun x ↦ Real.log (marginal p ({u} ∪ R) x), ?_, ?_, fun x ↦ ?_⟩
  · intro x y hxy
    simp only
    rw [marginal_dependsOn p ({v} ∪ R) fun w hw ↦ hxy w ?_,
      marginal_dependsOn p R fun w hw ↦ hxy w ?_]
    · simp [R] at hw ⊢
      grind
    · simp [R] at hw ⊢
      grind
  · refine hlog _ _ fun w hw ↦ ?_
    simp [R] at hw ⊢
    grind
  · have hcover : {u} ∪ {v} ∪ R = univ := by
      ext w
      simp only [R, mem_union, mem_singleton, mem_sdiff, mem_univ, true_and, mem_insert,
        iff_true]
      tauto
    have hx := h x
    rw [hcover, marginal_univ] at hx
    have hpx : p x = marginal p ({u} ∪ R) x * marginal p ({v} ∪ R) x / marginal p R x := by
      rw [eq_div_iff (hne R x), hx]
    rw [hpx, Real.log_div (mul_ne_zero (hne _ x) (hne _ x)) (hne R x),
      Real.log_mul (hne _ x) (hne _ x)]
    ring

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Hammersley–Clifford.** A strictly positive `p` whose conditional independence satisfies the
pairwise Markov property factorises over the cliques of `G`. The potentials are the exponentials
of the Möbius components of `log p`; these vanish off the cliques, since a non-clique contains two
non-adjacent vertices `i`, `j` and `log p` splits into a part ignoring `i` and one ignoring `j`. -/
theorem IsPairwiseMarkov.factorizes (hp : ∀ x, 0 < p x)
    (h : IsPairwiseMarkov G (DiscreteCondIndep p)) : Factorizes G p := by
  rcases isEmpty_or_nonempty (∀ v, Ω v) with hΩ | ⟨⟨xstar⟩⟩
  · exact ⟨fun _ _ ↦ 0, fun _ _ ↦ le_rfl, fun _ _ _ _ ↦ rfl, fun x ↦ isEmptyElim x⟩
  set f : (∀ v, Ω v) → ℝ := fun x ↦ Real.log (p x)
  have hzero : ∀ A : Finset V, ¬ G.IsClique (A : Set V) → ∀ x, interaction xstar f A x = 0 := by
    intro A hA x
    simp only [SimpleGraph.IsClique, Set.Pairwise, not_forall, mem_coe] at hA
    obtain ⟨i, hi, j, hj, hij, hadj⟩ := hA
    obtain ⟨h₁, h₂, hd₁, hd₂, hsplit⟩ := (h i j hij hadj).exists_log_eq_add hp hij
    have hf : f = fun y ↦ h₁ y + h₂ y := funext hsplit
    rw [hf, interaction_add, interaction_eq_zero xstar hd₁ hi, interaction_eq_zero xstar hd₂ hj,
      add_zero]
  refine ⟨fun A x ↦ Real.exp (interaction xstar f A x), fun _ _ ↦ (Real.exp_pos _).le,
    fun A x y hxy ↦ ?_, fun x ↦ ?_⟩
  · simp only
    rw [interaction_dependsOn xstar f A hxy]
  · rw [← Real.exp_sum, sum_filter_of_ne fun A _ hA ↦ ?_, sum_interaction]
    · exact (Real.exp_log (hp x)).symm
    · by_contra hcl
      exact hA (hzero A hcl x)

/-- For `p > 0`, clique factorisation and the global, local and pairwise Markov properties of
`DiscreteCondIndep p` are equivalent. -/
theorem DiscreteCondIndep.factorizes_tfae (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : ∀ x, 0 < p x) :
    [Factorizes G p, IsGlobalMarkov G (DiscreteCondIndep p), IsLocalMarkov G (DiscreteCondIndep p),
      IsPairwiseMarkov G (DiscreteCondIndep p)].TFAE := by
  have hI := DiscreteCondIndep.graphoid p hp
  tfae_have 1 → 2 := Factorizes.isGlobalMarkov
  tfae_have 2 → 3 := IsGlobalMarkov.isLocalMarkov
  tfae_have 3 → 4 := IsLocalMarkov.isPairwiseMarkov hI.toSemigraphoid
  tfae_have 4 → 1 := IsPairwiseMarkov.factorizes hp
  tfae_finish

end GraphicalModel
