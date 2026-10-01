/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Function.DependsOn
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import StatsMLlib.Probability.GraphicalModel.Markov

/-!
# Conditional independence for finite discrete distributions

For a finite family of finite-valued variables `x : ∀ v, Ω v` and a function `p` on configurations,
`DiscreteCondIndep p A B C` is the product form of `X_A ⫫ X_B | X_C`:
`p_{A ∪ B ∪ C} · p_C = p_{A ∪ C} · p_{B ∪ C}` pointwise, where `p_S` is the marginal on `S`. It uses
no conditional probability, so no case split on vanishing marginals is needed in the definition.
Normalisation of `p` is never assumed.

## Main definitions

* `GraphicalModel.agree S x`: the configurations that agree with `x` on `S`.
* `GraphicalModel.marginal p S x`: the marginal of `p` on `S`, as a function of the full
  configuration `x`.
* `GraphicalModel.DiscreteCondIndep p A B C`: the product-form conditional independence.

## Main results

* `GraphicalModel.DiscreteCondIndep.semigraphoid`: for `p ≥ 0`, a semigraphoid.
* `GraphicalModel.DiscreteCondIndep.graphoid`: for `p > 0`, a graphoid.
* `GraphicalModel.DiscreteCondIndep.markov_tfae`: for `p > 0`, the global, local and pairwise
  Markov properties are equivalent.
-/

namespace GraphicalModel

open Finset Function

section DependsOn

variable {V : Type*} {Ω : V → Type*} {β : Type*}

/-- A function that depends only on `S` and only on `T` depends only on `S ∩ T`. -/
theorem dependsOn_inter {f : (∀ v, Ω v) → β} {S T : Set V} [DecidablePred (· ∈ S)]
    (hS : DependsOn f S) (hT : DependsOn f T) : DependsOn f (S ∩ T) := by
  intro x y hxy
  let z : ∀ v, Ω v := fun v ↦ if v ∈ S then x v else y v
  have hxz : f x = f z := hS fun v hv ↦ by simp [z, hv]
  have hzy : f z = f y := hT fun v hv ↦ by
    by_cases hvS : v ∈ S
    · simpa [z, hvS] using hxy v ⟨hvS, hv⟩
    · simp [z, hvS]
  exact hxz.trans hzy

end DependsOn

variable {V : Type*} [Fintype V] [DecidableEq V] {Ω : V → Type*} [∀ v, Fintype (Ω v)]
  [∀ v, DecidableEq (Ω v)]

/-- The configurations that agree with `x` on `S`. -/
def agree (S : Finset V) (x : ∀ v, Ω v) : Finset (∀ v, Ω v) :=
  univ.filter fun y ↦ ∀ v ∈ S, y v = x v

theorem mem_agree {S : Finset V} {x y : ∀ v, Ω v} : y ∈ agree S x ↔ ∀ v ∈ S, y v = x v := by
  simp [agree]

theorem self_mem_agree (S : Finset V) (x : ∀ v, Ω v) : x ∈ agree S x :=
  mem_agree.2 fun _ _ ↦ rfl

/-- The marginal of `p` on `S`, evaluated at the restriction of `x` to `S`. -/
def marginal (p : (∀ v, Ω v) → ℝ) (S : Finset V) (x : ∀ v, Ω v) : ℝ :=
  ∑ y ∈ agree S x, p y

/-- Product-form conditional independence `X_A ⫫ X_B | X_C` for a finite discrete `p`. -/
def DiscreteCondIndep (p : (∀ v, Ω v) → ℝ) (A B C : Finset V) : Prop :=
  ∀ x, marginal p (A ∪ B ∪ C) x * marginal p C x = marginal p (A ∪ C) x * marginal p (B ∪ C) x

variable {p : (∀ v, Ω v) → ℝ}

theorem marginal_dependsOn (p : (∀ v, Ω v) → ℝ) (S : Finset V) :
    DependsOn (marginal p S) (S : Set V) := by
  intro x x' hxx'
  have : agree S x = agree S x' := by
    ext y
    simp only [mem_agree]
    exact forall₂_congr fun v hv ↦ by rw [hxx' v hv]
  simp [marginal, this]

theorem marginal_univ (p : (∀ v, Ω v) → ℝ) (x : ∀ v, Ω v) : marginal p univ x = p x := by
  have : agree univ x = {x} := by
    ext y
    simp [mem_agree, funext_iff]
  simp [marginal, this]

theorem marginal_nonneg (hp : ∀ x, 0 ≤ p x) (S : Finset V) (x : ∀ v, Ω v) :
    0 ≤ marginal p S x :=
  sum_nonneg fun y _ ↦ hp y

theorem marginal_pos (hp : ∀ x, 0 < p x) (S : Finset V) (x : ∀ v, Ω v) : 0 < marginal p S x :=
  sum_pos (fun y _ ↦ hp y) ⟨x, self_mem_agree S x⟩

/-- A marginal that vanishes at `x` stays zero on any larger vertex set. -/
theorem marginal_eq_zero_of_subset (hp : ∀ x, 0 ≤ p x) {S T : Finset V} (hST : S ⊆ T)
    {x : ∀ v, Ω v} (h : marginal p S x = 0) : marginal p T x = 0 := by
  have hzero := (sum_eq_zero_iff_of_nonneg fun y _ ↦ hp y).1 h
  exact sum_eq_zero fun y hy ↦ hzero y (mem_agree.2 fun v hv ↦ mem_agree.1 hy v (hST hv))

/-- Summing a marginal on `S` over the coordinates `T ⊆ S` gives the marginal on `S \ T`. -/
theorem sum_agree_compl_marginal {S T : Finset V} (hTS : T ⊆ S) (x : ∀ v, Ω v) :
    ∑ y ∈ agree Tᶜ x, marginal p S y = marginal p (S \ T) x := by
  unfold marginal
  rw [sum_comm' (t' := agree (S \ T) x)
    (s' := fun z ↦ {fun v ↦ if v ∈ T then z v else x v}) ?_]
  · simp
  intro y z
  simp only [mem_agree, mem_compl, mem_singleton, mem_sdiff]
  constructor
  · rintro ⟨hy, hz⟩
    refine ⟨funext fun v ↦ ?_, fun v ⟨hvS, hvT⟩ ↦ ?_⟩
    · by_cases hvT : v ∈ T
      · simpa [hvT] using (hz v (hTS hvT)).symm
      · simpa [hvT] using hy v hvT
    · rw [hz v hvS, hy v hvT]
  · rintro ⟨rfl, hz⟩
    refine ⟨fun v hvT ↦ by simp [hvT], fun v hvS ↦ ?_⟩
    by_cases hvT : v ∈ T
    · simp [hvT]
    · simpa [hvT] using hz v ⟨hvS, hvT⟩

/-- A factor depending only on coordinates outside `T` comes out of a sum over the coordinates
in `T`. -/
theorem sum_agree_compl_mul_of_dependsOn {S T : Finset V} {f : (∀ v, Ω v) → ℝ}
    (hf : DependsOn f (S : Set V)) (hST : Disjoint S T) (g : (∀ v, Ω v) → ℝ) (x : ∀ v, Ω v) :
    ∑ y ∈ agree Tᶜ x, g y * f y = (∑ y ∈ agree Tᶜ x, g y) * f x := by
  rw [sum_mul]
  refine sum_congr rfl fun y hy ↦ ?_
  rw [hf fun v hv ↦ mem_agree.1 hy v (mem_compl.2 (disjoint_left.1 hST hv))]

/-- `sum_agree_compl_mul_of_dependsOn` with the factor on the left. -/
theorem sum_agree_compl_dependsOn_mul {S T : Finset V} {f : (∀ v, Ω v) → ℝ}
    (hf : DependsOn f (S : Set V)) (hST : Disjoint S T) (g : (∀ v, Ω v) → ℝ) (x : ∀ v, Ω v) :
    ∑ y ∈ agree Tᶜ x, f y * g y = f x * ∑ y ∈ agree Tᶜ x, g y := by
  rw [mul_sum]
  refine sum_congr rfl fun y hy ↦ ?_
  rw [hf fun v hv ↦ mem_agree.1 hy v (mem_compl.2 (disjoint_left.1 hST hv))]

namespace DiscreteCondIndep

variable {A B C D : Finset V}

theorem symm (h : DiscreteCondIndep p A B C) : DiscreteCondIndep p B A C := by
  intro x
  rw [union_comm B A, mul_comm (marginal p (B ∪ C) x)]
  exact h x

theorem trivial (A C : Finset V) : DiscreteCondIndep p A ∅ C := by
  intro x
  simp

theorem decomp (hAD : Disjoint A D) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (h : DiscreteCondIndep p A (B ∪ D) C) : DiscreteCondIndep p A B C := by
  intro x
  have hsum := congrArg (fun F ↦ ∑ y ∈ agree Dᶜ x, F y) (funext h)
  simp only at hsum
  rw [sum_agree_compl_mul_of_dependsOn (marginal_dependsOn p C) hCD,
    sum_agree_compl_marginal (by grind),
    sum_agree_compl_dependsOn_mul (marginal_dependsOn p (A ∪ C)) (by grind [disjoint_left]),
    sum_agree_compl_marginal (by grind)] at hsum
  have h1 : (A ∪ (B ∪ D) ∪ C) \ D = A ∪ B ∪ C := by grind [disjoint_left]
  have h2 : (B ∪ D ∪ C) \ D = B ∪ C := by grind [disjoint_left]
  rwa [h1, h2] at hsum

/-- Rewrite the marginals of `A ⫫ B | C ∪ D` into the vertex sets of `A ⫫ B ∪ D | C`. -/
private theorem union_cond_eq (h : DiscreteCondIndep p A B (C ∪ D)) (x : ∀ v, Ω v) :
    marginal p (A ∪ (B ∪ D) ∪ C) x * marginal p (D ∪ C) x =
      marginal p (A ∪ D ∪ C) x * marginal p (B ∪ D ∪ C) x := by
  have e1 : A ∪ B ∪ (C ∪ D) = A ∪ (B ∪ D) ∪ C := by grind
  have e2 : A ∪ (C ∪ D) = A ∪ D ∪ C := by grind
  have e3 : B ∪ (C ∪ D) = B ∪ D ∪ C := by grind
  have e4 : C ∪ D = D ∪ C := union_comm C D
  have hx := h x
  rwa [e1, e2, e3, e4] at hx

theorem weakUnion (hp : ∀ x, 0 ≤ p x) (hAB : Disjoint A B) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (h : DiscreteCondIndep p A (B ∪ D) C) :
    DiscreteCondIndep p A B (C ∪ D) := by
  have hD : DiscreteCondIndep p A D C := decomp hAB hBD.symm hBC.symm (union_comm B D ▸ h)
  intro x
  have e1 : A ∪ B ∪ (C ∪ D) = A ∪ (B ∪ D) ∪ C := by grind
  have e2 : A ∪ (C ∪ D) = A ∪ D ∪ C := by grind
  have e3 : B ∪ (C ∪ D) = B ∪ D ∪ C := by grind
  rw [e1, e2, e3, union_comm C D]
  have H := h x
  have H2 := hD x
  by_cases hC : marginal p C x = 0
  · rw [marginal_eq_zero_of_subset (T := D ∪ C) hp (by grind) hC,
      marginal_eq_zero_of_subset (T := A ∪ D ∪ C) hp (by grind) hC]
    ring
  · refine mul_right_cancel₀ hC ?_
    linear_combination marginal p (D ∪ C) x * H - marginal p (B ∪ D ∪ C) x * H2

theorem contraction (hp : ∀ x, 0 ≤ p x) (h1 : DiscreteCondIndep p A B (C ∪ D))
    (h2 : DiscreteCondIndep p A D C) : DiscreteCondIndep p A (B ∪ D) C := by
  intro x
  have H1 := union_cond_eq h1 x
  have H2 := h2 x
  by_cases hQ : marginal p (D ∪ C) x = 0
  · rw [marginal_eq_zero_of_subset (T := A ∪ (B ∪ D) ∪ C) hp (by grind) hQ,
      marginal_eq_zero_of_subset (T := B ∪ D ∪ C) hp (by grind) hQ]
    ring
  · refine mul_right_cancel₀ hQ ?_
    linear_combination marginal p C x * H1 + marginal p (B ∪ D ∪ C) x * H2

theorem intersection (hp : ∀ x, 0 < p x) (hAD : Disjoint A D) (hBD : Disjoint B D)
    (hCD : Disjoint C D) (h1 : DiscreteCondIndep p A B (C ∪ D))
    (h2 : DiscreteCondIndep p A D (C ∪ B)) : DiscreteCondIndep p A (B ∪ D) C := by
  have hne : ∀ S y, marginal p S y ≠ 0 := fun S y ↦ (marginal_pos hp S y).ne'
  -- `g = p_{A ∪ C ∪ D} / p_{C ∪ D} = p_{A ∪ B ∪ C} / p_{B ∪ C}` depends only on `A ∪ C`
  let g : (∀ v, Ω v) → ℝ := fun y ↦ marginal p (A ∪ D ∪ C) y / marginal p (D ∪ C) y
  have H1 := union_cond_eq h1
  have H2 : ∀ y, marginal p (A ∪ (B ∪ D) ∪ C) y * marginal p (B ∪ C) y =
      marginal p (A ∪ B ∪ C) y * marginal p (B ∪ D ∪ C) y := by
    intro y
    have e1 : A ∪ D ∪ (C ∪ B) = A ∪ (B ∪ D) ∪ C := by grind
    have e2 : A ∪ (C ∪ B) = A ∪ B ∪ C := by grind
    have e3 : D ∪ (C ∪ B) = B ∪ D ∪ C := by grind
    have hy := h2 y
    rwa [e1, e2, e3, union_comm C B] at hy
  have hgR : DependsOn g ((A ∪ D ∪ C : Finset V) : Set V) := by
    intro y y' hyy'
    simp only [g]
    rw [marginal_dependsOn p _ hyy',
      marginal_dependsOn p (D ∪ C) fun v hv ↦ hyy' v (by simp only [coe_union] at hv ⊢; grind)]
  have hgW : DependsOn g ((A ∪ B ∪ C : Finset V) : Set V) := by
    have hg : g = fun y ↦ marginal p (A ∪ B ∪ C) y / marginal p (B ∪ C) y := by
      funext y
      rw [div_eq_div_iff (hne _ y) (hne _ y)]
      refine mul_right_cancel₀ (hne (B ∪ D ∪ C) y) ?_
      linear_combination (-marginal p (B ∪ C) y) * H1 y + marginal p (D ∪ C) y * H2 y
    rw [hg]
    intro y y' hyy'
    dsimp only
    rw [marginal_dependsOn p _ hyy',
      marginal_dependsOn p (B ∪ C) fun v hv ↦ hyy' v (by simp only [coe_union] at hv ⊢; grind)]
  have hg : DependsOn g ((A ∪ C : Finset V) : Set V) := by
    refine (dependsOn_inter hgR hgW).mono fun v hv ↦ ?_
    simp only [coe_union, Set.mem_inter_iff, Set.mem_union, mem_coe] at hv ⊢
    grind [disjoint_left]
  have hRg : ∀ y, marginal p (A ∪ D ∪ C) y = g y * marginal p (D ∪ C) y := fun y ↦
    (div_mul_cancel₀ _ (hne _ y)).symm
  intro x
  -- summing `p_{A ∪ C ∪ D} = g · p_{C ∪ D}` over the coordinates in `D`
  have hAC : marginal p (A ∪ C) x = g x * marginal p C x := by
    have hsum := congrArg (fun F ↦ ∑ y ∈ agree Dᶜ x, F y) (funext hRg)
    simp only at hsum
    rw [sum_agree_compl_marginal (by grind),
      sum_agree_compl_dependsOn_mul hg (by grind [disjoint_left]),
      sum_agree_compl_marginal (by grind)] at hsum
    have e1 : (A ∪ D ∪ C) \ D = A ∪ C := by grind [disjoint_left]
    have e2 : (D ∪ C) \ D = C := by grind [disjoint_left]
    rwa [e1, e2] at hsum
  have hP : marginal p (A ∪ (B ∪ D) ∪ C) x = g x * marginal p (B ∪ D ∪ C) x := by
    refine mul_right_cancel₀ (hne (D ∪ C) x) ?_
    linear_combination H1 x + marginal p (B ∪ D ∪ C) x * hRg x
  rw [hP, hAC]
  ring

end DiscreteCondIndep

variable (p) in
/-- For `p ≥ 0`, product-form conditional independence is a semigraphoid. -/
theorem DiscreteCondIndep.semigraphoid (hp : ∀ x, 0 ≤ p x) :
    Semigraphoid (DiscreteCondIndep p) where
  trivial _ := DiscreteCondIndep.trivial _ _
  symm _ _ _ h := h.symm
  decomp _ _ hAD _ hBD hCD h := DiscreteCondIndep.decomp hAD hBD hCD h
  weakUnion hAB _ _ hBC hBD _ h := DiscreteCondIndep.weakUnion hp hAB hBC hBD h
  contraction _ _ _ _ _ _ h1 h2 := DiscreteCondIndep.contraction hp h1 h2

variable (p) in
/-- For `p > 0`, product-form conditional independence is a graphoid. -/
theorem DiscreteCondIndep.graphoid (hp : ∀ x, 0 < p x) : Graphoid (DiscreteCondIndep p) where
  toSemigraphoid := DiscreteCondIndep.semigraphoid p fun x ↦ (hp x).le
  intersection _ _ hAD _ hBD hCD h1 h2 := DiscreteCondIndep.intersection hp hAD hBD hCD h1 h2

/-- For `p > 0`, the global, local and pairwise Markov properties of `DiscreteCondIndep p` with
respect to `G` are equivalent. -/
theorem DiscreteCondIndep.markov_tfae (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : ∀ x, 0 < p x) :
    [IsGlobalMarkov G (DiscreteCondIndep p), IsLocalMarkov G (DiscreteCondIndep p),
      IsPairwiseMarkov G (DiscreteCondIndep p)].TFAE :=
  (DiscreteCondIndep.graphoid p hp).markov_tfae

end GraphicalModel
