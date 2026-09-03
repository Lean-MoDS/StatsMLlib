/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
import StatsMLlib.LearningTheory.Rademacher.Symmetrization
import StatsMLlib.LearningTheory.Rademacher.Signs
import Mathlib.Analysis.InnerProductSpace.PiL2
import StatsMLlib.LearningTheory.FunctionClass.HilbertPredictor
import StatsMLlib.LearningTheory.UniformDeviation.Confidence
import StatsMLlib.LearningTheory.Rademacher.Reindex

/-!
# Rademacher Complexity of L2 Linear Predictors

The empirical Rademacher bound for linear predictors with Euclidean parameter and input bounds.

## Main definitions

This module uses Euclidean spaces and the empirical Rademacher complexity from `StatsMLlib.LearningTheory.Rademacher.Defs`.

## Main results

* `linear_predictor_l2_bound'`: L2 linear-predictor complexity bound.
* `linear_predictor_l2_bound`: public form of the same bound.
-/

universe v

open Real
open scoped ENNReal

variable {ι : Type v} [Nonempty ι]
variable (d n : ℕ) (Y : Fin n → EuclideanSpace ℝ (Fin d)) (σ : Signs n)

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

theorem weighted_sum_norm_squared_expansion:
    ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 = ∑ k : Fin n, ∑ l : Fin n, ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ := by
  let g := fun l ↦ (σ l : ℝ) • Y l
  calc
  _ = ⟪∑ k : Fin n, g k, ∑ l : Fin n, g l⟫ := Eq.symm (real_inner_self_eq_norm_sq (∑ k : Fin n, g k))
  _ = ∑ k : Fin n, ⟪g k, ∑ l : Fin n, g l⟫ := sum_inner Finset.univ g (∑ l : Fin n, g l)
  _ = ∑ k : Fin n, ∑ l : Fin n, ⟪g k, g l⟫ := by
    apply congrArg
    ext k
    exact inner_sum Finset.univ g (g k)

theorem individual_weighted_norms_sum:
    ∑ k : Fin n, ‖(σ k : ℝ) • Y k‖ ^ 2 = ∑ k : Fin n, ∑ l : Fin n, if k ≠ l then 0 else  ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ := by
  let g := fun l ↦ (σ l : ℝ) • Y l
  trans ∑ k : Fin n, ⟪g k, g k⟫
  · apply congrArg
    ext k
    exact Eq.symm (real_inner_self_eq_norm_sq (g k))
  · dsimp [g]
    simp

theorem rademacher_sum_variance_zero
    (Y : Fin n → EuclideanSpace ℝ (Fin d)):
    ∑ σ : Signs n, (‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 - ∑ k : Fin n, ‖(σ k : ℝ) • Y k‖ ^ 2) = 0 := by
  calc
  _ = ∑ σ : Signs n, ∑ k : Fin n, ∑ l : Fin n, (if k ≠ l then (⟪(σ k : ℝ) • (Y k), (σ l : ℝ) • (Y l)⟫) else (0 : ℝ)) := by
    apply congrArg
    ext σ
    let g (l : Fin n) : EuclideanSpace ℝ (Fin d) := (σ l : ℝ) • (Y l)
    rw [weighted_sum_norm_squared_expansion d n Y σ, individual_weighted_norms_sum d n Y σ]
    suffices (∑ k : Fin n, ∑ l : Fin n, ⟪g k, g l⟫ - ∑ k : Fin n, ∑ l : Fin n, if k ≠ l then (0 : ℝ) else ⟪g k, g l⟫) =
      ∑ k : Fin n, ∑ l : Fin n, if k ≠ l then ⟪g k, g l⟫ else (0 : ℝ) from by
      exact this
    have t : (∑ k : Fin n, ∑ l : Fin n, ⟪g k, g l⟫ - ∑ k : Fin n, ∑ l : Fin n, if k ≠ l then (0 : ℝ) else ⟪g k, g l⟫) =
      ∑ k : Fin n, ∑ l : Fin n, if k ≠ l then ⟪g k, g l⟫ else (0 : ℝ) := by
      calc
      _ = ∑ k : Fin n, ((∑ l : Fin n, ⟪g k, g l⟫) - (∑ l : Fin n, if k ≠ l then (0 : ℝ) else ⟪g k, g l⟫)) := by
        simp
      _ = ∑ k : Fin n, ∑ l : Fin n, (⟪g k, g l⟫ - if k ≠ l then (0 : ℝ) else ⟪g k, g l⟫) := by
        apply congrArg
        ext k
        simp
      _ = ∑ k : Fin n, ∑ l : Fin n, if k ≠ l then ⟪g k, g l⟫ - (0 : ℝ) else ⟪g k, g l⟫ - ⟪g k, g l⟫ := by
        apply congrArg
        ext k
        apply congrArg
        ext l
        exact sub_ite (k ≠ l) ⟪g k, g l⟫ 0 ⟪g k, g l⟫
      _ = ∑ k : Fin n, ∑ l : Fin n, if k ≠ l then ⟪g k, g l⟫ else (0 : ℝ) := by simp
    rw [t]
  _ = _ := by
    have e : ∀ (k l : Fin n), k ≠ l → ∑ σ : Signs n, ⟪(σ k : ℝ) • (Y k), (σ l : ℝ) • (Y l)⟫ = (0 : ℝ) := by
      intro k l pkl
      have : ∑ σ : Signs n, ⟪(σ k : ℝ) • (Y k), (σ l : ℝ) • (Y l)⟫ = ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) * ⟪Y k, Y l⟫ := by
        calc
        _ = ∑ σ : Signs n, (σ k : ℝ) * ⟪Y k, (σ l : ℝ) • (Y l)⟫ := by
          apply congrArg
          ext σ
          exact real_inner_smul_left (Y k) ((σ l : ℝ) • (Y l)) (σ k : ℝ)
        _ = ∑ σ : Signs n, (σ k : ℝ) * ((σ l : ℝ) * ⟪Y k, Y l⟫) := by
          apply congrArg
          ext σ
          apply congrArg
          exact real_inner_smul_right (Y k) ((Y l)) (σ l : ℝ)
        _ = _ := by
          apply congrArg
          ext σ
          ring
      rw [this]
      suffices ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) = (0 : ℝ) from by
        calc
        _ = (∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ)) * ⟪Y k, Y l⟫ := by
          symm
          apply Finset.sum_mul Finset.univ
        _ = 0 * ⟪Y k, Y l⟫ := by rw [this]
        _ = _ := by simp
      exact rademacher_orthogonality n k l pkl
    calc
    _ = ∑ k : Fin n, ∑ σ : Signs n, ∑ l : Fin n, (if k ≠ l then ⟪(σ k : ℝ) • (Y k), (σ l : ℝ) • (Y l)⟫ else (0 : ℝ)) := by
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ l : Fin n, ∑ σ : Signs n, (if k ≠ l then ⟪(σ k : ℝ) • (Y k), (σ l : ℝ) • (Y l)⟫ else (0 : ℝ)) := by
      apply congrArg
      ext k
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ l : Fin n, (if k ≠ l then ∑ σ : Signs n, ⟪(σ k : ℝ) • (Y k), (σ l : ℝ) • (Y l)⟫ else (0 : ℝ)) := by
      apply congrArg
      ext k
      apply congrArg
      ext l
      simp
    _ = ∑ k : Fin n, ∑ l : Fin n, (if k ≠ l then (0 : ℝ) else (0 : ℝ)) := by
      apply congrArg
      ext k
      apply congrArg
      ext l
      exact ite_congr rfl (e k l) (congrFun rfl)
    _ = (0 : ℝ) := by simp

theorem linear_predictor_l2_bound'
    (W X : ℝ)
    (hx : 0 ≤ X) (hw : 0 ≤ W)
    (Y' : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (w' : ι → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W):
    empiricalRademacherComplexity
      n (fun (i : ι) a ↦ ⟪((Subtype.val ∘ w') i), a⟫) (Subtype.val ∘ Y') ≤
    X * W / √(n : ℝ) := by
  let w := (Subtype.val ∘ w')
  let Y := (Subtype.val ∘ Y')
  have px : ∀ (i : Fin n), ‖Y i‖ ≤ X := by
    intro i
    dsimp [Y]
    apply mem_closedBall_zero_iff.mp
    exact Subtype.coe_prop (Y' i)
  have py : ∀ i, ‖w i‖ ≤ W := by
    intro i
    dsimp [w]
    apply mem_closedBall_zero_iff.mp
    exact Subtype.coe_prop (w' i)
  calc
  _ =
    ((Fintype.card (Signs n) : ℝ))⁻¹ *
      ∑ σ : Signs n, ⨆ i, ((n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * ⟪w i, Y k⟫|) := by
    dsimp only [empiricalRademacherComplexity]
    repeat apply congrArg
    ext σ
    apply congrArg
    ext i
    trans (|(n : ℝ)⁻¹| * |∑ k : Fin n, (σ k : ℝ) * ⟪w i, Y k⟫|)
    · rw [abs_mul]
    · simp
  _ =
    (Fintype.card (Signs n) : ℝ)⁻¹ *
      ∑ σ : Signs n, ((n : ℝ)⁻¹ * ⨆ i, |∑ k : Fin n, (σ k : ℝ) * ⟪w i, Y k⟫|) := by
    repeat apply congrArg
    ext σ
    symm
    apply mul_iSup_of_nonneg
    simp
  _ =
    (Fintype.card (Signs n) : ℝ)⁻¹ *
      ((n : ℝ)⁻¹ * ∑ σ : Signs n, (⨆ i, |∑ k : Fin n, (σ k : ℝ) * ⟪w i, Y k⟫|)) := by
    apply congrArg
    symm
    apply Finset.mul_sum
  _ =
    (n : ℝ)⁻¹ * ((Fintype.card (Signs n) : ℝ)⁻¹ *
      (∑ σ : Signs n, (⨆ i, |∑ k : Fin n, (σ k : ℝ) * ⟪w i, Y k⟫|))) := by
    ring
  _ = (n : ℝ)⁻¹ *
    ((Fintype.card (Signs n) : ℝ)⁻¹ *
      ∑ σ : Signs n, ⨆ i, |⟪w i, ∑ k : Fin n, ((σ k) : ℝ) • (Y k)⟫|) := by
    repeat apply congrArg
    ext σ
    apply congrArg
    ext i
    apply congrArg
    rw [inner_sum]
    apply congrArg
    ext k
    symm
    apply real_inner_smul_right
  _ ≤ (n : ℝ)⁻¹ * ((Fintype.card (Signs n) : ℝ)⁻¹ *
      ∑ σ : Signs n, ⨆ (i : ι), W * ‖(∑ k : Fin n, ((σ k) : ℝ) • (Y k))‖) := by
    repeat apply mul_le_mul_of_nonneg_left
    apply Finset.sum_le_sum
    intro i_1 hi_1
    apply ciSup_mono
    · rw [bddAbove_def]
      use W * (n * X)
      intro y hy
      simp only [Int.reduceNeg, Set.range_const, Set.mem_singleton_iff] at hy
      rw [hy]
      apply mul_le_mul
      · simp only [le_refl]
      · have r : ‖∑ x_1 : Fin n, (i_1 x_1 : ℝ) • (Y x_1)‖ ≤ (n : ℝ) * X := by
          calc
          _ ≤ ∑ x_1 : Fin n, ‖(i_1 x_1 : ℝ) • (Y x_1)‖ := by
            apply norm_sum_le
          _ = ∑ x_1 : Fin n, ‖(Y x_1)‖ := by
            apply congrArg
            ext x_1
            rw [norm_smul]
            simp
          _ ≤ ∑ x_1 : Fin n, X := by
            apply Finset.sum_le_sum
            intro i_2 hi_2
            apply px
          _ = (n : ℝ) * X := by simp
        exact r
      apply norm_nonneg
      exact hw
    · intro x
      trans ‖w x‖ * ‖∑ k : Fin n, (i_1 k : ℝ) • Y k‖
      · apply abs_real_inner_le_norm
      · apply mul_le_mul_of_nonneg_right
        · dsimp [w]
          apply py
        · apply norm_nonneg
    simp
    simp
  _ = (n : ℝ)⁻¹ * ((Fintype.card (Signs n) : ℝ)⁻¹ *
      ∑ σ : Signs n, W * ‖(∑ k : Fin n, ((σ k) : ℝ) • (Y k))‖) := by
    repeat apply congrArg
    ext σ
    rw [ciSup_const]
  _ = (n : ℝ)⁻¹ * ((Fintype.card (Signs n) : ℝ)⁻¹ *
      (W * ∑ σ : Signs n, ‖(∑ k : Fin n, ((σ k) : ℝ) • (Y k))‖)) := by
    repeat apply congrArg
    rw [Finset.mul_sum]
  _ = (n : ℝ)⁻¹ *
      (W * (((Fintype.card (Signs n) : ℝ))⁻¹ * ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • (Y k)‖)) := by
    apply congrArg
    ring
  _ = W * (n : ℝ)⁻¹ * ((Fintype.card (Signs n) : ℝ)⁻¹ *
      ∑ σ : Signs n, ‖(∑ k : Fin n, ((σ k) : ℝ) • (Y k))‖):= by
    ring
  _ ≤ W * (n : ℝ)⁻¹ * √(
    ((Fintype.card (Signs n) : ℝ))⁻¹ *
      ∑ σ : Signs n, ‖(∑ k : Fin n, ((σ k) : ℝ) • (Y k))‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_left
    · apply le_sqrt_of_sq_le
      let f (σ : Signs n) := (1 : ℝ)
      let g (σ : Signs n) := ‖∑ k : Fin n, (σ k : ℝ) • (Y k)‖ * ((Fintype.card (Signs n) : ℝ))⁻¹
      suffices (∑ σ : Signs n, f σ * g σ) ^ 2 ≤ (∑ σ : Signs n, (f σ) ^ 2) * (∑ σ : Signs n, (g σ) ^ 2) from by
        dsimp [f, g] at this
        simp only [Int.reduceNeg, one_mul, one_pow,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
        have p : (((Fintype.card (Signs n)) : ℝ)⁻¹ * ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • (Y k)‖) =
          (∑ x_1 : Signs n, ‖∑ k : Fin n, (x_1 k : ℝ) • (Y k)‖ * ((Fintype.card (Signs n)) : ℝ)⁻¹) := by
            trans (∑ x_1 : Signs n, ‖∑ k : Fin n, (x_1 k : ℝ) • (Y k)‖) * ((Fintype.card (Signs n)) : ℝ)⁻¹
            · ring
            · apply Finset.sum_mul
        have q : (Fintype.card (Signs n) : ℝ) * ∑ σ : Signs n, (‖∑ k : Fin n, (σ k : ℝ) • (Y k)‖ * (Fintype.card (Signs n) : ℝ)⁻¹) ^ 2 =
          ((Fintype.card (Signs n)) : ℝ)⁻¹ * ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • (Y k)‖ ^ 2 := by
          calc
          _ = (Fintype.card (Signs n) : ℝ) * ∑ σ : Signs n, ((‖∑ k : Fin n, (σ k : ℝ) • (Y k)‖ ^ 2) * ((Fintype.card (Signs n) : ℝ)⁻¹) ^ 2) := by
            repeat apply congrArg
            ext σ
            field_simp
          _ = (Fintype.card (Signs n) : ℝ) * ((∑ σ : Signs n, (‖∑ k : Fin n, (σ k : ℝ) • (Y k)‖ ^ 2)) * (((Fintype.card (Signs n) : ℝ)⁻¹) ^ 2)) := by
            apply congrArg
            symm
            apply Finset.sum_mul
          _ = (Fintype.card (Signs n) : ℝ) * (((Fintype.card (Signs n) : ℝ)⁻¹) ^ 2) * (∑ σ : Signs n, (‖∑ k : Fin n, (σ k : ℝ) • (Y k)‖ ^ 2)) := by
            ring
          _ = _ := by
            have e : (Fintype.card (Signs n) : ℝ) * (((Fintype.card (Signs n) : ℝ)⁻¹) ^ 2) = (Fintype.card (Signs n) : ℝ)⁻¹ := by
              calc
              _ = (Fintype.card (Signs n) : ℝ) * (((Fintype.card (Signs n) : ℝ)⁻¹) * ((Fintype.card (Signs n) : ℝ)⁻¹)) := by
                apply congrArg
                apply pow_two
              _ = ((Fintype.card (Signs n) : ℝ) * ((Fintype.card (Signs n) : ℝ)⁻¹)) * ((Fintype.card (Signs n) : ℝ)⁻¹) := by
                symm
                apply mul_assoc
              _ = _ := by simp
            rw [e]
        rw [p, Eq.symm q]
        exact this
      apply Finset.sum_mul_sq_le_sq_mul_sq
    · by_cases hn : 0 < n
      · aesop
      · simp only [not_lt, nonpos_iff_eq_zero] at hn
        rw [hn]
        simp
  _ = W * (n : ℝ)⁻¹ * √(
    ((Fintype.card (Signs n) : ℝ))⁻¹ *
      ∑ σ : Signs n, (∑ k : Fin n, ‖((σ k) : ℝ) • (Y k)‖ ^ 2)) := by
    apply congrArg
    apply congrArg
    apply congrArg
    have := rademacher_sum_variance_zero d n Y
    simp only [Int.reduceNeg, Finset.sum_sub_distrib] at this
    linarith
  _ = W * (n : ℝ)⁻¹ * √(
    ((Fintype.card (Signs n) : ℝ))⁻¹ *
      ∑ σ : Signs n, (∑ k : Fin n, ‖(Y k)‖ ^ 2)) := by
    repeat apply congrArg
    ext σ
    apply congrArg
    ext k
    rw [norm_smul]
    simp
  _ ≤ W * (n : ℝ)⁻¹ * √(
    ((Fintype.card (Signs n) : ℝ))⁻¹ *
      ∑ σ : Signs n, (∑ k : Fin n, X ^ 2)) := by
    apply mul_le_mul_of_nonneg_left
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro k hk
    rw [sq_le_sq]
    simp only [abs_norm]
    rw [abs_of_nonneg]
    exact px k
    exact hx
    exact le_of_lt (by simp)
    · by_cases hn : 0 < n
      · aesop
      · simp only [not_lt, nonpos_iff_eq_zero] at hn
        rw [hn]
        simp
  _ = W * (n : ℝ)⁻¹ * √((n : ℝ) * X ^ 2) := by
    have q : (
    ((Fintype.card (Signs n) : ℝ))⁻¹ *
      ∑ σ : Signs n, (∑ k : Fin n, X ^ 2)) =
      ((n : ℝ) * X ^ 2) := by
      calc
      _ = ((Fintype.card (Signs n) : ℝ))⁻¹ * ((Fintype.card (Signs n) : ℝ) * ((n : ℝ) * X ^ 2)) := by simp
      _ = ((Fintype.card (Signs n) : ℝ))⁻¹ * (Fintype.card (Signs n) : ℝ) * ((n : ℝ) * X ^ 2) := by ring
      _ = ((n : ℝ) * X ^ 2) := by
        field_simp
    rw [q]
  _ = W * (n : ℝ)⁻¹ * √(n : ℝ) * X := by
    have q : √(n * X ^ 2) = √(n : ℝ) * X := by
      simp only [Nat.cast_nonneg, sqrt_mul, mul_eq_mul_left_iff, sqrt_eq_zero, Nat.cast_eq_zero]
      left
      exact sqrt_sq hx
    rw [q]
    ring
  _ = X * W * ((n : ℝ)⁻¹ * √(n : ℝ)) := by ring
  _ = X * W * (1 / √(n : ℝ)) := by
    by_cases hn : 0 < n
    · rw [(by apply eq_one_div_of_mul_eq_one_left; field_simp; exact sq_sqrt (Nat.cast_nonneg' n) : ((n : ℝ)⁻¹ * √(n : ℝ)) = (1 / √(n : ℝ)))]
    · simp only [not_lt, nonpos_iff_eq_zero] at hn
      rw [hn]
      simp
  _ = X * W / √(n : ℝ) := by ring

/-- Empirical Rademacher bound for Euclidean-bounded linear predictors. -/
theorem linear_predictor_l2_bound
    {n : ℕ}
    (d : ℕ)
    (W X : ℝ)
    (hx : 0 ≤ X) (hw : 0 ≤ W)
    (Y' : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (w' : ι → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :
    empiricalRademacherComplexity
      n (fun (i : ι) a ↦ ⟪((Subtype.val ∘ w') i), a⟫) (Subtype.val ∘ Y') ≤
    X * W / √(n : ℝ) := by
  exact linear_predictor_l2_bound' (d := d) (n := n) (W := W) (X := X) hx hw Y' w'

/-- Linear prediction with both the weight and input restricted to closed Euclidean balls. -/
noncomputable def linearPredictorL2
    {d : ℕ} {W X : ℝ}
    (w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) : ℝ :=
  ⟪(w : EuclideanSpace ℝ (Fin d)), (x : EuclideanSpace ℝ (Fin d))⟫

lemma continuous_linearPredictorL2_weight
    {d : ℕ} {W X : ℝ}
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :
    Continuous fun w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W ↦
      linearPredictorL2 w x := by
  unfold linearPredictorL2
  fun_prop

lemma continuous_linearPredictorL2_input
    {d : ℕ} {W X : ℝ}
    (w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :
    Continuous fun x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X ↦
      linearPredictorL2 w x := by
  unfold linearPredictorL2
  fun_prop

/-- Pointwise boundedness needed by the generalization theorem. -/
lemma abs_linearPredictorL2_le
    {d : ℕ} {W X : ℝ} (hW : 0 ≤ W)
    (w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :
    |linearPredictorL2 w x| ≤ X * W := by
  calc
    |linearPredictorL2 w x|
        ≤ ‖(w : EuclideanSpace ℝ (Fin d))‖ *
            ‖(x : EuclideanSpace ℝ (Fin d))‖ := by
          exact abs_real_inner_le_norm
            (w : EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    _ ≤ W * X := by
      apply mul_le_mul
      · exact mem_closedBall_zero_iff.mp w.property
      · exact mem_closedBall_zero_iff.mp x.property
      · exact norm_nonneg (x : EuclideanSpace ℝ (Fin d))
      · exact hW
    _ = X * W := mul_comm W X

/--
Sample-dependent empirical Rademacher-complexity bound for the full class of
`ℓ₂`-bounded linear predictors.
-/
theorem linear_predictor_l2_empirical_bound_of_sample
    (d n : ℕ) (W X : ℝ) (hW : 0 ≤ W)
    (S : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :
    empiricalRademacherComplexity n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ) S
      ≤ W * (n : ℝ)⁻¹ *
        Real.sqrt
          (∑ k : Fin n, ‖(S k : EuclideanSpace ℝ (Fin d))‖ ^ 2) := by
  let : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW).to_subtype
  change empiricalRademacherComplexity n
    (fun (w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W)
        (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) ↦
      ⟪(w : EuclideanSpace ℝ (Fin d)), (x : EuclideanSpace ℝ (Fin d))⟫) S
      ≤ W * (n : ℝ)⁻¹ *
        Real.sqrt
          (∑ k : Fin n, ‖(S k : EuclideanSpace ℝ (Fin d))‖ ^ 2)
  rw [empiricalRademacherComplexity_comp]
  exact hilbertPredictor_empiricalRademacherComplexity_le
    (H := EuclideanSpace ℝ (Fin d)) W hW (Subtype.val ∘ S)

/--
Empirical Rademacher-complexity bound for the full class of `ℓ₂`-bounded
linear predictors on an `ℓ₂`-bounded input space.
-/
theorem linear_predictor_l2_empirical_bound
    (d n : ℕ) (W X : ℝ) (hX : 0 ≤ X) (hW : 0 ≤ W)
    (S : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :
    empiricalRademacherComplexity n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ) S
      ≤ X * W / Real.sqrt (n : ℝ) := by
  calc
    empiricalRademacherComplexity n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ) S ≤
        W * (n : ℝ)⁻¹ *
          Real.sqrt
            (∑ k : Fin n,
              ‖(S k : EuclideanSpace ℝ (Fin d))‖ ^ 2) :=
      linear_predictor_l2_empirical_bound_of_sample d n W X hW S
    _ ≤ W * (n : ℝ)⁻¹ * Real.sqrt (∑ _k : Fin n, X ^ 2) := by
      gcongr with k
      exact mem_closedBall_zero_iff.mp (S k).property
    _ = W * (n : ℝ)⁻¹ * Real.sqrt ((n : ℝ) * X ^ 2) := by simp
    _ = W * (n : ℝ)⁻¹ * (Real.sqrt (n : ℝ) * X) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hX]
    _ = X * W / Real.sqrt (n : ℝ) := by
      by_cases hn : 0 < n
      · have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
        field_simp [hsqrt]
        rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        simp

-- The generalization bounds below need a different context from the fixed-sample
-- estimates above: the sample index implicit rather than explicit, a probability
-- space, and the product-measure notation.
section Generalization

universe u

open MeasureTheory ProbabilityTheory

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

set_option hygiene false in
local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
Expected Rademacher-complexity bound for the full `ℓ₂`-bounded linear class:

`Rₙ(F₂,W; μ) ≤ X * W / √n`.
-/
theorem linear_predictor_l2_rademacher_complexity_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hX : 0 ≤ X) (hW : 0 ≤ W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) :
    rademacherComplexity n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
        μ Z
      ≤ X * W / Real.sqrt (n : ℝ) := by
  let : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW).to_subtype
  apply rademacherComplexity_le_of_empirical_le_separable
    (F := linearPredictorL2) (X := Z)
  · intro w
    exact (continuous_linearPredictorL2_input w).measurable.comp hZ
  · exact mul_nonneg hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le hW w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound d n W X hX hW

/--
Expected uniform-deviation bound for the full `ℓ₂`-bounded linear class:

`𝔼[UDₙ] ≤ 2 * X * W / √n`.
-/
theorem linear_predictor_l2_uniform_deviation_expectation_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 ≤ X) (hW : 0 ≤ W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) :
    μⁿ[fun S : Fin n → Ω ↦
      uniformDeviation n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
        μ Z (Z ∘ S)]
      ≤ 2 * (X * W / Real.sqrt (n : ℝ)) := by
  let : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW).to_subtype
  let : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :=
    (Metric.nonempty_closedBall.mpr hX).to_subtype
  apply uniform_deviation_expectation_le_of_empirical_le_separable
    (F := linearPredictorL2) hn
  · exact fun w ↦ (continuous_linearPredictorL2_input w).measurable
  · exact hZ
  · exact mul_nonneg hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le hW w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound d n W X hX hW

/--
High-probability `ε`-form bound for the full `ℓ₂` linear class:

`Pr{UDₙ ≥ 2 X W / √n + ε} ≤ exp (-n ε² / (2 (X W)²))`.
-/
theorem linear_predictor_l2_uniform_deviation_tail_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (_hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S |
      2 * (X * W / Real.sqrt (n : ℝ)) + ε ≤
        uniformDeviation n
          (linearPredictorL2 :
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
          μ Z (Z ∘ S)}).toReal
      ≤ (-ε ^ 2 * n / (2 * (X * W) ^ 2)).exp := by
  let : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW.le).to_subtype
  let : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :=
    (Metric.nonempty_closedBall.mpr hX.le).to_subtype
  apply uniform_deviation_tail_bound_separable_of_empirical_le
    (F := linearPredictorL2)
  · exact fun w ↦ (continuous_linearPredictorL2_input w).measurable
  · exact hZ
  · exact mul_pos hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le hW.le w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound d n W X hX.le hW.le
  · exact hε

/--
End-to-end confidence bound for the full `ℓ₂`-bounded linear class:

`Pr{UDₙ ≥ 2 X W / √n + X W √(2 log(1/δ)/n)} ≤ δ`.

The first term is the Rademacher-complexity contribution and the second is
the concentration contribution.
-/
theorem linear_predictor_l2_uniform_deviation_tail_bound_delta
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * (X * W / Real.sqrt (n : ℝ)) +
          (X * W) * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n
          (linearPredictorL2 :
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
          μ Z (Z ∘ S)}).toReal ≤ δ := by
  let : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW.le).to_subtype
  let : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :=
    (Metric.nonempty_closedBall.mpr hX.le).to_subtype
  apply uniform_deviation_tail_bound_separable_of_empirical_le_delta
    (μ := μ) hn (F := linearPredictorL2)
  · exact fun w ↦ (continuous_linearPredictorL2_input w).measurable
  · exact hZ
  · exact mul_pos hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le hW.le w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound d n W X hX.le hW.le
  · exact hδ
  · exact hδ_one

/--
Sample-dependent end-to-end confidence bound for the full `ℓ₂` class:

`Pr{UDₙ ≥ (2W/n) √(∑ₖ ‖Zₖ‖²)
    + 3 X W √(2 log(2/δ)/n)} ≤ δ`.

The empirical norm sum is retained instead of being replaced by `n X²`.
-/
theorem linear_predictor_l2_uniform_deviation_tail_bound_of_sample_delta
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 *
          (W * (n : ℝ)⁻¹ *
            Real.sqrt
              (∑ k : Fin n,
                ‖(Z (S k) : EuclideanSpace ℝ (Fin d))‖ ^ 2)) +
        3 * ((X * W) * Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
          uniformDeviation n
            (linearPredictorL2 :
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
                Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
            μ Z (Z ∘ S)}).toReal ≤ δ := by
  let : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW.le).to_subtype
  let : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :=
    (Metric.nonempty_closedBall.mpr hX.le).to_subtype
  have htail :=
    uniform_deviation_tail_bound_separable_of_sample_empirical_le_delta
      (μ := μ) (n := n) hn
      (linearPredictorL2 :
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
      (fun w ↦ (continuous_linearPredictorL2_input w).measurable)
      Z hZ
      (fun S ↦
        W * (n : ℝ)⁻¹ *
          Real.sqrt
            (∑ k : Fin n, ‖(S k : EuclideanSpace ℝ (Fin d))‖ ^ 2))
      (mul_pos hX hW)
      (fun w x ↦ abs_linearPredictorL2_le hW.le w x)
      continuous_linearPredictorL2_weight
      (linear_predictor_l2_empirical_bound_of_sample d n W X hW.le)
      hδ hδ_one
  simpa only [Function.comp_apply] using htail


/-! ## Examples

Worked uses of this module's public API. They are elaborated with the library, so they
double as acceptance tests that these statements stay usable as written.
-/

/-!
## `ℓ₂` linear predictors

For weights with $\lVert w\rVert_2\le W$ and inputs with
$\lVert x\rVert_2\le X$, the deterministic end-to-end estimate is

$$
\Pr\!\left\{
  \operatorname{UD}_n
  \ge \frac{2XW}{\sqrt n}
    +XW\sqrt{\frac{2\log(1/\delta)}{n}}
\right\}\le\delta.
$$

`linear_predictor_l2_uniform_deviation_tail_bound_delta` obtains this result
by composing the fixed-sample linear estimate with the generic bridge.
-/

/-- Main deterministic-threshold example for the `ℓ₂` linear class. -/
example
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * (X * W / Real.sqrt (n : ℝ)) +
          (X * W) * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n
          (linearPredictorL2 :
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
          μ Z (Z ∘ S)}).toReal ≤ δ := by
  exact linear_predictor_l2_uniform_deviation_tail_bound_delta
    d W X hn hX hW Z hZ hδ hδ_one

/-!
The sample-dependent variant retains the observed quadratic radius:

$$
\Pr\!\left\{
  \operatorname{UD}_n
  \ge \frac{2W}{n}\sqrt{\sum_k\lVert Z_k\rVert_2^2}
    +3XW\sqrt{\frac{2\log(2/\delta)}{n}}
\right\}\le\delta.
$$
-/

/-- Main sample-dependent example for the `ℓ₂` linear class. -/
example
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 *
          (W * (n : ℝ)⁻¹ *
            Real.sqrt
              (∑ k : Fin n,
                ‖(Z (S k) : EuclideanSpace ℝ (Fin d))‖ ^ 2)) +
        3 * ((X * W) * Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
          uniformDeviation n
            (linearPredictorL2 :
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
                Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
            μ Z (Z ∘ S)}).toReal ≤ δ := by
  exact linear_predictor_l2_uniform_deviation_tail_bound_of_sample_delta
    d W X hn hX hW Z hZ hδ hδ_one

end Generalization
