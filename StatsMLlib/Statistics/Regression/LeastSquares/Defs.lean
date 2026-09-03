/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import StatsMLlib.LearningTheory.EmpiricalProcess.Metric
import StatsMLlib.LearningTheory.EmpiricalRiskMinimization.Defs
import StatsMLlib.Probability.Gaussian.Basic
import Mathlib

/-!
# Least Squares Regression: Core Definitions

This file contains the fundamental definitions for analyzing least squares regression.

## Main Definitions

* `IsStarShaped` - A function class is star-shaped around 0
* `localizedBall` - Ball in a function class w.r.t. empirical norm
* `stdGaussianPi` - Product measure of n i.i.d. standard Gaussians
* `LocalGaussianComplexity` - Local Gaussian complexity at radius δ
* `satisfiesCriticalInequality` - The critical inequality G_n(δ)/δ ≤ δ/(2σ)
* `shiftedClass` - The shifted function class F - {f*}
* `isLeastSquaresEstimator` - Definition of least squares estimator
* `RegressionModel` - The regression model y_i = f*(x_i) + σw_i

-/

open MeasureTheory Finset BigOperators Real ProbabilityTheory GaussianMeasure

namespace LeastSquares

open EmpiricalProcess

variable {X : Type*}

/-- Star-shaped set: A set H of functions is star-shaped around 0 if:
1. The zero function is in H
2. For any h ∈ H and α ∈ [0,1], we have α • h ∈ H -/
def IsStarShaped (H : Set (X → ℝ)) : Prop :=
  (0 : X → ℝ) ∈ H ∧ ∀ h ∈ H, ∀ α : ℝ, 0 ≤ α → α ≤ 1 → (α • h) ∈ H

/-- The localized ball B_n(δ; H) = {h ∈ H : ‖h‖_n ≤ δ} -/
def localizedBall {n : ℕ} (H : Set (X → ℝ)) (δ : ℝ) (x : Fin n → X) : Set (X → ℝ) :=
  {h ∈ H | empiricalNorm n (fun i => h (x i)) ≤ δ}

/-- Local Gaussian complexity:
G_n(δ; H) = 𝔼_w[sup_{h ∈ B_n(δ;H)} |n⁻¹ Σᵢ wᵢh(xᵢ)|]
where w ~ N(0, I_n) -/
noncomputable def LocalGaussianComplexity (n : ℕ) (H : Set (X → ℝ)) (δ : ℝ) (x : Fin n → X) : ℝ :=
  ∫ w, ⨆ h ∈ localizedBall H δ x, |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)| ∂(stdGaussianPi n)

/-- The critical inequality: G_n(δ)/δ ≤ δ/(2σ) -/
def satisfiesCriticalInequality (n : ℕ) (σ δ : ℝ) (H : Set (X → ℝ)) (x : Fin n → X) : Prop :=
  LocalGaussianComplexity n H δ x / δ ≤ δ / (2 * σ)

/-- The shifted class F* = F - {f*} = {f - f* : f ∈ F} -/
def shiftedClass (F : Set (X → ℝ)) (f_star : X → ℝ) : Set (X → ℝ) :=
  {h | ∃ f ∈ F, h = f - f_star}

/-- f - f* is in the shifted class when f ∈ F -/
lemma mem_shiftedClass_of_mem {F : Set (X → ℝ)} {f_star f : X → ℝ} (hf : f ∈ F) :
    f - f_star ∈ shiftedClass F f_star :=
  ⟨f, hf, rfl⟩

/-- 0 is in the shifted class when f* ∈ F -/
lemma zero_mem_shiftedClass_of_f_star_mem {F : Set (X → ℝ)} {f_star : X → ℝ} (hf : f_star ∈ F) :
    (0 : X → ℝ) ∈ shiftedClass F f_star := by
  use f_star, hf
  ext x
  simp

/-- A function f_hat is the least squares estimator if:
1. f_hat ∈ F
2. For all f ∈ F: Σᵢ(yᵢ - f_hat(xᵢ))² ≤ Σᵢ(yᵢ - f(xᵢ))² -/
def isLeastSquaresEstimator {n : ℕ} (y : Fin n → ℝ) (F : Set (X → ℝ)) (x : Fin n → X)
    (f_hat : X → ℝ) : Prop :=
  f_hat ∈ F ∧ ∀ f ∈ F, ∑ i, (y i - f_hat (x i))^2 ≤ ∑ i, (y i - f (x i))^2

/-- The optimality condition of least squares -/
lemma isLeastSquaresEstimator.le_of_mem {n : ℕ} {y : Fin n → ℝ} {F : Set (X → ℝ)} {x : Fin n → X}
    {f_hat : X → ℝ} (h : isLeastSquaresEstimator y F x f_hat) {f : X → ℝ} (hf : f ∈ F) :
    ∑ i, (y i - f_hat (x i))^2 ≤ ∑ i, (y i - f (x i))^2 :=
  h.2 f hf

/-! ### Regression Model -/

/-- The regression model bundles:
- x : design points
- f_star : true function
- σ : noise scale (positive)
- noiseDistribution : distribution of noise (default: stdGaussianPi n)

The model equation is: y_i = f*(x_i) + σ * w_i where w ~ noiseDistribution -/
structure RegressionModel (n : ℕ) (X : Type*) where
  /-- Design points -/
  x : Fin n → X
  /-- True regression function -/
  f_star : X → ℝ
  /-- Noise scale -/
  σ : ℝ
  /-- σ is positive -/
  hσ_pos : 0 < σ
  /-- Noise distribution (default: n i.i.d. standard Gaussians) -/
  noiseDistribution : Measure (Fin n → ℝ) := stdGaussianPi n

variable {n : ℕ}

/-- The response given a noise realization:
y_i = f*(x_i) + σ * w_i -/
def RegressionModel.response (M : RegressionModel n X) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => M.f_star (M.x i) + M.σ * w i

/-- Response at index i equals f*(x_i) + σ * w_i -/
@[simp]
lemma RegressionModel.response_apply (M : RegressionModel n X) (w : Fin n → ℝ) (i : Fin n) :
    M.response w i = M.f_star (M.x i) + M.σ * w i := rfl

/-- σ² is positive -/
lemma RegressionModel.sq_σ_pos (M : RegressionModel n X) : 0 < M.σ ^ 2 :=
  sq_pos_of_pos M.hσ_pos

/-- σ is non-negative -/
lemma RegressionModel.σ_nonneg (M : RegressionModel n X) : 0 ≤ M.σ :=
  le_of_lt M.hσ_pos

/-- Least-squares estimation is empirical risk minimisation.

`isLeastSquaresEstimator` is the squared-loss specialisation of the general predicate
`IsERM`; this is the bridge between them.

The bridge lives here rather than beside `IsERM` because `ARCHITECTURE.md` puts
`LearningTheory` below `Statistics` in the import order, so only this side can see both.

Three gaps are closed in the statement. The general predicate quantifies over a whole
hypothesis type, so the class `F` is used as one via `↥F`. The general predicate
normalises by `n⁻¹`, which is positive and so preserves the inequality. And the sample
is a single family of observations, so the pairs `(x k, y k)` are packaged as one. -/
theorem isLeastSquaresEstimator.isERM {n : ℕ} {y : Fin n → ℝ} {F : Set (X → ℝ)}
    {x : Fin n → X} {f_hat : X → ℝ} (h : isLeastSquaresEstimator y F x f_hat) :
    IsERM n (fun f : ↥F ↦ fun p : X × ℝ ↦ (p.2 - (f : X → ℝ) p.1) ^ 2)
      (fun k ↦ (x k, y k)) ⟨f_hat, h.1⟩ := by
  intro f
  have hle : ∑ k : Fin n, (y k - f_hat (x k)) ^ 2 ≤
      ∑ k : Fin n, (y k - (f : X → ℝ) (x k)) ^ 2 := h.le_of_mem f.2
  have hn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  simpa [empiricalRisk] using mul_le_mul_of_nonneg_left hle hn

end LeastSquares
