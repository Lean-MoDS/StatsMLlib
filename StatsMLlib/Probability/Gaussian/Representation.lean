/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Linear representation of centered Gaussian measures on `Fin n → ℝ`

Every centered Gaussian measure `ρ` on `Fin n → ℝ` is the image of the standard Gaussian
product measure `stdGaussianPi n` under the linear map `g ↦ A *ᵥ g`, where `A` is the
(positive semidefinite) square root of the covariance matrix of `ρ`.

## Main definitions

* `GaussianMeasure.covMatrix ρ`: the covariance matrix `(cov[x i, x j; ρ])ᵢⱼ` of a measure `ρ`
  on `Fin n → ℝ`.
* `GaussianMeasure.covSqrt ρ`: the matrix square root `CFC.sqrt (covMatrix ρ)`.

## Main results

* `GaussianMeasure.isGaussian_stdGaussianPi`: the standard Gaussian product measure is Gaussian.
* `GaussianMeasure.covMatrix_posSemidef`: covariance matrices are positive semidefinite.
* `GaussianMeasure.covSqrt_mul_self`, `GaussianMeasure.covSqrt_transpose`,
  `GaussianMeasure.sum_covSqrt_mul_covSqrt`: algebraic properties of `covSqrt`.
* `GaussianMeasure.eq_map_stdGaussianPi_of_isGaussian`: a centered Gaussian measure `ρ` equals
  the pushforward of `stdGaussianPi n` along `g ↦ covSqrt ρ *ᵥ g`.
* `GaussianMeasure.integral_eq_integral_stdGaussianPi`: the corresponding change of variables
  formula for integrals.
-/

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder

namespace GaussianMeasure

variable {n : ℕ}

/-- Covariance matrix of a measure on `Fin n → ℝ`. -/
noncomputable def covMatrix (ρ : Measure (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦ cov[fun x ↦ x i, fun x ↦ x j; ρ]

lemma covMatrix_apply (ρ : Measure (Fin n → ℝ)) (i j : Fin n) :
    covMatrix ρ i j = cov[fun x ↦ x i, fun x ↦ x j; ρ] := rfl

/-- `stdGaussianPi n` is the image of the standard Gaussian on `EuclideanSpace ℝ (Fin n)`. -/
lemma stdGaussianPi_eq_map_stdGaussian (n : ℕ) :
    stdGaussianPi n =
      (stdGaussian (EuclideanSpace ℝ (Fin n))).map (EuclideanSpace.equiv (Fin n) ℝ) := by
  rw [← map_pi_eq_stdGaussian (ι := Fin n), Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id.symm

/-- The standard Gaussian product measure is a Gaussian measure. -/
instance isGaussian_stdGaussianPi (n : ℕ) : IsGaussian (stdGaussianPi n) := by
  rw [stdGaussianPi_eq_map_stdGaussian]
  exact isGaussian_map (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap

/-- The covariance matrix of `ρ` is the matrix of the covariance bilinear form of the
corresponding measure on `EuclideanSpace ℝ (Fin n)` in the standard basis. -/
lemma covMatrix_apply_eq_covarianceBilin (ρ : Measure (Fin n → ℝ)) [IsFiniteMeasure ρ]
    (hρ : MemLp id 2 ρ) (i j : Fin n) :
    covMatrix ρ i j = covarianceBilin (ρ.map (toLp 2))
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hν : MemLp id 2 (ρ.map (toLp 2)) :=
    (memLp_map_measure_iff (by fun_prop) (by fun_prop)).2
      ((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp_memLp' hρ)
  rw [covarianceBilin_apply_eq_cov hν, covariance_map_fun (by fun_prop) (by fun_prop)
    (by fun_prop)]
  simp [covMatrix_apply, EuclideanSpace.inner_single_left]

/-- The covariance matrix of a square-integrable finite measure is positive semidefinite. -/
lemma covMatrix_posSemidef (ρ : Measure (Fin n → ℝ)) [IsFiniteMeasure ρ]
    (hρ : MemLp id 2 ρ) : (covMatrix ρ).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨IsHermitian.ext fun i j ↦ ?_, fun x ↦ ?_⟩
  · simp [covMatrix_apply, covariance_comm]
  have hx : toLp 2 x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  have key : star x ⬝ᵥ covMatrix ρ *ᵥ x =
      covarianceBilin (ρ.map (toLp 2)) (toLp 2 x) (toLp 2 x) := by
    rw [hx]
    simp [← covMatrix_apply_eq_covarianceBilin ρ hρ, dotProduct, mulVec, Finset.mul_sum,
      mul_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  exact key ▸ covarianceBilin_self_nonneg _

/-- The linear factor `covSqrt ρ = √(covMatrix ρ)`. -/
noncomputable def covSqrt (ρ : Measure (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt (covMatrix ρ)

/-- `covSqrt ρ` is symmetric. -/
lemma covSqrt_transpose (ρ : Measure (Fin n → ℝ)) : (covSqrt ρ)ᵀ = covSqrt ρ := by
  have h := (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (covMatrix ρ))).1
  simpa [covSqrt, IsHermitian, conjTranspose_eq_transpose_of_trivial] using h

/-- `covSqrt ρ` is a square root of the covariance matrix. -/
lemma covSqrt_mul_self (ρ : Measure (Fin n → ℝ)) [IsFiniteMeasure ρ] (hρ : MemLp id 2 ρ) :
    covSqrt ρ * covSqrt ρ = covMatrix ρ :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.2 (covMatrix_posSemidef ρ hρ))

/-- Entrywise form of `covSqrt ρ * (covSqrt ρ)ᵀ = covMatrix ρ`. -/
lemma sum_covSqrt_mul_covSqrt (ρ : Measure (Fin n → ℝ)) [IsFiniteMeasure ρ]
    (hρ : MemLp id 2 ρ) (i j : Fin n) :
    ∑ k, covSqrt ρ i k * covSqrt ρ j k = covMatrix ρ i j := by
  rw [← covSqrt_mul_self ρ hρ, mul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← congrFun (congrFun (covSqrt_transpose ρ) k) j]
  rfl

/-- A centered Gaussian measure on `Fin n → ℝ` is the image of the standard Gaussian product
measure under `g ↦ covSqrt ρ *ᵥ g`. -/
theorem eq_map_stdGaussianPi_of_isGaussian (ρ : Measure (Fin n → ℝ)) [IsGaussian ρ]
    (hρ : ∫ x, x ∂ρ = 0) :
    ρ = (stdGaussianPi n).map (fun g ↦ covSqrt ρ *ᵥ g) := by
  have hC := covMatrix_posSemidef ρ IsGaussian.memLp_two_id
  have : IsGaussian (ρ.map (toLp 2)) :=
    isGaussian_map (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap
  have hν : ρ.map (toLp 2) = multivariateGaussian 0 (covMatrix ρ) := by
    apply IsGaussian.ext
    · rw [integral_id_multivariateGaussian']
      have h := (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.integral_id_map
        (IsGaussian.integrable_id (μ := ρ))
      rw [hρ, map_zero] at h
      exact h
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        fun i j ↦ ?_
      rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
        covarianceBilin_multivariateGaussian hC]
      simp [← covMatrix_apply_eq_covarianceBilin ρ IsGaussian.memLp_two_id]
  calc ρ = (ρ.map (toLp 2)).map ofLp := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        simp [Function.comp_def]
    _ = (stdGaussianPi n).map (fun g ↦ covSqrt ρ *ᵥ g) := by
        rw [hν, multivariateGaussian, ← map_pi_eq_stdGaussian (ι := Fin n),
          Measure.map_map (by fun_prop) (by fun_prop),
          Measure.map_map (by fun_prop) (by fun_prop)]
        simp [stdGaussianPi, Function.comp_def, covSqrt]

/-- Change of variables: integrals against a centered Gaussian measure `ρ` are integrals
against `stdGaussianPi n` after the substitution `x = covSqrt ρ *ᵥ g`. -/
theorem integral_eq_integral_stdGaussianPi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ρ : Measure (Fin n → ℝ)) [IsGaussian ρ] (hρ : ∫ x, x ∂ρ = 0)
    {F : (Fin n → ℝ) → E} (hF : AEStronglyMeasurable F ρ) :
    ∫ x, F x ∂ρ = ∫ g, F (covSqrt ρ *ᵥ g) ∂(stdGaussianPi n) := by
  have h := eq_map_stdGaussianPi_of_isGaussian ρ hρ
  have hcont : Continuous fun g : Fin n → ℝ ↦ covSqrt ρ *ᵥ g :=
    (Matrix.toLin' (covSqrt ρ)).continuous_of_finiteDimensional
  rw [h] at hF
  rw [← integral_map hcont.aemeasurable hF, ← h]

end GaussianMeasure
