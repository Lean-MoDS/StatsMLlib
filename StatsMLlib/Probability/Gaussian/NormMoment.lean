/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.LinearAlgebra.Matrix.OperatorNorm
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Second moments of the standard Gaussian measure

Let `g` be distributed according to `stdGaussian E` on a finite-dimensional real inner product
space `E`. This file collects the moment identities of `g` that are used for singular value bounds
of Gaussian matrices: linear functionals of `g` are centered with covariance given by the inner
product, `𝔼 ‖g‖² = dim E`, and `𝔼 ‖A g‖² = ‖A‖_F²` for a matrix `A`, together with the first
moment bounds `𝔼 ‖g‖ ≤ √(dim E)` and `𝔼 ‖A g‖ ≤ ‖A‖_F` obtained from `(𝔼 X)² ≤ 𝔼 X²`.
It also records that a family of continuous linear functionals of a Gaussian vector is a Gaussian
process.

## Main results

* `ProbabilityTheory.IsGaussian.isGaussianProcess_strongDual`: continuous linear functionals of a
  Gaussian measure form a Gaussian process.
* `ProbabilityTheory.covariance_inner_stdGaussian`: `cov[⟪u, g⟫, ⟪v, g⟫] = ⟪u, v⟫`.
* `ProbabilityTheory.integral_inner_sq_stdGaussian`: `𝔼 ⟪u, g⟫² = ‖u‖²`.
* `ProbabilityTheory.integral_norm_sq_stdGaussian`: `𝔼 ‖g‖² = dim E`.
* `ProbabilityTheory.integral_norm_stdGaussian_le`: `𝔼 ‖g‖ ≤ √(dim E)`.
* `ProbabilityTheory.integral_norm_toEuclideanLin_sq_stdGaussian`: `𝔼 ‖A g‖² = ∑ᵢⱼ Aᵢⱼ²`.
* `ProbabilityTheory.integral_norm_toEuclideanLin_stdGaussian_le`: `𝔼 ‖A g‖ ≤ √(∑ᵢⱼ Aᵢⱼ²)`.
-/

open MeasureTheory Module
open scoped RealInnerProductSpace ENNReal

namespace ProbabilityTheory

/-! ### Gaussian processes of linear functionals -/

section Process

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- A family of continuous linear functionals of a Gaussian measure is a Gaussian process. -/
lemma IsGaussian.isGaussianProcess_strongDual {μ : Measure F} [IsGaussian μ] {T : Type*}
    (L : T → StrongDual ℝ F) : IsGaussianProcess (fun t x ↦ L t x) μ where
  hasGaussianLaw I := IsGaussian.hasGaussianLaw_id.map (ContinuousLinearMap.pi fun i : I ↦ L i)

end Process

/-! ### Linear functionals of the standard Gaussian -/

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The process `t ↦ ⟪u t, g⟫` is a Gaussian process under the standard Gaussian measure. -/
lemma isGaussianProcess_inner_stdGaussian {T : Type*} (u : T → E) :
    IsGaussianProcess (fun t x ↦ ⟪u t, x⟫) (stdGaussian E) :=
  IsGaussian.isGaussianProcess_strongDual fun t ↦ innerSL ℝ (u t)

lemma memLp_two_inner_stdGaussian (u : E) : MemLp (fun x ↦ ⟪u, x⟫) 2 (stdGaussian E) :=
  (innerSL ℝ u).comp_memLp' IsGaussian.memLp_two_id

lemma integrable_inner_stdGaussian (u : E) : Integrable (fun x ↦ ⟪u, x⟫) (stdGaussian E) :=
  (memLp_two_inner_stdGaussian u).integrable (by norm_num)

lemma integrable_inner_sq_stdGaussian (u : E) :
    Integrable (fun x ↦ ⟪u, x⟫ ^ 2) (stdGaussian E) :=
  (memLp_two_inner_stdGaussian u).integrable_sq

/-- Linear functionals of a standard Gaussian vector are centered. -/
lemma integral_inner_stdGaussian (u : E) : ∫ x, ⟪u, x⟫ ∂stdGaussian E = 0 := by
  simpa using integral_strongDual_stdGaussian (innerSL ℝ u)

/-- The covariance of two linear functionals of a standard Gaussian vector is the inner product
of the representing vectors. -/
lemma covariance_inner_stdGaussian (u v : E) :
    cov[fun x ↦ ⟪u, x⟫, fun x ↦ ⟪v, x⟫; stdGaussian E] = ⟪u, v⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_stdGaussian]
  exact innerSL_apply_apply ℝ u v

lemma variance_inner_stdGaussian (u : E) :
    Var[fun x ↦ ⟪u, x⟫; stdGaussian E] = ‖u‖ ^ 2 := by
  rw [← covariance_self (memLp_two_inner_stdGaussian u).aemeasurable,
    covariance_inner_stdGaussian, real_inner_self_eq_norm_sq]

/-- The second moment of a linear functional of a standard Gaussian vector. -/
lemma integral_inner_sq_stdGaussian (u : E) : ∫ x, ⟪u, x⟫ ^ 2 ∂stdGaussian E = ‖u‖ ^ 2 := by
  rw [← variance_of_integral_eq_zero (memLp_two_inner_stdGaussian u).aemeasurable
    (integral_inner_stdGaussian u), variance_inner_stdGaussian]

lemma integral_sum_inner_sq_stdGaussian {m : Type*} [Fintype m] (u : m → E) :
    ∫ x, ∑ i, ⟪u i, x⟫ ^ 2 ∂stdGaussian E = ∑ i, ‖u i‖ ^ 2 := by
  rw [integral_finsetSum _ fun i _ ↦ integrable_inner_sq_stdGaussian (u i)]
  simp_rw [integral_inner_sq_stdGaussian]

/-! ### The norm of the standard Gaussian -/

lemma integrable_norm_stdGaussian : Integrable (fun x ↦ ‖x‖) (stdGaussian E) :=
  IsGaussian.integrable_id.norm

lemma integrable_norm_sq_stdGaussian : Integrable (fun x ↦ ‖x‖ ^ 2) (stdGaussian E) :=
  IsGaussian.memLp_two_id.norm.integrable_sq

/-- `𝔼 ‖g‖² = dim E` for a standard Gaussian vector `g`. -/
lemma integral_norm_sq_stdGaussian : ∫ x, ‖x‖ ^ 2 ∂stdGaussian E = finrank ℝ E := by
  set b := stdOrthonormalBasis ℝ E
  have h : (fun x : E ↦ ‖x‖ ^ 2) = fun x ↦ ∑ i, ⟪b i, x⟫ ^ 2 :=
    funext fun x ↦ (b.sum_sq_inner_right x).symm
  rw [h, integral_sum_inner_sq_stdGaussian]
  simp

/-- `(𝔼 X)² ≤ 𝔼 X²` for a nonnegative square integrable `X` under a probability measure, in the
form `𝔼 X ≤ √(𝔼 X²)`. -/
lemma integral_le_sqrt_integral_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∫ ω, X ω ∂P ≤ √(∫ ω, X ω ^ 2 ∂P) := by
  have h := variance_nonneg X P
  rw [variance_eq_sub hX] at h
  simp only [Pi.pow_apply] at h
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- `𝔼 ‖g‖ ≤ √(dim E)` for a standard Gaussian vector `g`. -/
lemma integral_norm_stdGaussian_le : ∫ x, ‖x‖ ∂stdGaussian E ≤ √(finrank ℝ E : ℝ) := by
  rw [← integral_norm_sq_stdGaussian]
  exact integral_le_sqrt_integral_sq IsGaussian.memLp_two_id.norm

end InnerProduct

/-! ### Euclidean spaces and matrices -/

section Euclidean

variable {ι m : Type*} [Fintype ι] [Fintype m]

/-- `𝔼 ‖g‖² = |ι|` for a standard Gaussian vector `g` of `EuclideanSpace ℝ ι`. -/
lemma integral_norm_sq_stdGaussian_euclideanSpace :
    ∫ x, ‖x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) = Fintype.card ι := by
  rw [integral_norm_sq_stdGaussian, finrank_euclideanSpace]

/-- `𝔼 ‖g‖ ≤ √|ι|` for a standard Gaussian vector `g` of `EuclideanSpace ℝ ι`. -/
lemma integral_norm_stdGaussian_euclideanSpace_le :
    ∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ ι) ≤ √(Fintype.card ι : ℝ) := by
  simpa [finrank_euclideanSpace] using
    integral_norm_stdGaussian_le (E := EuclideanSpace ℝ ι)

variable [DecidableEq ι]

lemma memLp_two_norm_toEuclideanLin_stdGaussian (A : Matrix m ι ℝ) :
    MemLp (fun x ↦ ‖A.toEuclideanLin x‖) 2 (stdGaussian (EuclideanSpace ℝ ι)) :=
  (LinearMap.toContinuousLinearMap A.toEuclideanLin).comp_memLp' IsGaussian.memLp_two_id |>.norm

lemma integrable_norm_toEuclideanLin_stdGaussian (A : Matrix m ι ℝ) :
    Integrable (fun x ↦ ‖A.toEuclideanLin x‖) (stdGaussian (EuclideanSpace ℝ ι)) :=
  (memLp_two_norm_toEuclideanLin_stdGaussian A).integrable (by norm_num)

/-- `𝔼 ‖A g‖² = ∑ᵢⱼ Aᵢⱼ²` for a standard Gaussian vector `g`. -/
lemma integral_norm_toEuclideanLin_sq_stdGaussian (A : Matrix m ι ℝ) :
    ∫ x, ‖A.toEuclideanLin x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) = ∑ i, ∑ j, A i j ^ 2 := by
  have h : (fun x ↦ ‖A.toEuclideanLin x‖ ^ 2) =
      fun x ↦ ∑ i, ⟪WithLp.toLp 2 (A i), x⟫ ^ 2 := by
    funext x
    rw [A.norm_toEuclideanLin_sq]
    simp [PiLp.inner_apply, mul_comm]
  rw [h, integral_sum_inner_sq_stdGaussian]
  simp [EuclideanSpace.real_norm_sq_eq]

/-- `𝔼 ‖A g‖ ≤ √(∑ᵢⱼ Aᵢⱼ²)` for a standard Gaussian vector `g`. -/
lemma integral_norm_toEuclideanLin_stdGaussian_le (A : Matrix m ι ℝ) :
    ∫ x, ‖A.toEuclideanLin x‖ ∂stdGaussian (EuclideanSpace ℝ ι) ≤ √(∑ i, ∑ j, A i j ^ 2) := by
  rw [← integral_norm_toEuclideanLin_sq_stdGaussian]
  exact integral_le_sqrt_integral_sq (memLp_two_norm_toEuclideanLin_stdGaussian A)

end Euclidean

end ProbabilityTheory
