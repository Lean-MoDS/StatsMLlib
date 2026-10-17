/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.LinearAlgebra.Matrix.OperatorNorm
import StatsMLlib.Probability.Gaussian.LipschitzConcentrationEuclidean

/-!
# Concentration of singular values of a standard Gaussian matrix

Let `W` be an `m × n` matrix with independent standard Gaussian entries, modelled as
`Matrix.ofEuclidean w` for `w ∼ stdGaussian (EuclideanSpace ℝ (m × n))`. Every singular value of
`W` is a `1`-Lipschitz function of `w`, so Gaussian Lipschitz concentration applies directly.
Throughout, `‖A‖` denotes the `L²` operator norm from `Matrix.Norms.L2Operator`.

## Main results

* `ProbabilityTheory.integrable_singularValues_ofEuclidean`,
  `ProbabilityTheory.integrable_minSingularValue_ofEuclidean`,
  `ProbabilityTheory.integrable_l2_opNorm_ofEuclidean_mul`: integrability of these functionals.
* `ProbabilityTheory.stdGaussian_abs_singularValues_sub_integral_ge`: two-sided tail bound
  `P(|σ_k(W) - 𝔼 σ_k(W)| ≥ δ) ≤ 2 exp (-δ² / 2)`.
* `ProbabilityTheory.stdGaussian_abs_singularValues_div_sqrt_sub_integral_ge`: the normalized
  version `P(|σ_k(W)/√m - 𝔼 σ_k(W)/√m| ≥ δ) ≤ 2 exp (-m δ² / 2)`, where `m` is the number of rows.
* `ProbabilityTheory.stdGaussian_minSingularValue_le_integral_sub`: lower tail of the smallest
  singular value, `P(σ_min(W) ≤ 𝔼 σ_min(W) - t) ≤ exp (-t² / 2)`.
* `ProbabilityTheory.stdGaussian_integral_add_le_l2_opNorm_mul`: upper tail of `‖W A‖` for a fixed
  nonzero matrix `A`, `P(‖W A‖ ≥ 𝔼 ‖W A‖ + t) ≤ exp (-t² / (2 ‖A‖²))`.
-/

open MeasureTheory Real Matrix GaussianLipConcen
open scoped Matrix.Norms.L2Operator

namespace ProbabilityTheory

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq n]

/-! ## Integrability -/

/-- Each singular value of a standard Gaussian matrix is integrable. -/
theorem integrable_singularValues_ofEuclidean (k : ℕ) :
    Integrable (fun w : EuclideanSpace ℝ (m × n) => (ofEuclidean w).singularValues k)
      (stdGaussian (EuclideanSpace ℝ (m × n))) :=
  integrable_stdGaussian_of_lipschitz (lipschitzWith_singularValues_ofEuclidean k)

/-- The smallest singular value of a standard Gaussian matrix is integrable. -/
theorem integrable_minSingularValue_ofEuclidean :
    Integrable (fun w : EuclideanSpace ℝ (m × n) => (ofEuclidean w).minSingularValue)
      (stdGaussian (EuclideanSpace ℝ (m × n))) :=
  integrable_stdGaussian_of_lipschitz lipschitzWith_minSingularValue_ofEuclidean

/-- For a fixed `A`, the operator norm of `W A` for a standard Gaussian matrix `W` is
integrable. -/
theorem integrable_l2_opNorm_ofEuclidean_mul (A : Matrix n l ℝ) :
    Integrable (fun w : EuclideanSpace ℝ (m × n) => ‖ofEuclidean w * A‖)
      (stdGaussian (EuclideanSpace ℝ (m × n))) :=
  integrable_stdGaussian_of_lipschitz (lipschitzWith_l2_opNorm_ofEuclidean_mul A)

/-! ## Two-sided concentration of each singular value -/

variable [Nonempty m] [Nonempty n]

/-- **Concentration of singular values.** Each singular value of a standard Gaussian matrix
satisfies `P(|σ_k(W) - 𝔼 σ_k(W)| ≥ δ) ≤ 2 exp (-δ² / 2)`. -/
theorem stdGaussian_abs_singularValues_sub_integral_ge (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | δ ≤ |(ofEuclidean w).singularValues k -
          ∫ v, (ofEuclidean v).singularValues k ∂stdGaussian (EuclideanSpace ℝ (m × n))|}).toReal ≤
      2 * exp (-δ ^ 2 / 2) := by
  have h := stdGaussian_lipschitz_concentration one_pos
    (lipschitzWith_singularValues_ofEuclidean (m := m) (n := n) k) δ hδ
  simpa using h

/-- **Normalized concentration of singular values.** With `m` the number of rows,
`P(|σ_k(W)/√m - 𝔼 σ_k(W)/√m| ≥ δ) ≤ 2 exp (-m δ² / 2)`. -/
theorem stdGaussian_abs_singularValues_div_sqrt_sub_integral_ge (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | δ ≤ |(ofEuclidean w).singularValues k / √(Fintype.card m) -
          ∫ v, (ofEuclidean v).singularValues k / √(Fintype.card m)
            ∂stdGaussian (EuclideanSpace ℝ (m × n))|}).toReal ≤
      2 * exp (-(Fintype.card m * δ ^ 2) / 2) := by
  set c : ℝ := √(Fintype.card m)
  have hc : 0 < c := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hset : {w : EuclideanSpace ℝ (m × n) | δ ≤ |(ofEuclidean w).singularValues k / c -
        ∫ v, (ofEuclidean v).singularValues k / c ∂stdGaussian (EuclideanSpace ℝ (m × n))|} =
      {w | δ * c ≤ |(ofEuclidean w).singularValues k -
        ∫ v, (ofEuclidean v).singularValues k ∂stdGaussian (EuclideanSpace ℝ (m × n))|} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    rw [integral_div, ← sub_div, abs_div, abs_of_pos hc, le_div_iff₀ hc]
  have h := stdGaussian_abs_singularValues_sub_integral_ge (m := m) (n := n) k
    (mul_pos hδ hc)
  rw [hset]
  convert h using 3
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

/-! ## One-sided bounds -/

/-- **Lower tail of the smallest singular value.**
`P(σ_min(W) ≤ 𝔼 σ_min(W) - t) ≤ exp (-t² / 2)`. -/
theorem stdGaussian_minSingularValue_le_integral_sub {t : ℝ} (ht : 0 < t) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | (ofEuclidean w).minSingularValue ≤
          (∫ v, (ofEuclidean v).minSingularValue ∂stdGaussian (EuclideanSpace ℝ (m × n))) -
            t}).toReal ≤
      exp (-t ^ 2 / 2) := by
  have h := stdGaussian_lipschitz_concentration_lower one_pos
    (lipschitzWith_minSingularValue_ofEuclidean (m := m) (n := n)) t ht
  simpa using h

/-- **Upper tail of `‖W A‖`.** For a fixed nonzero matrix `A`,
`P(‖W A‖ ≥ 𝔼 ‖W A‖ + t) ≤ exp (-t² / (2 ‖A‖²))`. -/
theorem stdGaussian_integral_add_le_l2_opNorm_mul (A : Matrix n l ℝ) (hA : A ≠ 0) {t : ℝ}
    (ht : 0 < t) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | ∫ v, ‖ofEuclidean v * A‖ ∂stdGaussian (EuclideanSpace ℝ (m × n)) + t ≤
          ‖ofEuclidean w * A‖}).toReal ≤
      exp (-t ^ 2 / (2 * ‖A‖ ^ 2)) := by
  have h := stdGaussian_lipschitz_concentration_upper (nnnorm_pos.2 hA)
    (lipschitzWith_l2_opNorm_ofEuclidean_mul (m := m) A) t ht
  convert h using 4
  · ext w
    constructor <;> intro hw <;> linarith
  · rw [coe_nnnorm]

end ProbabilityTheory
