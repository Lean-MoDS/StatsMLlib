/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import StatsMLlib.Probability.Gaussian.ChiMean
import StatsMLlib.Probability.RandomMatrix.GaussianBilinear
import StatsMLlib.Probability.RandomMatrix.GaussianSingularValue

/-!
# Tail bounds for the extreme singular values of Gaussian random matrices

Let `W` be an `N × d` matrix with independent standard Gaussian entries, modelled as
`Matrix.ofEuclidean w` for `w ∼ stdGaussian (EuclideanSpace ℝ (m × n))`, with
`N = Fintype.card m` rows and `d = Fintype.card n` columns. For a fixed matrix `A`, this file
proves one-sided tail bounds for the largest and smallest singular values of `X = W A`, and
specializes them to the `Σ`-Gaussian ensemble `A = √Σ`, whose rows are independent
`N(0, Σ)` vectors. Throughout, `‖A‖` denotes the `L²` operator norm.

## Main results

* `ProbabilityTheory.sqrt_card_sub_sqrt_card_le_integral_minSingularValue`:
  `√N - √d ≤ 𝔼 σ_min(W)` for `d ≤ N`.
* `ProbabilityTheory.stdGaussian_l2_opNorm_mul_div_sqrt_ge`: upper tail
  `P(‖W A‖ / √N ≥ ‖A‖ (1 + δ) + ‖A‖_F / √N) ≤ exp (-N δ² / 2)`.
* `ProbabilityTheory.stdGaussian_minSingularValue_div_sqrt_le`: lower tail
  `P(σ_min(W) / √N ≤ 1 - δ - √(d / N)) ≤ exp (-N δ² / 2)`.
* `ProbabilityTheory.stdGaussian_minSingularValue_mul_div_sqrt_le`: lower tail
  `P(σ_min(W A) / √N ≤ σ_min(A) (1 - δ - √(d / N))) ≤ exp (-N δ² / 2)`.
* `ProbabilityTheory.stdGaussian_minSingularValue_mul_div_sqrt_le_frobenius`: lower tail
  `P(σ_min(W A) / √N ≤ σ_min(A) (1 - δ) - ‖A‖_F / √N) ≤ exp (-N δ² / 2)`.
* `ProbabilityTheory.stdGaussian_singularValues_zero_mul_sqrt_div_sqrt_ge`,
  `ProbabilityTheory.stdGaussian_singularValues_mul_sqrt_div_sqrt_le`,
  `ProbabilityTheory.stdGaussian_singularValues_mul_sqrt_div_sqrt_le_trace`: the same bounds for
  the `Σ`-Gaussian ensemble `X = W √Σ`, with `‖√Σ‖_F² = tr Σ`.
* `Matrix.minSingularValue_pos_of_injective`, `Matrix.sum_sq_sqrt_eq_trace`,
  `Matrix.minSingularValue_sqrt_pos`: deterministic facts used for the `Σ`-ensemble.
-/

open MeasureTheory Metric Real Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- A matrix whose associated linear map is injective has a positive smallest singular value. -/
theorem minSingularValue_pos_of_injective [Nonempty n] (A : Matrix m n ℝ)
    (hA : Function.Injective A.toEuclideanLin) : 0 < A.minSingularValue := by
  have hne : (sphere (0 : EuclideanSpace ℝ n) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hc : Continuous fun v : EuclideanSpace ℝ n => ‖A.toEuclideanLin v‖ :=
    continuous_norm.comp A.toEuclideanLin.continuous_of_finiteDimensional
  obtain ⟨x, hx, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ n) 1).exists_isMinOn hne
    hc.continuousOn
  have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx1
  refine lt_of_lt_of_le (norm_pos_iff.mpr fun h => hx0 (hA (h.trans (map_zero _).symm)))
    (A.le_minSingularValue fun v hv => isMinOn_iff.mp hmin v (mem_sphere_zero_iff_norm.mpr hv))

omit [DecidableEq n] in
/-- For a symmetric matrix `A`, `∑ᵢⱼ Aᵢⱼ² = tr (A * A)`. -/
theorem sum_sq_eq_trace_mul_self {A : Matrix n n ℝ} (hA : Aᵀ = A) :
    ∑ i, ∑ j, A i j ^ 2 = (A * A).trace := by
  simp only [trace, diag, mul_apply, sq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hA i) j
  rw [transpose_apply] at h
  rw [h]

/-- `‖√Σ‖_F² = tr Σ` for a positive semidefinite `Σ`. -/
theorem sum_sq_sqrt_eq_trace {S : Matrix n n ℝ} (hS : S.PosSemidef) :
    ∑ i, ∑ j, CFC.sqrt S i j ^ 2 = S.trace := by
  have hT : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    have h := (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg S)).1
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using h
  rw [sum_sq_eq_trace_mul_self hT,
    CFC.sqrt_mul_sqrt_self S (Matrix.nonneg_iff_posSemidef.2 hS)]

/-- `σ_min(√Σ) > 0` for a positive definite `Σ`. -/
theorem minSingularValue_sqrt_pos [Nonempty n] {S : Matrix n n ℝ} (hS : S.PosDef) :
    0 < (CFC.sqrt S).minSingularValue := by
  have hnn : 0 ≤ S := Matrix.nonneg_iff_posSemidef.2 hS.posSemidef
  have hU : IsUnit (CFC.sqrt S) := by
    rw [isUnit_iff_isUnit_det]
    have h := (isUnit_iff_isUnit_det _).1 hS.isUnit
    rw [← CFC.sqrt_mul_sqrt_self S hnn, det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  refine (CFC.sqrt S).minSingularValue_pos_of_injective fun x y hxy => ?_
  simp only [toLpLin_apply] at hxy
  exact WithLp.ofLp_injective 2 (mulVec_injective_of_isUnit hU (congrArg WithLp.ofLp hxy))

end Matrix

namespace ProbabilityTheory

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
  [Nonempty m] [Nonempty n]

/-! ## Expectation of the smallest singular value -/

/-- `√N - √d ≤ 𝔼 σ_min(W)` for an `N × d` standard Gaussian matrix `W` with `d ≤ N`. -/
theorem sqrt_card_sub_sqrt_card_le_integral_minSingularValue
    (h : Fintype.card n ≤ Fintype.card m) :
    √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) ≤
      ∫ w, (ofEuclidean w).minSingularValue ∂stdGaussian (EuclideanSpace ℝ (m × n)) := by
  have hd : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ n) := by
    rw [finrank_euclideanSpace]
    exact Fintype.card_pos
  have h1 := sqrt_finrank_sub_sqrt_finrank_le_integral_norm_stdGaussian_sub
    (F := EuclideanSpace ℝ m) hd (by simpa [finrank_euclideanSpace] using h)
  simp only [finrank_euclideanSpace] at h1
  exact h1.trans integral_norm_sub_integral_norm_le_integral_minSingularValue

/-! ## Largest singular value -/

/-- **Upper tail of `‖W A‖`.** For a fixed nonzero `A` and `δ > 0`,
`P(‖W A‖ / √N ≥ ‖A‖ (1 + δ) + ‖A‖_F / √N) ≤ exp (-N δ² / 2)`. -/
theorem stdGaussian_l2_opNorm_mul_div_sqrt_ge [Nonempty l] (A : Matrix n l ℝ) (hA : A ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | ‖A‖ * (1 + δ) + √(∑ i, ∑ j, A i j ^ 2) / √(Fintype.card m : ℝ) ≤
          ‖ofEuclidean w * A‖ / √(Fintype.card m : ℝ)}).toReal ≤
      exp (-(Fintype.card m * δ ^ 2) / 2) := by
  have hN0 : (0 : ℝ) < Fintype.card m := Nat.cast_pos.2 Fintype.card_pos
  have hN : 0 < √(Fintype.card m : ℝ) := Real.sqrt_pos.2 hN0
  have hAn : 0 < ‖A‖ := norm_pos_iff.2 hA
  have ht : 0 < ‖A‖ * √(Fintype.card m : ℝ) * δ := by positivity
  have key := stdGaussian_integral_add_le_l2_opNorm_mul (m := m) A hA ht
  have hE := (integral_l2_opNorm_ofEuclidean_mul_le (m := m) A).2
  have hexp : -(‖A‖ * √(Fintype.card m : ℝ) * δ) ^ 2 / (2 * ‖A‖ ^ 2) =
      -(Fintype.card m * δ ^ 2) / 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hN0.le]
    field_simp
  rw [hexp] at key
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)) key
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw ⊢
  have hw' := mul_le_mul_of_nonneg_right hw hN.le
  rw [add_mul, div_mul_cancel₀ _ hN.ne', div_mul_cancel₀ _ hN.ne'] at hw'
  linarith

/-! ## Smallest singular value -/

/-- **Lower tail of `σ_min(W)`.** For `d ≤ N` and `δ > 0`,
`P(σ_min(W) / √N ≤ 1 - δ - √(d / N)) ≤ exp (-N δ² / 2)`. -/
theorem stdGaussian_minSingularValue_div_sqrt_le (h : Fintype.card n ≤ Fintype.card m) {δ : ℝ}
    (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | (ofEuclidean w).minSingularValue / √(Fintype.card m : ℝ) ≤
          1 - δ - √((Fintype.card n : ℝ) / Fintype.card m)}).toReal ≤
      exp (-(Fintype.card m * δ ^ 2) / 2) := by
  have hN0 : (0 : ℝ) < Fintype.card m := Nat.cast_pos.2 Fintype.card_pos
  have hN : 0 < √(Fintype.card m : ℝ) := Real.sqrt_pos.2 hN0
  have ht : 0 < √(Fintype.card m : ℝ) * δ := by positivity
  have key := stdGaussian_minSingularValue_le_integral_sub (m := m) (n := n) ht
  have hE := sqrt_card_sub_sqrt_card_le_integral_minSingularValue h
  have hexp : -(√(Fintype.card m : ℝ) * δ) ^ 2 / 2 = -(Fintype.card m * δ ^ 2) / 2 := by
    rw [mul_pow, Real.sq_sqrt hN0.le]
  rw [hexp] at key
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)) key
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw ⊢
  rw [div_le_iff₀ hN, Real.sqrt_div' _ hN0.le] at hw
  have e : (1 - δ - √(Fintype.card n : ℝ) / √(Fintype.card m : ℝ)) * √(Fintype.card m : ℝ) =
      √(Fintype.card m : ℝ) - √(Fintype.card m : ℝ) * δ - √(Fintype.card n : ℝ) := by
    field_simp
  linarith

/-- **Lower tail of `σ_min(W A)`.** For `σ_min(A) > 0`, `d ≤ N` and `δ > 0`,
`P(σ_min(W A) / √N ≤ σ_min(A) (1 - δ - √(d / N))) ≤ exp (-N δ² / 2)`. -/
theorem stdGaussian_minSingularValue_mul_div_sqrt_le (A : Matrix n l ℝ)
    (hA : 0 < A.minSingularValue) (h : Fintype.card n ≤ Fintype.card m) {δ : ℝ} (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | (ofEuclidean w * A).minSingularValue / √(Fintype.card m : ℝ) ≤
          A.minSingularValue * (1 - δ - √((Fintype.card n : ℝ) / Fintype.card m))}).toReal ≤
      exp (-(Fintype.card m * δ ^ 2) / 2) := by
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_))
    (stdGaussian_minSingularValue_div_sqrt_le h hδ)
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw ⊢
  have hN : 0 < √(Fintype.card m : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hmul := minSingularValue_mul_le (ofEuclidean w) A
  refine le_of_mul_le_mul_right ?_ hA
  calc (ofEuclidean w).minSingularValue / √(Fintype.card m : ℝ) * A.minSingularValue
      = (ofEuclidean w).minSingularValue * A.minSingularValue / √(Fintype.card m : ℝ) := by
        ring
    _ ≤ (ofEuclidean w * A).minSingularValue / √(Fintype.card m : ℝ) :=
        div_le_div_of_nonneg_right hmul hN.le
    _ ≤ _ := hw.trans_eq (mul_comm _ _)

/-- **Lower tail of `σ_min(W A)`, Frobenius form.** For `σ_min(A) > 0`, `d ≤ N` and `δ > 0`,
`P(σ_min(W A) / √N ≤ σ_min(A) (1 - δ) - ‖A‖_F / √N) ≤ exp (-N δ² / 2)`. -/
theorem stdGaussian_minSingularValue_mul_div_sqrt_le_frobenius (A : Matrix n n ℝ)
    (hA : 0 < A.minSingularValue) (h : Fintype.card n ≤ Fintype.card m) {δ : ℝ} (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | (ofEuclidean w * A).minSingularValue / √(Fintype.card m : ℝ) ≤
          A.minSingularValue * (1 - δ) -
            √(∑ i, ∑ j, A i j ^ 2) / √(Fintype.card m : ℝ)}).toReal ≤
      exp (-(Fintype.card m * δ ^ 2) / 2) := by
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_))
    (stdGaussian_minSingularValue_mul_div_sqrt_le A hA h hδ)
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw ⊢
  refine hw.trans ?_
  have hN0 : (0 : ℝ) < Fintype.card m := Nat.cast_pos.2 Fintype.card_pos
  have hN : 0 < √(Fintype.card m : ℝ) := Real.sqrt_pos.2 hN0
  have hF : A.minSingularValue * √(Fintype.card n : ℝ) ≤ √(∑ i, ∑ j, A i j ^ 2) := by
    rw [← Real.sqrt_sq hA.le, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith [card_mul_minSingularValue_sq_le A])
  have hF' := div_le_div_of_nonneg_right hF hN.le
  rw [Real.sqrt_div' _ hN0.le]
  have e : A.minSingularValue * (1 - δ - √(Fintype.card n : ℝ) / √(Fintype.card m : ℝ)) =
      A.minSingularValue * (1 - δ) -
        A.minSingularValue * √(Fintype.card n : ℝ) / √(Fintype.card m : ℝ) := by
    ring
  rw [e]
  linarith

/-! ## The `Σ`-Gaussian ensemble -/

/-- **Upper tail for the `Σ`-Gaussian ensemble.** For `Σ ⪰ 0`, `Σ ≠ 0` and `δ > 0`,
`P(σ_max(W √Σ) / √N ≥ σ_max(√Σ) (1 + δ) + √(tr Σ / N)) ≤ exp (-N δ² / 2)`. -/
theorem stdGaussian_singularValues_zero_mul_sqrt_div_sqrt_ge {S : Matrix n n ℝ}
    (hS : S.PosSemidef) (hS0 : S ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | (CFC.sqrt S).singularValues 0 * (1 + δ) + √(S.trace / Fintype.card m) ≤
          (ofEuclidean w * CFC.sqrt S).singularValues 0 / √(Fintype.card m : ℝ)}).toReal ≤
      exp (-(Fintype.card m * δ ^ 2) / 2) := by
  have hA : CFC.sqrt S ≠ 0 := by
    intro h0
    apply hS0
    rw [← CFC.sqrt_mul_sqrt_self S (Matrix.nonneg_iff_posSemidef.2 hS), h0, zero_mul]
  have key := stdGaussian_l2_opNorm_mul_div_sqrt_ge (m := m) (CFC.sqrt S) hA hδ
  simp only [singularValues_zero_eq_l2_opNorm]
  rwa [sum_sq_sqrt_eq_trace hS, ← Real.sqrt_div' _ (Nat.cast_nonneg _)] at key

/-- **Lower tail for the `Σ`-Gaussian ensemble.** For `Σ ≻ 0`, `d ≤ N` and `δ > 0`,
`P(σ_min(W √Σ) / √N ≤ σ_min(√Σ) (1 - δ - √(d / N))) ≤ exp (-N δ² / 2)`. -/
theorem stdGaussian_singularValues_mul_sqrt_div_sqrt_le {S : Matrix n n ℝ} (hS : S.PosDef)
    (h : Fintype.card n ≤ Fintype.card m) {δ : ℝ} (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | (ofEuclidean w * CFC.sqrt S).singularValues (Fintype.card n - 1) /
            √(Fintype.card m : ℝ) ≤
          (CFC.sqrt S).singularValues (Fintype.card n - 1) *
            (1 - δ - √((Fintype.card n : ℝ) / Fintype.card m))}).toReal ≤
      exp (-(Fintype.card m * δ ^ 2) / 2) := by
  simp only [singularValues_card_sub_one]
  exact stdGaussian_minSingularValue_mul_div_sqrt_le _ (minSingularValue_sqrt_pos hS) h hδ

/-- **Lower tail for the `Σ`-Gaussian ensemble, trace form.** For `Σ ≻ 0`, `d ≤ N` and
`δ > 0`, `P(σ_min(W √Σ) / √N ≤ σ_min(√Σ) (1 - δ) - √(tr Σ / N)) ≤ exp (-N δ² / 2)`. -/
theorem stdGaussian_singularValues_mul_sqrt_div_sqrt_le_trace {S : Matrix n n ℝ}
    (hS : S.PosDef) (h : Fintype.card n ≤ Fintype.card m) {δ : ℝ} (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (m × n))
        {w | (ofEuclidean w * CFC.sqrt S).singularValues (Fintype.card n - 1) /
            √(Fintype.card m : ℝ) ≤
          (CFC.sqrt S).singularValues (Fintype.card n - 1) * (1 - δ) -
            √(S.trace / Fintype.card m)}).toReal ≤
      exp (-(Fintype.card m * δ ^ 2) / 2) := by
  simp only [singularValues_card_sub_one]
  have key := stdGaussian_minSingularValue_mul_div_sqrt_le_frobenius (m := m) _
    (minSingularValue_sqrt_pos hS) h hδ
  rwa [sum_sq_sqrt_eq_trace hS.posSemidef, ← Real.sqrt_div' _ (Nat.cast_nonneg _)] at key

end ProbabilityTheory
