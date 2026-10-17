/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Analysis.ChiMeanSequence
import StatsMLlib.Probability.Gaussian.NormMoment
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The mean of the chi distribution

For a standard Gaussian vector `g` in a real inner product space `E` of dimension `k`, the
expectation `𝔼 ‖g‖` is the mean of the chi distribution with `k` degrees of freedom. This file
proves that these means satisfy `𝔼 ‖g_k‖ * 𝔼 ‖g_{k+1}‖ = k`, and deduces that `k ↦ √k - 𝔼 ‖g_k‖`
is antitone on `k ≥ 1`.

## Main definitions

* `ProbabilityTheory.stdGaussianPDFReal E`: the density `(2π)^(-k/2) exp (-‖x‖² / 2)` of
  `stdGaussian E` with respect to `volume`.

## Main results

* `ProbabilityTheory.stdGaussian_eq_withDensity`: `stdGaussian E` has density
  `stdGaussianPDFReal E` with respect to `volume`.
* `ProbabilityTheory.integral_norm_stdGaussian_pos`: `0 < 𝔼 ‖g‖` when `dim E ≥ 1`.
* `ProbabilityTheory.integral_norm_stdGaussian_mul_of_finrank_eq_add_one`:
  `𝔼 ‖g_E‖ * 𝔼 ‖g_F‖ = dim E` when `dim F = dim E + 1` and `dim E ≥ 1`.
* `ProbabilityTheory.sqrt_sub_sqrt_le_integral_norm_stdGaussian_sub`:
  `√n - √d ≤ 𝔼 ‖g_n‖ - 𝔼 ‖g_d‖` for `1 ≤ d ≤ n`.
* `ProbabilityTheory.antitoneOn_sqrt_sub_integral_norm_stdGaussian`: `k ↦ √k - 𝔼 ‖g_k‖` is
  antitone on `k ≥ 1`.
* `ProbabilityTheory.sqrt_finrank_sub_sqrt_finrank_le_integral_norm_stdGaussian_sub`: the same
  increment bound for arbitrary finite-dimensional spaces `E`, `F` with `1 ≤ dim E ≤ dim F`.

## Implementation notes

The density is identified through characteristic functions. Polar coordinates
(`MeasureTheory.integral_fun_norm_addHaar`) express `𝔼 ‖g‖` as `J k / J (k - 1)` with
`J j = ∫_{r > 0} r ^ j exp (-r² / 2) dr`, and the Gamma function recursion gives
`J (j + 2) = (j + 1) * J j`.
-/

open MeasureTheory Module Real Set
open scoped RealInnerProductSpace ENNReal

namespace ProbabilityTheory

/-! ### The density of the standard Gaussian measure -/

section Density

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The density `(2π)^(-dim E / 2) exp (-‖x‖² / 2)` of the standard Gaussian measure on `E`. -/
noncomputable def stdGaussianPDFReal (x : E) : ℝ :=
  ((2 * π) ^ ((finrank ℝ E : ℝ) / 2))⁻¹ * rexp (-‖x‖ ^ 2 / 2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma stdGaussianPDFReal_nonneg (x : E) : 0 ≤ stdGaussianPDFReal E x := by
  unfold stdGaussianPDFReal
  positivity

omit [FiniteDimensional ℝ E] in
@[fun_prop]
lemma measurable_stdGaussianPDFReal : Measurable (stdGaussianPDFReal E) := by
  unfold stdGaussianPDFReal
  fun_prop

lemma integral_stdGaussianPDFReal : ∫ x, stdGaussianPDFReal E x = 1 := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := 1 / 2) (by norm_num)
  have hπ : π / (1 / 2) = 2 * π := by ring
  simp_rw [hπ] at h
  unfold stdGaussianPDFReal
  rw [integral_const_mul]
  simp_rw [neg_div, div_eq_inv_mul (‖_‖ ^ 2), ← neg_mul, one_div] at h ⊢
  rw [h, inv_mul_cancel₀ (by positivity)]

lemma integrable_stdGaussianPDFReal : Integrable (stdGaussianPDFReal E) :=
  Integrable.of_integral_ne_zero (by rw [integral_stdGaussianPDFReal]; exact one_ne_zero)

/-- The standard Gaussian measure has density `stdGaussianPDFReal E` with respect to `volume`. -/
theorem stdGaussian_eq_withDensity :
    stdGaussian E = volume.withDensity (fun x ↦ ENNReal.ofReal (stdGaussianPDFReal E x)) := by
  have : IsProbabilityMeasure
      (volume.withDensity (fun x ↦ ENNReal.ofReal (stdGaussianPDFReal E x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_stdGaussianPDFReal E)
        (ae_of_all _ (stdGaussianPDFReal_nonneg E)), integral_stdGaussianPDFReal,
      ENNReal.ofReal_one]
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  rw [charFun_stdGaussian, charFun_apply, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := E) (b := 1 / 2)
    (by norm_num) Complex.I t
  have hC : ∀ x : E, (ENNReal.ofReal (stdGaussianPDFReal E x)).toReal •
      Complex.exp (⟪x, t⟫ * Complex.I) =
      (((2 * π) ^ ((finrank ℝ E : ℝ) / 2))⁻¹ : ℝ) *
        Complex.exp (-(1 / 2) * ‖x‖ ^ 2 + Complex.I * ⟪t, x⟫) := by
    intro x
    rw [ENNReal.toReal_ofReal (stdGaussianPDFReal_nonneg E x), Complex.real_smul,
      stdGaussianPDFReal, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add,
      real_inner_comm]
    congr 2
    push_cast
    ring
  simp_rw [hC]
  rw [integral_const_mul, h]
  have h2 : (π : ℂ) / (1 / 2) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [h2, show ((finrank ℝ E : ℂ) / 2) = (((finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (by positivity), ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (by positivity), Complex.ofReal_one, one_mul, Complex.I_sq]
  congr 1
  ring

variable {E}

/-- Integrals against `stdGaussian E` are integrals against `volume` weighted by the density. -/
lemma integral_stdGaussian_eq_integral_mul (f : E → ℝ) :
    ∫ x, f x ∂stdGaussian E = ∫ x, stdGaussianPDFReal E x * f x := by
  rw [stdGaussian_eq_withDensity, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (stdGaussianPDFReal_nonneg E _), smul_eq_mul]

end Density

/-! ### Radial moments -/

/-- The radial moment `∫_{r > 0} r ^ j exp (-r² / 2) dr`. -/
private noncomputable def radialMoment (j : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), r ^ j * rexp (-(1 / 2) * r ^ (2 : ℝ))

private lemma radialMoment_eq {j : ℝ} (hj : -1 < j) :
    radialMoment j = (1 / 2) ^ (-(j + 1) / 2) * (1 / 2) * Gamma ((j + 1) / 2) :=
  integral_rpow_mul_exp_neg_mul_rpow two_pos hj (by norm_num)

private lemma radialMoment_pos {j : ℝ} (hj : -1 < j) : 0 < radialMoment j := by
  rw [radialMoment_eq hj]
  have : 0 < Gamma ((j + 1) / 2) := Gamma_pos_of_pos (by linarith)
  positivity

private lemma radialMoment_add_two {j : ℝ} (hj : -1 < j) :
    radialMoment (j + 2) = (j + 1) * radialMoment j := by
  have hj' : (0 : ℝ) < (j + 1) / 2 := by linarith
  rw [radialMoment_eq hj, radialMoment_eq (by linarith),
    show (j + 2 + 1) / 2 = (j + 1) / 2 + 1 by ring, Gamma_add_one hj'.ne',
    show -(j + 2 + 1) / 2 = -(j + 1) / 2 + -1 by ring,
    rpow_add (by norm_num), rpow_neg_one]
  ring

section Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Polar coordinates: `𝔼 ‖g‖ * J (dim E - 1) = J (dim E)`. -/
private lemma integral_norm_stdGaussian_mul_radialMoment (hE : 1 ≤ finrank ℝ E) :
    (∫ x, ‖x‖ ∂stdGaussian E) * radialMoment ((finrank ℝ E : ℝ) - 1) =
      radialMoment (finrank ℝ E) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set d := finrank ℝ E with hd
  set C : ℝ := ((2 * π) ^ ((d : ℝ) / 2))⁻¹ with hC
  have hpow : ∀ y : ℝ, 0 < y → y ^ (d - 1) = y ^ ((d : ℝ) - 1) := by
    intro y _
    rw [← rpow_natCast, Nat.cast_sub hE, Nat.cast_one]
  have hexp : ∀ y : ℝ, rexp (-y ^ 2 / 2) = rexp (-(1 / 2) * y ^ (2 : ℝ)) := by
    intro y
    rw [rpow_two]
    ring_nf
  have h1 : (1 : ℝ) = d * volume.real (Metric.ball (0 : E) 1) *
      (C * radialMoment ((d : ℝ) - 1)) := by
    have h := integral_fun_norm_addHaar (volume : Measure E) (fun r ↦ C * rexp (-r ^ 2 / 2))
    refine (integral_stdGaussianPDFReal E).symm.trans ?_
    simp only [stdGaussianPDFReal, ← hd, ← hC] at h ⊢
    have hI : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • (C * rexp (-y ^ 2 / 2)) =
        C * radialMoment ((d : ℝ) - 1) := by
      rw [radialMoment, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
      simp only [smul_eq_mul, hpow y hy, hexp]
      ring
    rw [h, hI, nsmul_eq_mul, smul_eq_mul, mul_assoc]
  have hc : ∫ x, ‖x‖ ∂stdGaussian E = d * volume.real (Metric.ball (0 : E) 1) *
      (C * radialMoment d) := by
    have h := integral_fun_norm_addHaar (volume : Measure E) (fun r ↦ C * rexp (-r ^ 2 / 2) * r)
    rw [integral_stdGaussian_eq_integral_mul]
    simp only [stdGaussianPDFReal, ← hd, ← hC] at h ⊢
    have hI : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • (C * rexp (-y ^ 2 / 2) * y) =
        C * radialMoment d := by
      rw [radialMoment, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      have hy' : y ^ (d : ℝ) = y ^ (d - 1) * y := by
        rw [rpow_natCast, ← pow_succ, Nat.sub_add_cancel hE]
      simp only [smul_eq_mul, hy', hexp]
      ring
    rw [h, hI, nsmul_eq_mul, smul_eq_mul, mul_assoc]
  linear_combination radialMoment ((d : ℝ) - 1) * hc - radialMoment d * h1

/-- The mean of the chi distribution is positive in positive dimension. -/
theorem integral_norm_stdGaussian_pos (hE : 1 ≤ finrank ℝ E) :
    0 < ∫ x, ‖x‖ ∂stdGaussian E := by
  have h := integral_norm_stdGaussian_mul_radialMoment hE
  have hE' : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hE
  have h1 : 0 < radialMoment ((finrank ℝ E : ℝ) - 1) := radialMoment_pos (by linarith)
  have h2 : 0 < radialMoment (finrank ℝ E) := radialMoment_pos (by linarith)
  rw [← h] at h2
  exact pos_of_mul_pos_left h2 h1.le

/-- The means of consecutive chi distributions multiply to the smaller dimension. -/
theorem integral_norm_stdGaussian_mul_of_finrank_eq_add_one {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (hE : 1 ≤ finrank ℝ E) (hF : finrank ℝ F = finrank ℝ E + 1) :
    (∫ x, ‖x‖ ∂stdGaussian E) * (∫ y, ‖y‖ ∂stdGaussian F) = finrank ℝ E := by
  have hE' : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hE
  have hcE := integral_norm_stdGaussian_mul_radialMoment hE
  have hcF := integral_norm_stdGaussian_mul_radialMoment (E := F) (by omega)
  have hrec := radialMoment_add_two (j := (finrank ℝ E : ℝ) - 1) (by linarith)
  rw [hF] at hcF
  push_cast at hcF
  rw [add_sub_cancel_right] at hcF
  rw [show (finrank ℝ E : ℝ) - 1 + 2 = finrank ℝ E + 1 by ring, sub_add_cancel] at hrec
  have h1 : 0 < radialMoment ((finrank ℝ E : ℝ) - 1) := radialMoment_pos (by linarith)
  have h2 : 0 < radialMoment (finrank ℝ E) := radialMoment_pos (by linarith)
  have key : ((∫ x, ‖x‖ ∂stdGaussian E) * (∫ y, ‖y‖ ∂stdGaussian F)) *
      (radialMoment ((finrank ℝ E : ℝ) - 1) * radialMoment (finrank ℝ E)) =
      finrank ℝ E * (radialMoment ((finrank ℝ E : ℝ) - 1) * radialMoment (finrank ℝ E)) := by
    linear_combination (∫ y, ‖y‖ ∂stdGaussian F) * radialMoment (finrank ℝ E) * hcE +
      radialMoment (finrank ℝ E) * hcF + radialMoment (finrank ℝ E) * hrec
  exact mul_right_cancel₀ (by positivity) key

end Polar

/-! ### Euclidean spaces -/

section Euclidean

/-- The mean of the chi distribution with `k ≥ 1` degrees of freedom is positive. -/
theorem integral_norm_stdGaussian_euclideanSpace_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < ∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin k)) :=
  integral_norm_stdGaussian_pos (by simpa using hk)

/-- `c k * c (k + 1) = k` for the chi means `c k = 𝔼 ‖g_k‖`. -/
theorem integral_norm_stdGaussian_euclideanSpace_mul_succ {k : ℕ} (hk : 1 ≤ k) :
    (∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin k))) *
      (∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin (k + 1)))) = k := by
  simpa using integral_norm_stdGaussian_mul_of_finrank_eq_add_one
    (E := EuclideanSpace ℝ (Fin k)) (F := EuclideanSpace ℝ (Fin (k + 1)))
    (by simpa using hk) (by simp)

/-- `√(k + 1) - √k ≤ 𝔼 ‖g_{k+1}‖ - 𝔼 ‖g_k‖` for `k ≥ 1`. -/
theorem sqrt_succ_sub_sqrt_le_integral_norm_stdGaussian_sub {k : ℕ} (hk : 1 ≤ k) :
    √(k + 1 : ℝ) - √k ≤ ∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin (k + 1))) -
      ∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin k)) :=
  _root_.sqrt_succ_sub_sqrt_le_sub_of_mul_succ_eq
    (fun k ↦ ∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin k)))
    (fun _ hk ↦ integral_norm_stdGaussian_euclideanSpace_pos hk)
    (fun _ hk ↦ integral_norm_stdGaussian_euclideanSpace_mul_succ hk)
    (fun k _ ↦ by simpa using integral_norm_stdGaussian_euclideanSpace_le (ι := Fin k)) k hk

/-- `√n - √d ≤ 𝔼 ‖g_n‖ - 𝔼 ‖g_d‖` for `1 ≤ d ≤ n`. -/
theorem sqrt_sub_sqrt_le_integral_norm_stdGaussian_sub {d n : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    √(n : ℝ) - √d ≤ ∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin n)) -
      ∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin d)) :=
  _root_.sqrt_sub_sqrt_le_sub_of_mul_succ_eq
    (fun k ↦ ∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin k)))
    (fun _ hk ↦ integral_norm_stdGaussian_euclideanSpace_pos hk)
    (fun _ hk ↦ integral_norm_stdGaussian_euclideanSpace_mul_succ hk)
    (fun k _ ↦ by simpa using integral_norm_stdGaussian_euclideanSpace_le (ι := Fin k)) hd hdn

/-- `k ↦ √k - 𝔼 ‖g_k‖` is antitone on `k ≥ 1`. -/
theorem antitoneOn_sqrt_sub_integral_norm_stdGaussian :
    AntitoneOn (fun k : ℕ ↦ √(k : ℝ) - ∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin k)))
      (Ici 1) := by
  intro d hd n _ hdn
  have := sqrt_sub_sqrt_le_integral_norm_stdGaussian_sub hd hdn
  simp only
  linarith

end Euclidean

/-! ### General finite-dimensional spaces -/

section General

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- `𝔼 ‖g‖` only depends on the dimension of `E`. -/
lemma integral_norm_stdGaussian_eq_euclideanSpace :
    ∫ x, ‖x‖ ∂stdGaussian E = ∫ x, ‖x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin (finrank ℝ E))) := by
  rw [← stdGaussian_map (stdOrthonormalBasis ℝ E).repr, integral_map (by fun_prop) (by fun_prop)]
  simp

/-- `√(dim F) - √(dim E) ≤ 𝔼 ‖g_F‖ - 𝔼 ‖g_E‖` for `1 ≤ dim E ≤ dim F`. -/
theorem sqrt_finrank_sub_sqrt_finrank_le_integral_norm_stdGaussian_sub
    (hE : 1 ≤ finrank ℝ E) (hEF : finrank ℝ E ≤ finrank ℝ F) :
    √(finrank ℝ F : ℝ) - √(finrank ℝ E : ℝ) ≤
      ∫ y, ‖y‖ ∂stdGaussian F - ∫ x, ‖x‖ ∂stdGaussian E := by
  rw [integral_norm_stdGaussian_eq_euclideanSpace (E := E),
    integral_norm_stdGaussian_eq_euclideanSpace (E := F)]
  exact sqrt_sub_sqrt_le_integral_norm_stdGaussian_sub hE hEF

end General

end ProbabilityTheory
