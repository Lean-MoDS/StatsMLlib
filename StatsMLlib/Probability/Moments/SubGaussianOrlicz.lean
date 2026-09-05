/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Moments.Orlicz
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Properties of sub-Gaussian random variables

Tail and moment estimates for the Orlicz norms of
`StatsMLlib.Probability.Moments.Orlicz`, following HDP Section 2.6-2.8.

## Main definitions

This module introduces no new definitions.

## Main results

* `measure_abs_ge_le_of_hasOrliczPsi2Bound`: the sub-Gaussian tail estimate for
  an admissible scale, and `measure_abs_ge_le_orliczPsi2Norm` for the norm
  itself (HDP Proposition 2.6.6(i)).
* `HasOrliczPsi2Bound.mul`: the product of two admissible `ψ₂` scales is an
  admissible `ψ₁` scale for the product.
* `orliczPsi1Norm_mul_le`: `‖X Y‖_{ψ₁} ≤ ‖X‖_{ψ₂} ‖Y‖_{ψ₂}`
  (HDP Lemma 2.8.6), and `orliczPsi1Norm_sq_le` its diagonal case.
* `integral_abs_le_orliczPsi2Norm` and `integral_sq_le_orliczPsi2Norm`: the
  cases `p = 1` and `p = 2` of HDP Proposition 2.6.6(ii), with a cruder
  absolute constant than the textbook's `C √p`.
* `orliczPsi2Norm_sub_integral_le` and `orliczPsi1Norm_sub_integral_le`: the
  centering lemmas, HDP Lemma 2.7.8 and its `ψ₁` counterpart.
* `integral_rpow_abs_le_of_hasOrliczPsi2Bound` and
  `integral_rpow_abs_rpow_inv_le_orliczPsi2Norm`: HDP Proposition 2.6.6(ii) for
  a general exponent `p ≥ 1`, in integral and `L^p` form.
* `hasOrliczPsi2Bound_of_measure_abs_ge_le` and
  `orliczPsi2Norm_le_of_measure_abs_ge_le`: the converse of Proposition
  2.6.6(i), obtained from the layer-cake formula.  The textbook calls the tail
  form "equivalent" to the norm form but proves only one direction; this is the
  other one.
-/

open MeasureTheory Real
open scoped ENNReal NNReal

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ## Tails -/

/-- HDP Proposition 2.6.6(i) for an admissible scale: a sub-Gaussian variable
has Gaussian tails. -/
lemma measure_abs_ge_le_of_hasOrliczPsi2Bound {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} {K : ℝ} (hXm : AEMeasurable X μ) (hK : HasOrliczPsi2Bound X μ K)
    {t : ℝ} (ht : 0 ≤ t) :
    (μ {ω | t ≤ |X ω|}).toReal ≤ 2 * exp (-t ^ 2 / K ^ 2) := by
  have hKpos := hK.pos
  have hK2 : (0 : ℝ) < K ^ 2 := pow_pos hKpos 2
  have hfm : AEMeasurable (fun ω => ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hXm.pow_const 2).div_const (K ^ 2)).exp)
  have hsub : {ω | t ≤ |X ω|}
      ⊆ {ω | ENNReal.ofReal (exp (t ^ 2 / K ^ 2))
          ≤ ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2))} := by
    intro ω hω
    refine ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_)
    have hnum : t ^ 2 ≤ X ω ^ 2 := by
      rw [← sq_abs (X ω)]
      exact pow_le_pow_left₀ ht hω 2
    gcongr
  have hmarkov :=
    (mul_meas_ge_le_lintegral₀ hfm (ENNReal.ofReal (exp (t ^ 2 / K ^ 2)))).trans hK.2
  have hle : ENNReal.ofReal (exp (t ^ 2 / K ^ 2)) * μ {ω | t ≤ |X ω|} ≤ 2 := by
    refine le_trans ?_ hmarkov
    gcongr
  have hfin : ENNReal.ofReal (exp (t ^ 2 / K ^ 2)) * μ {ω | t ≤ |X ω|} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)
  have hreal : exp (t ^ 2 / K ^ 2) * (μ {ω | t ≤ |X ω|}).toReal ≤ 2 := by
    have := (ENNReal.toReal_le_toReal hfin (by norm_num)).mpr hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_nonneg _)] at this
  have hexp : (0 : ℝ) < exp (t ^ 2 / K ^ 2) := exp_pos _
  rw [neg_div, exp_neg, ← div_eq_mul_inv, le_div_iff₀ hexp]
  linarith [hreal, mul_comm ((μ {ω | t ≤ |X ω|}).toReal) (exp (t ^ 2 / K ^ 2))]

/-- HDP Proposition 2.6.6(i): a sub-Gaussian variable has Gaussian tails with
the `ψ₂` norm as the scale. -/
lemma measure_abs_ge_le_orliczPsi2Norm {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hXm : AEMeasurable X μ) (hfin : HasFiniteOrliczPsi2Norm X μ)
    (hpos : 0 < orliczPsi2Norm X μ) {t : ℝ} (ht : 0 ≤ t) :
    (μ {ω | t ≤ |X ω|}).toReal ≤ 2 * exp (-t ^ 2 / orliczPsi2Norm X μ ^ 2) :=
  measure_abs_ge_le_of_hasOrliczPsi2Bound hXm
    (hasOrliczPsi2Bound_orliczPsi2Norm hXm hfin hpos) ht

/-! ## Products -/

/-- The product of two admissible `ψ₂` scales is an admissible `ψ₁` scale for
the product of the variables. -/
lemma HasOrliczPsi2Bound.mul {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} {a b : ℝ} (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (ha : HasOrliczPsi2Bound X μ a) (hb : HasOrliczPsi2Bound Y μ b) :
    HasOrliczPsi1Bound (fun ω => X ω * Y ω) μ (a * b) := by
  have hap := ha.pos
  have hbp := hb.pos
  refine ⟨mul_pos hap hbp, ?_⟩
  have hpt : ∀ ω, exp (|X ω * Y ω| / (a * b))
      ≤ 1 / 2 * exp (X ω ^ 2 / a ^ 2) + 1 / 2 * exp (Y ω ^ 2 / b ^ 2) := by
    intro ω
    have hu : (0 : ℝ) ≤ |X ω| / a := by positivity
    have hv : (0 : ℝ) ≤ |Y ω| / b := by positivity
    have harg : |X ω * Y ω| / (a * b) = |X ω| / a * (|Y ω| / b) := by
      rw [abs_mul]
      field_simp
    have hsqu : (|X ω| / a) ^ 2 = X ω ^ 2 / a ^ 2 := by rw [div_pow, sq_abs]
    have hsqv : (|Y ω| / b) ^ 2 = Y ω ^ 2 / b ^ 2 := by rw [div_pow, sq_abs]
    have hyoung : |X ω| / a * (|Y ω| / b)
        ≤ ((|X ω| / a) ^ 2 + (|Y ω| / b) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|X ω| / a - |Y ω| / b)]
    have h1 : exp (|X ω| / a * (|Y ω| / b))
        ≤ exp ((|X ω| / a) ^ 2 / 2) * exp ((|Y ω| / b) ^ 2 / 2) := by
      rw [← exp_add]
      exact exp_le_exp.mpr (by linarith)
    have e1 : exp ((|X ω| / a) ^ 2 / 2) * exp ((|X ω| / a) ^ 2 / 2)
        = exp ((|X ω| / a) ^ 2) := by rw [← exp_add]; ring_nf
    have e2 : exp ((|Y ω| / b) ^ 2 / 2) * exp ((|Y ω| / b) ^ 2 / 2)
        = exp ((|Y ω| / b) ^ 2) := by rw [← exp_add]; ring_nf
    have h2 : exp ((|X ω| / a) ^ 2 / 2) * exp ((|Y ω| / b) ^ 2 / 2)
        ≤ 1 / 2 * exp ((|X ω| / a) ^ 2) + 1 / 2 * exp ((|Y ω| / b) ^ 2) := by
      nlinarith [mul_self_nonneg (exp ((|X ω| / a) ^ 2 / 2) - exp ((|Y ω| / b) ^ 2 / 2)),
        e1, e2]
    rw [harg, ← hsqu, ← hsqv]
    exact h1.trans h2
  have hmX : AEMeasurable (fun ω => ENNReal.ofReal (exp (X ω ^ 2 / a ^ 2))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hXm.pow_const 2).div_const (a ^ 2)).exp)
  have hmY : AEMeasurable (fun ω => ENNReal.ofReal (exp (Y ω ^ 2 / b ^ 2))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hYm.pow_const 2).div_const (b ^ 2)).exp)
  calc
    ∫⁻ ω, ENNReal.ofReal (exp (|X ω * Y ω| / (a * b))) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (exp (X ω ^ 2 / a ^ 2))
            + ENNReal.ofReal (1 / 2) *
              ENNReal.ofReal (exp (Y ω ^ 2 / b ^ 2))) ∂μ := by
      refine lintegral_mono fun ω => ?_
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (1 / 2) * ∫⁻ ω, ENNReal.ofReal (exp (X ω ^ 2 / a ^ 2)) ∂μ
        + ENNReal.ofReal (1 / 2) *
          ∫⁻ ω, ENNReal.ofReal (exp (Y ω ^ 2 / b ^ 2)) ∂μ := by
      rw [lintegral_add_left' (hmX.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (1 / 2) * 2 + ENNReal.ofReal (1 / 2) * 2 := by
      gcongr
      · exact ha.2
      · exact hb.2
    _ = 2 := by
      rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num

/-- HDP Lemma 2.8.6: `‖X Y‖_{ψ₁} ≤ ‖X‖_{ψ₂} ‖Y‖_{ψ₂}`. -/
lemma orliczPsi1Norm_mul_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hXfin : HasFiniteOrliczPsi2Norm X μ) (hYfin : HasFiniteOrliczPsi2Norm Y μ) :
    orliczPsi1Norm (fun ω => X ω * Y ω) μ
      ≤ orliczPsi2Norm X μ * orliczPsi2Norm Y μ := by
  have hA : 0 ≤ orliczPsi2Norm X μ := orliczPsi2Norm_nonneg hXfin
  have hB : 0 ≤ orliczPsi2Norm Y μ := orliczPsi2Norm_nonneg hYfin
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set A := orliczPsi2Norm X μ
  set B := orliczPsi2Norm Y μ
  set δ : ℝ := min 1 (ε / (A + B + 1)) with hδ_def
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (A + B + 1) ≤ ε := by
    have h := min_le_right (1 : ℝ) (ε / (A + B + 1))
    have hpos : (0 : ℝ) < A + B + 1 := by linarith
    calc δ * (A + B + 1) ≤ ε / (A + B + 1) * (A + B + 1) := by
          exact mul_le_mul_of_nonneg_right h hpos.le
      _ = ε := by field_simp
  obtain ⟨a, ha, halt⟩ :=
    Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi2Bound X μ K}) hXfin hδpos
  obtain ⟨b, hb, hblt⟩ :=
    Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi2Bound Y μ K}) hYfin hδpos
  have haA : a < A + δ := halt
  have hbB : b < B + δ := hblt
  have hprod := orliczPsi1Norm_le (HasOrliczPsi2Bound.mul hXm hYm ha hb)
  have hbound : a * b ≤ A * B + ε := by
    nlinarith [ha.pos, hb.pos, hδpos, hδ1, hδε, hA, hB]
  linarith

/-- The diagonal case of HDP Lemma 2.8.6: `‖X²‖_{ψ₁} ≤ ‖X‖_{ψ₂}²`. -/
lemma orliczPsi1Norm_sq_le {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hXfin : HasFiniteOrliczPsi2Norm X μ) :
    orliczPsi1Norm (fun ω => X ω ^ 2) μ ≤ orliczPsi2Norm X μ ^ 2 := by
  simpa [pow_two] using orliczPsi1Norm_mul_le hXm hXm hXfin hXfin

/-! ## Moments -/

/-- Turn a lower-Lebesgue bound into a Bochner bound for a nonnegative
integrand. -/
private lemma integral_le_of_lintegral_ofReal_le {μ : Measure Ω} {f : Ω → ℝ}
    {c : ℝ} (hf : AEStronglyMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) (hc : 0 ≤ c)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal c) :
    ∫ ω, f ω ∂μ ≤ c := by
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hf]
  calc
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ).toReal ≤ (ENNReal.ofReal c).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = c := ENNReal.toReal_ofReal hc

/-- `t ≤ exp (t ^ 2)`. -/
private lemma le_exp_sq (t : ℝ) : t ≤ exp (t ^ 2) := by
  have h := Real.add_one_le_exp (t ^ 2)
  nlinarith [sq_nonneg (t - 1 / 2)]

/-- `u ≤ exp u`. -/
private lemma le_exp_self (u : ℝ) : u ≤ exp u := by
  have h := Real.add_one_le_exp u
  linarith

/-- The first absolute moment of a sub-Gaussian variable, for an admissible
scale.  This is HDP Proposition 2.6.6(ii) at `p = 1`, with a cruder constant. -/
lemma integral_abs_le_of_hasOrliczPsi2Bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ} (hXm : AEMeasurable X μ) (hK : HasOrliczPsi2Bound X μ K) :
    ∫ ω, |X ω| ∂μ ≤ 2 * K := by
  have hKpos := hK.pos
  have hpt : ∀ ω, |X ω| ≤ K * exp (X ω ^ 2 / K ^ 2) := by
    intro ω
    have h := le_exp_sq (|X ω| / K)
    rw [div_pow, sq_abs] at h
    calc |X ω| = K * (|X ω| / K) := by field_simp
      _ ≤ K * exp (X ω ^ 2 / K ^ 2) := by gcongr
  refine integral_le_of_lintegral_ofReal_le
    ((continuous_abs.measurable.comp_aemeasurable hXm).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => abs_nonneg _) (by positivity) ?_
  calc
    ∫⁻ ω, ENNReal.ofReal |X ω| ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal K * ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2)) ∂μ := by
      refine lintegral_mono fun ω => ?_
      rw [← ENNReal.ofReal_mul hKpos.le]
      exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * 2 := by gcongr; exact hK.2
    _ = ENNReal.ofReal (2 * K) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
      norm_num

/-- The first absolute moment is controlled by the `ψ₂` norm. -/
lemma integral_abs_le_orliczPsi2Norm {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : AEMeasurable X μ) (hfin : HasFiniteOrliczPsi2Norm X μ) :
    ∫ ω, |X ω| ∂μ ≤ 2 * orliczPsi2Norm X μ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, halt⟩ :=
    Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi2Bound X μ K}) hfin (half_pos hε)
  have hle := integral_abs_le_of_hasOrliczPsi2Bound hXm ha
  have haA : a < orliczPsi2Norm X μ + ε / 2 := halt
  linarith

/-- The second moment of a sub-Gaussian variable, for an admissible scale.
This is HDP Proposition 2.6.6(ii) at `p = 2`, with a cruder constant. -/
lemma integral_sq_le_of_hasOrliczPsi2Bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ} (hXm : AEMeasurable X μ) (hK : HasOrliczPsi2Bound X μ K) :
    ∫ ω, X ω ^ 2 ∂μ ≤ 2 * K ^ 2 := by
  have hKpos := hK.pos
  have hK2 : (0 : ℝ) < K ^ 2 := pow_pos hKpos 2
  have hpt : ∀ ω, X ω ^ 2 ≤ K ^ 2 * exp (X ω ^ 2 / K ^ 2) := by
    intro ω
    have h := le_exp_self (X ω ^ 2 / K ^ 2)
    calc X ω ^ 2 = K ^ 2 * (X ω ^ 2 / K ^ 2) := by field_simp
      _ ≤ K ^ 2 * exp (X ω ^ 2 / K ^ 2) := by gcongr
  refine integral_le_of_lintegral_ofReal_le
    ((hXm.pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => sq_nonneg _) (by positivity) ?_
  calc
    ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (K ^ 2) *
            ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2)) ∂μ := by
      refine lintegral_mono fun ω => ?_
      rw [← ENNReal.ofReal_mul hK2.le]
      exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (K ^ 2) * ∫⁻ ω, ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K ^ 2) * 2 := by gcongr; exact hK.2
    _ = ENNReal.ofReal (2 * K ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
      norm_num

/-- The second moment is controlled by the square of the `ψ₂` norm. -/
lemma integral_sq_le_orliczPsi2Norm {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : AEMeasurable X μ) (hfin : HasFiniteOrliczPsi2Norm X μ) :
    ∫ ω, X ω ^ 2 ∂μ ≤ 2 * orliczPsi2Norm X μ ^ 2 := by
  have hA : 0 ≤ orliczPsi2Norm X μ := orliczPsi2Norm_nonneg hfin
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set A := orliczPsi2Norm X μ
  set δ : ℝ := min 1 (ε / (4 * A + 4)) with hδ_def
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (4 * A + 4) ≤ ε := by
    have h := min_le_right (1 : ℝ) (ε / (4 * A + 4))
    have hpos : (0 : ℝ) < 4 * A + 4 := by linarith
    calc δ * (4 * A + 4) ≤ ε / (4 * A + 4) * (4 * A + 4) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = ε := by field_simp
  obtain ⟨a, ha, halt⟩ :=
    Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi2Bound X μ K}) hfin hδpos
  have hle := integral_sq_le_of_hasOrliczPsi2Bound hXm ha
  have haA : a < A + δ := halt
  nlinarith [ha.pos, hδpos, hδ1, hδε, hA]

/-! ## Centering -/

/-- HDP Lemma 2.7.8: centering changes the `ψ₂` norm by at most an absolute
factor. -/
lemma orliczPsi2Norm_sub_integral_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : AEMeasurable X μ) (hfin : HasFiniteOrliczPsi2Norm X μ) :
    orliczPsi2Norm (fun ω => X ω - ∫ ω, X ω ∂μ) μ
      ≤ (1 + 2 / √(Real.log 2)) * orliczPsi2Norm X μ := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : (0 : ℝ) < √(Real.log 2) := Real.sqrt_pos.mpr hlog
  have hA : 0 ≤ orliczPsi2Norm X μ := orliczPsi2Norm_nonneg hfin
  set c : ℝ := ∫ ω, X ω ∂μ with hc
  have hcfin : HasFiniteOrliczPsi2Norm (fun _ : Ω => -c) μ :=
    ⟨|(-c)| / √(Real.log 2) + 1,
      (hasOrliczPsi2Bound_const_iff (-c) (by positivity)).mpr (by linarith)⟩
  have hadd : orliczPsi2Norm (fun ω => X ω + -c) μ
      ≤ orliczPsi2Norm X μ + orliczPsi2Norm (fun _ : Ω => -c) μ :=
    orliczPsi2Norm_add_le hXm aemeasurable_const hfin hcfin
  have hconst : orliczPsi2Norm (fun _ : Ω => -c) μ = |c| / √(Real.log 2) := by
    rw [orliczPsi2Norm_const (μ := μ) (-c), abs_neg]
  have habs : |c| ≤ 2 * orliczPsi2Norm X μ := by
    have h1 : |c| ≤ ∫ ω, |X ω| ∂μ := abs_integral_le_integral_abs
    exact h1.trans (integral_abs_le_orliczPsi2Norm hXm hfin)
  have hfun : (fun ω => X ω - c) = fun ω => X ω + -c := by funext ω; ring
  rw [hfun]
  refine hadd.trans ?_
  rw [hconst]
  have hdiv : |c| / √(Real.log 2)
      ≤ 2 * orliczPsi2Norm X μ / √(Real.log 2) := by gcongr
  calc
    orliczPsi2Norm X μ + |c| / √(Real.log 2)
        ≤ orliczPsi2Norm X μ + 2 * orliczPsi2Norm X μ / √(Real.log 2) := by
      linarith
    _ = (1 + 2 / √(Real.log 2)) * orliczPsi2Norm X μ := by
      field_simp


/-- The first absolute moment of a sub-exponential variable, for an admissible
scale. -/
lemma integral_abs_le_of_hasOrliczPsi1Bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ} (hXm : AEMeasurable X μ) (hK : HasOrliczPsi1Bound X μ K) :
    ∫ ω, |X ω| ∂μ ≤ 2 * K := by
  have hKpos := hK.pos
  have hpt : ∀ ω, |X ω| ≤ K * exp (|X ω| / K) := by
    intro ω
    have h := le_exp_self (|X ω| / K)
    calc |X ω| = K * (|X ω| / K) := by field_simp
      _ ≤ K * exp (|X ω| / K) := by gcongr
  have habsm : AEMeasurable (fun ω => |X ω|) μ :=
    continuous_abs.measurable.comp_aemeasurable hXm
  refine integral_le_of_lintegral_ofReal_le habsm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => abs_nonneg _) (by positivity) ?_
  calc
    ∫⁻ ω, ENNReal.ofReal |X ω| ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal K * ENNReal.ofReal (exp (|X ω| / K)) ∂μ := by
      refine lintegral_mono fun ω => ?_
      rw [← ENNReal.ofReal_mul hKpos.le]
      exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (exp (|X ω| / K)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * 2 := by gcongr; exact hK.2
    _ = ENNReal.ofReal (2 * K) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
      norm_num

/-- The first absolute moment is controlled by the `ψ₁` norm. -/
lemma integral_abs_le_orliczPsi1Norm {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : AEMeasurable X μ) (hfin : HasFiniteOrliczPsi1Norm X μ) :
    ∫ ω, |X ω| ∂μ ≤ 2 * orliczPsi1Norm X μ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, halt⟩ :=
    Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi1Bound X μ K}) hfin (half_pos hε)
  have hle := integral_abs_le_of_hasOrliczPsi1Bound hXm ha
  have haA : a < orliczPsi1Norm X μ + ε / 2 := halt
  linarith

/-- HDP Lemma 2.7.10, the `ψ₁` centering lemma. -/
lemma orliczPsi1Norm_sub_integral_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : AEMeasurable X μ) (hfin : HasFiniteOrliczPsi1Norm X μ) :
    orliczPsi1Norm (fun ω => X ω - ∫ ω, X ω ∂μ) μ
      ≤ (1 + 2 / Real.log 2) * orliczPsi1Norm X μ := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ orliczPsi1Norm X μ := orliczPsi1Norm_nonneg hfin
  set c : ℝ := ∫ ω, X ω ∂μ with hc
  have hcfin : HasFiniteOrliczPsi1Norm (fun _ : Ω => -c) μ :=
    ⟨|(-c)| / Real.log 2 + 1,
      (hasOrliczPsi1Bound_const_iff (-c) (by positivity)).mpr (by linarith)⟩
  have hadd : orliczPsi1Norm (fun ω => X ω + -c) μ
      ≤ orliczPsi1Norm X μ + orliczPsi1Norm (fun _ : Ω => -c) μ :=
    orliczPsi1Norm_add_le hXm aemeasurable_const hfin hcfin
  have hconst : orliczPsi1Norm (fun _ : Ω => -c) μ = |c| / Real.log 2 := by
    rw [orliczPsi1Norm_const (μ := μ) (-c), abs_neg]
  have habs : |c| ≤ 2 * orliczPsi1Norm X μ :=
    (abs_integral_le_integral_abs).trans (integral_abs_le_orliczPsi1Norm hXm hfin)
  have hfun : (fun ω => X ω - c) = fun ω => X ω + -c := by funext ω; ring
  rw [hfun]
  refine hadd.trans ?_
  rw [hconst]
  have hdiv : |c| / Real.log 2 ≤ 2 * orliczPsi1Norm X μ / Real.log 2 := by gcongr
  calc
    orliczPsi1Norm X μ + |c| / Real.log 2
        ≤ orliczPsi1Norm X μ + 2 * orliczPsi1Norm X μ / Real.log 2 := by linarith
    _ = (1 + 2 / Real.log 2) * orliczPsi1Norm X μ := by field_simp


/-- The elementary maximisation `u ^ s ≤ (s / e) ^ s * exp u` underlying the
moment bound, for real exponents. -/
private lemma rpow_le_const_mul_exp {u s : ℝ} (hu : 0 ≤ u) (hs : 0 < s) :
    u ^ s ≤ (s / exp 1) ^ s * exp u := by
  rcases eq_or_lt_of_le hu with rfl | hupos
  · rw [Real.zero_rpow (ne_of_gt hs)]
    positivity
  · have hlog : Real.log (u / s) ≤ u / s - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hdiv : Real.log (u / s) = Real.log u - Real.log s :=
      Real.log_div (ne_of_gt hupos) (ne_of_gt hs)
    have hkey : Real.log u * s ≤ Real.log (s / exp 1) * s + u := by
      rw [Real.log_div (ne_of_gt hs) (exp_ne_zero 1), Real.log_exp]
      have hmul : s * Real.log (u / s) ≤ s * (u / s - 1) :=
        mul_le_mul_of_nonneg_left hlog hs.le
      rw [hdiv] at hmul
      have hus : s * (u / s - 1) = u - s := by field_simp
      nlinarith [hmul, hus]
    rw [Real.rpow_def_of_pos hupos, Real.rpow_def_of_pos (by positivity),
      ← Real.exp_add]
    exact exp_le_exp.mpr hkey

/-- HDP Proposition 2.6.6(ii), integral form: the `p`-th absolute moment of a
sub-Gaussian variable, for an admissible scale. -/
lemma integral_rpow_abs_le_of_hasOrliczPsi2Bound {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K p : ℝ} (hXm : AEMeasurable X μ)
    (hK : HasOrliczPsi2Bound X μ K) (hp : 0 < p) :
    ∫ ω, |X ω| ^ p ∂μ ≤ 2 * K ^ p * (p / (2 * exp 1)) ^ (p / 2) := by
  have hKpos := hK.pos
  have hconst : (0 : ℝ) < (p / (2 * exp 1)) ^ (p / 2) := by
    refine Real.rpow_pos_of_pos ?_ _
    positivity
  have hpt : ∀ ω, |X ω| ^ p
      ≤ K ^ p * (p / (2 * exp 1)) ^ (p / 2) * exp (X ω ^ 2 / K ^ 2) := by
    intro ω
    have ht : (0 : ℝ) ≤ |X ω| / K := by positivity
    have hsq : (0 : ℝ) ≤ X ω ^ 2 / K ^ 2 := by positivity
    have hmax := rpow_le_const_mul_exp hsq (by positivity : (0 : ℝ) < p / 2)
    have hscale : (p / 2 / exp 1) = p / (2 * exp 1) := by ring
    rw [hscale] at hmax
    have hsplit : |X ω| ^ p = (X ω ^ 2 / K ^ 2) ^ (p / 2) * K ^ p := by
      have h1 : (X ω ^ 2 / K ^ 2) = (|X ω| / K) ^ (2 : ℕ) := by
        rw [div_pow, sq_abs]
      rw [h1, ← Real.rpow_natCast (|X ω| / K) 2, ← Real.rpow_mul ht]
      have h2 : ((2 : ℕ) : ℝ) * (p / 2) = p := by push_cast; ring
      rw [h2, Real.div_rpow (abs_nonneg _) hKpos.le,
        div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hKpos p))]
    rw [hsplit]
    calc
      (X ω ^ 2 / K ^ 2) ^ (p / 2) * K ^ p
          ≤ ((p / (2 * exp 1)) ^ (p / 2) * exp (X ω ^ 2 / K ^ 2)) * K ^ p := by
        gcongr
      _ = K ^ p * (p / (2 * exp 1)) ^ (p / 2) * exp (X ω ^ 2 / K ^ 2) := by ring
  set C : ℝ := K ^ p * (p / (2 * exp 1)) ^ (p / 2) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact mul_pos (Real.rpow_pos_of_pos hKpos p) hconst
  have habsm : AEMeasurable (fun ω => |X ω| ^ p) μ :=
    (Measurable.pow_const measurable_id p).comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable hXm)
  refine integral_le_of_lintegral_ofReal_le habsm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p)
    (by positivity) ?_
  calc
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal C * ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2)) ∂μ := by
      refine lintegral_mono fun ω => ?_
      rw [← ENNReal.ofReal_mul hCpos.le]
      exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * 2 := by gcongr; exact hK.2
    _ = ENNReal.ofReal (2 * K ^ p * (p / (2 * exp 1)) ^ (p / 2)) := by
      have hEq : (2 : ℝ) * K ^ p * (p / (2 * exp 1)) ^ (p / 2) = C * 2 := by
        rw [hCdef]; ring
      rw [hEq, ENNReal.ofReal_mul hCpos.le]
      norm_num

/-- HDP Proposition 2.6.6(ii): the `L^p` norm of a sub-Gaussian variable grows
at most like `√p`. -/
lemma integral_rpow_abs_rpow_inv_le_orliczPsi2Norm {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {K p : ℝ} (hXm : AEMeasurable X μ)
    (hK : HasOrliczPsi2Bound X μ K) (hp : 1 ≤ p) :
    (∫ ω, |X ω| ^ p ∂μ) ^ p⁻¹ ≤ 2 * K * √p := by
  have hppos : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  have hKpos := hK.pos
  have hmain := integral_rpow_abs_le_of_hasOrliczPsi2Bound hXm hK hppos
  have hbase : (0 : ℝ) ≤ ∫ ω, |X ω| ^ p ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) p
  have hrhs : (0 : ℝ) ≤ 2 * K ^ p * (p / (2 * exp 1)) ^ (p / 2) := by
    have : (0 : ℝ) < (p / (2 * exp 1)) ^ (p / 2) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hKp : (0 : ℝ) < K ^ p := Real.rpow_pos_of_pos hKpos p
    positivity
  have hstep : (∫ ω, |X ω| ^ p ∂μ) ^ p⁻¹
      ≤ (2 * K ^ p * (p / (2 * exp 1)) ^ (p / 2)) ^ p⁻¹ :=
    Real.rpow_le_rpow hbase hmain (by positivity)
  refine hstep.trans ?_
  have hApos : (0 : ℝ) ≤ (p / (2 * exp 1)) ^ (p / 2) :=
    (Real.rpow_pos_of_pos (by positivity) _).le
  have hKp : (0 : ℝ) ≤ K ^ p := (Real.rpow_pos_of_pos hKpos p).le
  have hfac : (2 * K ^ p * (p / (2 * exp 1)) ^ (p / 2)) ^ p⁻¹
      = (2 : ℝ) ^ p⁻¹ * K * (p / (2 * exp 1)) ^ (2 : ℝ)⁻¹ := by
    rw [Real.mul_rpow (by positivity) hApos, Real.mul_rpow (by norm_num) hKp,
      ← Real.rpow_mul hKpos.le,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p / (2 * exp 1)),
      mul_inv_cancel₀ (ne_of_gt hppos), Real.rpow_one]
    congr 2
    field_simp
  rw [hfac]
  have h2 : (2 : ℝ) ^ p⁻¹ ≤ 2 := by
    calc (2 : ℝ) ^ p⁻¹ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by rw [inv_le_one_iff₀]; right; exact hp)
      _ = 2 := Real.rpow_one 2
  have h3 : (p / (2 * exp 1)) ^ (2 : ℝ)⁻¹ ≤ √p := by
    rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    refine Real.sqrt_le_sqrt ?_
    have hden : (1 : ℝ) ≤ 2 * exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    calc p / (2 * exp 1) ≤ p / 1 := by gcongr
      _ = p := by ring
  have hKnn : (0 : ℝ) ≤ K := hKpos.le
  have hb0 : (0 : ℝ) ≤ (p / (2 * exp 1)) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  exact mul_le_mul (mul_le_mul_of_nonneg_right h2 hKnn) h3 hb0 (by positivity)


/-! ## From tails back to the `ψ₂` norm -/

/-- The Gaussian first moment on the half line. -/
private lemma integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ t in Set.Ioi (0 : ℝ), t * exp (-b * t ^ 2) = (2 * b)⁻¹ := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => -(2 * b)⁻¹ * exp (-b * t ^ 2))
        (x * exp (-b * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -b * t ^ 2) (-b * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (-b)
    have h2 := h1.exp.const_mul (-(2 * b)⁻¹)
    have heq : -(2 * b)⁻¹ * (exp (-b * x ^ 2) * (-b * (2 * x)))
        = x * exp (-b * x ^ 2) := by
      have hb' : b ≠ 0 := ne_of_gt hb
      field_simp
    rwa [heq] at h2
  have hcont : ContinuousWithinAt (fun t : ℝ => -(2 * b)⁻¹ * exp (-b * t ^ 2))
      (Set.Ici 0) 0 := by fun_prop
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => t * exp (-b * t ^ 2)) (Set.Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq hb).integrableOn
  have hbot : Filter.Tendsto (fun t : ℝ => -b * t ^ 2) Filter.atTop Filter.atBot := by
    have hsq : Filter.Tendsto (fun t : ℝ => t ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop (by norm_num)
    exact (Filter.tendsto_const_mul_atBot_of_neg (by linarith)).mpr hsq
  have hlim : Filter.Tendsto (fun t : ℝ => -(2 * b)⁻¹ * exp (-b * t ^ 2))
      Filter.atTop (nhds 0) := by
    have := (Real.tendsto_exp_atBot.comp hbot).const_mul (-(2 * b)⁻¹)
    simpa using this
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [hmain]
  simp

/-- The antiderivative used in the layer-cake computation. -/
private lemma intervalIntegral_layercake_kernel {K : ℝ} (hK : 0 < K) (a : ℝ) :
    ∫ t in (0 : ℝ)..a, 2 * t / K ^ 2 * exp (t ^ 2 / K ^ 2)
      = exp (a ^ 2 / K ^ 2) - 1 := by
  have hK2 : (K : ℝ) ^ 2 ≠ 0 := by positivity
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => exp (s ^ 2 / K ^ 2))
      (2 * t / K ^ 2 * exp (t ^ 2 / K ^ 2)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / K ^ 2) (2 * t / K ^ 2) t := by
      simpa using (hasDerivAt_pow 2 t).div_const (K ^ 2)
    simpa [mul_comm] using h1.exp
  have hcont : Continuous fun t : ℝ => 2 * t / K ^ 2 * exp (t ^ 2 / K ^ 2) := by
    fun_prop
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => exp (s ^ 2 / K ^ 2))
    (fun t _ => hderiv t) (hcont.intervalIntegrable 0 a)
  rw [hmain]
  simp


/-- HDP Proposition 2.6.6, converse direction: a Gaussian tail bound with scale
`L` makes `2 * L` an admissible `ψ₂` scale.  The textbook proof of Theorem 3.1.1
uses this when it calls the tail form "equivalent" to the norm form; it is the
only direction the text does not prove. -/
lemma hasOrliczPsi2Bound_of_measure_abs_ge_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {L : ℝ} (hXm : AEMeasurable X μ)
    (hL : 0 < L)
    (htail : ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ |X ω|}).toReal ≤ 2 * exp (-t ^ 2 / L ^ 2)) :
    HasOrliczPsi2Bound X μ (2 * L) := by
  have hL2 : (0 : ℝ) < L ^ 2 := pow_pos hL 2
  set K : ℝ := 2 * L with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  set g : ℝ → ℝ := fun t => 2 * t / K ^ 2 * exp (t ^ 2 / K ^ 2) with hgdef
  have hgcont : Continuous g := by rw [hgdef]; fun_prop
  have habsm : AEMeasurable (fun ω => |X ω|) μ :=
    continuous_abs.measurable.comp_aemeasurable hXm
  -- the layer-cake identity
  have hlayer : ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..|X ω|, g t) ∂μ
      = ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t ≤ |X a|} * ENNReal.ofReal (g t) :=
    lintegral_comp_eq_lintegral_meas_le_mul μ
      (Filter.Eventually.of_forall fun ω => abs_nonneg _) habsm
      (fun t _ => (hgcont.intervalIntegrable 0 t))
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        have : (0 : ℝ) < t := ht
        rw [hgdef]
        positivity)
  -- the left-hand side is the centred exponential moment
  have hLHS : ∀ ω, ∫ t in (0 : ℝ)..|X ω|, g t = exp (X ω ^ 2 / K ^ 2) - 1 := by
    intro ω
    rw [hgdef, intervalIntegral_layercake_kernel hKpos, sq_abs]
  -- the right-hand side is bounded by an explicit Gaussian integral
  have hpt : ∀ t : ℝ, 2 * exp (-t ^ 2 / L ^ 2) * g t
      = (L ^ 2)⁻¹ * (t * exp (-(3 / (4 * L ^ 2)) * t ^ 2)) := by
    intro t
    rw [hgdef, hKdef]
    have hstep : exp (-t ^ 2 / L ^ 2) * exp (t ^ 2 / (2 * L) ^ 2)
        = exp (-(3 / (4 * L ^ 2)) * t ^ 2) := by
      rw [← exp_add]
      congr 1
      field_simp
      ring
    calc
      2 * exp (-t ^ 2 / L ^ 2) * (2 * t / (2 * L) ^ 2 * exp (t ^ 2 / (2 * L) ^ 2))
          = (L ^ 2)⁻¹ * t *
            (exp (-t ^ 2 / L ^ 2) * exp (t ^ 2 / (2 * L) ^ 2)) := by
        field_simp
      _ = (L ^ 2)⁻¹ * (t * exp (-(3 / (4 * L ^ 2)) * t ^ 2)) := by
        rw [hstep]; ring
  have hbpos : (0 : ℝ) < 3 / (4 * L ^ 2) := by positivity
  have hgauss : ∫ t in Set.Ioi (0 : ℝ), 2 * exp (-t ^ 2 / L ^ 2) * g t = 2 / 3 := by
    simp_rw [hpt]
    rw [MeasureTheory.integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq hbpos]
    field_simp
    ring
  have hintble : MeasureTheory.IntegrableOn
      (fun t : ℝ => 2 * exp (-t ^ 2 / L ^ 2) * g t) (Set.Ioi 0) := by
    have hbase : MeasureTheory.IntegrableOn
        (fun t : ℝ => (L ^ 2)⁻¹ * (t * exp (-(3 / (4 * L ^ 2)) * t ^ 2)))
        (Set.Ioi 0) :=
      ((integrable_mul_exp_neg_mul_sq hbpos).const_mul _).integrableOn
    simpa [hpt] using hbase
  have hRHS : ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t ≤ |X a|} * ENNReal.ofReal (g t)
      ≤ ENNReal.ofReal (2 / 3) := by
    have hbound : ∀ t ∈ Set.Ioi (0 : ℝ),
        μ {a | t ≤ |X a|} * ENNReal.ofReal (g t)
          ≤ ENNReal.ofReal (2 * exp (-t ^ 2 / L ^ 2) * g t) := by
      intro t ht
      have htn : (0 : ℝ) ≤ t := le_of_lt ht
      have hmeas : μ {a | t ≤ |X a|} ≤ ENNReal.ofReal (2 * exp (-t ^ 2 / L ^ 2)) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ {a | t ≤ |X a|})]
        exact ENNReal.ofReal_le_ofReal (htail t htn)
      have hgn : (0 : ℝ) ≤ g t := by rw [hgdef]; positivity
      calc
        μ {a | t ≤ |X a|} * ENNReal.ofReal (g t)
            ≤ ENNReal.ofReal (2 * exp (-t ^ 2 / L ^ 2)) * ENNReal.ofReal (g t) := by
          gcongr
        _ = ENNReal.ofReal (2 * exp (-t ^ 2 / L ^ 2) * g t) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
    calc
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t ≤ |X a|} * ENNReal.ofReal (g t)
          ≤ ∫⁻ t in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (2 * exp (-t ^ 2 / L ^ 2) * g t) := by
        refine MeasureTheory.setLIntegral_mono' measurableSet_Ioi ?_
        exact hbound
      _ = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), 2 * exp (-t ^ 2 / L ^ 2) * g t) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintble]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        have : (0 : ℝ) < t := ht
        rw [hgdef]
        positivity
      _ = ENNReal.ofReal (2 / 3) := by rw [hgauss]
  -- assemble
  refine ⟨hKpos, ?_⟩
  have hsplit : ∀ ω, ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2))
      = 1 + ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2) - 1) := by
    intro ω
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num)
      (sub_nonneg.mpr (Real.one_le_exp (by positivity)))]
    congr 1
    ring
  calc
    ∫⁻ ω, ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2)) ∂μ
        = ∫⁻ ω, (1 + ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2) - 1)) ∂μ := by
      simp_rw [hsplit]
    _ = 1 + ∫⁻ ω, ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2) - 1) ∂μ := by
      rw [MeasureTheory.lintegral_add_left' aemeasurable_const, lintegral_const,
        measure_univ, mul_one]
    _ = 1 + ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..|X ω|, g t) ∂μ := by
      simp_rw [hLHS]
    _ = 1 + ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t ≤ |X a|} * ENNReal.ofReal (g t) := by
      rw [hlayer]
    _ ≤ 1 + ENNReal.ofReal (2 / 3) := by gcongr
    _ ≤ 2 := by
      rw [show (2 : ℝ≥0∞) = 1 + 1 by norm_num]
      gcongr
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)


/-- A Gaussian tail bound with scale `L` makes `X` sub-Gaussian with
`‖X‖_{ψ₂} ≤ 2 * L`. -/
lemma orliczPsi2Norm_le_of_measure_abs_ge_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {L : ℝ} (hXm : AEMeasurable X μ)
    (hL : 0 < L)
    (htail : ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ |X ω|}).toReal ≤ 2 * exp (-t ^ 2 / L ^ 2)) :
    HasFiniteOrliczPsi2Norm X μ ∧ orliczPsi2Norm X μ ≤ 2 * L :=
  ⟨⟨2 * L, hasOrliczPsi2Bound_of_measure_abs_ge_le hXm hL htail⟩,
    orliczPsi2Norm_le (hasOrliczPsi2Bound_of_measure_abs_ge_le hXm hL htail)⟩

end
