/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Moments.SubGaussianOrlicz
import StatsMLlib.Probability.Concentration.Bernstein

/-!
# Bernstein's inequality for sub-exponential variables

A centred variable with finite `ψ₁` norm has a quadratic
cumulant-generating function on a neighbourhood of the origin, and feeding that
into the generic Bernstein tail optimiser of
`StatsMLlib.Probability.Concentration.Bernstein` gives the two-scale tail bound.

The single-variable moment-generating bound is obtained from the pointwise
estimate `exp u ≤ 1 + u + u ^ 2 * exp |u|`, which needs no interchange of
expectation and infinite sum.

## Main definitions

This module introduces no new definitions.

## Main results

* `cgf_le_of_hasOrliczPsi1Bound`: the local quadratic cumulant bound.
* `bernstein_subExponential`: the two-scale tail bound for an independent sum.
* `bernstein_subExponential_smul`: its weighted form.  The weights are assumed
  nonzero: a coordinate with `a i = 0` contributes an almost surely vanishing
  summand and no positive `ψ₁` scale of the form `|a i| * K`, so such
  coordinates are removed from the index set rather than carried.
* `bernstein_inequality_two_sided`: the two-sided form of the bounded
  Bernstein inequality, the only part missing from
  `StatsMLlib.Probability.Concentration.Bernstein`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ## Pointwise exponential estimates -/

/-- `s ^ 2 ≤ 2 * exp s` for `s ≥ 0`. -/
private lemma sq_le_two_mul_exp {s : ℝ} (hs : 0 ≤ s) : s ^ 2 ≤ 2 * exp s := by
  have h := Real.quadratic_le_exp_of_nonneg hs
  nlinarith

/-- A global second-order estimate for the exponential, with a crude constant:
`exp u ≤ 1 + u + u ^ 2 * exp |u|`. -/
private lemma exp_le_one_add_add_sq_mul_exp_abs (u : ℝ) :
    exp u ≤ 1 + u + u ^ 2 * exp |u| := by
  rcases le_or_gt 0 u with hu | hu
  · -- `exp u - 1 ≤ u * exp u`, applied twice
    rw [abs_of_nonneg hu]
    have hneg : 1 - u ≤ exp (-u) := by
      have := Real.add_one_le_exp (-u)
      linarith
    have hexp : (0 : ℝ) < exp u := exp_pos u
    have hmul : exp u - 1 ≤ u * exp u := by
      have h := mul_le_mul_of_nonneg_left hneg hexp.le
      rw [← exp_add, add_neg_cancel, exp_zero] at h
      nlinarith
    nlinarith [hmul, hexp, hu]
  · -- `exp u ≤ 1 + u + u ^ 2 / 2` for `u ≤ 0`
    rw [abs_of_neg hu]
    have hv : (0 : ℝ) ≤ -u := by linarith
    have hq := Real.quadratic_le_exp_of_nonneg hv
    have hexpv : (0 : ℝ) < exp (-u) := exp_pos _
    have hpos : (0 : ℝ) < 1 + u + u ^ 2 / 2 := by nlinarith [sq_nonneg (u + 1)]
    have hkey : 1 ≤ exp (-u) * (1 + u + u ^ 2 / 2) := by
      have hfac : (1 + -u + (-u) ^ 2 / 2) * (1 + u + u ^ 2 / 2)
          = 1 + u ^ 4 / 4 := by ring
      nlinarith [hq, hpos, sq_nonneg (u ^ 2)]
    have hle : exp u ≤ 1 + u + u ^ 2 / 2 := by
      have hmul : exp u * (exp (-u) * (1 + u + u ^ 2 / 2)) = 1 + u + u ^ 2 / 2 := by
        rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
      nlinarith [exp_pos u, hkey]
    have h1 : (1 : ℝ) ≤ exp (-u) := by
      have := Real.add_one_le_exp (-u)
      linarith
    nlinarith [sq_nonneg u, h1]

/-! ## Exponential moments -/

/-- A sub-exponential variable has an integrable exponential at its own
scale. -/
lemma integrable_exp_abs_div_of_hasOrliczPsi1Bound {μ : Measure Ω} {X : Ω → ℝ}
    {K : ℝ} (hXm : AEMeasurable X μ) (hK : HasOrliczPsi1Bound X μ K) :
    Integrable (fun ω => exp (|X ω| / K)) μ := by
  have habsm : AEMeasurable (fun ω => |X ω|) μ :=
    continuous_abs.measurable.comp_aemeasurable hXm
  refine ⟨((habsm.div_const K).exp).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => (exp_pos _).le)]
  exact lt_of_le_of_lt hK.2 (by norm_num)


/-- The exponential moment of a sub-exponential variable at its own scale is at
most `2`. -/
lemma integral_exp_abs_div_le_of_hasOrliczPsi1Bound {μ : Measure Ω} {X : Ω → ℝ}
    {K : ℝ} (hXm : AEMeasurable X μ) (hK : HasOrliczPsi1Bound X μ K) :
    ∫ ω, exp (|X ω| / K) ∂μ ≤ 2 := by
  have habsm : AEMeasurable (fun ω => |X ω|) μ :=
    continuous_abs.measurable.comp_aemeasurable hXm
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => (exp_pos _).le)
    ((habsm.div_const K).exp).aestronglyMeasurable]
  calc
    (∫⁻ ω, ENNReal.ofReal (exp (|X ω| / K)) ∂μ).toReal ≤ (2 : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by norm_num) hK.2
    _ = 2 := by norm_num

/-- A sub-exponential variable is integrable. -/
lemma integrable_of_hasOrliczPsi1Bound {μ : Measure Ω} {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ) (hK : HasOrliczPsi1Bound X μ K) :
    Integrable X μ := by
  have hKpos := hK.pos
  refine Integrable.mono'
    ((integrable_exp_abs_div_of_hasOrliczPsi1Bound hXm hK).const_mul K)
    hXm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have h := Real.add_one_le_exp (|X ω| / K)
  rw [Real.norm_eq_abs]
  calc |X ω| = K * (|X ω| / K) := by field_simp
    _ ≤ K * exp (|X ω| / K) := by gcongr; linarith

/-- Exponential tilts of a sub-exponential variable are integrable on the
scale's neighbourhood of the origin. -/
lemma integrable_exp_mul_of_hasOrliczPsi1Bound {μ : Measure Ω} {X : Ω → ℝ}
    {K l : ℝ} (hXm : AEMeasurable X μ) (hK : HasOrliczPsi1Bound X μ K)
    (hl : |l| ≤ (2 * K)⁻¹) :
    Integrable (fun ω => exp (l * X ω)) μ := by
  have hKpos := hK.pos
  refine Integrable.mono' (integrable_exp_abs_div_of_hasOrliczPsi1Bound hXm hK)
    ((hXm.const_mul l).exp).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  refine exp_le_exp.mpr ?_
  have habs : l * X ω ≤ |l| * |X ω| := by
    calc l * X ω ≤ |l * X ω| := le_abs_self _
      _ = |l| * |X ω| := abs_mul _ _
  have hstep : |l| * |X ω| ≤ (2 * K)⁻¹ * |X ω| := by gcongr
  have hinv : (2 * K)⁻¹ ≤ K⁻¹ := by
    rw [inv_le_inv₀ (by positivity) hKpos]
    linarith
  have hfinal : (2 * K)⁻¹ * |X ω| ≤ |X ω| / K := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
  linarith

/-- The moment-generating function of a centred sub-exponential variable is
sub-Gaussian on a neighbourhood of the origin. -/
lemma mgf_le_of_hasOrliczPsi1Bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K l : ℝ} (hXm : AEMeasurable X μ) (hK : HasOrliczPsi1Bound X μ K)
    (hcenter : ∫ ω, X ω ∂μ = 0) (hl : |l| ≤ (2 * K)⁻¹) :
    mgf X μ l ≤ exp (16 * l ^ 2 * K ^ 2) := by
  have hKpos := hK.pos
  have hexpint := integrable_exp_abs_div_of_hasOrliczPsi1Bound hXm hK
  have hXint := integrable_of_hasOrliczPsi1Bound hXm hK
  have hexpl := integrable_exp_mul_of_hasOrliczPsi1Bound hXm hK hl
  have hpt : ∀ ω, exp (l * X ω)
      ≤ 1 + l * X ω + 8 * l ^ 2 * K ^ 2 * exp (|X ω| / K) := by
    intro ω
    have hbase := exp_le_one_add_add_sq_mul_exp_abs (l * X ω)
    have habs : |l * X ω| ≤ |X ω| / (2 * K) := by
      rw [abs_mul]
      have hstep : |l| * |X ω| ≤ (2 * K)⁻¹ * |X ω| := by gcongr
      rw [div_eq_inv_mul]
      exact hstep
    have hsq : (l * X ω) ^ 2 ≤ 8 * l ^ 2 * K ^ 2 * exp (|X ω| / (2 * K)) := by
      have hs : (0 : ℝ) ≤ |X ω| / (2 * K) := by positivity
      have h2 := sq_le_two_mul_exp hs
      have hXsq : X ω ^ 2 = (2 * K) ^ 2 * (|X ω| / (2 * K)) ^ 2 := by
        rw [div_pow, sq_abs]
        field_simp
      calc (l * X ω) ^ 2 = l ^ 2 * X ω ^ 2 := by ring
        _ = l ^ 2 * ((2 * K) ^ 2 * (|X ω| / (2 * K)) ^ 2) := by rw [hXsq]
        _ ≤ l ^ 2 * ((2 * K) ^ 2 * (2 * exp (|X ω| / (2 * K)))) := by
          gcongr
        _ = 8 * l ^ 2 * K ^ 2 * exp (|X ω| / (2 * K)) := by ring
    have hprod : (l * X ω) ^ 2 * exp |l * X ω|
        ≤ 8 * l ^ 2 * K ^ 2 * exp (|X ω| / K) := by
      have hexpmono : exp |l * X ω| ≤ exp (|X ω| / (2 * K)) := exp_le_exp.mpr habs
      have hsum : exp (|X ω| / (2 * K)) * exp (|X ω| / (2 * K))
          = exp (|X ω| / K) := by
        rw [← exp_add]
        congr 1
        field_simp
        ring
      calc (l * X ω) ^ 2 * exp |l * X ω|
          ≤ (8 * l ^ 2 * K ^ 2 * exp (|X ω| / (2 * K))) *
            exp (|X ω| / (2 * K)) := by
            gcongr
        _ = 8 * l ^ 2 * K ^ 2 * exp (|X ω| / K) := by
            rw [mul_assoc, hsum]
    linarith
  have hRHSint : Integrable
      (fun ω => 1 + l * X ω + 8 * l ^ 2 * K ^ 2 * exp (|X ω| / K)) μ :=
    ((integrable_const 1).add (hXint.const_mul l)).add (hexpint.const_mul _)
  have hexp2 := integral_exp_abs_div_le_of_hasOrliczPsi1Bound hXm hK
  have hcoef : (0 : ℝ) ≤ 8 * l ^ 2 * K ^ 2 := by positivity
  have hfinal : mgf X μ l ≤ 1 + 16 * l ^ 2 * K ^ 2 := by
    rw [mgf]
    calc
      ∫ ω, exp (l * X ω) ∂μ
          ≤ ∫ ω, (1 + l * X ω + 8 * l ^ 2 * K ^ 2 * exp (|X ω| / K)) ∂μ :=
        integral_mono hexpl hRHSint hpt
      _ = 1 + 8 * l ^ 2 * K ^ 2 * ∫ ω, exp (|X ω| / K) ∂μ := by
        rw [integral_add (f := fun ω => 1 + l * X ω)
            (g := fun ω => 8 * l ^ 2 * K ^ 2 * exp (|X ω| / K))
            ((integrable_const 1).add (hXint.const_mul l))
            (hexpint.const_mul _),
          integral_add (f := fun _ : Ω => (1 : ℝ)) (g := fun ω => l * X ω)
            (integrable_const 1) (hXint.const_mul l),
          integral_const]
        simp only [integral_const_mul]
        rw [hcenter]
        simp
      _ ≤ 1 + 16 * l ^ 2 * K ^ 2 := by
        have := mul_le_mul_of_nonneg_left hexp2 hcoef
        linarith
  refine hfinal.trans ?_
  have := Real.add_one_le_exp (16 * l ^ 2 * K ^ 2)
  linarith


/-- The cumulant-generating function of a centred sub-exponential variable is
quadratic on a neighbourhood of the origin. -/
lemma cgf_le_of_hasOrliczPsi1Bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K l : ℝ} (hXm : AEMeasurable X μ)
    (hK : HasOrliczPsi1Bound X μ K) (hcenter : ∫ ω, X ω ∂μ = 0)
    (hl : |l| ≤ (2 * K)⁻¹) :
    cgf X μ l ≤ 16 * l ^ 2 * K ^ 2 := by
  have hpos : 0 < mgf X μ l :=
    mgf_pos (integrable_exp_mul_of_hasOrliczPsi1Bound hXm hK hl)
  rw [cgf]
  calc
    Real.log (mgf X μ l) ≤ Real.log (exp (16 * l ^ 2 * K ^ 2)) :=
      Real.log_le_log hpos (mgf_le_of_hasOrliczPsi1Bound hXm hK hcenter hl)
    _ = 16 * l ^ 2 * K ^ 2 := Real.log_exp _

/-- Rescaling a sub-exponential variable rescales an admissible scale. -/
lemma HasOrliczPsi1Bound.const_mul {μ : Measure Ω} {X : Ω → ℝ} {K c s : ℝ}
    (hK : HasOrliczPsi1Bound X μ K) (hs : 0 < s) (hle : |c| * K ≤ s) :
    HasOrliczPsi1Bound (fun ω => c * X ω) μ s := by
  have hKpos := hK.pos
  refine ⟨hs, le_trans (lintegral_mono fun ω => ?_) hK.2⟩
  refine ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_)
  rw [abs_mul, div_le_div_iff₀ hs hKpos]
  calc |c| * |X ω| * K = |X ω| * (|c| * K) := by ring
    _ ≤ |X ω| * s := by gcongr

/-- Exponential integrability of an independent sum, for almost-everywhere
measurable summands.  Mathlib's `iIndepFun.integrable_exp_mul_sum` asks for
genuine measurability. -/
private lemma integrable_exp_mul_sum₀ {ι : Type*} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ι → Ω → ℝ} {t : ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, AEMeasurable (X i) μ)
    {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    Integrable (fun ω => exp (t * (∑ i ∈ s, X i) ω)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi_notin_s h_rec =>
      have h_int_s : ∀ j ∈ s, Integrable (fun ω : Ω => exp (t * X j ω)) μ :=
        fun j hj => h_int j (Finset.mem_insert_of_mem hj)
      specialize h_rec h_int_s
      rw [Finset.sum_insert hi_notin_s]
      refine IndepFun.integrable_exp_mul_add ?_
        (h_int i (Finset.mem_insert_self _ _)) h_rec
      exact (h_indep.indepFun_finsetSum_of_notMem₀ h_meas hi_notin_s).symm

/-! ## Bernstein's inequality -/

/-- Bernstein's inequality for sub-exponential variables. -/
theorem bernstein_subExponential {ι : Type*} [Fintype ι] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} {Ki : ι → ℝ} {b v t : ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ) (h_indep : iIndepFun X μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hK : ∀ i, HasOrliczPsi1Bound (X i) μ (Ki i))
    (hbpos : 0 < b) (hb : ∀ i, Ki i ≤ b)
    (hvpos : 0 < v) (hv : ∑ i, Ki i ^ 2 ≤ v) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |(∑ i, X i) ω|}).toReal
      ≤ 2 * exp (-(1 / 64) * min (t ^ 2 / v) (t / b)) := by
  have hdom : ∀ (l : ℝ), |l| ≤ (2 * 16 * b)⁻¹ → ∀ i, |l| ≤ (2 * Ki i)⁻¹ := by
    intro l hlb i
    have hKi := (hK i).pos
    refine hlb.trans ?_
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith [hb i]
  have hint : ∀ l : ℝ, |l| ≤ (2 * 16 * b)⁻¹ →
      Integrable (fun ω => exp (l * (∑ i, X i) ω)) μ := by
    intro l hlb
    exact integrable_exp_mul_sum₀ h_indep hXm
      (fun i _ => integrable_exp_mul_of_hasOrliczPsi1Bound (hXm i) (hK i) (hdom l hlb i))
  have hcgf : ∀ l : ℝ, |l| ≤ (2 * 16 * b)⁻¹ →
      cgf (∑ i, X i) μ l ≤ 16 * l ^ 2 * v := by
    intro l hlb
    rw [h_indep.cgf_sum₀ hXm (s := Finset.univ)
      (fun i _ => integrable_exp_mul_of_hasOrliczPsi1Bound (hXm i) (hK i)
        (hdom l hlb i))]
    calc
      ∑ i, cgf (X i) μ l ≤ ∑ i, 16 * l ^ 2 * Ki i ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact cgf_le_of_hasOrliczPsi1Bound (hXm i) (hK i) (hcenter i) (hdom l hlb i)
      _ = 16 * l ^ 2 * ∑ i, Ki i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 16 * l ^ 2 * v := by gcongr
  have hmain := bernstein_two_sided_of_cgf_bound (μ := μ) (Y := ∑ i, X i)
    (v := v) (b := b) (C := 16) (t := t) (by norm_num) hvpos hbpos hcgf hint ht
  refine hmain.trans (le_of_eq ?_)
  norm_num

/-- The weighted form of Bernstein's inequality for sub-exponential
variables. -/
theorem bernstein_subExponential_smul {ι : Type*} [Fintype ι] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} {a : ι → ℝ} {K b v t : ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ) (h_indep : iIndepFun X μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hK : ∀ i, HasOrliczPsi1Bound (X i) μ K) (ha : ∀ i, a i ≠ 0)
    (hbpos : 0 < b) (hb : ∀ i, |a i| * K ≤ b)
    (hvpos : 0 < v) (hv : ∑ i, (|a i| * K) ^ 2 ≤ v) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |(∑ i, fun ω => a i * X i ω) ω|}).toReal
      ≤ 2 * exp (-(1 / 64) * min (t ^ 2 / v) (t / b)) := by
  have hYm : ∀ i, AEMeasurable (fun ω => a i * X i ω) μ :=
    fun i => (hXm i).const_mul _
  have hYindep : iIndepFun (fun i ω => a i * X i ω) μ := by
    simpa [Function.comp_def] using
      h_indep.comp (fun i x => a i * x) (fun _ => by fun_prop)
  have hYcenter : ∀ i, ∫ ω, a i * X i ω ∂μ = 0 := by
    intro i
    rw [integral_const_mul, hcenter i, mul_zero]
  have hYK : ∀ i, HasOrliczPsi1Bound (fun ω => a i * X i ω) μ (|a i| * K) := by
    intro i
    exact (hK i).const_mul (mul_pos (abs_pos.mpr (ha i)) (hK i).pos) le_rfl
  exact bernstein_subExponential hYm hYindep hYcenter hYK hbpos hb hvpos hv ht


/-- The two-sided bounded Bernstein inequality.  The one-sided half is
`bernstein_inequality`; only the two-sided packaging is added here. -/
theorem bernstein_inequality_two_sided {ι : Type*} [Fintype ι] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} {b v t : ℝ}
    (hb : 0 ≤ b) (hv : 0 < v) (ht : 0 ≤ t)
    (h_indep : iIndepFun X μ) (hXm : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hvar : ∑ i, variance (X i) μ ≤ v) :
    (μ {ω | t ≤ |(∑ i, X i) ω|}).toReal
      ≤ 2 * exp (-(t ^ 2) / (2 * (v + b * t / 3))) := by
  have hup := bernstein_inequality hb hv ht h_indep hXm hcenter hbound hvar
  have hXm' : ∀ i, AEMeasurable (fun ω => -X i ω) μ := fun i => (hXm i).neg
  have hindep' : iIndepFun (fun i ω => -X i ω) μ := by
    simpa [Function.comp_def] using
      h_indep.comp (fun _ x => -x) (fun _ => by fun_prop)
  have hcenter' : ∀ i, ∫ ω, -X i ω ∂μ = 0 := by
    intro i
    rw [integral_neg, hcenter i, neg_zero]
  have hbound' : ∀ i, ∀ᵐ ω ∂μ, |(-X i ω)| ≤ b := by
    intro i
    filter_upwards [hbound i] with ω hω
    rwa [abs_neg]
  have hvarneg : ∀ i, variance (fun ω => -X i ω) μ = variance (X i) μ := by
    intro i
    exact variance_neg (X := X i) (μ := μ)
  have hvar' : ∑ i, variance (fun ω => -X i ω) μ ≤ v := by
    simpa [hvarneg] using hvar
  have hdown := bernstein_inequality hb hv ht hindep' hXm' hcenter' hbound' hvar'
  have hsetneg : ∀ ω, (∑ i, fun ω => -X i ω) ω = -((∑ i, X i) ω) := by
    intro ω
    simp [Finset.sum_apply]
  have hsub : {ω | t ≤ |(∑ i, X i) ω|}
      ⊆ {ω | t ≤ (∑ i, X i) ω} ∪ {ω | t ≤ (∑ i, fun ω => -X i ω) ω} := by
    intro ω hω
    have hω' : t ≤ |(∑ i, X i) ω| := hω
    rcases le_abs.mp hω' with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      show t ≤ (∑ i, fun ω => -X i ω) ω
      rw [hsetneg]
      exact h
  calc
    (μ {ω | t ≤ |(∑ i, X i) ω|}).toReal
        ≤ (μ ({ω | t ≤ (∑ i, X i) ω}
            ∪ {ω | t ≤ (∑ i, fun ω => -X i ω) ω})).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ ≤ (μ {ω | t ≤ (∑ i, X i) ω}).toReal
        + (μ {ω | t ≤ (∑ i, fun ω => -X i ω) ω}).toReal :=
      measureReal_union_le _ _
    _ ≤ exp (-(t ^ 2) / (2 * (v + b * t / 3)))
        + exp (-(t ^ 2) / (2 * (v + b * t / 3))) := add_le_add hup hdown
    _ = 2 * exp (-(t ^ 2) / (2 * (v + b * t / 3))) := by ring

end
