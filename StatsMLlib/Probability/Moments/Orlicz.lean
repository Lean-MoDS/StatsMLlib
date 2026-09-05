/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Orlicz norms `ψ₂` and `ψ₁`

The sub-Gaussian norm `‖X‖_{ψ₂}` and the sub-exponential norm `‖X‖_{ψ₁}` of a
real random variable, as the Luxemburg norms of the Young functions
`t ↦ exp (t ^ 2) - 1` and `t ↦ exp t - 1`.

The defining condition is stated as a lower Lebesgue integral rather than a
Bochner integral: `exp (X ^ 2 / K ^ 2) ≥ 1`, so on a probability measure a
Bochner integral of a non-integrable exponential would evaluate to the junk
value `0` and satisfy `≤ 2` vacuously.  With `∫⁻` the condition fails as it
should, and monotonicity in `K` is immediate.

## Main definitions

* `HasOrliczPsi2Bound X μ K`: `K` is an admissible `ψ₂` scale for `X`.
* `orliczPsi2Norm X μ`: the `ψ₂` norm, the infimum of the admissible scales.
* `HasFiniteOrliczPsi2Norm X μ`: some scale is admissible, i.e. `X` is
  sub-Gaussian.
* `HasOrliczPsi1Bound`, `orliczPsi1Norm`, `HasFiniteOrliczPsi1Norm`: the
  sub-exponential analogues.

## Main results

* `HasOrliczPsi2Bound.mono`: the admissible scales are upward closed.
* `orliczPsi2Norm_le`: an admissible scale bounds the norm.
* `hasOrliczPsi2Bound_orliczPsi2Norm`: the defining infimum is attained.
* `orliczPsi2Norm_mono`: monotonicity in the size of the variable.
* `orliczPsi2Norm_const_mul`: absolute homogeneity.
* `HasOrliczPsi2Bound.add` and `orliczPsi2Norm_add_le`: subadditivity, the
  Luxemburg triangle inequality for the Young function `t ↦ exp (t ^ 2)`.
* `orliczPsi2Norm_const`: `‖c‖_{ψ₂} = |c| / √(log 2)` (HDP Exercise 2.24(a)).
* `orliczPsi2Norm_le_of_abs_le`: a bounded variable is sub-Gaussian
  (HDP Exercise 2.24(b)).

Each of these has a `ψ₁` counterpart with `log 2` in place of `√(log 2)`.
-/

open MeasureTheory Real
open scoped ENNReal NNReal Pointwise

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ## The `ψ₂` norm -/

/-- `K` is an admissible sub-Gaussian scale for `X`: `E[exp (X² / K²)] ≤ 2`. -/
def HasOrliczPsi2Bound (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧ ∫⁻ ω, ENNReal.ofReal (exp (X ω ^ 2 / K ^ 2)) ∂μ ≤ 2

/-- The sub-Gaussian norm `‖X‖_{ψ₂}`, the infimum of the admissible scales. -/
def orliczPsi2Norm (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | HasOrliczPsi2Bound X μ K}

/-- `X` is sub-Gaussian: some sub-Gaussian scale is admissible. -/
def HasFiniteOrliczPsi2Norm (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ K : ℝ, HasOrliczPsi2Bound X μ K

lemma HasOrliczPsi2Bound.pos {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (h : HasOrliczPsi2Bound X μ K) : 0 < K := h.1

/-- The set of admissible sub-Gaussian scales is bounded below by `0`. -/
lemma bddBelow_orliczPsi2Bound (X : Ω → ℝ) (μ : Measure Ω) :
    BddBelow {K : ℝ | HasOrliczPsi2Bound X μ K} :=
  ⟨0, fun _ hK => hK.pos.le⟩

/-- The admissible sub-Gaussian scales are upward closed. -/
lemma HasOrliczPsi2Bound.mono {X : Ω → ℝ} {μ : Measure Ω} {K K' : ℝ}
    (h : HasOrliczPsi2Bound X μ K) (hKK' : K ≤ K') :
    HasOrliczPsi2Bound X μ K' := by
  refine ⟨h.pos.trans_le hKK', le_trans (lintegral_mono fun ω => ?_) h.2⟩
  refine ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_)
  have hK : 0 < K ^ 2 := pow_pos h.pos 2
  have hK' : 0 < K' ^ 2 := pow_pos (h.pos.trans_le hKK') 2
  exact div_le_div_of_nonneg_left (sq_nonneg _) hK
    (by nlinarith [h.pos, sq_nonneg (K' - K)])

/-- An admissible sub-Gaussian scale bounds the `ψ₂` norm. -/
lemma orliczPsi2Norm_le {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (h : HasOrliczPsi2Bound X μ K) : orliczPsi2Norm X μ ≤ K :=
  csInf_le (bddBelow_orliczPsi2Bound X μ) h

lemma orliczPsi2Norm_nonneg {X : Ω → ℝ} {μ : Measure Ω}
    (hfin : HasFiniteOrliczPsi2Norm X μ) : 0 ≤ orliczPsi2Norm X μ :=
  le_csInf hfin fun _ hK => hK.pos.le

/-- Monotonicity of the `ψ₂` norm in the size of the variable. -/
lemma orliczPsi2Norm_mono {X Y : Ω → ℝ} {μ : Measure Ω}
    (hfin : HasFiniteOrliczPsi2Norm Y μ)
    (hXY : ∀ᵐ ω ∂μ, |X ω| ≤ |Y ω|) :
    orliczPsi2Norm X μ ≤ orliczPsi2Norm Y μ := by
  refine csInf_le_csInf (bddBelow_orliczPsi2Bound X μ) hfin fun K hK => ?_
  refine ⟨hK.pos, le_trans (lintegral_mono_ae ?_) hK.2⟩
  filter_upwards [hXY] with ω hω
  refine ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_)
  have hK2 : (0 : ℝ) < K ^ 2 := pow_pos hK.pos 2
  have hsq : X ω ^ 2 ≤ Y ω ^ 2 := by
    rw [← sq_abs (X ω), ← sq_abs (Y ω)]
    gcongr
  gcongr

/-- Positivity of `log 2`, used throughout the constant computations. -/
private lemma log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- A scale is admissible for a constant exactly when it dominates
`|c| / √(log 2)`. -/
lemma hasOrliczPsi2Bound_const_iff {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : ℝ) {K : ℝ} (hK : 0 < K) :
    HasOrliczPsi2Bound (fun _ : Ω => c) μ K ↔ |c| / √(Real.log 2) ≤ K := by
  have hlog := log_two_pos
  have hsqrt : (0 : ℝ) < √(Real.log 2) := Real.sqrt_pos.mpr hlog
  have hK2 : (0 : ℝ) < K ^ 2 := pow_pos hK 2
  have hint : ∫⁻ _ : Ω, ENNReal.ofReal (exp (c ^ 2 / K ^ 2)) ∂μ
      = ENNReal.ofReal (exp (c ^ 2 / K ^ 2)) := by
    simp
  have hstep : ENNReal.ofReal (exp (c ^ 2 / K ^ 2)) ≤ 2 ↔ c ^ 2 / K ^ 2 ≤ Real.log 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2),
      Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
  have hstep2 : c ^ 2 / K ^ 2 ≤ Real.log 2 ↔ |c| / √(Real.log 2) ≤ K := by
    rw [div_le_iff₀ hK2, div_le_iff₀ hsqrt]
    constructor
    · intro h
      have h1 : |c| ^ 2 ≤ (K * √(Real.log 2)) ^ 2 := by
        rw [sq_abs, mul_pow, Real.sq_sqrt hlog.le]
        linarith
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (abs_nonneg c), Real.sqrt_sq (by positivity)] at h2
    · intro h
      have h1 : |c| ^ 2 ≤ (K * √(Real.log 2)) ^ 2 := by gcongr
      rw [sq_abs, mul_pow, Real.sq_sqrt hlog.le] at h1
      linarith
  constructor
  · rintro ⟨-, hle⟩
    rw [hint] at hle
    exact hstep2.mp (hstep.mp hle)
  · intro hle
    exact ⟨hK, by rw [hint]; exact hstep.mpr (hstep2.mpr hle)⟩

/-- Exercise 2.24(a): the `ψ₂` norm of an almost surely constant variable. -/
lemma orliczPsi2Norm_const {μ : Measure Ω} [IsProbabilityMeasure μ] (c : ℝ) :
    orliczPsi2Norm (fun _ : Ω => c) μ = |c| / √(Real.log 2) := by
  have hsqrt : (0 : ℝ) < √(Real.log 2) := Real.sqrt_pos.mpr log_two_pos
  have ha : (0 : ℝ) ≤ |c| / √(Real.log 2) := by positivity
  have hset : {K : ℝ | HasOrliczPsi2Bound (fun _ : Ω => c) μ K}
      = {K : ℝ | 0 < K ∧ |c| / √(Real.log 2) ≤ K} := by
    ext K
    exact ⟨fun hK => ⟨hK.pos, (hasOrliczPsi2Bound_const_iff c hK.pos).mp hK⟩,
      fun hK => (hasOrliczPsi2Bound_const_iff c hK.1).mpr hK.2⟩
  have hbdd : BddBelow {K : ℝ | 0 < K ∧ |c| / √(Real.log 2) ≤ K} :=
    ⟨0, fun _ hK => hK.1.le⟩
  rw [orliczPsi2Norm, hset]
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_csInf ⟨|c| / √(Real.log 2) + 1, by constructor <;> linarith⟩ fun _ hK => hK.2)
  exact csInf_le hbdd ⟨by linarith, by linarith⟩

/-- Exercise 2.24(b): an almost surely bounded variable is sub-Gaussian. -/
lemma orliczPsi2Norm_le_of_abs_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b : ℝ} (hb : 0 ≤ b) (hX : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    orliczPsi2Norm X μ ≤ b / √(Real.log 2) := by
  have hfin : HasFiniteOrliczPsi2Norm (fun _ : Ω => b) μ :=
    ⟨b / √(Real.log 2) + 1, (hasOrliczPsi2Bound_const_iff b
      (by positivity)).mpr (by rw [abs_of_nonneg hb]; linarith)⟩
  have hmono : orliczPsi2Norm X μ ≤ orliczPsi2Norm (fun _ : Ω => b) μ := by
    refine orliczPsi2Norm_mono hfin ?_
    filter_upwards [hX] with ω hω
    rwa [abs_of_nonneg hb]
  rwa [orliczPsi2Norm_const b, abs_of_nonneg hb] at hmono

/-- The `ψ₂` scale is absolutely homogeneous. -/
lemma orliczPsi2Norm_const_mul {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : ℝ) (X : Ω → ℝ) :
    orliczPsi2Norm (fun ω => c * X ω) μ = |c| * orliczPsi2Norm X μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using orliczPsi2Norm_const (μ := μ) (0 : ℝ)
  have habs : (0 : ℝ) < |c| := abs_pos.mpr hc
  have hpt : ∀ (K : ℝ) (ω : Ω), K ≠ 0 →
      (c * X ω) ^ 2 / K ^ 2 = X ω ^ 2 / (|c|⁻¹ * K) ^ 2 := by
    intro K ω hK
    rw [mul_pow, mul_pow, ← sq_abs c]
    field_simp
  have hset : {K : ℝ | HasOrliczPsi2Bound (fun ω => c * X ω) μ K}
      = |c| • {K : ℝ | HasOrliczPsi2Bound X μ K} := by
    ext K
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt habs)]
    simp only [Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro ⟨hK, h⟩
      refine ⟨by positivity, le_trans (le_of_eq (lintegral_congr fun ω => ?_)) h⟩
      rw [hpt K ω (ne_of_gt hK)]
    · rintro ⟨hK, h⟩
      have hKpos : 0 < K := by
        have hmul := mul_pos habs hK
        rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt habs), one_mul] at hmul
      refine ⟨hKpos, le_trans (le_of_eq (lintegral_congr fun ω => ?_)) h⟩
      rw [← hpt K ω (ne_of_gt hKpos)]
  rw [orliczPsi2Norm, orliczPsi2Norm, hset, Real.sInf_smul_of_nonneg habs.le,
    smul_eq_mul]

/-- Two-point convexity of `t ↦ exp (t ^ 2)`. -/
private lemma exp_sq_convex_comb {u v lam : ℝ} (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) :
    exp ((lam * u + (1 - lam) * v) ^ 2)
      ≤ lam * exp (u ^ 2) + (1 - lam) * exp (v ^ 2) := by
  have hsq : (lam * u + (1 - lam) * v) ^ 2 ≤ lam * u ^ 2 + (1 - lam) * v ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hlam (sub_nonneg.mpr hlam')) (sq_nonneg (u - v))]
  calc
    exp ((lam * u + (1 - lam) * v) ^ 2) ≤ exp (lam * u ^ 2 + (1 - lam) * v ^ 2) :=
      exp_le_exp.mpr hsq
    _ ≤ lam * exp (u ^ 2) + (1 - lam) * exp (v ^ 2) := by
      simpa using convexOn_exp.2 (Set.mem_univ (u ^ 2)) (Set.mem_univ (v ^ 2))
        hlam (by linarith) (by ring)

/-- Admissible sub-Gaussian scales add: this is the Luxemburg subadditivity for
the Young function `t ↦ exp (t ^ 2)`. -/
lemma HasOrliczPsi2Bound.add {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} {a b : ℝ} (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (ha : HasOrliczPsi2Bound X μ a) (hb : HasOrliczPsi2Bound Y μ b) :
    HasOrliczPsi2Bound (fun ω => X ω + Y ω) μ (a + b) := by
  have hap := ha.pos
  have hbp := hb.pos
  have hab : 0 < a + b := by linarith
  refine ⟨hab, ?_⟩
  set lam : ℝ := a / (a + b) with hlam_def
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam ≤ 1 := by rw [hlam_def, div_le_one hab]; linarith
  have hlam' : 1 - lam = b / (a + b) := by rw [hlam_def]; field_simp; ring
  have hpt : ∀ ω, exp ((X ω + Y ω) ^ 2 / (a + b) ^ 2)
      ≤ lam * exp (X ω ^ 2 / a ^ 2) + (1 - lam) * exp (Y ω ^ 2 / b ^ 2) := by
    intro ω
    have key := exp_sq_convex_comb (u := |X ω| / a) (v := |Y ω| / b) hlam0 hlam1
    have harg : lam * (|X ω| / a) + (1 - lam) * (|Y ω| / b)
        = (|X ω| + |Y ω|) / (a + b) := by
      rw [hlam_def, hlam']
      field_simp
    have hsqX : (|X ω| / a) ^ 2 = X ω ^ 2 / a ^ 2 := by rw [div_pow, sq_abs]
    have hsqY : (|Y ω| / b) ^ 2 = Y ω ^ 2 / b ^ 2 := by rw [div_pow, sq_abs]
    rw [harg, hsqX, hsqY] at key
    refine le_trans (exp_le_exp.mpr ?_) key
    rw [div_pow]
    have hab2 : (0 : ℝ) < (a + b) ^ 2 := pow_pos hab 2
    have hnum : (X ω + Y ω) ^ 2 ≤ (|X ω| + |Y ω|) ^ 2 := by
      rw [← sq_abs (X ω + Y ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 2
    gcongr
  have hmX : AEMeasurable (fun ω => ENNReal.ofReal (exp (X ω ^ 2 / a ^ 2))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hXm.pow_const 2).div_const (a ^ 2)).exp)
  have hmY : AEMeasurable (fun ω => ENNReal.ofReal (exp (Y ω ^ 2 / b ^ 2))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hYm.pow_const 2).div_const (b ^ 2)).exp)
  calc
    ∫⁻ ω, ENNReal.ofReal (exp ((X ω + Y ω) ^ 2 / (a + b) ^ 2)) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal lam * ENNReal.ofReal (exp (X ω ^ 2 / a ^ 2))
            + ENNReal.ofReal (1 - lam) *
              ENNReal.ofReal (exp (Y ω ^ 2 / b ^ 2))) ∂μ := by
      refine lintegral_mono fun ω => ?_
      rw [← ENNReal.ofReal_mul hlam0, ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 1 - lam),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal lam * ∫⁻ ω, ENNReal.ofReal (exp (X ω ^ 2 / a ^ 2)) ∂μ
        + ENNReal.ofReal (1 - lam) *
          ∫⁻ ω, ENNReal.ofReal (exp (Y ω ^ 2 / b ^ 2)) ∂μ := by
      rw [lintegral_add_left' (hmX.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal lam * 2 + ENNReal.ofReal (1 - lam) * 2 := by
      gcongr
      · exact ha.2
      · exact hb.2
    _ = 2 := by
      rw [← add_mul, ← ENNReal.ofReal_add hlam0 (by linarith : (0:ℝ) ≤ 1 - lam)]
      norm_num

/-- The `ψ₂` scale is subadditive. -/
lemma orliczPsi2Norm_add_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hXfin : HasFiniteOrliczPsi2Norm X μ) (hYfin : HasFiniteOrliczPsi2Norm Y μ) :
    orliczPsi2Norm (fun ω => X ω + Y ω) μ
      ≤ orliczPsi2Norm X μ + orliczPsi2Norm Y μ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, halt⟩ := Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi2Bound X μ K})
    hXfin (half_pos hε)
  obtain ⟨b, hb, hblt⟩ := Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi2Bound Y μ K})
    hYfin (half_pos hε)
  have hsum := orliczPsi2Norm_le (HasOrliczPsi2Bound.add hXm hYm ha hb)
  have haX : a < orliczPsi2Norm X μ + ε / 2 := halt
  have hbY : b < orliczPsi2Norm Y μ + ε / 2 := hblt
  linarith

/-- The infimum defining the `ψ₂` norm is attained. -/
lemma hasOrliczPsi2Bound_orliczPsi2Norm {μ : Measure Ω} {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hfin : HasFiniteOrliczPsi2Norm X μ)
    (hpos : 0 < orliczPsi2Norm X μ) :
    HasOrliczPsi2Bound X μ (orliczPsi2Norm X μ) := by
  set L := orliczPsi2Norm X μ with hLdef
  refine ⟨hpos, ?_⟩
  set Kn : ℕ → ℝ := fun n => L + 1 / (n + 1) with hKn
  have hKadm : ∀ n, HasOrliczPsi2Bound X μ (Kn n) := by
    intro n
    obtain ⟨a, ha, halt⟩ :=
      Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi2Bound X μ K}) hfin
        (show (0 : ℝ) < 1 / (n + 1) by positivity)
    exact ha.mono (le_of_lt halt)
  set f : ℕ → Ω → ℝ≥0∞ :=
    fun n ω => ENNReal.ofReal (exp (X ω ^ 2 / Kn n ^ 2)) with hf
  have hfmeas : ∀ n, AEMeasurable (f n) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((hXm.pow_const 2).div_const (Kn n ^ 2)).exp)
  have hKt : Filter.Tendsto Kn Filter.atTop (nhds L) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Filter.Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L) := tendsto_const_nhds
    simpa [hKn] using hc.add h0
  have hlim : ∀ ω, Filter.liminf (fun n => f n ω) Filter.atTop
      = ENNReal.ofReal (exp (X ω ^ 2 / L ^ 2)) := by
    intro ω
    have hdiv : Filter.Tendsto (fun n => X ω ^ 2 / Kn n ^ 2) Filter.atTop
        (nhds (X ω ^ 2 / L ^ 2)) :=
      tendsto_const_nhds.div (hKt.pow 2) (pow_ne_zero 2 (ne_of_gt hpos))
    exact Filter.Tendsto.liminf_eq
      (ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp hdiv))
  calc
    ∫⁻ ω, ENNReal.ofReal (exp (X ω ^ 2 / L ^ 2)) ∂μ
        = ∫⁻ ω, Filter.liminf (fun n => f n ω) Filter.atTop ∂μ := by
      simp_rw [hlim]
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, f n ω ∂μ) Filter.atTop :=
      lintegral_liminf_le' hfmeas
    _ ≤ 2 :=
      Filter.liminf_le_of_frequently_le'
        (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => (hKadm n).2))

/-! ## The `ψ₁` norm -/

/-- `K` is an admissible sub-exponential scale for `X`: `E[exp (|X| / K)] ≤ 2`. -/
def HasOrliczPsi1Bound (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : Prop :=
  0 < K ∧ ∫⁻ ω, ENNReal.ofReal (exp (|X ω| / K)) ∂μ ≤ 2

/-- The sub-exponential norm `‖X‖_{ψ₁}`, the infimum of the admissible scales. -/
def orliczPsi1Norm (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | HasOrliczPsi1Bound X μ K}

/-- `X` is sub-exponential: some sub-exponential scale is admissible. -/
def HasFiniteOrliczPsi1Norm (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ K : ℝ, HasOrliczPsi1Bound X μ K

lemma HasOrliczPsi1Bound.pos {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (h : HasOrliczPsi1Bound X μ K) : 0 < K := h.1

/-- The set of admissible sub-exponential scales is bounded below by `0`. -/
lemma bddBelow_orliczPsi1Bound (X : Ω → ℝ) (μ : Measure Ω) :
    BddBelow {K : ℝ | HasOrliczPsi1Bound X μ K} :=
  ⟨0, fun _ hK => hK.pos.le⟩

/-- The admissible sub-exponential scales are upward closed. -/
lemma HasOrliczPsi1Bound.mono {X : Ω → ℝ} {μ : Measure Ω} {K K' : ℝ}
    (h : HasOrliczPsi1Bound X μ K) (hKK' : K ≤ K') :
    HasOrliczPsi1Bound X μ K' := by
  refine ⟨h.pos.trans_le hKK', le_trans (lintegral_mono fun ω => ?_) h.2⟩
  exact ENNReal.ofReal_le_ofReal (exp_le_exp.mpr
    (div_le_div_of_nonneg_left (abs_nonneg _) h.pos hKK'))

/-- An admissible sub-exponential scale bounds the `ψ₁` norm. -/
lemma orliczPsi1Norm_le {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ}
    (h : HasOrliczPsi1Bound X μ K) : orliczPsi1Norm X μ ≤ K :=
  csInf_le (bddBelow_orliczPsi1Bound X μ) h

lemma orliczPsi1Norm_nonneg {X : Ω → ℝ} {μ : Measure Ω}
    (hfin : HasFiniteOrliczPsi1Norm X μ) : 0 ≤ orliczPsi1Norm X μ :=
  le_csInf hfin fun _ hK => hK.pos.le

/-- Monotonicity of the `ψ₁` norm in the size of the variable. -/
lemma orliczPsi1Norm_mono {X Y : Ω → ℝ} {μ : Measure Ω}
    (hfin : HasFiniteOrliczPsi1Norm Y μ)
    (hXY : ∀ᵐ ω ∂μ, |X ω| ≤ |Y ω|) :
    orliczPsi1Norm X μ ≤ orliczPsi1Norm Y μ := by
  refine csInf_le_csInf (bddBelow_orliczPsi1Bound X μ) hfin fun K hK => ?_
  refine ⟨hK.pos, le_trans (lintegral_mono_ae ?_) hK.2⟩
  have hKpos : (0 : ℝ) < K := hK.pos
  filter_upwards [hXY] with ω hω
  exact ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (by gcongr))

/-- A scale is admissible for a constant exactly when it dominates `|c| / log 2`. -/
lemma hasOrliczPsi1Bound_const_iff {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : ℝ) {K : ℝ} (hK : 0 < K) :
    HasOrliczPsi1Bound (fun _ : Ω => c) μ K ↔ |c| / Real.log 2 ≤ K := by
  have hlog := log_two_pos
  have hint : ∫⁻ _ : Ω, ENNReal.ofReal (exp (|c| / K)) ∂μ
      = ENNReal.ofReal (exp (|c| / K)) := by simp
  have hstep : ENNReal.ofReal (exp (|c| / K)) ≤ 2 ↔ |c| / K ≤ Real.log 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2),
      Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
  have hstep2 : |c| / K ≤ Real.log 2 ↔ |c| / Real.log 2 ≤ K := by
    rw [div_le_iff₀ hK, div_le_iff₀ hlog]
    constructor <;> intro h <;> nlinarith
  constructor
  · rintro ⟨-, hle⟩
    rw [hint] at hle
    exact hstep2.mp (hstep.mp hle)
  · intro hle
    exact ⟨hK, by rw [hint]; exact hstep.mpr (hstep2.mpr hle)⟩

/-- The `ψ₁` norm of an almost surely constant variable. -/
lemma orliczPsi1Norm_const {μ : Measure Ω} [IsProbabilityMeasure μ] (c : ℝ) :
    orliczPsi1Norm (fun _ : Ω => c) μ = |c| / Real.log 2 := by
  have ha : (0 : ℝ) ≤ |c| / Real.log 2 := by
    exact div_nonneg (abs_nonneg c) log_two_pos.le
  have hset : {K : ℝ | HasOrliczPsi1Bound (fun _ : Ω => c) μ K}
      = {K : ℝ | 0 < K ∧ |c| / Real.log 2 ≤ K} := by
    ext K
    exact ⟨fun hK => ⟨hK.pos, (hasOrliczPsi1Bound_const_iff c hK.pos).mp hK⟩,
      fun hK => (hasOrliczPsi1Bound_const_iff c hK.1).mpr hK.2⟩
  have hbdd : BddBelow {K : ℝ | 0 < K ∧ |c| / Real.log 2 ≤ K} :=
    ⟨0, fun _ hK => hK.1.le⟩
  rw [orliczPsi1Norm, hset]
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_csInf ⟨|c| / Real.log 2 + 1, by constructor <;> linarith⟩ fun _ hK => hK.2)
  exact csInf_le hbdd ⟨by linarith, by linarith⟩

/-- An almost surely bounded variable is sub-exponential. -/
lemma orliczPsi1Norm_le_of_abs_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b : ℝ} (hb : 0 ≤ b) (hX : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    orliczPsi1Norm X μ ≤ b / Real.log 2 := by
  have hfin : HasFiniteOrliczPsi1Norm (fun _ : Ω => b) μ :=
    ⟨b / Real.log 2 + 1, (hasOrliczPsi1Bound_const_iff b
      (by positivity)).mpr (by rw [abs_of_nonneg hb]; linarith)⟩
  have hmono : orliczPsi1Norm X μ ≤ orliczPsi1Norm (fun _ : Ω => b) μ := by
    refine orliczPsi1Norm_mono hfin ?_
    filter_upwards [hX] with ω hω
    rwa [abs_of_nonneg hb]
  rwa [orliczPsi1Norm_const b, abs_of_nonneg hb] at hmono

/-- The `ψ₁` scale is absolutely homogeneous. -/
lemma orliczPsi1Norm_const_mul {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : ℝ) (X : Ω → ℝ) :
    orliczPsi1Norm (fun ω => c * X ω) μ = |c| * orliczPsi1Norm X μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using orliczPsi1Norm_const (μ := μ) (0 : ℝ)
  have habs : (0 : ℝ) < |c| := abs_pos.mpr hc
  have hpt : ∀ (K : ℝ) (ω : Ω), K ≠ 0 → |c * X ω| / K = |X ω| / (|c|⁻¹ * K) := by
    intro K ω hK
    rw [abs_mul]
    field_simp
  have hset : {K : ℝ | HasOrliczPsi1Bound (fun ω => c * X ω) μ K}
      = |c| • {K : ℝ | HasOrliczPsi1Bound X μ K} := by
    ext K
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt habs)]
    simp only [Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro ⟨hK, h⟩
      refine ⟨by positivity, le_trans (le_of_eq (lintegral_congr fun ω => ?_)) h⟩
      rw [hpt K ω (ne_of_gt hK)]
    · rintro ⟨hK, h⟩
      have hKpos : 0 < K := by
        have hmul := mul_pos habs hK
        rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt habs), one_mul] at hmul
      refine ⟨hKpos, le_trans (le_of_eq (lintegral_congr fun ω => ?_)) h⟩
      rw [← hpt K ω (ne_of_gt hKpos)]
  rw [orliczPsi1Norm, orliczPsi1Norm, hset, Real.sInf_smul_of_nonneg habs.le,
    smul_eq_mul]

/-- Admissible sub-exponential scales add. -/
lemma HasOrliczPsi1Bound.add {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} {a b : ℝ} (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (ha : HasOrliczPsi1Bound X μ a) (hb : HasOrliczPsi1Bound Y μ b) :
    HasOrliczPsi1Bound (fun ω => X ω + Y ω) μ (a + b) := by
  have hap := ha.pos
  have hbp := hb.pos
  have hab : 0 < a + b := by linarith
  refine ⟨hab, ?_⟩
  set lam : ℝ := a / (a + b) with hlam_def
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam ≤ 1 := by rw [hlam_def, div_le_one hab]; linarith
  have hlam' : 1 - lam = b / (a + b) := by rw [hlam_def]; field_simp; ring
  have hpt : ∀ ω, exp (|X ω + Y ω| / (a + b))
      ≤ lam * exp (|X ω| / a) + (1 - lam) * exp (|Y ω| / b) := by
    intro ω
    have key : exp (lam * (|X ω| / a) + (1 - lam) * (|Y ω| / b))
        ≤ lam * exp (|X ω| / a) + (1 - lam) * exp (|Y ω| / b) := by
      simpa using convexOn_exp.2 (Set.mem_univ (|X ω| / a)) (Set.mem_univ (|Y ω| / b))
        hlam0 (by linarith) (by ring)
    have harg : lam * (|X ω| / a) + (1 - lam) * (|Y ω| / b)
        = (|X ω| + |Y ω|) / (a + b) := by
      rw [hlam_def, hlam']
      field_simp
    rw [harg] at key
    refine le_trans (exp_le_exp.mpr ?_) key
    gcongr
    exact abs_add_le _ _
  have habsX : AEMeasurable (fun ω => |X ω|) μ :=
    continuous_abs.measurable.comp_aemeasurable hXm
  have habsY : AEMeasurable (fun ω => |Y ω|) μ :=
    continuous_abs.measurable.comp_aemeasurable hYm
  have hmX : AEMeasurable (fun ω => ENNReal.ofReal (exp (|X ω| / a))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((habsX.div_const a).exp)
  have hmY : AEMeasurable (fun ω => ENNReal.ofReal (exp (|Y ω| / b))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((habsY.div_const b).exp)
  calc
    ∫⁻ ω, ENNReal.ofReal (exp (|X ω + Y ω| / (a + b))) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal lam * ENNReal.ofReal (exp (|X ω| / a))
            + ENNReal.ofReal (1 - lam) * ENNReal.ofReal (exp (|Y ω| / b))) ∂μ := by
      refine lintegral_mono fun ω => ?_
      rw [← ENNReal.ofReal_mul hlam0,
        ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - lam),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal lam * ∫⁻ ω, ENNReal.ofReal (exp (|X ω| / a)) ∂μ
        + ENNReal.ofReal (1 - lam) * ∫⁻ ω, ENNReal.ofReal (exp (|Y ω| / b)) ∂μ := by
      rw [lintegral_add_left' (hmX.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal lam * 2 + ENNReal.ofReal (1 - lam) * 2 := by
      gcongr
      · exact ha.2
      · exact hb.2
    _ = 2 := by
      rw [← add_mul, ← ENNReal.ofReal_add hlam0 (by linarith : (0 : ℝ) ≤ 1 - lam)]
      norm_num

/-- The `ψ₁` scale is subadditive. -/
lemma orliczPsi1Norm_add_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hXfin : HasFiniteOrliczPsi1Norm X μ) (hYfin : HasFiniteOrliczPsi1Norm Y μ) :
    orliczPsi1Norm (fun ω => X ω + Y ω) μ
      ≤ orliczPsi1Norm X μ + orliczPsi1Norm Y μ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, halt⟩ := Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi1Bound X μ K})
    hXfin (half_pos hε)
  obtain ⟨b, hb, hblt⟩ := Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi1Bound Y μ K})
    hYfin (half_pos hε)
  have hsum := orliczPsi1Norm_le (HasOrliczPsi1Bound.add hXm hYm ha hb)
  have haX : a < orliczPsi1Norm X μ + ε / 2 := halt
  have hbY : b < orliczPsi1Norm Y μ + ε / 2 := hblt
  linarith

/-- The infimum defining the `ψ₁` norm is attained. -/
lemma hasOrliczPsi1Bound_orliczPsi1Norm {μ : Measure Ω} {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hfin : HasFiniteOrliczPsi1Norm X μ)
    (hpos : 0 < orliczPsi1Norm X μ) :
    HasOrliczPsi1Bound X μ (orliczPsi1Norm X μ) := by
  set L := orliczPsi1Norm X μ with hLdef
  refine ⟨hpos, ?_⟩
  set Kn : ℕ → ℝ := fun n => L + 1 / (n + 1) with hKn
  have hKadm : ∀ n, HasOrliczPsi1Bound X μ (Kn n) := by
    intro n
    obtain ⟨a, ha, halt⟩ :=
      Real.lt_sInf_add_pos (s := {K : ℝ | HasOrliczPsi1Bound X μ K}) hfin
        (show (0 : ℝ) < 1 / (n + 1) by positivity)
    exact ha.mono (le_of_lt halt)
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (exp (|X ω| / Kn n)) with hf
  have habsX : AEMeasurable (fun ω => |X ω|) μ :=
    continuous_abs.measurable.comp_aemeasurable hXm
  have hfmeas : ∀ n, AEMeasurable (f n) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((habsX.div_const (Kn n)).exp)
  have hKt : Filter.Tendsto Kn Filter.atTop (nhds L) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Filter.Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L) := tendsto_const_nhds
    simpa [hKn] using hc.add h0
  have hlim : ∀ ω, Filter.liminf (fun n => f n ω) Filter.atTop
      = ENNReal.ofReal (exp (|X ω| / L)) := by
    intro ω
    have hdiv : Filter.Tendsto (fun n => |X ω| / Kn n) Filter.atTop
        (nhds (|X ω| / L)) :=
      tendsto_const_nhds.div hKt (ne_of_gt hpos)
    exact Filter.Tendsto.liminf_eq
      (ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp hdiv))
  calc
    ∫⁻ ω, ENNReal.ofReal (exp (|X ω| / L)) ∂μ
        = ∫⁻ ω, Filter.liminf (fun n => f n ω) Filter.atTop ∂μ := by simp_rw [hlim]
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, f n ω ∂μ) Filter.atTop :=
      lintegral_liminf_le' hfmeas
    _ ≤ 2 :=
      Filter.liminf_le_of_frequently_le'
        (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => (hKadm n).2))

end
