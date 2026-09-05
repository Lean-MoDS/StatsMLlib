/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Concentration.SubExponential

/-!
# Concentration of the Euclidean norm

HDP Theorem 3.1.1: for a random vector with independent sub-Gaussian
coordinates of unit second moment, `‖X‖₂` concentrates around `√n` at the
sub-Gaussian scale `K ^ 2`.

## Main definitions

* `centredSqScale`: the `ψ₁` scale carried by the centred squares `Xᵢ² - 1`.

## Main results

* `hasOrliczPsi1Bound_sq_sub_one`: Step 1 of the textbook proof, that the
  centred squares are sub-exponential.
* `sq_norm_concentration`: Step 2, concentration of `n⁻¹ ‖X‖₂²` around `1`.
* `norm_concentration_tail`: the tail form,
  `P{|‖X‖₂ - √n| ≥ t} ≤ 2 exp (-c t² / K⁴)`.
* `norm_concentration_hdp`: the `ψ₂`-norm form of HDP Theorem 3.1.1.

The textbook proof calls the tail form "equivalent" to the norm form.  Only one
direction of that equivalence is proved in the text; the other is
`orliczPsi2Norm_le_of_measure_abs_ge_le` in
`StatsMLlib.Probability.Moments.SubGaussianOrlicz`, and it is what turns
`norm_concentration_tail` into `norm_concentration_hdp`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Step 3 of the textbook proof: for `z, δ ≥ 0`, a deviation of `z` from `1`
forces a deviation of `z ^ 2` from `1`. -/
private lemma max_le_abs_sq_sub_one {z δ : ℝ} (hz : 0 ≤ z) (hδ : 0 ≤ δ)
    (h : δ ≤ |z - 1|) : max δ (δ ^ 2) ≤ |z ^ 2 - 1| := by
  have hfac : |z ^ 2 - 1| = |z - 1| * (z + 1) := by
    rw [show z ^ 2 - 1 = (z - 1) * (z + 1) by ring, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ z + 1)]
  rcases le_or_gt 1 z with hz1 | hz1
  · have habs : |z - 1| = z - 1 := abs_of_nonneg (by linarith)
    rw [habs] at h
    rw [hfac, habs]
    refine max_le ?_ ?_ <;> nlinarith
  · have habs : |z - 1| = 1 - z := by
      rw [abs_of_nonpos (by linarith : z - 1 ≤ 0)]
      ring
    rw [habs] at h
    have hδ1 : δ ≤ 1 := by linarith
    rw [hfac, habs]
    refine max_le ?_ ?_ <;> nlinarith


/-- The `ψ₁` scale carried by the centred squares `Xᵢ² - 1` of a family of
sub-Gaussian variables of scale `K` and unit second moment. -/
def centredSqScale (K : ℝ) : ℝ := (1 + 4 / Real.log 2) * K ^ 2

lemma centredSqScale_pos {K : ℝ} (hK : 0 < K) : 0 < centredSqScale K := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [centredSqScale]
  positivity

lemma one_le_centredSqScale {K : ℝ} (hK : 1 ≤ 2 * K ^ 2) :
    1 ≤ centredSqScale K := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  rw [centredSqScale]
  have h4 : (4 : ℝ) ≤ 4 / Real.log 2 := by
    rw [le_div_iff₀ hlog]
    nlinarith
  nlinarith

/-- Step 1 of the textbook proof: the centred squares of a sub-Gaussian family
are sub-exponential at scale `centredSqScale K`. -/
lemma hasOrliczPsi1Bound_sq_sub_one {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ} (hXm : AEMeasurable X μ)
    (hK : HasOrliczPsi2Bound X μ K) (hK2 : 1 ≤ 2 * K ^ 2) :
    HasOrliczPsi1Bound (fun ω => X ω ^ 2 - 1) μ (centredSqScale K) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos := hK.pos
  have hsq : HasOrliczPsi1Bound (fun ω => X ω * X ω) μ (K * K) :=
    HasOrliczPsi2Bound.mul hXm hXm hK hK
  have hsq' : HasOrliczPsi1Bound (fun ω => X ω ^ 2) μ (K ^ 2) := by
    have hfun : (fun ω => X ω * X ω) = fun ω => X ω ^ 2 := by
      funext ω; ring
    rw [hfun] at hsq
    simpa [pow_two] using hsq
  have hconst : HasOrliczPsi1Bound (fun _ : Ω => (-1 : ℝ)) μ (2 / Real.log 2) := by
    refine (hasOrliczPsi1Bound_const_iff (-1 : ℝ) (by positivity)).mpr ?_
    rw [abs_neg, abs_one]
    rw [div_le_div_iff₀ hlog hlog]
    nlinarith
  have hadd := HasOrliczPsi1Bound.add (μ := μ) ((hXm.pow_const 2)) aemeasurable_const
    hsq' hconst
  have hfun : (fun ω => X ω ^ 2 + -1) = fun ω => X ω ^ 2 - 1 := by
    funext ω; ring
  rw [hfun] at hadd
  refine hadd.mono ?_
  rw [centredSqScale]
  have h4 : 2 / Real.log 2 ≤ 4 / Real.log 2 * K ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hlog hlog]
    nlinarith
  nlinarith


/-- Step 2 of the textbook proof: concentration of `n⁻¹ ‖X‖₂²` around `1`. -/
theorem sq_norm_concentration {n : ℕ} (hn : 0 < n) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) μ) (h_indep : iIndepFun X μ)
    {K : ℝ} (hK : ∀ i, HasOrliczPsi2Bound (X i) μ K)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) {u : ℝ} (hu : 0 ≤ u) :
    (μ {ω | u ≤ |(n : ℝ)⁻¹ * (∑ i, X i ω ^ 2) - 1|}).toReal
      ≤ 2 * exp (-(1 / 64) *
          min (u ^ 2 * n / centredSqScale K ^ 2)
            (u * n / centredSqScale K)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hi0 : Fin n := ⟨0, hn⟩
  have hKpos := (hK hi0).pos
  have hK2 : 1 ≤ 2 * K ^ 2 := by
    have h := integral_sq_le_of_hasOrliczPsi2Bound (hXm hi0) (hK hi0)
    rw [hsecond hi0] at h
    exact h
  set K' : ℝ := centredSqScale K with hK'def
  have hK'pos : 0 < K' := centredSqScale_pos hKpos
  set Y : Fin n → Ω → ℝ := fun i ω => X i ω ^ 2 - 1 with hYdef
  have hYm : ∀ i, AEMeasurable (Y i) μ := fun i => (hXm i).pow_const 2 |>.sub_const 1
  have hY1 : ∀ i, HasOrliczPsi1Bound (Y i) μ K' := fun i =>
    hasOrliczPsi1Bound_sq_sub_one (hXm i) (hK i) hK2
  have hYindep : iIndepFun Y μ := by
    simpa [hYdef, Function.comp_def] using
      h_indep.comp (fun _ x => x ^ 2 - 1) (fun _ => by fun_prop)
  have hYint : ∀ i, Integrable (Y i) μ := fun i =>
    integrable_of_hasOrliczPsi1Bound (hYm i) (hY1 i)
  have hXsqint : ∀ i, Integrable (fun ω => X i ω ^ 2) μ := by
    intro i
    have hadd : Integrable (fun ω => Y i ω + 1) μ :=
      (hYint i).add (integrable_const 1)
    have hfun : (fun ω => Y i ω + 1) = fun ω => X i ω ^ 2 := by
      funext ω
      show X i ω ^ 2 - 1 + 1 = X i ω ^ 2
      ring
    rwa [hfun] at hadd
  have hYcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    rw [hYdef]
    simp only
    rw [integral_sub (hXsqint i) (integrable_const 1), hsecond i, integral_const]
    simp
  have ha : ∀ _i : Fin n, ((n : ℝ)⁻¹ : ℝ) ≠ 0 := fun _ => by positivity
  have habs : |((n : ℝ)⁻¹ : ℝ)| = (n : ℝ)⁻¹ := abs_of_pos (by positivity)
  have hb : ∀ _i : Fin n, |((n : ℝ)⁻¹ : ℝ)| * K' ≤ K' / n := fun _ =>
    le_of_eq (by rw [habs, div_eq_inv_mul])
  have hv : ∑ _i : Fin n, (|((n : ℝ)⁻¹ : ℝ)| * K') ^ 2 ≤ K' ^ 2 / n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, habs]
    refine le_of_eq ?_
    field_simp
  have hmain := bernstein_subExponential_smul (μ := μ) (X := Y)
    (a := fun _ => ((n : ℝ)⁻¹ : ℝ)) (K := K') (b := K' / n) (v := K' ^ 2 / n)
    (t := u) hYm hYindep hYcenter hY1 ha (by positivity) hb (by positivity) hv hu
  have hset : ∀ ω, (∑ i, fun ω => ((n : ℝ)⁻¹ : ℝ) * Y i ω) ω
      = (n : ℝ)⁻¹ * (∑ i, X i ω ^ 2) - 1 := by
    intro ω
    rw [Finset.sum_apply]
    simp only [hYdef]
    have hdist : ∀ x : Fin n, ((n : ℝ)⁻¹ : ℝ) * (X x ω ^ 2 - 1)
        = (n : ℝ)⁻¹ * X x ω ^ 2 - (n : ℝ)⁻¹ := by
      intro x; ring
    simp_rw [hdist]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp only [hset] at hmain
  refine hmain.trans (le_of_eq ?_)
  congr 2
  rw [div_div_eq_mul_div, div_div_eq_mul_div]


/-- Steps 3 of the textbook proof: the tail form of HDP Theorem 3.1.1. -/
theorem norm_concentration_tail {n : ℕ} (hn : 0 < n) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) μ) (h_indep : iIndepFun X μ)
    {K : ℝ} (hK : ∀ i, HasOrliczPsi2Bound (X i) μ K)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) {t : ℝ} (ht : 0 ≤ t) :
    (μ {ω | t ≤ |√(∑ i, X i ω ^ 2) - √(n : ℝ)|}).toReal
      ≤ 2 * exp (-(1 / 64) * t ^ 2 / centredSqScale K ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  have hsqn2 : (√(n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hi0 : Fin n := ⟨0, hn⟩
  have hKpos := (hK hi0).pos
  have hK2 : 1 ≤ 2 * K ^ 2 := by
    have h := integral_sq_le_of_hasOrliczPsi2Bound (hXm hi0) (hK hi0)
    rw [hsecond hi0] at h
    exact h
  set K' : ℝ := centredSqScale K with hK'def
  have hK'pos : 0 < K' := centredSqScale_pos hKpos
  have hK'one : 1 ≤ K' := one_le_centredSqScale hK2
  set δ : ℝ := t / √(n : ℝ) with hδdef
  have hδ : 0 ≤ δ := by positivity
  have hsub : {ω | t ≤ |√(∑ i, X i ω ^ 2) - √(n : ℝ)|}
      ⊆ {ω | max δ (δ ^ 2) ≤ |(n : ℝ)⁻¹ * (∑ i, X i ω ^ 2) - 1|} := by
    intro ω hω
    have hSnn : (0 : ℝ) ≤ ∑ i, X i ω ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hznn : (0 : ℝ) ≤ √(∑ i, X i ω ^ 2) / √(n : ℝ) := by positivity
    have hzsq : (√(∑ i, X i ω ^ 2) / √(n : ℝ)) ^ 2
        = (n : ℝ)⁻¹ * (∑ i, X i ω ^ 2) := by
      rw [div_pow, Real.sq_sqrt hSnn, hsqn2]
      field_simp
    have hω' : t ≤ |√(∑ i, X i ω ^ 2) - √(n : ℝ)| := hω
    have hfac : √(∑ i, X i ω ^ 2) - √(n : ℝ)
        = √(n : ℝ) * (√(∑ i, X i ω ^ 2) / √(n : ℝ) - 1) := by
      field_simp
    rw [hfac, abs_mul, abs_of_pos hsqn] at hω'
    have hdev : δ ≤ |√(∑ i, X i ω ^ 2) / √(n : ℝ) - 1| := by
      rw [hδdef, div_le_iff₀ hsqn]
      linarith [hω']
    have hkey := max_le_abs_sq_sub_one hznn hδ hdev
    rwa [hzsq] at hkey
  have hstep2 := sq_norm_concentration hn X hXm h_indep hK hsecond
    (u := max δ (δ ^ 2)) (le_max_of_le_left hδ)
  have hmeas : (μ {ω | t ≤ |√(∑ i, X i ω ^ 2) - √(n : ℝ)|}).toReal
      ≤ (μ {ω | max δ (δ ^ 2) ≤ |(n : ℝ)⁻¹ * (∑ i, X i ω ^ 2) - 1|}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  refine (hmeas.trans hstep2).trans ?_
  have hmin : δ ^ 2 * n / K' ^ 2
      ≤ min (max δ (δ ^ 2) ^ 2 * n / K' ^ 2) (max δ (δ ^ 2) * n / K') := by
    refine le_min ?_ ?_
    · gcongr
      exact le_max_left _ _
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rcases le_or_gt δ 1 with hδ1 | hδ1
      · have hmax : max δ (δ ^ 2) = δ := max_eq_left (by nlinarith)
        rw [hmax]
        have hle : δ ≤ K' := by linarith
        calc δ ^ 2 * (n : ℝ) * K' = δ * (n : ℝ) * K' * δ := by ring
          _ ≤ δ * (n : ℝ) * K' * K' :=
            mul_le_mul_of_nonneg_left hle (by positivity)
          _ = δ * (n : ℝ) * K' ^ 2 := by ring
      · have hmax : max δ (δ ^ 2) = δ ^ 2 := max_eq_right (by nlinarith)
        rw [hmax]
        have hle : K' ≤ K' ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hδn : δ ^ 2 * n = t ^ 2 := by
    rw [hδdef, div_pow, hsqn2]
    field_simp
  have hfinal : -(1 / 64) *
        min (max δ (δ ^ 2) ^ 2 * n / K' ^ 2) (max δ (δ ^ 2) * n / K')
      ≤ -(1 / 64) * t ^ 2 / K' ^ 2 := by
    have h := hmin
    rw [hδn] at h
    have heq : -(1 / 64) * t ^ 2 / K' ^ 2 = -(1 / 64) * (t ^ 2 / K' ^ 2) := by
      ring
    rw [heq]
    linarith
  gcongr


/-- HDP Theorem 3.1.1, concentration of the norm: for a random vector with
independent sub-Gaussian coordinates of unit second moment,
`‖ ‖X‖₂ - √n ‖_{ψ₂} ≤ C K ^ 2`. -/
theorem norm_concentration_hdp {n : ℕ} (hn : 0 < n) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) μ) (h_indep : iIndepFun X μ)
    {K : ℝ} (hK : ∀ i, HasOrliczPsi2Bound (X i) μ K)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) :
    ∃ C : ℝ, 0 < C ∧
      HasFiniteOrliczPsi2Norm (fun ω => √(∑ i, X i ω ^ 2) - √(n : ℝ)) μ ∧
      orliczPsi2Norm (fun ω => √(∑ i, X i ω ^ 2) - √(n : ℝ)) μ ≤ C * K ^ 2 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hi0 : Fin n := ⟨0, hn⟩
  have hKpos := (hK hi0).pos
  set K' : ℝ := centredSqScale K with hK'def
  have hK'pos : 0 < K' := centredSqScale_pos hKpos
  have hsum : AEMeasurable (fun ω => ∑ i, X i ω ^ 2) μ := by
    have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin n))
      (fun i (_ : i ∈ Finset.univ) => (hXm i).pow_const 2)
    have hfun : (∑ i : Fin n, fun ω => X i ω ^ 2) = fun ω => ∑ i, X i ω ^ 2 := by
      funext ω
      exact Finset.sum_apply ω _ _
    rwa [hfun] at h
  have hZm : AEMeasurable (fun ω => √(∑ i, X i ω ^ 2) - √(n : ℝ)) μ :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable hsum).sub_const _
  have htail : ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ |√(∑ i, X i ω ^ 2) - √(n : ℝ)|}).toReal
        ≤ 2 * exp (-t ^ 2 / (8 * K') ^ 2) := by
    intro t ht
    have hexp : -(1 / 64 : ℝ) * t ^ 2 / K' ^ 2 = -t ^ 2 / (8 * K') ^ 2 := by
      field_simp
      ring
    rw [← hexp]
    exact norm_concentration_tail hn X hXm h_indep hK hsecond ht
  obtain ⟨hfin, hle⟩ :=
    orliczPsi2Norm_le_of_measure_abs_ge_le hZm (by positivity) htail
  refine ⟨16 * (1 + 4 / Real.log 2), by positivity, hfin, ?_⟩
  refine hle.trans (le_of_eq ?_)
  rw [hK'def, centredSqScale]
  ring


/-! ## Examples

Worked uses of this module's public API.  They are elaborated with the library,
so they double as acceptance tests that these statements stay usable as written.
-/

/-- Theorem 3.1.1 in the form the textbook states it: the deviation of the norm
from `√n` is sub-Gaussian at scale `K ^ 2`. -/
example {n : ℕ} (hn : 0 < n) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, AEMeasurable (X i) μ)
    (h_indep : iIndepFun X μ) {K : ℝ}
    (hK : ∀ i, HasOrliczPsi2Bound (X i) μ K)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) :
    ∃ C : ℝ, 0 < C ∧
      orliczPsi2Norm (fun ω => √(∑ i, X i ω ^ 2) - √(n : ℝ)) μ ≤ C * K ^ 2 := by
  obtain ⟨C, hC, _, hle⟩ := norm_concentration_hdp hn X hXm h_indep hK hsecond
  exact ⟨C, hC, hle⟩

/-- The coordinates of such a vector necessarily have `2 K ^ 2 ≥ 1`; this is the
`K ≳ 1` remark used in Step 2 of the textbook proof. -/
example {n : ℕ} (hn : 0 < n) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, AEMeasurable (X i) μ) {K : ℝ}
    (hK : ∀ i, HasOrliczPsi2Bound (X i) μ K)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) :
    1 ≤ 2 * K ^ 2 := by
  have hi0 : Fin n := ⟨0, hn⟩
  have h := integral_sq_le_of_hasOrliczPsi2Bound (hXm hi0) (hK hi0)
  rwa [hsecond hi0] at h

end
