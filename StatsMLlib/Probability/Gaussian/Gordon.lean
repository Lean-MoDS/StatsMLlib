/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Analysis.SoftMinMax
import StatsMLlib.Probability.Gaussian.Kahane

/-!
# Gordon's inequality

Let `μ` and `ν` be centered Gaussian measures on `S × T → ℝ` with the same variances. Suppose the
covariances within a row are larger under `μ` and those across rows are smaller under `μ`:

* `cov_ν(x_{st}, x_{st'}) ≤ cov_μ(x_{st}, x_{st'})` for `t ≠ t'`;
* `cov_μ(x_{st}, x_{s't'}) ≤ cov_ν(x_{st}, x_{s't'})` for `s ≠ s'`.

Then `∫ min_s max_t (x + q)_{st} dμ ≤ ∫ min_s max_t (x + q)_{st} dν` for every `q`.

The proof replaces `min_s max_t` by the smooth soft-min-max `G_β`, whose mixed second partial
derivatives have the signs required by Kahane's comparison inequality, and lets `β → ∞`.

## Main results

* `GaussianMeasure.hasBoundedDerivs_softMinMax`: `G_β` satisfies the regularity hypotheses of
  Kahane's inequality.
* `GaussianMeasure.integral_minMax_le_gordon`: Gordon's inequality.
-/

open MeasureTheory ProbabilityTheory Real Finset

namespace GaussianMeasure

variable {S T : Type*} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
  [DecidableEq S] [DecidableEq T]

/-- The soft-min-max `G_β` has gradient bounded by `1` and Hessian entries bounded by `4 |β|`. -/
lemma hasBoundedDerivs_softMinMax {β : ℝ} (hβ : β ≠ 0) :
    HasBoundedDerivs (softMinMax (S := S) (T := T) β) 1 (4 * |β|) where
  differentiable := differentiable_softMinMax β
  norm_fderiv_le := norm_fderiv_softMinMax_le hβ
  contDiff_pderiv := contDiff_fderiv_softMinMax_single hβ
  norm_fderiv_pderiv_le i x := norm_fderiv_fderiv_softMinMax_single_le hβ x i

omit [Nonempty S] [Nonempty T] [DecidableEq S] [DecidableEq T] in
lemma integrable_sum_abs_add (ν : Measure (S × T → ℝ)) [IsGaussian ν] (q : S × T → ℝ) :
    Integrable (fun x : S × T → ℝ ↦ ∑ i, |x i| + ∑ i, |q i|) ν :=
  (integrable_finsetSum _ fun i _ ↦
    (IsGaussian.integrable_dual ν (ContinuousLinearMap.proj i)).abs).add (integrable_const _)

omit [Nonempty S] [Nonempty T] [DecidableEq S] [DecidableEq T] in
lemma sum_abs_add_le (x q : S × T → ℝ) : ∑ i, |(x + q) i| ≤ ∑ i, |x i| + ∑ i, |q i| := by
  rw [← sum_add_distrib]
  exact sum_le_sum fun i _ ↦ abs_add_le _ _

omit [DecidableEq S] [DecidableEq T] in
lemma continuous_minMax : Continuous (minMax (S := S) (T := T)) :=
  Continuous.finset_inf'_apply univ_nonempty fun s _ ↦
    Continuous.finset_sup'_apply univ_nonempty fun t _ ↦ continuous_apply (s, t)

omit [DecidableEq S] [DecidableEq T] in
lemma integrable_minMax_add (ν : Measure (S × T → ℝ)) [IsGaussian ν] (q : S × T → ℝ) :
    Integrable (fun x ↦ minMax (x + q)) ν :=
  (integrable_sum_abs_add ν q).mono'
    (continuous_minMax.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs]
      exact (abs_minMax_le _).trans (sum_abs_add_le x q))

omit [DecidableEq S] [DecidableEq T] in
lemma integrable_softMinMax_add (ν : Measure (S × T → ℝ)) [IsGaussian ν] {β : ℝ} (hβ : 0 < β)
    (q : S × T → ℝ) : Integrable (fun x ↦ softMinMax β (x + q)) ν :=
  ((integrable_sum_abs_add ν q).add (integrable_const
    ((log (Fintype.card S) + log (Fintype.card T)) / β))).mono'
    ((differentiable_softMinMax β).continuous.comp
      (continuous_id.add continuous_const)).aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs]
      refine (abs_softMinMax_le hβ _).trans ?_
      show _ ≤ (∑ i, |x i| + ∑ i, |q i|) + _
      linarith [sum_abs_add_le x q])

/-- **Gordon's inequality.** Let `μ` and `ν` be centered Gaussian measures on `S × T → ℝ` with
the same variances, such that covariances within a row are larger under `μ` and covariances
across rows are smaller under `μ`. Then `∫ min_s max_t (x + q) dμ ≤ ∫ min_s max_t (x + q) dν`. -/
theorem integral_minMax_le_gordon {μ ν : Measure (S × T → ℝ)} [IsGaussian μ] [IsGaussian ν]
    (hμ : ∫ x, x ∂μ = 0) (hν : ∫ x, x ∂ν = 0)
    (hvar : ∀ i, cov[fun x ↦ x i, fun x ↦ x i; μ] = cov[fun x ↦ x i, fun x ↦ x i; ν])
    (hrow : ∀ s t t', t ≠ t' →
      cov[fun x ↦ x (s, t), fun x ↦ x (s, t'); ν] ≤ cov[fun x ↦ x (s, t), fun x ↦ x (s, t'); μ])
    (hcross : ∀ s s' t t', s ≠ s' →
      cov[fun x ↦ x (s, t), fun x ↦ x (s', t'); μ] ≤
        cov[fun x ↦ x (s, t), fun x ↦ x (s', t'); ν])
    (q : S × T → ℝ) :
    ∫ x, minMax (x + q) ∂μ ≤ ∫ x, minMax (x + q) ∂ν := by
  have hlogS : 0 ≤ log (Fintype.card S) := log_natCast_nonneg _
  have hlogT : 0 ≤ log (Fintype.card T) := log_natCast_nonneg _
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set β := (log (Fintype.card S) + log (Fintype.card T) + 1) / ε with hβ_def
  have hβ : 0 < β := by positivity
  -- Kahane's inequality for `G_β(· + q)`
  have hK : ∫ x, softMinMax β (x + q) ∂μ ≤ ∫ x, softMinMax β (x + q) ∂ν := by
    refine integral_le_integral_kahane_of_fintype hμ hν
      ((hasBoundedDerivs_softMinMax hβ.ne').comp_add_right q) hvar ?_
    rintro ⟨s, t⟩ ⟨s', t'⟩ hij x
    rw [fderiv_pderiv_comp_add_right]
    by_cases hs : s = s'
    · subst hs
      have ht : t ≠ t' := fun h ↦ hij (by rw [h])
      have h1 := sub_nonneg.2 (hrow s t t' ht)
      have h2 : fderiv ℝ (pderiv (softMinMax β) (s, t)) (x + q) (Pi.single (s, t') 1) ≤ 0 :=
        fderiv_fderiv_softMinMax_single_same_row_nonpos hβ (x + q) s ht
      nlinarith [mul_nonneg h1 (neg_nonneg.2 h2)]
    · have h1 := sub_nonpos.2 (hcross s s' t t' hs)
      have h2 : 0 ≤ fderiv ℝ (pderiv (softMinMax β) (s, t)) (x + q) (Pi.single (s', t') 1) :=
        fderiv_fderiv_softMinMax_single_diff_row_nonneg hβ (x + q) hs t t'
      nlinarith [mul_nonneg (neg_nonneg.2 h1) h2]
  -- compare `G_β` with `min max` on both sides
  have hconst : ∀ (ρ : Measure (S × T → ℝ)) [IsProbabilityMeasure ρ] (g : (S × T → ℝ) → ℝ)
      (c : ℝ), Integrable g ρ → ∫ x, (g x + c) ∂ρ = ∫ x, g x ∂ρ + c := by
    intro ρ _ g c hg
    rw [integral_add hg (integrable_const c), integral_const]
    simp
  have h1 : ∫ x, minMax (x + q) ∂μ ≤
      ∫ x, softMinMax β (x + q) ∂μ + log (Fintype.card S) / β := by
    rw [← hconst μ _ _ (integrable_softMinMax_add μ hβ q)]
    refine integral_mono (integrable_minMax_add μ q)
      ((integrable_softMinMax_add μ hβ q).add (integrable_const _)) fun x ↦ ?_
    linarith [minMax_sub_le_softMinMax hβ (x + q)]
  have h2 : ∫ x, softMinMax β (x + q) ∂ν ≤
      ∫ x, minMax (x + q) ∂ν + log (Fintype.card T) / β := by
    rw [← hconst ν _ _ (integrable_minMax_add ν q)]
    exact integral_mono (integrable_softMinMax_add ν hβ q)
      ((integrable_minMax_add ν q).add (integrable_const _)) fun x ↦
        softMinMax_le_minMax_add hβ (x + q)
  have h3 : log (Fintype.card S) / β + log (Fintype.card T) / β ≤ ε := by
    rw [← add_div, hβ_def, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end GaussianMeasure
