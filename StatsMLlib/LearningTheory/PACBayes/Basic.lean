/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Entropy.DonskerVaradhan
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A general PAC-Bayes bound

Let `P` be a probability measure on a sample space `Ω` and `ν` a prior probability measure on a
parameter space `Θ`. For a bounded jointly measurable `g : Ω → Θ → ℝ` and `δ > 0`, put
`M = ∫ ω, ∫ θ, exp (g ω θ) ∂ν ∂P`. With `P`-probability at least `1 - δ`, simultaneously for every
posterior `ρ` with finite KL divergence from `ν`,

  `∫ θ, g ω θ ∂ρ ≤ KL(ρ ‖ ν) + log (M / δ)`.

The bound is stated for any upper bound of `M`, so that a moment-generating-function estimate can
be substituted directly.

The proof combines the Donsker–Varadhan inequality, applied for each fixed `ω`, with Markov's
inequality for `ω ↦ ∫ θ, exp (g ω θ) ∂ν`.

An event quantifying over all posteriors `ρ` is an uncountable intersection, so the results are
stated as the existence of a measurable event `A` of probability at least `1 - δ` on which the
bound holds for every `ρ`.

## Main results

* `exists_measurableSet_integral_le_toReal_klDiv_add_log`: the bound above.
* `pacBayes_convex`: for a convex function `D`, continuous on a closed convex set `K`, and
  `K`-valued pairs `(r ω θ, R θ)`, with `P`-probability at least `1 - δ`, for every posterior `ρ`,
  `D (∫ r ω ∂ρ, ∫ R ∂ρ) ≤ (KL(ρ ‖ ν) + log (M / δ)) / n`, where
  `M = ∫ ω, ∫ θ, exp (n * D (r ω θ, R θ)) ∂ν ∂P`.
-/

open MeasureTheory Real InformationTheory Function
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

/-- **PAC-Bayes bound.** For bounded jointly measurable `g` and `δ > 0`, there is a measurable
event of `P`-probability at least `1 - δ` on which, for every posterior `ρ` with finite KL
divergence from the prior `ν`, `∫ g ω ∂ρ ≤ KL(ρ ‖ ν) + log (M / δ)`, where `M` is any upper
bound for `∫ ω, ∫ θ, exp (g ω θ) ∂ν ∂P`. -/
theorem exists_measurableSet_integral_le_toReal_klDiv_add_log
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure Θ) [IsProbabilityMeasure ν]
    {g : Ω → Θ → ℝ} (hg : Measurable (uncurry g)) {B : ℝ} (hB : ∀ ω θ, |g ω θ| ≤ B)
    {M : ℝ} (hM : ∫ ω, ∫ θ, exp (g ω θ) ∂ν ∂P ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Set Ω, MeasurableSet A ∧ 1 - δ ≤ P.real A ∧
      ∀ ω ∈ A, ∀ ρ : Measure Θ, IsProbabilityMeasure ρ → klDiv ρ ν ≠ ∞ →
        ∫ θ, g ω θ ∂ρ ≤ (klDiv ρ ν).toReal + log (M / δ) := by
  set X : Ω → ℝ := fun ω ↦ ∫ θ, exp (g ω θ) ∂ν with hX_def
  have hg_meas (ω : Ω) : Measurable (g ω) := hg.comp measurable_prodMk_left
  have hg_int (ω : Ω) (ρ : Measure Θ) [IsProbabilityMeasure ρ] : Integrable (g ω) ρ :=
    Integrable.of_bound (hg_meas ω).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun θ ↦ by simpa [Real.norm_eq_abs] using hB ω θ)
  have hexp_int (ω : Ω) : Integrable (fun θ ↦ exp (g ω θ)) ν :=
    Integrable.of_bound (hg_meas ω).exp.aestronglyMeasurable (exp B)
      (Filter.Eventually.of_forall fun θ ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr (le_of_abs_le (hB ω θ)))
  -- `exp (-B) ≤ X ω ≤ exp B`
  have hX_lower (ω : Ω) : exp (-B) ≤ X ω := by
    have h := integral_mono (integrable_const (exp (-B))) (hexp_int ω)
      (fun θ ↦ exp_le_exp.mpr (neg_le_of_abs_le (hB ω θ)))
    simpa using h
  have hX_upper (ω : Ω) : X ω ≤ exp B := by
    have h := integral_mono (hexp_int ω) (integrable_const (exp B))
      (fun θ ↦ exp_le_exp.mpr (le_of_abs_le (hB ω θ)))
    simpa using h
  have hX_pos (ω : Ω) : 0 < X ω := (exp_pos _).trans_le (hX_lower ω)
  have hX_meas : Measurable X :=
    (StronglyMeasurable.integral_prod_right (f := fun ω θ ↦ exp (g ω θ))
      (measurable_exp.comp hg).stronglyMeasurable).measurable
  have hX_int : Integrable X P :=
    Integrable.of_bound hX_meas.aestronglyMeasurable (exp B)
      (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (hX_pos ω)]
        exact hX_upper ω)
  have hM_pos : 0 < M := by
    have h := integral_mono (integrable_const (exp (-B))) hX_int hX_lower
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    exact (exp_pos _).trans_le (h.trans hM)
  -- the good event and its probability, via Markov's inequality
  refine ⟨{ω | X ω < M / δ}, measurableSet_lt hX_meas measurable_const, ?_, ?_⟩
  · have h_markov := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω ↦ (hX_pos ω).le) hX_int (M / δ)
    have h_compl : {ω | X ω < M / δ}ᶜ = {ω | M / δ ≤ X ω} := by
      ext ω
      simp
    have h_bad : P.real {ω | M / δ ≤ X ω} ≤ δ := by
      have h' : M / δ * P.real {ω | M / δ ≤ X ω} ≤ M / δ * δ := by
        rw [div_mul_cancel₀ M hδ.ne']
        exact h_markov.trans hM
      exact le_of_mul_le_mul_left h' (div_pos hM_pos hδ)
    have h_eq := probReal_compl_eq_one_sub (μ := P)
      (measurableSet_lt hX_meas measurable_const : MeasurableSet {ω | X ω < M / δ})
    rw [h_compl] at h_eq
    linarith
  · intro ω hω ρ hρ hKL
    have h_dv := integral_sub_toReal_klDiv_le_log_integral_exp (hexp_int ω) (hg_int ω ρ) hKL
    have h_log : log (X ω) ≤ log (M / δ) := log_le_log (hX_pos ω) (le_of_lt hω)
    linarith

/-- **PAC-Bayes bound for a convex comparison function.** Let `D` be convex and continuous on a
closed convex set `K ⊆ ℝ × ℝ`, and let `(r ω θ, R θ) ∈ K`. With `P`-probability at least `1 - δ`,
for every posterior `ρ` with finite KL divergence from the prior `ν`,
`D (∫ r ω ∂ρ, ∫ R ∂ρ) ≤ (KL(ρ ‖ ν) + log (M / δ)) / n` with
`M = ∫ ω, ∫ θ, exp (n * D (r ω θ, R θ)) ∂ν ∂P`. -/
theorem pacBayes_convex
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure Θ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) {K : Set (ℝ × ℝ)} {D : ℝ × ℝ → ℝ}
    (hD : ConvexOn ℝ K D) (hDc : ContinuousOn D K) (hK : IsClosed K) (hD_meas : Measurable D)
    {r : Ω → Θ → ℝ} {R : Θ → ℝ} (hr : Measurable (uncurry r)) (hR : Measurable R)
    {B : ℝ} (hr_bound : ∀ ω θ, |r ω θ| ≤ B) (hR_bound : ∀ θ, |R θ| ≤ B)
    (hrR : ∀ ω θ, (r ω θ, R θ) ∈ K)
    {B' : ℝ} (hD_bound : ∀ ω θ, |D (r ω θ, R θ)| ≤ B')
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Set Ω, MeasurableSet A ∧ 1 - δ ≤ P.real A ∧
      ∀ ω ∈ A, ∀ ρ : Measure Θ, IsProbabilityMeasure ρ → klDiv ρ ν ≠ ∞ →
        D (∫ θ, r ω θ ∂ρ, ∫ θ, R θ ∂ρ) ≤
          ((klDiv ρ ν).toReal +
            log ((∫ ω, ∫ θ, exp (n * D (r ω θ, R θ)) ∂ν ∂P) / δ)) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpair_meas : Measurable fun p : Ω × Θ ↦ (r p.1 p.2, R p.2) :=
    hr.prodMk (hR.comp measurable_snd)
  have hg : Measurable (uncurry fun ω θ ↦ (n : ℝ) * D (r ω θ, R θ)) :=
    measurable_const.mul (hD_meas.comp hpair_meas)
  have hg_bound (ω : Ω) (θ : Θ) : |(n : ℝ) * D (r ω θ, R θ)| ≤ n * B' := by
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (hD_bound ω θ) hn'.le
  obtain ⟨A, hA, hPA, hA_bound⟩ :=
    exists_measurableSet_integral_le_toReal_klDiv_add_log P ν hg hg_bound le_rfl hδ
  refine ⟨A, hA, hPA, fun ω hω ρ hρ hKL ↦ ?_⟩
  have hr_meas : Measurable (r ω) := hr.comp measurable_prodMk_left
  have hr_int : Integrable (r ω) ρ :=
    Integrable.of_bound hr_meas.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun θ ↦ by simpa [Real.norm_eq_abs] using hr_bound ω θ)
  have hR_int : Integrable R ρ :=
    Integrable.of_bound hR.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun θ ↦ by simpa [Real.norm_eq_abs] using hR_bound θ)
  have hD_int : Integrable (fun θ ↦ D (r ω θ, R θ)) ρ :=
    Integrable.of_bound (hD_meas.comp (hr_meas.prodMk hR)).aestronglyMeasurable B'
      (Filter.Eventually.of_forall fun θ ↦ by simpa [Real.norm_eq_abs] using hD_bound ω θ)
  -- Jensen's inequality for the `K`-valued map `θ ↦ (r ω θ, R θ)`
  have h_jensen : D (∫ θ, r ω θ ∂ρ, ∫ θ, R θ ∂ρ) ≤ ∫ θ, D (r ω θ, R θ) ∂ρ := by
    rw [← integral_pair hr_int hR_int]
    exact hD.map_integral_le hDc hK (Filter.Eventually.of_forall fun θ ↦ hrR ω θ)
      (hr_int.prodMk hR_int) hD_int
  have h_bound := hA_bound ω hω ρ hρ hKL
  rw [integral_const_mul] at h_bound
  rw [le_div_iff₀ hn']
  nlinarith

end ProbabilityTheory
