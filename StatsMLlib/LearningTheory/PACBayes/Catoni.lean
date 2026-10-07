/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.LearningTheory.PACBayes.Basic
import StatsMLlib.LearningTheory.EmpiricalRiskMinimization.Defs
import StatsMLlib.Probability.Independence.FinsetPi
import Mathlib.Probability.Moments.SubGaussian

/-!
# Catoni's PAC-Bayes bound

Let `S : Fin n → Ω` be an i.i.d. sample from `μ`, mapped to data by `Z : Ω → 𝒵`, and let
`ℓ : Θ → 𝒵 → ℝ` be a loss with values in `[0, C]`. Write `R θ = populationRisk ℓ μ Z θ` and
`r S θ = empiricalRisk n ℓ (Z ∘ S) θ`. For a prior `ν` on `Θ`, an inverse temperature `β > 0` and
`δ > 0`, with probability at least `1 - δ` over the sample, simultaneously for every posterior `ρ`
with finite KL divergence from `ν`,

  `∫ R ∂ρ ≤ ∫ r S ∂ρ + β * C ^ 2 / (8 * n) + (KL(ρ ‖ ν) + log (1 / δ)) / β`.

## Main results

* `integral_exp_populationRisk_sub_empiricalRisk_le`: Hoeffding's moment-generating-function
  bound `∫ exp (β * (R θ - r S θ)) ∂μⁿ ≤ exp (β ^ 2 * C ^ 2 / (8 * n))` for each fixed `θ`.
* `catoni_bound`: Catoni's PAC-Bayes bound.
-/

open MeasureTheory Real InformationTheory Function
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω Θ 𝒵 : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace 𝒵]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}

local notation "μⁿ" => Measure.pi (fun _ : Fin n ↦ μ)

omit [MeasurableSpace Θ] [MeasurableSpace 𝒵] in
/-- The population risk of a loss with values in `[0, C]` lies in `[0, C]`. -/
lemma populationRisk_mem_Icc {ℓ : Θ → 𝒵 → ℝ} {Z : Ω → 𝒵} {C : ℝ}
    (hℓC : ∀ θ z, ℓ θ z ∈ Set.Icc 0 C) (θ : Θ) :
    populationRisk ℓ μ Z θ ∈ Set.Icc 0 C := by
  refine ⟨integral_nonneg fun ω ↦ (hℓC θ (Z ω)).1, ?_⟩
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω ↦ (hℓC θ (Z ω)).1)
    (integrable_const (μ := μ) C) (Filter.Eventually.of_forall fun ω ↦ (hℓC θ (Z ω)).2)
  simpa [populationRisk] using h

omit [MeasurableSpace Θ] [MeasurableSpace 𝒵] in
/-- The empirical risk of a loss with values in `[0, C]` lies in `[0, C]`. -/
lemma empiricalRisk_mem_Icc (hn : 0 < n) {ℓ : Θ → 𝒵 → ℝ} {C : ℝ}
    (hℓC : ∀ θ z, ℓ θ z ∈ Set.Icc 0 C) (S : Fin n → 𝒵) (θ : Θ) :
    empiricalRisk n ℓ S θ ∈ Set.Icc 0 C := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_sum_le : ∑ k : Fin n, ℓ θ (S k) ≤ n * C := by
    simpa using Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) ↦ (hℓC θ (S k)).2
  have h_sum_nonneg : 0 ≤ ∑ k : Fin n, ℓ θ (S k) :=
    Finset.sum_nonneg fun k _ ↦ (hℓC θ (S k)).1
  refine ⟨mul_nonneg (inv_nonneg.mpr hn'.le) h_sum_nonneg, ?_⟩
  rw [empiricalRisk, inv_mul_le_iff₀ hn']
  exact h_sum_le

omit [MeasurableSpace Θ] in
/-- **Hoeffding's moment-generating-function bound** for the gap between population and
empirical risk at a fixed parameter `θ`:
`∫ exp (β * (R θ - r S θ)) ∂μⁿ ≤ exp (β ^ 2 * C ^ 2 / (8 * n))`. -/
theorem integral_exp_populationRisk_sub_empiricalRisk_le (hn : 0 < n)
    {ℓ : Θ → 𝒵 → ℝ} (hℓ : ∀ θ, Measurable (ℓ θ)) {Z : Ω → 𝒵} (hZ : Measurable Z) {C : ℝ}
    (hℓC : ∀ θ z, ℓ θ z ∈ Set.Icc 0 C) (θ : Θ) (β : ℝ) :
    ∫ S, exp (β * (populationRisk ℓ μ Z θ - empiricalRisk n ℓ (Z ∘ S) θ)) ∂μⁿ ≤
      exp (β ^ 2 * C ^ 2 / (8 * n)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set Rθ := populationRisk ℓ μ Z θ with hRθ
  -- the centred loss of one observation
  set W : Ω → ℝ := fun ω ↦ Rθ - ℓ θ (Z ω) with hW
  have hW_meas : Measurable W := measurable_const.sub ((hℓ θ).comp hZ)
  have hW_mem (ω : Ω) : W ω ∈ Set.Icc (Rθ - C) (Rθ - 0) :=
    ⟨by linarith [(hℓC θ (Z ω)).2], by linarith [(hℓC θ (Z ω)).1]⟩
  have hW_int : ∫ ω, W ω ∂μ = 0 := by
    have h_int : Integrable (fun ω ↦ ℓ θ (Z ω)) μ :=
      Integrable.of_mem_Icc 0 C ((hℓ θ).comp hZ).aemeasurable
        (Filter.Eventually.of_forall fun ω ↦ hℓC θ (Z ω))
    simp only [hW, integral_sub (integrable_const _) h_int, integral_const, probReal_univ,
      one_smul, hRθ, populationRisk, sub_self]
  -- each coordinate is sub-Gaussian with parameter `(C / 2) ^ 2`
  have h_subG (i : Fin n) :
      HasSubgaussianMGF (fun S : Fin n → Ω ↦ W (S i)) ((‖(Rθ - 0) - (Rθ - C)‖₊ / 2) ^ 2) μⁿ := by
    have h_map : (μⁿ).map (Function.eval i) = μ := pi_map_eval i
    refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hW_meas.comp (measurable_pi_apply i)).aemeasurable
      (Filter.Eventually.of_forall fun S ↦ hW_mem (S i)) ?_
    have h := integral_map (μ := μⁿ) (measurable_pi_apply i).aemeasurable
      hW_meas.aestronglyMeasurable
    rw [h_map] at h
    rw [← hW_int, h]
  have h_indep : iIndepFun (fun (i : Fin n) (S : Fin n → Ω) ↦ W (S i)) μⁿ :=
    pi_comp_eval_iIndepFun hW_meas
  have h_sum := HasSubgaussianMGF.sum_of_iIndepFun h_indep
    (s := Finset.univ) fun i _ ↦ h_subG i
  have h_mgf := h_sum.mgf_le (β / n)
  -- rewrite the integrand as the mgf of the sum at `β / n`
  have h_eq : (fun S : Fin n → Ω ↦
      exp (β * (Rθ - empiricalRisk n ℓ (Z ∘ S) θ))) =
      fun S ↦ exp (β / n * ∑ i ∈ Finset.univ, W (S i)) := by
    funext S
    congr 1
    simp only [hW, empiricalRisk, comp_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [h_eq]
  refine h_mgf.trans_eq ?_
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
    NNReal.coe_ofNat, sub_zero, sub_sub_cancel]
  field_simp
  rw [sq_abs]
  ring

/-- **Catoni's PAC-Bayes bound.** For a loss with values in `[0, C]`, a prior `ν`, `β > 0` and
`δ > 0`, there is a measurable event of `μⁿ`-probability at least `1 - δ` on which, for every
posterior `ρ` with finite KL divergence from `ν`,
`∫ R ∂ρ ≤ ∫ r S ∂ρ + β * C ^ 2 / (8 * n) + (KL(ρ ‖ ν) + log (1 / δ)) / β`. -/
theorem catoni_bound (hn : 0 < n) (ν : Measure Θ) [IsProbabilityMeasure ν]
    {ℓ : Θ → 𝒵 → ℝ} (hℓ : Measurable (uncurry ℓ)) {Z : Ω → 𝒵} (hZ : Measurable Z) {C : ℝ}
    (hℓC : ∀ θ z, ℓ θ z ∈ Set.Icc 0 C) {β : ℝ} (hβ : 0 < β) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Set (Fin n → Ω), MeasurableSet A ∧ 1 - δ ≤ (μⁿ).real A ∧
      ∀ S ∈ A, ∀ ρ : Measure Θ, IsProbabilityMeasure ρ → klDiv ρ ν ≠ ∞ →
        ∫ θ, populationRisk ℓ μ Z θ ∂ρ ≤
          ∫ θ, empiricalRisk n ℓ (Z ∘ S) θ ∂ρ + β * C ^ 2 / (8 * n) +
            ((klDiv ρ ν).toReal + log (1 / δ)) / β := by
  have hℓθ (θ : Θ) : Measurable (ℓ θ) := hℓ.comp measurable_prodMk_left
  set R : Θ → ℝ := fun θ ↦ populationRisk ℓ μ Z θ with hR
  set r : (Fin n → Ω) → Θ → ℝ := fun S θ ↦ empiricalRisk n ℓ (Z ∘ S) θ with hr
  set g : (Fin n → Ω) → Θ → ℝ := fun S θ ↦ β * (R θ - r S θ) with hg
  have hR_meas : Measurable R :=
    (StronglyMeasurable.integral_prod_right (f := fun θ ω ↦ ℓ θ (Z ω))
      (hℓ.comp (measurable_fst.prodMk (hZ.comp measurable_snd))).stronglyMeasurable).measurable
  have hr_meas : Measurable (uncurry r) := by
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ ↦ ?_)
    have hk : Measurable fun p : (Fin n → Ω) × Θ ↦ (p.2, Z (p.1 k)) := by fun_prop
    exact hℓ.comp hk
  have hg_meas : Measurable (uncurry g) :=
    measurable_const.mul ((hR_meas.comp measurable_snd).sub hr_meas)
  have hR_mem (θ : Θ) : R θ ∈ Set.Icc 0 C := populationRisk_mem_Icc μ hℓC θ
  have hr_mem (S : Fin n → Ω) (θ : Θ) : r S θ ∈ Set.Icc 0 C :=
    empiricalRisk_mem_Icc hn hℓC (Z ∘ S) θ
  have hg_bound (S : Fin n → Ω) (θ : Θ) : |g S θ| ≤ β * C := by
    rw [hg, abs_mul, abs_of_pos hβ]
    refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨?_, ?_⟩) hβ.le
    · linarith [(hR_mem θ).1, (hr_mem S θ).2]
    · linarith [(hR_mem θ).2, (hr_mem S θ).1]
  -- bound the double exponential moment by Fubini and Hoeffding
  have hM : ∫ S, ∫ θ, exp (g S θ) ∂ν ∂μⁿ ≤ exp (β ^ 2 * C ^ 2 / (8 * n)) := by
    have h_int : Integrable (uncurry fun S θ ↦ exp (g S θ)) ((μⁿ).prod ν) :=
      Integrable.of_bound (measurable_exp.comp hg_meas).aestronglyMeasurable (exp (β * C))
        (Filter.Eventually.of_forall fun p ↦ by
          rw [Real.norm_eq_abs, uncurry_apply_pair, abs_of_pos (exp_pos _)]
          exact exp_le_exp.mpr (le_of_abs_le (hg_bound p.1 p.2)))
    rw [integral_integral_swap h_int]
    have h_le := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ ↦ integral_nonneg fun S ↦ (exp_pos (g S θ)).le)
      (integrable_const (μ := ν) (exp (β ^ 2 * C ^ 2 / (8 * n))))
      (Filter.Eventually.of_forall fun θ ↦
        integral_exp_populationRisk_sub_empiricalRisk_le μ hn hℓθ hZ hℓC θ β)
    simpa using h_le
  obtain ⟨A, hA, hPA, hA_bound⟩ :=
    exists_measurableSet_integral_le_toReal_klDiv_add_log μⁿ ν hg_meas hg_bound hM hδ
  refine ⟨A, hA, hPA, fun S hS ρ hρ hKL ↦ ?_⟩
  have h := hA_bound S hS ρ hρ hKL
  have hR_int : Integrable R ρ :=
    Integrable.of_mem_Icc 0 C hR_meas.aemeasurable (Filter.Eventually.of_forall hR_mem)
  have hr_int : Integrable (r S) ρ :=
    Integrable.of_mem_Icc 0 C (hr_meas.comp measurable_prodMk_left).aemeasurable
      (Filter.Eventually.of_forall (hr_mem S))
  have h_lhs : ∫ θ, g S θ ∂ρ = β * (∫ θ, R θ ∂ρ - ∫ θ, r S θ ∂ρ) := by
    rw [hg, integral_const_mul, integral_sub hR_int hr_int]
  have h_log : log (exp (β ^ 2 * C ^ 2 / (8 * n)) / δ) =
      β ^ 2 * C ^ 2 / (8 * n) + log (1 / δ) := by
    rw [log_div (exp_pos _).ne' hδ.ne', log_exp, one_div, log_inv, sub_eq_add_neg]
  rw [h_lhs, h_log] at h
  have h_div : ∫ θ, R θ ∂ρ - ∫ θ, r S θ ∂ρ ≤
      ((klDiv ρ ν).toReal + (β ^ 2 * C ^ 2 / (8 * n) + log (1 / δ))) / β := by
    rw [le_div_iff₀ hβ]
    linarith
  have h_split : ((klDiv ρ ν).toReal + (β ^ 2 * C ^ 2 / (8 * n) + log (1 / δ))) / β =
      β * C ^ 2 / (8 * n) + ((klDiv ρ ν).toReal + log (1 / δ)) / β := by
    field_simp
    ring
  linarith

end ProbabilityTheory
