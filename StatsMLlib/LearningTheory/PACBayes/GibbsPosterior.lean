/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.LearningTheory.PACBayes.Catoni

/-!
# The Gibbs posterior and its PAC-Bayes oracle inequality

For a prior `ν`, an inverse temperature `β` and an empirical risk `r : Θ → ℝ`, the Gibbs posterior
is the tilted measure with density proportional to `exp (-β * r θ)` with respect to `ν`. By the
Donsker–Varadhan variational formula it minimizes `ρ ↦ ∫ r ∂ρ + KL(ρ ‖ ν) / β`. Combined with
Catoni's bound, this gives an oracle inequality: with probability at least `1 - δ`, the Gibbs
posterior's population risk is bounded by the right-hand side of Catoni's bound for every
competing posterior `ρ`.

## Main definitions

* `gibbsPosterior ν β r`: the Gibbs posterior `ν.tilted (fun θ ↦ -β * r θ)`.

## Main results

* `integral_add_toReal_klDiv_div_gibbsPosterior_le`: the Gibbs posterior minimizes
  `ρ ↦ ∫ r ∂ρ + KL(ρ ‖ ν) / β`.
* `catoni_bound_gibbsPosterior`: the PAC-Bayes oracle inequality for the Gibbs posterior.
-/

open MeasureTheory Real InformationTheory Function
open scoped ENNReal

namespace ProbabilityTheory

variable {Θ : Type*} [MeasurableSpace Θ]

/-- The Gibbs posterior with prior `ν`, inverse temperature `β` and empirical risk `r`: the
probability measure with density proportional to `exp (-β * r θ)` with respect to `ν`. -/
noncomputable def gibbsPosterior (ν : Measure Θ) (β : ℝ) (r : Θ → ℝ) : Measure Θ :=
  ν.tilted fun θ ↦ -β * r θ

section Bounded

variable {ν : Measure Θ} [IsProbabilityMeasure ν] {β : ℝ} {r : Θ → ℝ} {B : ℝ}

lemma integrable_exp_neg_mul_of_bound (hr : Measurable r) (hB : ∀ θ, |r θ| ≤ B) :
    Integrable (fun θ ↦ exp (-β * r θ)) ν :=
  Integrable.of_bound (measurable_exp.comp (measurable_const.mul hr)).aestronglyMeasurable
    (exp (|β| * B))
    (Filter.Eventually.of_forall fun θ ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      refine exp_le_exp.mpr ((le_abs_self _).trans ?_)
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hB θ) (abs_nonneg β))

lemma isProbabilityMeasure_gibbsPosterior (hr : Measurable r) (hB : ∀ θ, |r θ| ≤ B) :
    IsProbabilityMeasure (gibbsPosterior ν β r) :=
  isProbabilityMeasure_tilted (integrable_exp_neg_mul_of_bound hr hB)

omit [IsProbabilityMeasure ν] in
lemma integrable_of_bound_of_isProbabilityMeasure {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {f : Θ → ℝ} (hf : Measurable f) (hB : ∀ θ, |f θ| ≤ B) : Integrable f ρ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun θ ↦ by simpa [Real.norm_eq_abs] using hB θ)

lemma klDiv_gibbsPosterior_ne_top (hr : Measurable r) (hB : ∀ θ, |r θ| ≤ B) :
    klDiv (gibbsPosterior ν β r) ν ≠ ∞ := by
  have : IsProbabilityMeasure (ν.tilted fun θ ↦ -β * r θ) :=
    isProbabilityMeasure_gibbsPosterior hr hB
  refine klDiv_tilted_ne_top (integrable_exp_neg_mul_of_bound hr hB)
    (measurable_const.mul hr).aemeasurable ?_
  refine integrable_of_bound_of_isProbabilityMeasure (B := |β| * B) (measurable_const.mul hr)
    fun θ ↦ ?_
  rw [abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (hB θ) (abs_nonneg β)

/-- **The Gibbs posterior is optimal.** For `β > 0`, the Gibbs posterior minimizes
`ρ ↦ ∫ r ∂ρ + KL(ρ ‖ ν) / β` over probability measures `ρ` with finite KL divergence from `ν`. -/
theorem integral_add_toReal_klDiv_div_gibbsPosterior_le (hβ : 0 < β) (hr : Measurable r)
    (hB : ∀ θ, |r θ| ≤ B) (ρ : Measure Θ) [IsProbabilityMeasure ρ] (hKL : klDiv ρ ν ≠ ∞) :
    ∫ θ, r θ ∂(gibbsPosterior ν β r) + (klDiv (gibbsPosterior ν β r) ν).toReal / β ≤
      ∫ θ, r θ ∂ρ + (klDiv ρ ν).toReal / β := by
  have : IsProbabilityMeasure (ν.tilted fun θ ↦ -β * r θ) :=
    isProbabilityMeasure_gibbsPosterior hr hB
  have h_exp := integrable_exp_neg_mul_of_bound (ν := ν) (β := β) hr hB
  have h_meas : Measurable fun θ ↦ -β * r θ := measurable_const.mul hr
  have h_bound (θ : Θ) : |-β * r θ| ≤ |β| * B := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB θ) (abs_nonneg β)
  -- Donsker–Varadhan inequality for `ρ` and its equality case for the Gibbs posterior
  have h_le := integral_sub_toReal_klDiv_le_log_integral_exp h_exp
    (integrable_of_bound_of_isProbabilityMeasure (ρ := ρ) h_meas h_bound) hKL
  have h_eq := integral_sub_toReal_klDiv_tilted_eq h_exp h_meas.aemeasurable
    (integrable_of_bound_of_isProbabilityMeasure h_meas h_bound)
  simp only [neg_mul, integral_neg, integral_const_mul] at h_le h_eq
  rw [gibbsPosterior, ← sub_nonneg]
  have h_key : 0 ≤ β * (∫ θ, r θ ∂ρ - ∫ θ, r θ ∂(ν.tilted fun θ ↦ -β * r θ)) +
      ((klDiv ρ ν).toReal - (klDiv (ν.tilted fun θ ↦ -β * r θ) ν).toReal) := by
    simp only [neg_mul] at *
    linarith
  have h_rhs : ∫ θ, r θ ∂ρ + (klDiv ρ ν).toReal / β -
      (∫ θ, r θ ∂(ν.tilted fun θ ↦ -β * r θ) +
        (klDiv (ν.tilted fun θ ↦ -β * r θ) ν).toReal / β) =
      (β * (∫ θ, r θ ∂ρ - ∫ θ, r θ ∂(ν.tilted fun θ ↦ -β * r θ)) +
        ((klDiv ρ ν).toReal - (klDiv (ν.tilted fun θ ↦ -β * r θ) ν).toReal)) / β := by
    field_simp
    ring
  rw [h_rhs]
  exact div_nonneg h_key hβ.le

end Bounded

variable {Ω 𝒵 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒵]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}

local notation "μⁿ" => Measure.pi (fun _ : Fin n ↦ μ)

/-- **PAC-Bayes oracle inequality for the Gibbs posterior.** With `μⁿ`-probability at least
`1 - δ`, the Gibbs posterior `ρ̂ = gibbsPosterior ν β (r S)` satisfies, for every posterior `ρ`
with finite KL divergence from `ν`,
`∫ R ∂ρ̂ ≤ ∫ r S ∂ρ + β * C ^ 2 / (8 * n) + (KL(ρ ‖ ν) + log (1 / δ)) / β`. -/
theorem catoni_bound_gibbsPosterior (hn : 0 < n) (ν : Measure Θ) [IsProbabilityMeasure ν]
    {ℓ : Θ → 𝒵 → ℝ} (hℓ : Measurable (uncurry ℓ)) {Z : Ω → 𝒵} (hZ : Measurable Z) {C : ℝ}
    (hℓC : ∀ θ z, ℓ θ z ∈ Set.Icc 0 C) {β : ℝ} (hβ : 0 < β) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Set (Fin n → Ω), MeasurableSet A ∧ 1 - δ ≤ (μⁿ).real A ∧
      ∀ S ∈ A, ∀ ρ : Measure Θ, IsProbabilityMeasure ρ → klDiv ρ ν ≠ ∞ →
        ∫ θ, populationRisk ℓ μ Z θ
            ∂(gibbsPosterior ν β fun θ ↦ empiricalRisk n ℓ (Z ∘ S) θ) ≤
          ∫ θ, empiricalRisk n ℓ (Z ∘ S) θ ∂ρ + β * C ^ 2 / (8 * n) +
            ((klDiv ρ ν).toReal + log (1 / δ)) / β := by
  obtain ⟨A, hA, hPA, hA_bound⟩ := catoni_bound μ hn ν hℓ hZ hℓC hβ hδ
  refine ⟨A, hA, hPA, fun S hS ρ hρ hKL ↦ ?_⟩
  set r : Θ → ℝ := fun θ ↦ empiricalRisk n ℓ (Z ∘ S) θ with hr_def
  have hr : Measurable r := by
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ ↦ ?_)
    exact hℓ.comp (measurable_id.prodMk measurable_const)
  have hB (θ : Θ) : |r θ| ≤ C := by
    have h := empiricalRisk_mem_Icc hn hℓC (Z ∘ S) θ
    rw [abs_of_nonneg h.1]
    exact h.2
  have := isProbabilityMeasure_gibbsPosterior (ν := ν) (β := β) hr hB
  have h_catoni := hA_bound S hS (gibbsPosterior ν β r) this
    (klDiv_gibbsPosterior_ne_top hr hB)
  have h_opt := integral_add_toReal_klDiv_div_gibbsPosterior_le hβ hr hB ρ hKL
  have h_split (K : ℝ) : (K + log (1 / δ)) / β = K / β + log (1 / δ) / β := add_div _ _ _
  rw [h_split] at h_catoni ⊢
  linarith

end ProbabilityTheory
