/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# Donsker–Varadhan variational inequality

For probability measures `ρ` and `ν` on `Θ` and a function `h : Θ → ℝ` with `exp ∘ h`
`ν`-integrable, the Donsker–Varadhan inequality states

  `∫ h ∂ρ - KL(ρ ‖ ν) ≤ log ∫ exp h ∂ν`,

with equality when `ρ` is the Gibbs measure `ν.tilted h`, whose density with respect to `ν` is
`exp h / ∫ exp h ∂ν`. Together these say that `log ∫ exp h ∂ν` is the maximum over `ρ` of
`∫ h ∂ρ - KL(ρ ‖ ν)`.

The KL divergence `InformationTheory.klDiv` takes values in `ℝ≥0∞`; the statements below assume
it is finite and use its real part.

## Main results

* `integral_sub_toReal_klDiv_le_log_integral_exp`: the Donsker–Varadhan inequality.
* `klDiv_tilted_ne_top`: the Gibbs measure has finite KL divergence from `ν`.
* `integral_sub_toReal_klDiv_tilted_eq`: the Gibbs measure attains equality.
-/

open MeasureTheory Real InformationTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Θ : Type*} [MeasurableSpace Θ] {ν ρ : Measure Θ} {h : Θ → ℝ}

/-- **Donsker–Varadhan inequality.** For probability measures `ρ, ν` with `KL(ρ ‖ ν) < ∞`,
`∫ h ∂ρ - KL(ρ ‖ ν) ≤ log ∫ exp h ∂ν`. -/
theorem integral_sub_toReal_klDiv_le_log_integral_exp
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hν : Integrable (fun θ ↦ exp (h θ)) ν) (hρ : Integrable h ρ) (hKL : klDiv ρ ν ≠ ∞) :
    ∫ θ, h θ ∂ρ - (klDiv ρ ν).toReal ≤ log (∫ θ, exp (h θ) ∂ν) := by
  obtain ⟨hρν, h_int⟩ := klDiv_ne_top_iff.mp hKL
  have : IsProbabilityMeasure (ν.tilted h) := isProbabilityMeasure_tilted hν
  have hρ_tilted : ρ ≪ ν.tilted h := hρν.trans (absolutelyContinuous_tilted hν)
  -- `KL(ρ ‖ ν.tilted h) = KL(ρ ‖ ν) - ∫ h ∂ρ + log ∫ exp h ∂ν`, and the left side is nonnegative
  have h_eq : (klDiv ρ (ν.tilted h)).toReal
      = (klDiv ρ ν).toReal - ∫ θ, h θ ∂ρ + log (∫ θ, exp (h θ) ∂ν) := by
    rw [toReal_klDiv_of_measure_eq hρ_tilted (by simp), toReal_klDiv_of_measure_eq hρν (by simp),
      integral_llr_tilted_right hρν hρ hν h_int]
  have h_nonneg : 0 ≤ (klDiv ρ (ν.tilted h)).toReal := ENNReal.toReal_nonneg
  linarith

/-- Almost everywhere with respect to `ν`, the log-likelihood ratio of the Gibbs measure
`ν.tilted h` against `ν` is `h - log ∫ exp h ∂ν`. -/
lemma llr_tilted_self_ae_eq [SigmaFinite ν]
    (hν : Integrable (fun θ ↦ exp (h θ)) ν) (hh : AEMeasurable h ν) :
    llr (ν.tilted h) ν =ᵐ[ν] fun θ ↦ h θ - log (∫ θ, exp (h θ) ∂ν) := by
  filter_upwards [llr_tilted_left (Measure.AbsolutelyContinuous.refl ν) hν hh, llr_self ν]
    with θ h₁ h₂
  rw [h₁, h₂, Pi.zero_apply, add_zero]

/-- The Gibbs measure `ν.tilted h` has finite KL divergence from `ν` whenever `h` is integrable
against it. -/
lemma klDiv_tilted_ne_top [SigmaFinite ν]
    (hν : Integrable (fun θ ↦ exp (h θ)) ν) (hh : AEMeasurable h ν)
    (hρ : Integrable h (ν.tilted h)) :
    klDiv (ν.tilted h) ν ≠ ∞ := by
  refine klDiv_ne_top (tilted_absolutelyContinuous ν h) ?_
  have h_ae := (tilted_absolutelyContinuous ν h).ae_le (llr_tilted_self_ae_eq hν hh)
  exact (integrable_congr h_ae).mpr (hρ.sub (integrable_const _))

/-- **Equality case of Donsker–Varadhan.** The Gibbs measure `ν.tilted h` attains
`∫ h ∂(ν.tilted h) - KL(ν.tilted h ‖ ν) = log ∫ exp h ∂ν`. -/
theorem integral_sub_toReal_klDiv_tilted_eq [IsProbabilityMeasure ν]
    (hν : Integrable (fun θ ↦ exp (h θ)) ν) (hh : AEMeasurable h ν)
    (hρ : Integrable h (ν.tilted h)) :
    ∫ θ, h θ ∂(ν.tilted h) - (klDiv (ν.tilted h) ν).toReal = log (∫ θ, exp (h θ) ∂ν) := by
  have : IsProbabilityMeasure (ν.tilted h) := isProbabilityMeasure_tilted hν
  have h_ae := (tilted_absolutelyContinuous ν h).ae_le (llr_tilted_self_ae_eq hν hh)
  rw [toReal_klDiv_of_measure_eq (tilted_absolutelyContinuous ν h) (by simp),
    integral_congr_ae h_ae, integral_sub hρ (integrable_const _), integral_const]
  simp

end ProbabilityTheory
