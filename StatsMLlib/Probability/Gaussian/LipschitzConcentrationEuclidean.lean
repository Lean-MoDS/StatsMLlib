/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Gaussian.LipschitzConcentration
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Gaussian Lipschitz concentration for `stdGaussian` on Euclidean spaces

The Lipschitz concentration inequalities of `StatsMLlib.Probability.Gaussian.LipschitzConcentration`
are stated for `GaussianMeasure.stdGaussianE n` on `EuclideanSpace ℝ (Fin n)`. This file identifies
that measure with Mathlib's `ProbabilityTheory.stdGaussian` and transports the inequalities to
`stdGaussian (EuclideanSpace ℝ ι)` for an arbitrary nonempty finite index type `ι`.

## Main results

* `GaussianMeasure.stdGaussianE_eq_stdGaussian`: `stdGaussianE n = stdGaussian _`.
* `GaussianLipConcen.integrable_stdGaussian_of_lipschitz`: Lipschitz functions are integrable.
* `GaussianLipConcen.stdGaussian_lipschitz_concentration_upper`: upper tail bound
  `P(f - 𝔼 f ≥ t) ≤ exp (-t² / (2 L²))`.
* `GaussianLipConcen.stdGaussian_lipschitz_concentration_lower`: lower tail bound
  `P(f ≤ 𝔼 f - t) ≤ exp (-t² / (2 L²))`.
* `GaussianLipConcen.stdGaussian_lipschitz_concentration`: two-sided tail bound
  `P(|f - 𝔼 f| ≥ t) ≤ 2 exp (-t² / (2 L²))`.
-/

open MeasureTheory ProbabilityTheory Real GaussianMeasure
open scoped NNReal

namespace GaussianMeasure

/-- The pushforward definition `stdGaussianE n` agrees with Mathlib's `stdGaussian`. -/
lemma stdGaussianE_eq_stdGaussian (n : ℕ) :
    stdGaussianE n = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [stdGaussianE, ← map_pi_eq_stdGaussian]
  rfl

end GaussianMeasure

namespace GaussianLipConcen

variable {ι : Type*} [Fintype ι]

/-- The isometry `EuclideanSpace ℝ (Fin (card ι)) ≃ EuclideanSpace ℝ ι` used for transport. -/
private noncomputable def finIso (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ (Fin (Fintype.card ι)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι).symm

private lemma map_finIso :
    (stdGaussianE (Fintype.card ι)).map (finIso ι) = stdGaussian (EuclideanSpace ℝ ι) := by
  rw [stdGaussianE_eq_stdGaussian, stdGaussian_map]

private lemma stdGaussian_apply_eq (S : Set (EuclideanSpace ℝ ι)) :
    stdGaussian (EuclideanSpace ℝ ι) S = stdGaussianE (Fintype.card ι) (finIso ι ⁻¹' S) := by
  rw [← map_finIso]
  exact (finIso ι).toHomeomorph.toMeasurableEquiv.map_apply S

private lemma integral_stdGaussian_eq (f : EuclideanSpace ℝ ι → ℝ) :
    ∫ x, f x ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ y, f (finIso ι y) ∂stdGaussianE (Fintype.card ι) := by
  rw [← map_finIso]
  exact integral_map_equiv (finIso ι).toHomeomorph.toMeasurableEquiv f

/-- Lipschitz functions are integrable under the standard Gaussian on `EuclideanSpace ℝ ι`. -/
lemma integrable_stdGaussian_of_lipschitz {f : EuclideanSpace ℝ ι → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : Integrable f (stdGaussian (EuclideanSpace ℝ ι)) := by
  rw [← map_finIso]
  refine (integrable_map_equiv (finIso ι).toHomeomorph.toMeasurableEquiv f).2 ?_
  have hg : LipschitzWith (Real.toNNReal (L : ℝ)) (f ∘ finIso ι) := by
    simpa using hf.comp (finIso ι).lipschitz
  exact lipschitzE_integrable L.coe_nonneg hg

/-- **Gaussian Lipschitz concentration, upper tail.** For an `L`-Lipschitz function `f` of a
standard Gaussian vector, `P(f - 𝔼 f ≥ t) ≤ exp (-t² / (2 L²))`. -/
theorem stdGaussian_lipschitz_concentration_upper [Nonempty ι] {f : EuclideanSpace ℝ ι → ℝ}
    {L : ℝ≥0} (hL : 0 < L) (hf : LipschitzWith L f) (t : ℝ) (ht : 0 < t) :
    (stdGaussian (EuclideanSpace ℝ ι)
        {x | t ≤ f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ ι)}).toReal ≤
      exp (-t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hg : LipschitzWith L (f ∘ finIso ι) := by
    simpa using hf.comp (finIso ι).lipschitz
  have h := gaussian_lipschitz_concentration_one_sided hn hL hg t ht
  rw [stdGaussian_apply_eq, integral_stdGaussian_eq]
  exact h

/-- **Gaussian Lipschitz concentration, lower tail.** For an `L`-Lipschitz function `f` of a
standard Gaussian vector, `P(f ≤ 𝔼 f - t) ≤ exp (-t² / (2 L²))`. -/
theorem stdGaussian_lipschitz_concentration_lower [Nonempty ι] {f : EuclideanSpace ℝ ι → ℝ}
    {L : ℝ≥0} (hL : 0 < L) (hf : LipschitzWith L f) (t : ℝ) (ht : 0 < t) :
    (stdGaussian (EuclideanSpace ℝ ι)
        {x | f x ≤ ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ ι) - t}).toReal ≤
      exp (-t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  have hneg : LipschitzWith L (fun x ↦ -f x) := hf.neg
  have h := stdGaussian_lipschitz_concentration_upper hL hneg t ht
  rw [integral_neg] at h
  convert h using 4
  ext x
  constructor <;> intro hx <;> linarith

/-- **Gaussian Lipschitz concentration, two-sided.** For an `L`-Lipschitz function `f` of a
standard Gaussian vector, `P(|f - 𝔼 f| ≥ t) ≤ 2 exp (-t² / (2 L²))`. -/
theorem stdGaussian_lipschitz_concentration [Nonempty ι] {f : EuclideanSpace ℝ ι → ℝ}
    {L : ℝ≥0} (hL : 0 < L) (hf : LipschitzWith L f) (t : ℝ) (ht : 0 < t) :
    (stdGaussian (EuclideanSpace ℝ ι)
        {x | t ≤ |f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ ι)|}).toReal ≤
      2 * exp (-t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  set μ := stdGaussian (EuclideanSpace ℝ ι)
  have h_sub : {x | t ≤ |f x - ∫ y, f y ∂μ|} ⊆
      {x | t ≤ f x - ∫ y, f y ∂μ} ∪ {x | f x ≤ ∫ y, f y ∂μ - t} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    rcases le_abs'.1 hx with h | h
    · right; linarith
    · left; exact h
  calc (μ {x | t ≤ |f x - ∫ y, f y ∂μ|}).toReal
      ≤ (μ {x | t ≤ f x - ∫ y, f y ∂μ}).toReal + (μ {x | f x ≤ ∫ y, f y ∂μ - t}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        exact ENNReal.toReal_mono (by finiteness)
          ((measure_mono h_sub).trans (measure_union_le _ _))
    _ ≤ exp (-t ^ 2 / (2 * (L : ℝ) ^ 2)) + exp (-t ^ 2 / (2 * (L : ℝ) ^ 2)) :=
        add_le_add (stdGaussian_lipschitz_concentration_upper hL hf t ht)
          (stdGaussian_lipschitz_concentration_lower hL hf t ht)
    _ = 2 * exp (-t ^ 2 / (2 * (L : ℝ) ^ 2)) := by ring

end GaussianLipConcen
