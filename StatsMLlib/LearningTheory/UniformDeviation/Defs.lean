/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Notation

/-!
# Uniform Deviation

The empirical uniform deviation of a function class from its population expectations.

## Main definitions

* `uniformDeviation`: uniform deviation between empirical and population expectations.

## Main results

This module supplies the definition used by the downstream measurability and concentration bounds.
-/

noncomputable section

universe u v w

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {𝒳 : Type w}

/-- The largest absolute difference between empirical and population expectations over a function
class. -/
def uniformDeviation (n : ℕ) (f : ι → 𝒳 → ℝ) (μ : Measure Ω) (X : Ω → 𝒳)
    (S : Fin n → 𝒳) : ℝ :=
  ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, f i (S k) - μ[fun ω' ↦ f i (X ω')]|

end
