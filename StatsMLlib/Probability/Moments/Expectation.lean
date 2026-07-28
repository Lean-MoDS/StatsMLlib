/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Expectation Inequalities

Elementary bounds for expectations of almost-everywhere bounded random variables.

## Main definitions

This module introduces no new definitions.

## Main results

* `norm_expectation_le_of_norm_le_const`: bounds the norm of an expectation.
* `abs_expectation_le_of_abs_le_const`: scalar specialization using absolute values.
-/

open MeasureTheory ProbabilityTheory


variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma norm_expectation_le_of_norm_le_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : Ω → E} {C : ℝ} (h : ∀ᵐ (x : Ω) ∂μ, ‖f x‖ ≤ C) :
  ‖μ[f]‖ ≤ C := by
  calc
    _ ≤ C * (μ Set.univ).toReal := by apply norm_integral_le_of_norm_le_const h
    _ = _ := by
      have : μ (Set.univ : Set Ω) = 1 := isProbabilityMeasure_iff.mp (by assumption)
      rw [this]
      simp

lemma abs_expectation_le_of_abs_le_const
  {f : Ω → ℝ} {C : ℝ} (h : ∀ᵐ (x : Ω) ∂μ, |f x| ≤ C) :
  |μ[f]| ≤ C := by
  exact @norm_expectation_le_of_norm_le_const Ω _ _ _ ℝ _ _ f C h
