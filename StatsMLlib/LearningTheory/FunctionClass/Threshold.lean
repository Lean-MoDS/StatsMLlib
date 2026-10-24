/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.LearningTheory.UniformDeviation.Confidence

/-!
# Threshold classifiers on the real line

The class of threshold classifiers `x ↦ 1[x ≤ t]`, indexed by `t : ℝ`, is the basic 0-1 loss
class that is not continuous in its parameter, so no topology on the index space reduces its
suprema to a countable subclass.  It is nevertheless pointwise separable: approximating `t` from
above by rationals converges at every input, including `x = t`.

Its uniform deviation `sup_t |Fₙ(t) - F(t)|` is the Kolmogorov–Smirnov distance between the
empirical and population distribution functions, so the endpoint below is a
Rademacher-complexity form of the Glivenko–Cantelli theorem.

## Main definitions

* `thresholdClass`: the threshold classifiers `x ↦ 1[x ≤ t]`.

## Main results

* `pointwiseSeparable_thresholdClass`: the class is pointwise separable.
* `threshold_uniform_deviation_tail_bound_of_empirical_le_delta`: a confidence bound on the
  Kolmogorov–Smirnov distance from a fixed-sample Rademacher bound.
-/

open Filter Topology MeasureTheory ProbabilityTheory

universe u

variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/-- The threshold classifier `x ↦ 1[x ≤ t]`. -/
noncomputable def thresholdClass (t x : ℝ) : ℝ :=
  if x ≤ t then 1 else 0

lemma abs_thresholdClass_le (t x : ℝ) : |thresholdClass t x| ≤ 1 := by
  unfold thresholdClass
  split_ifs <;> norm_num

lemma measurable_thresholdClass (t : ℝ) : Measurable (thresholdClass t) :=
  Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

/--
Threshold classifiers form a pointwise separable class: rationals `r m` decreasing to `t` give
`1[x ≤ r m] → 1[x ≤ t]` at every input `x`.
-/
theorem pointwiseSeparable_thresholdClass : PointwiseSeparable thresholdClass := by
  obtain ⟨q, hq⟩ := exists_surjective_nat ℚ
  refine ⟨fun m ↦ (q m : ℝ), fun t ↦ ?_⟩
  have hr : ∀ m : ℕ, ∃ r : ℚ, t < r ∧ (r : ℝ) < t + 1 / ((m : ℝ) + 1) := fun m ↦
    exists_rat_btwn (lt_add_of_pos_right t (by positivity))
  choose r hr_gt hr_lt using hr
  choose u hu using fun m ↦ hq (r m)
  refine ⟨u, fun x ↦ ?_⟩
  simp only [hu]
  by_cases hx : x ≤ t
  · have h1 : (fun m ↦ thresholdClass (r m) x) = fun _ ↦ 1 :=
      funext fun m ↦ by simp [thresholdClass, hx.trans (hr_gt m).le]
    rw [h1, show thresholdClass t x = 1 by simp [thresholdClass, hx]]
    exact tendsto_const_nhds
  · have hxt : t < x := lt_of_not_ge hx
    have hlim : Tendsto (fun m ↦ (r m : ℝ)) atTop (𝓝 t) := by
      have hupper : Tendsto (fun m : ℕ ↦ t + 1 / ((m : ℝ) + 1)) atTop (𝓝 t) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add t
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
        (fun m ↦ (hr_gt m).le) (fun m ↦ (hr_lt m).le)
    have hev : ∀ᶠ m in atTop, (r m : ℝ) < x := hlim.eventually (gt_mem_nhds hxt)
    rw [show thresholdClass t x = 0 by simp [thresholdClass, hx]]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with m hm
    simp [thresholdClass, not_le.mpr hm]

/--
Confidence bound on the Kolmogorov–Smirnov distance `sup_t |Fₙ(t) - F(t)|` from a fixed-sample
bound `C` on the empirical Rademacher complexity of threshold classifiers.
-/
theorem threshold_uniform_deviation_tail_bound_of_empirical_le_delta
    [IsProbabilityMeasure μ] (hn : 0 < n)
    (X : Ω → ℝ) (hX : Measurable X)
    {C δ : ℝ} (hC : ∀ S : Fin n → ℝ, empiricalRademacherComplexity n thresholdClass S ≤ C)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * C + Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n thresholdClass μ X (X ∘ S)}).toReal ≤ δ := by
  simpa only [one_mul] using
    uniform_deviation_tail_bound_pointwiseSeparable_of_empirical_le_delta
      (μ := μ) hn thresholdClass measurable_thresholdClass X hX one_pos
      abs_thresholdClass_le pointwiseSeparable_thresholdClass hC hδ hδ_one

/-! ## Examples

Worked uses of this module's public API. They are elaborated with the library, so they
double as acceptance tests that these statements stay usable as written.
-/

/-- The Kolmogorov–Smirnov confidence bound for threshold classifiers. -/
example [IsProbabilityMeasure μ] (hn : 0 < n) (X : Ω → ℝ) (hX : Measurable X)
    {C δ : ℝ} (hC : ∀ S : Fin n → ℝ, empiricalRademacherComplexity n thresholdClass S ≤ C)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * C + Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n thresholdClass μ X (X ∘ S)}).toReal ≤ δ :=
  threshold_uniform_deviation_tail_bound_of_empirical_le_delta hn X hX hC hδ hδ_one
