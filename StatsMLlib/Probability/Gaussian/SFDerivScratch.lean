import StatsMLlib.Analysis.LogSumExp
import StatsMLlib.Probability.Gaussian.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory ProbabilityTheory Real Finset

namespace GaussianMeasure

variable {n : ℕ}

noncomputable def interpPath (m : Fin n → ℝ) (t : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    Fin n → ℝ :=
  fun i ↦ √(1 - t) * (p.1 i - m i) + √t * (p.2 i - m i) + m i

variable [NeZero n] (νX νY : Measure (Fin n → ℝ)) [IsGaussian νX] [IsGaussian νY]
  {m : Fin n → ℝ} {β : ℝ}

noncomputable def interpLSE (m : Fin n → ℝ) (β t : ℝ) : ℝ :=
  ∫ p, logSumExp β (interpPath m t p) ∂(νX.prod νY)

omit [NeZero n] in
/-- Pointwise derivative of the interpolation path. -/
lemma hasDerivAt_interpPath (m : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) {s : ℝ}
    (hs : s ∈ Set.Ioo 0 1) :
    HasDerivAt (fun u ↦ interpPath m u p)
      (fun i ↦ (p.2 i - m i) / (2 * √s) - (p.1 i - m i) / (2 * √(1 - s))) s := by
  rw [hasDerivAt_pi]
  intro i
  have h1 : HasDerivAt (fun u : ℝ ↦ √(1 - u)) (1 / (2 * √(1 - s)) * (-1)) s :=
    (Real.hasDerivAt_sqrt (by linarith [hs.2])).comp s ((hasDerivAt_id s).const_sub 1)
  have h2 : HasDerivAt (fun u : ℝ ↦ √u) (1 / (2 * √s)) s :=
    Real.hasDerivAt_sqrt hs.1.ne'
  convert ((h1.mul_const (p.1 i - m i)).add (h2.mul_const (p.2 i - m i))).add_const (m i)
    using 1
  · rfl
  · ring

/-- The derivative of the interpolation, before integration by parts. -/
lemma hasDerivAt_interpLSE (m : Fin n → ℝ) (hβ : 0 < β) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    HasDerivAt (interpLSE νX νY m β)
      (∫ p, ∑ i, softmax β (interpPath m t p) i *
        ((p.2 i - m i) / (2 * √t) - (p.1 i - m i) / (2 * √(1 - t))) ∂(νX.prod νY)) t := by
  obtain ⟨ht0, ht1⟩ := ht
  set μ := νX.prod νY
  set F : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun s p ↦ logSumExp β (interpPath m s p)
  set F' : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun s p ↦
    ∑ i, softmax β (interpPath m s p) i *
      ((p.2 i - m i) / (2 * √s) - (p.1 i - m i) / (2 * √(1 - s)))
  set S : Set ℝ := Set.Ioo (t / 2) ((1 + t) / 2)
  have hS : ∀ s ∈ S, s ∈ Set.Ioo (0 : ℝ) 1 := fun s hs ↦
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hSn : S ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  have hint1 : ∀ i, Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.1 i - m i) μ := fun i ↦
    ((integrable_eval_of_isGaussian νX i).comp_fst νY).sub (integrable_const _)
  have hint2 : ∀ i, Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.2 i - m i) μ := fun i ↦
    ((integrable_eval_of_isGaussian νY i).comp_snd νX).sub (integrable_const _)
  have hcont : ∀ s, Continuous (fun p ↦ interpPath m s p) := fun s ↦ by
    unfold interpPath
    fun_prop
  have hLSE : Continuous (logSumExp (ι := Fin n) β) := continuous_iff_continuousAt.2 fun x ↦
    (hasFDerivAt_logSumExp hβ.ne' x).continuousAt
  have hF_meas : ∀ s, AEStronglyMeasurable (F s) μ := fun s ↦
    (hLSE.comp (hcont s)).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' t) μ := by
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_finsetSum _ fun i _ ↦ ?_
    exact (((contDiff_softmax β i).continuous).comp (hcont t)).mul (by fun_prop)
  have hF_int : Integrable (F t) μ := by
    have hg : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
        ∑ i, (|p.1 i - m i| + |p.2 i - m i| + |m i|) + log (Fintype.card (Fin n)) / β) μ :=
      (integrable_finsetSum _ fun i _ ↦
        ((hint1 i).abs.add (hint2 i).abs).add (integrable_const _)).add (integrable_const _)
    refine hg.mono' (hF_meas t) (ae_of_all _ fun p ↦ ?_)
    rw [Real.norm_eq_abs]
    refine (abs_logSumExp_le hβ _).trans (add_le_add_left (sum_le_sum fun i _ ↦ ?_) _)
    have h1 : √(1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have h2 : √t ≤ 1 := Real.sqrt_le_one.mpr ht1.le
    simp only [interpPath]
    calc |√(1 - t) * (p.1 i - m i) + √t * (p.2 i - m i) + m i|
        ≤ |√(1 - t) * (p.1 i - m i)| + |√t * (p.2 i - m i)| + |m i| := abs_add_three _ _ _
      _ ≤ |p.1 i - m i| + |p.2 i - m i| + |m i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
            abs_of_nonneg (Real.sqrt_nonneg _)]
          gcongr
          · exact mul_le_of_le_one_left (abs_nonneg _) h1
          · exact mul_le_of_le_one_left (abs_nonneg _) h2
  set bound : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p ↦
    ∑ i, (|p.2 i - m i| / (2 * √(t / 2)) + |p.1 i - m i| / (2 * √((1 - t) / 2)))
  have h_bound : ∀ p, ∀ s ∈ S, ‖F' s p‖ ≤ bound p := by
    intro p s hs
    have hst : 2 * √(t / 2) ≤ 2 * √s := by
      gcongr
      exact hs.1.le
    have hst' : 2 * √((1 - t) / 2) ≤ 2 * √(1 - s) := by
      gcongr
      linarith [hs.2]
    have ht2 : 0 < 2 * √(t / 2) := by positivity
    have ht2' : 0 < 2 * √((1 - t) / 2) := by
      have : 0 < (1 - t) / 2 := by linarith
      positivity
    rw [Real.norm_eq_abs]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
    set σ := softmax β (interpPath m s p) i
    have hσ0 : 0 < σ := softmax_pos β _ i
    have hσ1 : σ ≤ 1 := softmax_le_one β _ i
    rw [abs_mul, abs_of_pos hσ0]
    calc σ * |(p.2 i - m i) / (2 * √s) - (p.1 i - m i) / (2 * √(1 - s))|
        ≤ |(p.2 i - m i) / (2 * √s) - (p.1 i - m i) / (2 * √(1 - s))| :=
          mul_le_of_le_one_left (abs_nonneg _) hσ1
      _ ≤ |p.2 i - m i| / (2 * √s) + |p.1 i - m i| / (2 * √(1 - s)) := by
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_div, abs_div, abs_of_pos (ht2.trans_le hst), abs_of_pos (ht2'.trans_le hst')]
      _ ≤ _ := by
          gcongr
  have hbound_int : Integrable bound μ := integrable_finsetSum _ fun i _ ↦
    ((hint2 i).abs.div_const _).add ((hint1 i).abs.div_const _)
  have h_diff : ∀ p, ∀ s ∈ S, HasDerivAt (F · p) (F' s p) s := by
    intro p s hs
    have hd := (hasFDerivAt_logSumExp hβ.ne' (interpPath m s p)).comp_hasDerivAt s
      (hasDerivAt_interpPath m p (hS s hs))
    convert hd using 1
    · rfl
    · simp [F', _root_.sum_apply]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hSn
    (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas (ae_of_all _ h_bound) hbound_int
    (ae_of_all _ h_diff)).2

end GaussianMeasure
