/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Analysis.LogSumExp
import StatsMLlib.Probability.Gaussian.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Sudakov–Fernique inequality

Let `ν_X` and `ν_Y` be Gaussian measures on `ℝⁿ` with the same mean, and write
`γ^X_ij = ∫ (xᵢ - xⱼ)² dν_X` and `γ^Y_ij = ∫ (yᵢ - yⱼ)² dν_Y` for their increment second moments.
This file compares the expected maxima `∫ max x dν_X` and `∫ max y dν_Y`:

* if `γ^X_ij ≤ γ^Y_ij` for all `i, j`, then `∫ max dν_X ≤ ∫ max dν_Y` (Sudakov–Fernique);
* in general, `|∫ max dν_X - ∫ max dν_Y| ≤ √(γ log n)` whenever `|γ^X_ij - γ^Y_ij| ≤ γ` for all
  `i, j`.

The proof follows [Chatterjee2005]. The maximum is replaced by the log-sum-exp function `F_β`.
Along the interpolation `Z_t = √(1 - t) (X - m) + √t (Y - m) + m` with `X` and `Y` independent,
Gaussian integration by parts expresses the derivative of `t ↦ 𝔼[F_β(Z_t)]` as
`(β / 4) 𝔼[∑ᵢⱼ pᵢ(Z_t) pⱼ(Z_t) (γ^Y_ij - γ^X_ij)]`, where `p` is the softmax vector.

Independence of `X` and `Y` is expressed by integrating over the product measure `ν_X.prod ν_Y`.

## Main definitions

* `GaussianMeasure.incrSq ν i j`: the increment second moment `∫ (xᵢ - xⱼ)² dν`.
* `GaussianMeasure.interpPath m t p`: the interpolation `√(1 - t) (x - m) + √t (y - m) + m`.

## Main results

* `GaussianMeasure.integral_sup'_le_of_incrSq_le`: the Sudakov–Fernique inequality.
* `GaussianMeasure.abs_integral_sup'_sub_le`: the quantitative comparison
  `|∫ max dν_X - ∫ max dν_Y| ≤ √(γ log n)`.
-/

open MeasureTheory ProbabilityTheory Real Finset

namespace GaussianMeasure

variable {n : ℕ}

/-- The increment second moment `∫ (xᵢ - xⱼ)² dν`. -/
noncomputable def incrSq (ν : Measure (Fin n → ℝ)) (i j : Fin n) : ℝ :=
  ∫ x, (x i - x j) ^ 2 ∂ν

/-- The interpolation path `√(1 - t) (x - m) + √t (y - m) + m` at the point `p = (x, y)`. -/
noncomputable def interpPath (m : Fin n → ℝ) (t : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    Fin n → ℝ :=
  fun i ↦ √(1 - t) * (p.1 i - m i) + √t * (p.2 i - m i) + m i

/-- The Hessian of log-sum-exp, `β (δᵢⱼ pᵢ - pᵢ pⱼ)`. -/
noncomputable def hessLSE (β : ℝ) (z : Fin n → ℝ) (i j : Fin n) : ℝ :=
  β * (softmax β z i * (if i = j then 1 else 0) - softmax β z i * softmax β z j)

lemma integral_eval_eq_of_integral_eq (ν : Measure (Fin n → ℝ)) [IsGaussian ν]
    {m : Fin n → ℝ} (hm : ∫ x, x ∂ν = m) (i : Fin n) : ∫ x, x i ∂ν = m i := by
  rw [← hm]
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i).integral_comp_comm
    IsGaussian.integrable_id

/-- The increment second moment in terms of the covariance matrix and the mean. -/
lemma covMatrix_add_sub_eq_incrSq (ν : Measure (Fin n → ℝ)) [IsGaussian ν]
    {m : Fin n → ℝ} (hm : ∫ x, x ∂ν = m) (i j : Fin n) :
    covMatrix ν i i + covMatrix ν j j - 2 * covMatrix ν i j = incrSq ν i j - (m i - m j) ^ 2 := by
  have hmem : ∀ k, MemLp (fun x : Fin n → ℝ ↦ x k) 2 ν := fun k ↦
    IsGaussian.memLp_dual ν (ContinuousLinearMap.proj k) 2 (by simp)
  have hvar := variance_fun_sub (hmem i) (hmem j)
  have hdiff : MemLp (fun x : Fin n → ℝ ↦ x i - x j) 2 ν := (hmem i).sub (hmem j)
  have hvar2 := variance_eq_sub hdiff
  have hmean : ∫ x, (x i - x j) ∂ν = m i - m j := by
    rw [integral_sub (integrable_eval_of_isGaussian ν i) (integrable_eval_of_isGaussian ν j),
      integral_eval_eq_of_integral_eq ν hm, integral_eval_eq_of_integral_eq ν hm]
  rw [covMatrix_apply, covMatrix_apply, covMatrix_apply,
    covariance_self (measurable_pi_apply i).aemeasurable,
    covariance_self (measurable_pi_apply j).aemeasurable, incrSq]
  simp only [Pi.pow_apply] at hvar2
  rw [hmean] at hvar2
  linarith

lemma abs_hessLSE_le (β : ℝ) (z : Fin n → ℝ) (i j : Fin n) [NeZero n] :
    |hessLSE β z i j| ≤ 2 * |β| := by
  have hi := softmax_pos β z i
  have hi1 := softmax_le_one β z i
  have hj := softmax_pos β z j
  have hj1 := softmax_le_one β z j
  rw [hessLSE, abs_mul, mul_comm 2]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
  rw [abs_le]
  split_ifs <;> constructor <;> nlinarith [mul_pos hi hj]

lemma continuous_hessLSE (β : ℝ) (i j : Fin n) [NeZero n] :
    Continuous fun z : Fin n → ℝ ↦ hessLSE β z i j := by
  have hc : ∀ k, Continuous fun z : Fin n → ℝ ↦ softmax β z k := fun k ↦
    (contDiff_softmax β k).continuous
  unfold hessLSE
  fun_prop

/-- Gaussian integration by parts for `x ↦ softmax β (a (x - m) + c) i`. -/
lemma integral_softmax_affine_mul (ν : Measure (Fin n → ℝ)) [IsGaussian ν] [NeZero n]
    {m : Fin n → ℝ} (hm : ∫ x, x ∂ν = m) {β : ℝ} (hβ : β ≠ 0) (a : ℝ) (c : Fin n → ℝ)
    (i : Fin n) :
    ∫ x, softmax β (a • (x - m) + c) i * (x i - m i) ∂ν =
      a * ∑ j, covMatrix ν i j * ∫ x, hessLSE β (a • (x - m) + c) i j ∂ν := by
  set A : (Fin n → ℝ) → (Fin n → ℝ) := fun x ↦ a • (x - m) + c with hA_def
  have hAd : ∀ x, HasFDerivAt A (a • ContinuousLinearMap.id ℝ (Fin n → ℝ)) x := fun x ↦ by
    have := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const m).const_smul a).add_const c
    simpa [hA_def] using this
  have hsd : Differentiable ℝ fun z : Fin n → ℝ ↦ softmax β z i :=
    (contDiff_softmax β i).differentiable one_ne_zero
  set H : (Fin n → ℝ) → ℝ := fun x ↦ softmax β (A x) i with hH_def
  have hHd : ∀ x, HasFDerivAt H
      ((fderiv ℝ (fun z ↦ softmax β z i) (A x)).comp (a • ContinuousLinearMap.id ℝ _)) x :=
    fun x ↦ (hsd (A x)).hasFDerivAt.comp x (hAd x)
  have hH : ContDiff ℝ 1 H := by
    have hA : ContDiff ℝ 1 A := by
      rw [hA_def]
      fun_prop
    exact (contDiff_softmax β i).comp hA
  have hM : ∀ x, ‖fderiv ℝ H x‖ ≤ 2 * |β| * |a| := fun x ↦ by
    rw [(hHd x).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul (norm_fderiv_softmax_le hβ _ i) ?_ (norm_nonneg _) (by positivity)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg a) ContinuousLinearMap.norm_id_le
  have hderiv : ∀ x j, fderiv ℝ H x (Pi.single j 1) = a * hessLSE β (A x) i j := fun x j ↦ by
    classical
    rw [(hHd x).fderiv, ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, fderiv_softmax_single hβ, smul_eq_mul, hessLSE]
  have key := integral_sub_mul_eq_sum_covMatrix ν hm hH hM i
  simp_rw [hderiv, integral_const_mul] at key
  rw [mul_sum]
  simp_rw [← mul_assoc, mul_comm a, mul_assoc]
  rw [← key]
  exact integral_congr_ae (ae_of_all _ fun x ↦ mul_comm _ _)

section Interpolation

variable [NeZero n] (νX νY : Measure (Fin n → ℝ)) [IsGaussian νX] [IsGaussian νY]
  {m : Fin n → ℝ} {β : ℝ}

/-- The interpolated log-sum-exp expectation `t ↦ ∫ F_β(Z_t) d(ν_X ⊗ ν_Y)`. -/
noncomputable def interpLSE (m : Fin n → ℝ) (β t : ℝ) : ℝ :=
  ∫ p, logSumExp β (interpPath m t p) ∂(νX.prod νY)

omit [NeZero n] in
lemma interpLSE_zero (m : Fin n → ℝ) (β : ℝ) :
    interpLSE νX νY m β 0 = ∫ x, logSumExp β x ∂νX := by
  have h : ∀ p : (Fin n → ℝ) × (Fin n → ℝ), interpPath m 0 p = p.1 := fun p ↦ by
    funext i
    simp [interpPath]
  simp_rw [interpLSE, h]
  rw [integral_fun_fst, probReal_univ, one_smul]

omit [NeZero n] in
lemma interpLSE_one (m : Fin n → ℝ) (β : ℝ) :
    interpLSE νX νY m β 1 = ∫ y, logSumExp β y ∂νY := by
  have h : ∀ p : (Fin n → ℝ) × (Fin n → ℝ), interpPath m 1 p = p.2 := fun p ↦ by
    funext i
    simp [interpPath]
  simp_rw [interpLSE, h]
  rw [integral_fun_snd, probReal_univ, one_smul]

omit [NeZero n] in
lemma continuous_interpPath (m : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    Continuous fun t ↦ interpPath m t p :=
  continuous_pi fun i ↦ by
    unfold interpPath
    fun_prop

omit [NeZero n] in
lemma continuous_interpPath_right (m : Fin n → ℝ) (t : ℝ) :
    Continuous (interpPath m t) :=
  continuous_pi fun i ↦ by
    unfold interpPath
    fun_prop

lemma continuous_logSumExp (hβ : 0 < β) : Continuous (logSumExp (ι := Fin n) β) :=
  continuous_iff_continuousAt.2 fun x ↦ (hasFDerivAt_logSumExp hβ.ne' x).continuousAt

/-- A dominating function for the interpolated log-sum-exp on `[0, 1]`. -/
noncomputable def interpBound (m : Fin n → ℝ) (β : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ i, (|p.1 i - m i| + |p.2 i - m i| + |m i|) + log n / β

lemma abs_logSumExp_interpPath_le (hβ : 0 < β) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    |logSumExp β (interpPath m t p)| ≤ interpBound m β p := by
  refine (abs_logSumExp_le hβ _).trans ?_
  rw [Fintype.card_fin, interpBound]
  gcongr with i
  have h1 : √(1 - t) ≤ 1 := Real.sqrt_le_one.2 (by linarith [ht.1])
  have h2 : √t ≤ 1 := Real.sqrt_le_one.2 ht.2
  calc |√(1 - t) * (p.1 i - m i) + √t * (p.2 i - m i) + m i|
      ≤ √(1 - t) * |p.1 i - m i| + √t * |p.2 i - m i| + |m i| := by
        have := abs_add_le (√(1 - t) * (p.1 i - m i)) (√t * (p.2 i - m i))
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _)] at this
        linarith [abs_add_le (√(1 - t) * (p.1 i - m i) + √t * (p.2 i - m i)) (m i)]
    _ ≤ |p.1 i - m i| + |p.2 i - m i| + |m i| := by
        gcongr
        · exact mul_le_of_le_one_left (abs_nonneg _) h1
        · exact mul_le_of_le_one_left (abs_nonneg _) h2

omit [NeZero n] in
lemma integrable_interpBound (m : Fin n → ℝ) (β : ℝ) :
    Integrable (interpBound m β) (νX.prod νY) := by
  refine (integrable_finsetSum _ fun i _ ↦ ?_).add (integrable_const _)
  refine ((((integrable_eval_of_isGaussian νX i).sub (integrable_const (m i))).abs.comp_fst
    νY).add ?_).add (integrable_const _)
  exact ((integrable_eval_of_isGaussian νY i).sub (integrable_const (m i))).abs.comp_snd νX

lemma continuousOn_interpLSE (m : Fin n → ℝ) (hβ : 0 < β) :
    ContinuousOn (interpLSE νX νY m β) (Set.Icc 0 1) := by
  refine continuousOn_of_dominated (bound := interpBound m β) (fun t _ ↦ ?_)
    (fun t ht ↦ ae_of_all _ fun p ↦ ?_) (integrable_interpBound νX νY m β)
    (ae_of_all _ fun p ↦ ?_)
  · exact ((continuous_logSumExp hβ).comp
      (continuous_interpPath_right m t)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_logSumExp_interpPath_le hβ ht p
  · exact ((continuous_logSumExp hβ).comp (continuous_interpPath m p)).continuousOn

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

lemma integrable_hessLSE_interp (m : Fin n → ℝ) (β t : ℝ) (i j : Fin n) :
    Integrable (fun p ↦ hessLSE β (interpPath m t p) i j) (νX.prod νY) :=
  (integrable_const (2 * |β|)).mono'
    ((continuous_hessLSE β i j).comp (continuous_interpPath_right m t)).aestronglyMeasurable
    (ae_of_all _ fun p ↦ by simpa [Real.norm_eq_abs] using abs_hessLSE_le β _ i j)

lemma norm_softmax_le_one (β : ℝ) (z : Fin n → ℝ) (i : Fin n) : ‖softmax β z i‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (softmax_pos β z i)]
  exact softmax_le_one β z i

lemma integrable_softmax_interp_mul_fst (m : Fin n → ℝ) (β t : ℝ) (i : Fin n) :
    Integrable (fun p ↦ softmax β (interpPath m t p) i * (p.1 i - m i)) (νX.prod νY) :=
  (((integrable_eval_of_isGaussian νX i).sub (integrable_const (m i))).comp_fst νY).bdd_mul
    ((contDiff_softmax β i).continuous.comp (continuous_interpPath_right m t)).aestronglyMeasurable
    (ae_of_all _ fun _ ↦ norm_softmax_le_one β _ i)

lemma integrable_softmax_interp_mul_snd (m : Fin n → ℝ) (β t : ℝ) (i : Fin n) :
    Integrable (fun p ↦ softmax β (interpPath m t p) i * (p.2 i - m i)) (νX.prod νY) :=
  (((integrable_eval_of_isGaussian νY i).sub (integrable_const (m i))).comp_snd νX).bdd_mul
    ((contDiff_softmax β i).continuous.comp (continuous_interpPath_right m t)).aestronglyMeasurable
    (ae_of_all _ fun _ ↦ norm_softmax_le_one β _ i)

/-- Gaussian integration by parts in the `x` variable along the interpolation. -/
lemma integral_softmax_mul_fst (hmX : ∫ x, x ∂νX = m) (hβ : 0 < β) (t : ℝ) (i : Fin n) :
    ∫ p, softmax β (interpPath m t p) i * (p.1 i - m i) ∂(νX.prod νY) =
      √(1 - t) * ∑ j, covMatrix νX i j * ∫ p, hessLSE β (interpPath m t p) i j ∂(νX.prod νY) := by
  set c : (Fin n → ℝ) → Fin n → ℝ := fun y k ↦ √t * (y k - m k) + m k
  have hZ : ∀ x y, interpPath m t (x, y) = √(1 - t) • (x - m) + c y := fun x y ↦ by
    funext k
    simp only [interpPath, c, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hint2 := integrable_hessLSE_interp νX νY m β t i
  have hint1 := integrable_softmax_interp_mul_fst νX νY m β t i
  calc ∫ p, softmax β (interpPath m t p) i * (p.1 i - m i) ∂(νX.prod νY)
      = ∫ y, ∫ x, softmax β (√(1 - t) • (x - m) + c y) i * (x i - m i) ∂νX ∂νY := by
        rw [integral_prod_symm _ hint1]
        simp only [hZ]
    _ = ∫ y, √(1 - t) * ∑ j, covMatrix νX i j *
          ∫ x, hessLSE β (√(1 - t) • (x - m) + c y) i j ∂νX ∂νY :=
        integral_congr_ae (ae_of_all _ fun y ↦
          integral_softmax_affine_mul νX hmX hβ.ne' _ _ i)
    _ = √(1 - t) * ∑ j, covMatrix νX i j *
          ∫ y, ∫ x, hessLSE β (√(1 - t) • (x - m) + c y) i j ∂νX ∂νY := by
        rw [integral_const_mul, integral_finsetSum]
        · simp_rw [integral_const_mul]
        · intro j _
          have := ((hint2 j).integral_prod_right).const_mul (covMatrix νX i j)
          simpa only [hZ] using this
    _ = _ := by
        congr 1
        refine sum_congr rfl fun j _ ↦ ?_
        rw [integral_prod_symm _ (hint2 j)]
        simp only [hZ]

/-- Gaussian integration by parts in the `y` variable along the interpolation. -/
lemma integral_softmax_mul_snd (hmY : ∫ y, y ∂νY = m) (hβ : 0 < β) (t : ℝ) (i : Fin n) :
    ∫ p, softmax β (interpPath m t p) i * (p.2 i - m i) ∂(νX.prod νY) =
      √t * ∑ j, covMatrix νY i j * ∫ p, hessLSE β (interpPath m t p) i j ∂(νX.prod νY) := by
  set c : (Fin n → ℝ) → Fin n → ℝ := fun x k ↦ √(1 - t) * (x k - m k) + m k
  have hZ : ∀ x y, interpPath m t (x, y) = √t • (y - m) + c x := fun x y ↦ by
    funext k
    simp only [interpPath, c, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hint2 := integrable_hessLSE_interp νX νY m β t i
  have hint1 := integrable_softmax_interp_mul_snd νX νY m β t i
  calc ∫ p, softmax β (interpPath m t p) i * (p.2 i - m i) ∂(νX.prod νY)
      = ∫ x, ∫ y, softmax β (√t • (y - m) + c x) i * (y i - m i) ∂νY ∂νX := by
        rw [integral_prod _ hint1]
        simp only [hZ]
    _ = ∫ x, √t * ∑ j, covMatrix νY i j *
          ∫ y, hessLSE β (√t • (y - m) + c x) i j ∂νY ∂νX :=
        integral_congr_ae (ae_of_all _ fun x ↦
          integral_softmax_affine_mul νY hmY hβ.ne' _ _ i)
    _ = √t * ∑ j, covMatrix νY i j *
          ∫ x, ∫ y, hessLSE β (√t • (y - m) + c x) i j ∂νY ∂νX := by
        rw [integral_const_mul, integral_finsetSum]
        · simp_rw [integral_const_mul]
        · intro j _
          have := ((hint2 j).integral_prod_left).const_mul (covMatrix νY i j)
          simpa only [hZ] using this
    _ = _ := by
        congr 1
        refine sum_congr rfl fun j _ ↦ ?_
        rw [integral_prod _ (hint2 j)]
        simp only [hZ]

/-- The derivative of the interpolation after integration by parts. -/
lemma deriv_interpLSE_eq (hmX : ∫ x, x ∂νX = m) (hmY : ∫ y, y ∂νY = m) (hβ : 0 < β)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    ∫ p, ∑ i, softmax β (interpPath m t p) i *
        ((p.2 i - m i) / (2 * √t) - (p.1 i - m i) / (2 * √(1 - t))) ∂(νX.prod νY) =
      β / 4 * ∫ p, ∑ i, ∑ j, softmax β (interpPath m t p) i * softmax β (interpPath m t p) j *
        (incrSq νY i j - incrSq νX i j) ∂(νX.prod νY) := by
  have hst : 0 < √t := Real.sqrt_pos.2 ht.1
  have hst' : 0 < √(1 - t) := Real.sqrt_pos.2 (by linarith [ht.2])
  set Δ : Fin n → Fin n → ℝ := fun i j ↦ covMatrix νY i j - covMatrix νX i j with hΔ
  -- contraction of the Hessian with `Δ`, pointwise
  have hpt : ∀ p, ∑ i, ∑ j, hessLSE β (interpPath m t p) i j * Δ i j =
      β / 2 * ∑ i, ∑ j, softmax β (interpPath m t p) i * softmax β (interpPath m t p) j *
        (incrSq νY i j - incrSq νX i j) := by
    intro p
    set q := softmax β (interpPath m t p)
    have hδ : ∀ i, ∑ j, q i * (if i = j then 1 else 0) * Δ i j = q i * Δ i i := fun i ↦ by
      simp [mul_ite]
    have hexp : ∑ i, ∑ j, hessLSE β (interpPath m t p) i j * Δ i j =
        β * (∑ i, q i * Δ i i - ∑ i, ∑ j, q i * q j * Δ i j) := by
      simp only [hessLSE, ← hδ, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
    have hincr : ∀ i j, Δ i i + Δ j j - 2 * Δ i j = incrSq νY i j - incrSq νX i j := by
      intro i j
      have hY := covMatrix_add_sub_eq_incrSq νY hmY i j
      have hX := covMatrix_add_sub_eq_incrSq νX hmX i j
      simp only [hΔ]
      linarith
    rw [hexp, sum_mul_sub_sum_mul_eq q (sum_softmax β _) Δ]
    simp only [hincr]
    ring
  have hI : ∀ i j, Integrable (fun p ↦ hessLSE β (interpPath m t p) i j * Δ i j)
      (νX.prod νY) := fun i j ↦ (integrable_hessLSE_interp νX νY m β t i j).mul_const _
  -- expand the left-hand side and integrate by parts
  calc ∫ p, ∑ i, softmax β (interpPath m t p) i *
          ((p.2 i - m i) / (2 * √t) - (p.1 i - m i) / (2 * √(1 - t))) ∂(νX.prod νY)
      = ∑ i, ((∫ p, softmax β (interpPath m t p) i * (p.2 i - m i) ∂(νX.prod νY)) / (2 * √t) -
          (∫ p, softmax β (interpPath m t p) i * (p.1 i - m i) ∂(νX.prod νY)) /
            (2 * √(1 - t))) := by
        rw [integral_finsetSum]
        · refine sum_congr rfl fun i _ ↦ ?_
          rw [← integral_div, ← integral_div, ← integral_sub]
          · exact integral_congr_ae (ae_of_all _ fun p ↦ by ring)
          · exact (integrable_softmax_interp_mul_snd νX νY m β t i).div_const _
          · exact (integrable_softmax_interp_mul_fst νX νY m β t i).div_const _
        · intro i _
          refine (((integrable_softmax_interp_mul_snd νX νY m β t i).div_const (2 * √t)).sub
            ((integrable_softmax_interp_mul_fst νX νY m β t i).div_const
              (2 * √(1 - t)))).congr (ae_of_all _ fun p ↦ ?_)
          simp only [Pi.sub_apply]
          ring
    _ = ∑ i, ∑ j, (1 / 2) * ∫ p, hessLSE β (interpPath m t p) i j * Δ i j ∂(νX.prod νY) := by
        refine sum_congr rfl fun i _ ↦ ?_
        rw [integral_softmax_mul_snd νX νY hmY hβ t i, integral_softmax_mul_fst νX νY hmX hβ t i]
        rw [mul_comm 2 √t, mul_div_mul_left _ _ hst.ne', mul_comm 2 √(1 - t),
          mul_div_mul_left _ _ hst'.ne', ← sub_div, ← sum_sub_distrib, sum_div]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [integral_mul_const]
        simp only [hΔ]
        ring
    _ = (1 / 2) * ∫ p, ∑ i, ∑ j, hessLSE β (interpPath m t p) i j * Δ i j ∂(νX.prod νY) := by
        rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hI i j, mul_sum]
        refine sum_congr rfl fun i _ ↦ ?_
        rw [integral_finsetSum _ fun j _ ↦ hI i j, mul_sum]
    _ = _ := by
        simp_rw [hpt]
        rw [integral_const_mul]
        ring

end Interpolation

section Main

variable [NeZero n] {νX νY : Measure (Fin n → ℝ)} [IsGaussian νX] [IsGaussian νY]
  {m : Fin n → ℝ}

omit [NeZero n] in
lemma integrable_sum_abs_eval (ν : Measure (Fin n → ℝ)) [IsGaussian ν] :
    Integrable (fun x : Fin n → ℝ ↦ ∑ i, |x i|) ν :=
  integrable_finsetSum _ fun i _ ↦ (integrable_eval_of_isGaussian ν i).abs

/-- `x ↦ max x` is integrable under a Gaussian measure. -/
lemma integrable_sup' (ν : Measure (Fin n → ℝ)) [IsGaussian ν] :
    Integrable (fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x) ν := by
  refine (integrable_sum_abs_eval ν).mono' ?_ (ae_of_all _ fun x ↦ ?_)
  · exact (Continuous.finset_sup'_apply univ_nonempty fun i _ ↦ continuous_apply i)
      |>.aestronglyMeasurable
  · obtain ⟨k, -, hk⟩ := exists_mem_eq_sup' univ_nonempty x
    rw [Real.norm_eq_abs, hk]
    exact single_le_sum (f := fun i ↦ |x i|) (fun i _ ↦ abs_nonneg _) (mem_univ k)

lemma integral_sup'_add_const (ν : Measure (Fin n → ℝ)) [IsGaussian ν] (c : ℝ) :
    ∫ x, (univ.sup' univ_nonempty x + c) ∂ν = ∫ x, univ.sup' univ_nonempty x ∂ν + c := by
  rw [integral_add (integrable_sup' ν) (integrable_const c), integral_const]
  simp

/-- `F_β` is integrable under a Gaussian measure. -/
lemma integrable_logSumExp (ν : Measure (Fin n → ℝ)) [IsGaussian ν] {β : ℝ} (hβ : 0 < β) :
    Integrable (logSumExp β) ν := by
  refine ((integrable_sum_abs_eval ν).add (integrable_const (log n / β))).mono' ?_
    (ae_of_all _ fun x ↦ ?_)
  · exact (continuous_iff_continuousAt.2 fun x ↦
      (hasFDerivAt_logSumExp hβ.ne' x).continuousAt).aestronglyMeasurable
  · simpa [Real.norm_eq_abs, Fintype.card_fin] using abs_logSumExp_le hβ x

/-- For every `β > 0`, `∫ F_β dν_X ≤ ∫ F_β dν_Y` under the Sudakov–Fernique hypothesis. -/
lemma integral_logSumExp_le (hmX : ∫ x, x ∂νX = m) (hmY : ∫ y, y ∂νY = m)
    (h : ∀ i j, incrSq νX i j ≤ incrSq νY i j) {β : ℝ} (hβ : 0 < β) :
    ∫ x, logSumExp β x ∂νX ≤ ∫ y, logSumExp β y ∂νY := by
  rw [← interpLSE_zero νX νY m β, ← interpLSE_one νX νY m β]
  have hmono : MonotoneOn (interpLSE νX νY m β) (Set.Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (continuousOn_interpLSE νX νY m hβ) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    · rw [interior_Icc] at ht
      exact (hasDerivAt_interpLSE νX νY m hβ ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hasDerivAt_interpLSE νX νY m hβ ht).deriv, deriv_interpLSE_eq νX νY hmX hmY hβ ht]
      refine mul_nonneg (by positivity) (integral_nonneg fun p ↦ ?_)
      refine sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ ?_
      exact mul_nonneg (mul_nonneg (softmax_pos β _ i).le (softmax_pos β _ j).le)
        (sub_nonneg.2 (h i j))
  exact hmono (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one

/-- For every `β > 0`, `|∫ F_β dν_X - ∫ F_β dν_Y| ≤ β γ / 4`. -/
lemma abs_integral_logSumExp_sub_le (hmX : ∫ x, x ∂νX = m) (hmY : ∫ y, y ∂νY = m)
    {γ : ℝ} (h : ∀ i j, |incrSq νX i j - incrSq νY i j| ≤ γ) {β : ℝ} (hβ : 0 < β) :
    |∫ x, logSumExp β x ∂νX - ∫ y, logSumExp β y ∂νY| ≤ β * γ / 4 := by
  rw [← interpLSE_zero νX νY m β, ← interpLSE_one νX νY m β, abs_sub_comm]
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (interpLSE νX νY m β) _ zero_lt_one
    (continuousOn_interpLSE νX νY m hβ) fun t ht ↦ hasDerivAt_interpLSE νX νY m hβ ht
  rw [sub_zero, div_one] at hslope
  rw [← hslope, deriv_interpLSE_eq νX νY hmX hmY hβ hc, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < β / 4)]
  have hbound : ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
      ‖∑ i, ∑ j, softmax β (interpPath m c p) i * softmax β (interpPath m c p) j *
        (incrSq νY i j - incrSq νX i j)‖ ≤ γ := by
    intro p
    set q := softmax β (interpPath m c p)
    calc ‖∑ i, ∑ j, q i * q j * (incrSq νY i j - incrSq νX i j)‖
        ≤ ∑ i, ∑ j, q i * q j * γ := by
          rw [Real.norm_eq_abs]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
          have hq : 0 ≤ q i * q j := mul_nonneg (softmax_pos β _ i).le (softmax_pos β _ j).le
          rw [abs_mul, abs_of_nonneg hq, abs_sub_comm]
          exact mul_le_mul_of_nonneg_left (h i j) hq
      _ = γ := by
          have hq : ∑ i, q i = 1 := sum_softmax β _
          rw [show (∑ i, ∑ j, q i * q j * γ) = (∑ i, q i) * ((∑ j, q j) * γ) by
            rw [sum_mul]
            refine sum_congr rfl fun i _ ↦ ?_
            rw [sum_mul, mul_sum]
            exact sum_congr rfl fun j _ ↦ by ring, hq]
          ring
  have := norm_integral_le_of_norm_le_const (μ := νX.prod νY) (ae_of_all _ hbound)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
  calc β / 4 * |∫ p, ∑ i, ∑ j, softmax β (interpPath m c p) i *
        softmax β (interpPath m c p) j * (incrSq νY i j - incrSq νX i j) ∂(νX.prod νY)|
      ≤ β / 4 * γ := mul_le_mul_of_nonneg_left this (by positivity)
    _ = β * γ / 4 := by ring

/-- **Sudakov–Fernique inequality.** If two Gaussian measures on `ℝⁿ` have the same mean and the
increments of the first are dominated in mean square by those of the second, then the expected
maximum of the first is at most that of the second. -/
theorem integral_sup'_le_of_incrSq_le (hmX : ∫ x, x ∂νX = m) (hmY : ∫ y, y ∂νY = m)
    (h : ∀ i j, incrSq νX i j ≤ incrSq νY i j) :
    ∫ x, univ.sup' univ_nonempty x ∂νX ≤ ∫ y, univ.sup' univ_nonempty y ∂νY := by
  have hlog : 0 ≤ log n := log_natCast_nonneg n
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set β := (log n + 1) / ε with hβ_def
  have hβ : 0 < β := by positivity
  have h1 : ∫ x, univ.sup' univ_nonempty x ∂νX ≤ ∫ x, logSumExp β x ∂νX :=
    integral_mono (integrable_sup' νX) (integrable_logSumExp νX hβ) fun x ↦
      sup'_le_logSumExp hβ x
  have h2 : ∫ y, logSumExp β y ∂νY ≤ ∫ y, univ.sup' univ_nonempty y ∂νY + log n / β := by
    rw [← integral_sup'_add_const νY]
    refine integral_mono (integrable_logSumExp νY hβ)
      ((integrable_sup' νY).add (integrable_const _)) fun y ↦ ?_
    simpa [Fintype.card_fin] using logSumExp_le_sup'_add hβ y
  have h3 : log n / β ≤ ε := by
    rw [hβ_def, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith [integral_logSumExp_le hmX hmY h hβ]

/-- If `a ≤ β γ / 4 + L / β` for every `β > 0`, then `a ≤ √(γ L)`. -/
lemma le_sqrt_mul_of_forall_le {a γ L : ℝ} (hγ : 0 ≤ γ) (hL : 0 ≤ L)
    (h : ∀ β : ℝ, 0 < β → a ≤ β * γ / 4 + L / β) : a ≤ √(γ * L) := by
  rcases hγ.eq_or_lt with rfl | hγ
  · -- `a ≤ L / β` for all `β`
    simp only [mul_zero, zero_div, zero_add, zero_mul, Real.sqrt_zero] at h ⊢
    refine le_of_not_gt fun ha ↦ ?_
    have := h (2 * (L + 1) / a) (by positivity)
    rw [div_div_eq_mul_div] at this
    have h2 : L * a / (2 * (L + 1)) < a := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases hL.eq_or_lt with rfl | hL
  · -- `a ≤ β γ / 4` for all `β`
    simp only [zero_div, add_zero, mul_zero, Real.sqrt_zero] at h ⊢
    refine le_of_not_gt fun ha ↦ ?_
    have := h (2 * a / (γ + 1)) (by positivity)
    have h2 : 2 * a / (γ + 1) * γ / 4 < a := by
      rw [div_mul_eq_mul_div, div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  · -- optimize: `β = 2 √(L / γ)`
    set s := √(L / γ) with hs_def
    have hs : 0 < s := Real.sqrt_pos.2 (div_pos hL hγ)
    have hs2 : s ^ 2 = L / γ := Real.sq_sqrt (div_pos hL hγ).le
    have hLs : L = s ^ 2 * γ := by rw [hs2]; field_simp
    have hsqrt : √(γ * L) = γ * s := by
      rw [hLs, show γ * (s ^ 2 * γ) = (γ * s) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    have := h (2 * s) (by positivity)
    rw [hsqrt]
    calc a ≤ 2 * s * γ / 4 + L / (2 * s) := this
      _ = γ * s := by rw [hLs]; field_simp; ring

/-- **Quantitative Sudakov–Fernique comparison.** If two Gaussian measures on `ℝⁿ` have the same
mean and their increment second moments differ by at most `γ`, then their expected maxima differ
by at most `√(γ log n)`. -/
theorem abs_integral_sup'_sub_le (hmX : ∫ x, x ∂νX = m) (hmY : ∫ y, y ∂νY = m)
    {γ : ℝ} (hγ : 0 ≤ γ) (h : ∀ i j, |incrSq νX i j - incrSq νY i j| ≤ γ) :
    |∫ x, univ.sup' univ_nonempty x ∂νX - ∫ y, univ.sup' univ_nonempty y ∂νY| ≤
      √(γ * log n) := by
  have hlog : 0 ≤ log n := log_natCast_nonneg n
  -- `0 ≤ ∫ F_β - ∫ max ≤ log n / β` for both measures
  have hgap : ∀ (ν : Measure (Fin n → ℝ)) [IsGaussian ν] (β : ℝ), 0 < β →
      ∫ x, univ.sup' univ_nonempty x ∂ν ≤ ∫ x, logSumExp β x ∂ν ∧
        ∫ x, logSumExp β x ∂ν ≤ ∫ x, univ.sup' univ_nonempty x ∂ν + log n / β := by
    intro ν _ β hβ
    refine ⟨integral_mono (integrable_sup' ν) (integrable_logSumExp ν hβ) fun x ↦
      sup'_le_logSumExp hβ x, ?_⟩
    rw [← integral_sup'_add_const ν]
    refine integral_mono (integrable_logSumExp ν hβ)
      ((integrable_sup' ν).add (integrable_const _)) fun y ↦ ?_
    simpa [Fintype.card_fin] using logSumExp_le_sup'_add hβ y
  refine le_sqrt_mul_of_forall_le hγ hlog fun β hβ ↦ ?_
  have hF := abs_integral_logSumExp_sub_le hmX hmY h hβ
  obtain ⟨hX1, hX2⟩ := hgap νX β hβ
  obtain ⟨hY1, hY2⟩ := hgap νY β hβ
  rw [abs_le] at hF ⊢
  constructor <;> linarith [hF.1, hF.2]

end Main

end GaussianMeasure
