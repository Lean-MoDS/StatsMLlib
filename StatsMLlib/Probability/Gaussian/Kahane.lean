/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Gaussian.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Gaussian interpolation and Kahane's comparison inequality

Let `μ` and `ν` be Gaussian measures on `ℝⁿ` with the same mean `m` and covariance matrices
`C_μ`, `C_ν`. For a smooth test function `f`, consider the interpolation
`Z_t = √(1 - t) (X - m) + √t (Y - m) + m`, with `X ∼ μ` and `Y ∼ ν` independent, and
`φ(t) = 𝔼[f(Z_t)]`. Gaussian integration by parts gives
`φ'(t) = (1 / 2) ∑ᵢⱼ (C_ν - C_μ)ᵢⱼ 𝔼[∂ᵢ∂ⱼ f(Z_t)]` for `t ∈ (0, 1)`.

Independence of `X` and `Y` is expressed by integrating over the product measure `μ.prod ν`.

Kahane's comparison inequality follows: if the variances agree and
`(C_μ - C_ν)ᵢⱼ ∂ᵢ∂ⱼ f ≤ 0` everywhere for `i ≠ j`, then `𝔼_μ[f] ≤ 𝔼_ν[f]`.

## Main definitions

* `GaussianMeasure.pderiv f i`: the partial derivative `x ↦ fderiv ℝ f x (Pi.single i 1)`.
* `GaussianMeasure.HasBoundedDerivs f M₁ M₂`: `f` has gradient bounded by `M₁`, and every partial
  derivative is `C¹` with derivative bounded by `M₂`.
* `GaussianMeasure.interpPath m t p`: the interpolation `√(1 - t) (x - m) + √t (y - m) + m`.
* `GaussianMeasure.interpInt μ ν m f t`: the interpolated expectation `∫ f(Z_t) d(μ ⊗ ν)`.
* `GaussianMeasure.interpDeriv μ ν m f t`: `(1 / 2) ∑ᵢⱼ (C_ν - C_μ)ᵢⱼ ∫ ∂ᵢ∂ⱼ f(Z_t) d(μ ⊗ ν)`.
* `GaussianMeasure.relabel e`: the coordinate relabeling `(ι → ℝ) ≃L[ℝ] (Fin N → ℝ)` along
  `e : ι ≃ Fin N`.

## Main results

* `GaussianMeasure.hasDerivAt_interpInt_interpDeriv`: the interpolation formula
  `φ'(t) = interpDeriv μ ν m f t` on `(0, 1)`.
* `GaussianMeasure.integral_le_integral_of_interpDeriv_nonneg`,
  `GaussianMeasure.abs_integral_sub_le_of_abs_interpDeriv_le`: comparison of `∫ f dμ` and
  `∫ f dν` from the sign or size of `interpDeriv`.
* `GaussianMeasure.integral_le_integral_kahane`: Kahane's comparison inequality on `Fin n → ℝ`.
* `GaussianMeasure.integral_le_integral_kahane_of_fintype`: Kahane's comparison inequality on
  `ι → ℝ` for any finite type `ι`, obtained by relabeling the coordinates.
* `GaussianMeasure.HasBoundedDerivs.comp_add_right`: translation preserves the hypotheses.
-/

open MeasureTheory ProbabilityTheory Real Finset

namespace GaussianMeasure

section Defs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The partial derivative `∂ᵢ f`. -/
noncomputable def pderiv (f : (ι → ℝ) → ℝ) (i : ι) : (ι → ℝ) → ℝ :=
  fun x ↦ fderiv ℝ f x (Pi.single i 1)

/-- `f` has gradient bounded by `M₁`, and every partial derivative `∂ᵢ f` is `C¹` with
derivative bounded by `M₂`. -/
structure HasBoundedDerivs (f : (ι → ℝ) → ℝ) (M₁ M₂ : ℝ) : Prop where
  differentiable : Differentiable ℝ f
  norm_fderiv_le : ∀ x, ‖fderiv ℝ f x‖ ≤ M₁
  contDiff_pderiv : ∀ i, ContDiff ℝ 1 (pderiv f i)
  norm_fderiv_pderiv_le : ∀ i x, ‖fderiv ℝ (pderiv f i) x‖ ≤ M₂

lemma pderiv_comp_add_right (f : (ι → ℝ) → ℝ) (q : ι → ℝ) (i : ι) :
    pderiv (fun x ↦ f (x + q)) i = fun x ↦ pderiv f i (x + q) := by
  funext x
  simp only [pderiv, fderiv_comp_add_right]

lemma fderiv_pderiv_comp_add_right (f : (ι → ℝ) → ℝ) (q : ι → ℝ) (i j : ι) (x : ι → ℝ) :
    fderiv ℝ (pderiv (fun x ↦ f (x + q)) i) x (Pi.single j 1) =
      fderiv ℝ (pderiv f i) (x + q) (Pi.single j 1) := by
  rw [pderiv_comp_add_right, fderiv_comp_add_right]

/-- Translation preserves `HasBoundedDerivs`. -/
lemma HasBoundedDerivs.comp_add_right {f : (ι → ℝ) → ℝ} {M₁ M₂ : ℝ}
    (hf : HasBoundedDerivs f M₁ M₂) (q : ι → ℝ) :
    HasBoundedDerivs (fun x ↦ f (x + q)) M₁ M₂ where
  differentiable := hf.differentiable.comp (differentiable_id.add_const q)
  norm_fderiv_le x := by
    rw [fderiv_comp_add_right]
    exact hf.norm_fderiv_le _
  contDiff_pderiv i := by
    rw [pderiv_comp_add_right]
    exact (hf.contDiff_pderiv i).comp (contDiff_id.add contDiff_const)
  norm_fderiv_pderiv_le i x := by
    rw [pderiv_comp_add_right, fderiv_comp_add_right]
    exact hf.norm_fderiv_pderiv_le i _

end Defs

variable {n : ℕ}

/-- The interpolation path `√(1 - t) (x - m) + √t (y - m) + m` at the point `p = (x, y)`. -/
noncomputable def interpPath (m : Fin n → ℝ) (t : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    Fin n → ℝ :=
  fun i ↦ √(1 - t) * (p.1 i - m i) + √t * (p.2 i - m i) + m i

lemma integral_eval_eq_of_integral_eq (ν : Measure (Fin n → ℝ)) [IsGaussian ν]
    {m : Fin n → ℝ} (hm : ∫ x, x ∂ν = m) (i : Fin n) : ∫ x, x i ∂ν = m i := by
  rw [← hm]
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i).integral_comp_comm
    IsGaussian.integrable_id

lemma continuous_interpPath (m : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    Continuous fun t ↦ interpPath m t p :=
  continuous_pi fun i ↦ by
    unfold interpPath
    fun_prop

lemma continuous_interpPath_right (m : Fin n → ℝ) (t : ℝ) :
    Continuous (interpPath m t) :=
  continuous_pi fun i ↦ by
    unfold interpPath
    fun_prop

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

section BoundedDerivs

variable {f : (Fin n → ℝ) → ℝ} {M₁ M₂ : ℝ}

lemma abs_clm_single_le {L : (Fin n → ℝ) →L[ℝ] ℝ} {M : ℝ} (hL : ‖L‖ ≤ M) (i : Fin n) :
    |L (Pi.single i 1)| ≤ M := by
  have := L.le_opNorm (Pi.single i 1)
  rw [show ‖(Pi.single i 1 : Fin n → ℝ)‖ = 1 by simp [Pi.norm_single], mul_one] at this
  simpa [Real.norm_eq_abs] using this.trans hL

lemma norm_le_sum_abs (x : Fin n → ℝ) : ‖x‖ ≤ ∑ i, |x i| :=
  (pi_norm_le_iff_of_nonneg (sum_nonneg fun i _ ↦ abs_nonneg (x i))).2 fun i ↦ by
    simpa [Real.norm_eq_abs] using
      single_le_sum (f := fun i ↦ |x i|) (fun j _ ↦ abs_nonneg (x j)) (mem_univ i)

lemma HasBoundedDerivs.abs_pderiv_le (hf : HasBoundedDerivs f M₁ M₂) (i : Fin n)
    (x : Fin n → ℝ) : |pderiv f i x| ≤ M₁ :=
  abs_clm_single_le (hf.norm_fderiv_le x) i

lemma HasBoundedDerivs.abs_pderiv_single_le (hf : HasBoundedDerivs f M₁ M₂) (i j : Fin n)
    (x : Fin n → ℝ) : |fderiv ℝ (pderiv f i) x (Pi.single j 1)| ≤ M₂ :=
  abs_clm_single_le (hf.norm_fderiv_pderiv_le i x) j

lemma HasBoundedDerivs.nonneg (hf : HasBoundedDerivs f M₁ M₂) : 0 ≤ M₁ :=
  (norm_nonneg _).trans (hf.norm_fderiv_le 0)

lemma HasBoundedDerivs.abs_le (hf : HasBoundedDerivs f M₁ M₂) (x : Fin n → ℝ) :
    |f x| ≤ |f 0| + M₁ * ∑ i, |x i| := by
  have hmv := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ hf.differentiable y) (fun y _ ↦ hf.norm_fderiv_le y) (Set.mem_univ 0)
    (Set.mem_univ x)
  simp only [Real.norm_eq_abs, sub_zero] at hmv
  have := abs_sub_abs_le_abs_sub (f x) (f 0)
  nlinarith [mul_le_mul_of_nonneg_left (norm_le_sum_abs x) hf.nonneg]

lemma fderiv_apply_eq_sum_pderiv (f : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ i, v i * pderiv f i x := by
  conv_lhs => rw [← univ_sum_single v]
  rw [map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [show (Pi.single i (v i) : Fin n → ℝ) = v i • Pi.single i 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, pderiv]

end BoundedDerivs

/-- Gaussian integration by parts for `x ↦ H (a (x - m) + c)`. -/
lemma integral_comp_affine_mul (ν : Measure (Fin n → ℝ)) [IsGaussian ν]
    {m : Fin n → ℝ} (hm : ∫ x, x ∂ν = m) {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ 1 H)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ H x‖ ≤ M) (a : ℝ) (c : Fin n → ℝ) (i : Fin n) :
    ∫ x, H (a • (x - m) + c) * (x i - m i) ∂ν =
      a * ∑ j, covMatrix ν i j * ∫ x, fderiv ℝ H (a • (x - m) + c) (Pi.single j 1) ∂ν := by
  set A : (Fin n → ℝ) → (Fin n → ℝ) := fun x ↦ a • (x - m) + c with hA_def
  have hAd : ∀ x, HasFDerivAt A (a • ContinuousLinearMap.id ℝ (Fin n → ℝ)) x := fun x ↦ by
    have := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const m).const_smul a).add_const c
    simpa [hA_def] using this
  have hHdiff : Differentiable ℝ H := hH.differentiable one_ne_zero
  have hHAd : ∀ x, HasFDerivAt (fun x ↦ H (A x))
      ((fderiv ℝ H (A x)).comp (a • ContinuousLinearMap.id ℝ _)) x :=
    fun x ↦ (hHdiff (A x)).hasFDerivAt.comp x (hAd x)
  have hHA : ContDiff ℝ 1 (fun x ↦ H (A x)) := by
    have hA : ContDiff ℝ 1 A := by
      rw [hA_def]
      fun_prop
    exact hH.comp hA
  have hM' : ∀ x, ‖fderiv ℝ (fun x ↦ H (A x)) x‖ ≤ M * |a| := fun x ↦ by
    rw [(hHAd x).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    refine mul_le_mul (hM _) ?_ (norm_nonneg _) hM0
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg a) ContinuousLinearMap.norm_id_le
  have hderiv : ∀ x j, fderiv ℝ (fun x ↦ H (A x)) x (Pi.single j 1) =
      a * fderiv ℝ H (A x) (Pi.single j 1) := fun x j ↦ by
    rw [(hHAd x).fderiv, ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  have key := integral_sub_mul_eq_sum_covMatrix ν hm hHA hM' i
  simp_rw [hderiv, integral_const_mul] at key
  rw [mul_sum]
  simp_rw [← mul_assoc, mul_comm a, mul_assoc]
  rw [← key]
  exact integral_congr_ae (ae_of_all _ fun x ↦ mul_comm _ _)

lemma abs_interpPath_le (m : Fin n → ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n) :
    |interpPath m t p i| ≤ |p.1 i - m i| + |p.2 i - m i| + |m i| := by
  have h1 : √(1 - t) ≤ 1 := Real.sqrt_le_one.2 (by linarith [ht.1])
  have h2 : √t ≤ 1 := Real.sqrt_le_one.2 ht.2
  calc |√(1 - t) * (p.1 i - m i) + √t * (p.2 i - m i) + m i|
      ≤ |√(1 - t) * (p.1 i - m i)| + |√t * (p.2 i - m i)| + |m i| := abs_add_three _ _ _
    _ ≤ |p.1 i - m i| + |p.2 i - m i| + |m i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _)]
        gcongr
        · exact mul_le_of_le_one_left (abs_nonneg _) h1
        · exact mul_le_of_le_one_left (abs_nonneg _) h2

section Interpolation

variable (μ ν : Measure (Fin n → ℝ)) [IsGaussian μ] [IsGaussian ν]
  {m : Fin n → ℝ} {f : (Fin n → ℝ) → ℝ} {M₁ M₂ : ℝ}

/-- The interpolated expectation `t ↦ ∫ f(Z_t) d(μ ⊗ ν)`. -/
noncomputable def interpInt (m : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ p, f (interpPath m t p) ∂(μ.prod ν)

/-- The derivative of the interpolated expectation after integration by parts. -/
noncomputable def interpDeriv (m : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, (covMatrix ν i j - covMatrix μ i j) *
    ∫ p, fderiv ℝ (pderiv f i) (interpPath m t p) (Pi.single j 1) ∂(μ.prod ν)

lemma interpInt_zero (m : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    interpInt μ ν m f 0 = ∫ x, f x ∂μ := by
  have h : ∀ p : (Fin n → ℝ) × (Fin n → ℝ), interpPath m 0 p = p.1 := fun p ↦ by
    funext i
    simp [interpPath]
  simp_rw [interpInt, h]
  rw [integral_fun_fst, probReal_univ, one_smul]

lemma interpInt_one (m : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    interpInt μ ν m f 1 = ∫ y, f y ∂ν := by
  have h : ∀ p : (Fin n → ℝ) × (Fin n → ℝ), interpPath m 1 p = p.2 := fun p ↦ by
    funext i
    simp [interpPath]
  simp_rw [interpInt, h]
  rw [integral_fun_snd, probReal_univ, one_smul]

lemma integrable_sum_abs_interp (m : Fin n → ℝ) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
      ∑ i, (|p.1 i - m i| + |p.2 i - m i| + |m i|)) (μ.prod ν) := by
  refine integrable_finsetSum _ fun i _ ↦ ?_
  refine ((((integrable_eval_of_isGaussian μ i).sub (integrable_const (m i))).abs.comp_fst
    ν).add ?_).add (integrable_const _)
  exact ((integrable_eval_of_isGaussian ν i).sub (integrable_const (m i))).abs.comp_snd μ

lemma abs_comp_interpPath_le (hf : HasBoundedDerivs f M₁ M₂) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    |f (interpPath m t p)| ≤ |f 0| + M₁ * ∑ i, (|p.1 i - m i| + |p.2 i - m i| + |m i|) := by
  have hM := hf.nonneg
  refine (hf.abs_le _).trans ?_
  gcongr with i _
  exact abs_interpPath_le m ht p i

lemma integrable_comp_interpPath (hf : HasBoundedDerivs f M₁ M₂) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) : Integrable (fun p ↦ f (interpPath m t p)) (μ.prod ν) :=
  ((integrable_const |f 0|).add ((integrable_sum_abs_interp μ ν m).const_mul M₁)).mono'
    (hf.differentiable.continuous.comp (continuous_interpPath_right m t)).aestronglyMeasurable
    (ae_of_all _ fun p ↦ by
      rw [Real.norm_eq_abs]
      exact abs_comp_interpPath_le hf ht p)

lemma continuousOn_interpInt (hf : HasBoundedDerivs f M₁ M₂) :
    ContinuousOn (interpInt μ ν m f) (Set.Icc 0 1) := by
  have hb : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
      |f 0| + M₁ * ∑ i, (|p.1 i - m i| + |p.2 i - m i| + |m i|)) (μ.prod ν) :=
    (integrable_const _).add ((integrable_sum_abs_interp μ ν m).const_mul M₁)
  refine continuousOn_of_dominated (fun t _ ↦ ?_) (fun t ht ↦ ae_of_all _ fun p ↦ ?_) hb
    (ae_of_all _ fun p ↦ ?_)
  · exact (hf.differentiable.continuous.comp
      (continuous_interpPath_right m t)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_comp_interpPath_le hf ht p
  · exact (hf.differentiable.continuous.comp (continuous_interpPath m p)).continuousOn

/-- The derivative of the interpolation, before integration by parts. -/
lemma hasDerivAt_interpInt (hf : HasBoundedDerivs f M₁ M₂) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    HasDerivAt (interpInt μ ν m f)
      (∫ p, ∑ i, pderiv f i (interpPath m t p) *
        ((p.2 i - m i) / (2 * √t) - (p.1 i - m i) / (2 * √(1 - t))) ∂(μ.prod ν)) t := by
  obtain ⟨ht0, ht1⟩ := ht
  set F : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun s p ↦ f (interpPath m s p)
  set F' : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun s p ↦
    ∑ i, pderiv f i (interpPath m s p) *
      ((p.2 i - m i) / (2 * √s) - (p.1 i - m i) / (2 * √(1 - s)))
  set S : Set ℝ := Set.Ioo (t / 2) ((1 + t) / 2)
  have hS : ∀ s ∈ S, s ∈ Set.Ioo (0 : ℝ) 1 := fun s hs ↦
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hSn : S ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  have hint1 : ∀ i, Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.1 i - m i)
      (μ.prod ν) := fun i ↦
    ((integrable_eval_of_isGaussian μ i).comp_fst ν).sub (integrable_const _)
  have hint2 : ∀ i, Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.2 i - m i)
      (μ.prod ν) := fun i ↦
    ((integrable_eval_of_isGaussian ν i).comp_snd μ).sub (integrable_const _)
  have hF_meas : ∀ s, AEStronglyMeasurable (F s) (μ.prod ν) := fun s ↦
    (hf.differentiable.continuous.comp (continuous_interpPath_right m s)).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' t) (μ.prod ν) := by
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_finsetSum _ fun i _ ↦ ?_
    exact (((hf.contDiff_pderiv i).continuous).comp (continuous_interpPath_right m t)).mul
      (by fun_prop)
  have hF_int : Integrable (F t) (μ.prod ν) :=
    integrable_comp_interpPath μ ν hf ⟨ht0.le, ht1.le⟩
  set bound : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p ↦
    ∑ i, M₁ * (|p.2 i - m i| / (2 * √(t / 2)) + |p.1 i - m i| / (2 * √((1 - t) / 2)))
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
    rw [abs_mul]
    refine mul_le_mul (hf.abs_pderiv_le i _) ?_ (abs_nonneg _) hf.nonneg
    calc |(p.2 i - m i) / (2 * √s) - (p.1 i - m i) / (2 * √(1 - s))|
        ≤ |p.2 i - m i| / (2 * √s) + |p.1 i - m i| / (2 * √(1 - s)) := by
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_div, abs_div, abs_of_pos (ht2.trans_le hst), abs_of_pos (ht2'.trans_le hst')]
      _ ≤ _ := by
          gcongr
  have hbound_int : Integrable bound (μ.prod ν) := integrable_finsetSum _ fun i _ ↦
    (((hint2 i).abs.div_const _).add ((hint1 i).abs.div_const _)).const_mul M₁
  have h_diff : ∀ p, ∀ s ∈ S, HasDerivAt (F · p) (F' s p) s := by
    intro p s hs
    have hd := (hf.differentiable (interpPath m s p)).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_interpPath m p (hS s hs))
    convert hd using 1
    · rfl
    · rw [fderiv_apply_eq_sum_pderiv]
      exact sum_congr rfl fun i _ ↦ mul_comm _ _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hSn
    (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas (ae_of_all _ h_bound) hbound_int
    (ae_of_all _ h_diff)).2

lemma continuous_fderiv_pderiv_single (hf : HasBoundedDerivs f M₁ M₂) (i j : Fin n) :
    Continuous fun z ↦ fderiv ℝ (pderiv f i) z (Pi.single j 1) :=
  ((hf.contDiff_pderiv i).continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma integrable_fderiv_pderiv_interp (hf : HasBoundedDerivs f M₁ M₂) (t : ℝ) (i j : Fin n) :
    Integrable (fun p ↦ fderiv ℝ (pderiv f i) (interpPath m t p) (Pi.single j 1))
      (μ.prod ν) :=
  (integrable_const M₂).mono'
    ((continuous_fderiv_pderiv_single hf i j).comp
      (continuous_interpPath_right m t)).aestronglyMeasurable
    (ae_of_all _ fun p ↦ by
      rw [Real.norm_eq_abs]
      exact hf.abs_pderiv_single_le i j _)

lemma integrable_pderiv_interp_mul_fst (hf : HasBoundedDerivs f M₁ M₂) (t : ℝ) (i : Fin n) :
    Integrable (fun p ↦ pderiv f i (interpPath m t p) * (p.1 i - m i)) (μ.prod ν) :=
  (((integrable_eval_of_isGaussian μ i).sub (integrable_const (m i))).comp_fst ν).bdd_mul
    ((hf.contDiff_pderiv i).continuous.comp
      (continuous_interpPath_right m t)).aestronglyMeasurable
    (ae_of_all _ fun _ ↦ by
      rw [Real.norm_eq_abs]
      exact hf.abs_pderiv_le i _)

lemma integrable_pderiv_interp_mul_snd (hf : HasBoundedDerivs f M₁ M₂) (t : ℝ) (i : Fin n) :
    Integrable (fun p ↦ pderiv f i (interpPath m t p) * (p.2 i - m i)) (μ.prod ν) :=
  (((integrable_eval_of_isGaussian ν i).sub (integrable_const (m i))).comp_snd μ).bdd_mul
    ((hf.contDiff_pderiv i).continuous.comp
      (continuous_interpPath_right m t)).aestronglyMeasurable
    (ae_of_all _ fun _ ↦ by
      rw [Real.norm_eq_abs]
      exact hf.abs_pderiv_le i _)

/-- Gaussian integration by parts in the `x` variable along the interpolation. -/
lemma integral_pderiv_interpPath_mul_fst (hm : ∫ x, x ∂μ = m) (hf : HasBoundedDerivs f M₁ M₂)
    (t : ℝ) (i : Fin n) :
    ∫ p, pderiv f i (interpPath m t p) * (p.1 i - m i) ∂(μ.prod ν) =
      √(1 - t) * ∑ j, covMatrix μ i j *
        ∫ p, fderiv ℝ (pderiv f i) (interpPath m t p) (Pi.single j 1) ∂(μ.prod ν) := by
  set c : (Fin n → ℝ) → Fin n → ℝ := fun y k ↦ √t * (y k - m k) + m k
  have hZ : ∀ x y, interpPath m t (x, y) = √(1 - t) • (x - m) + c y := fun x y ↦ by
    funext k
    simp only [interpPath, c, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hint2 := integrable_fderiv_pderiv_interp μ ν (m := m) hf t i
  calc ∫ p, pderiv f i (interpPath m t p) * (p.1 i - m i) ∂(μ.prod ν)
      = ∫ y, ∫ x, pderiv f i (√(1 - t) • (x - m) + c y) * (x i - m i) ∂μ ∂ν := by
        rw [integral_prod_symm _ (integrable_pderiv_interp_mul_fst μ ν (m := m) hf t i)]
        simp only [hZ]
    _ = ∫ y, √(1 - t) * ∑ j, covMatrix μ i j *
          ∫ x, fderiv ℝ (pderiv f i) (√(1 - t) • (x - m) + c y) (Pi.single j 1) ∂μ ∂ν :=
        integral_congr_ae (ae_of_all _ fun y ↦ integral_comp_affine_mul μ hm
          (hf.contDiff_pderiv i) (hf.norm_fderiv_pderiv_le i) _ _ i)
    _ = √(1 - t) * ∑ j, covMatrix μ i j *
          ∫ y, ∫ x, fderiv ℝ (pderiv f i) (√(1 - t) • (x - m) + c y) (Pi.single j 1) ∂μ ∂ν := by
        rw [integral_const_mul, integral_finsetSum]
        · simp_rw [integral_const_mul]
        · intro j _
          have := ((hint2 j).integral_prod_right).const_mul (covMatrix μ i j)
          simpa only [hZ] using this
    _ = _ := by
        congr 1
        refine sum_congr rfl fun j _ ↦ ?_
        rw [integral_prod_symm _ (hint2 j)]
        simp only [hZ]

/-- Gaussian integration by parts in the `y` variable along the interpolation. -/
lemma integral_pderiv_interpPath_mul_snd (hm : ∫ y, y ∂ν = m) (hf : HasBoundedDerivs f M₁ M₂)
    (t : ℝ) (i : Fin n) :
    ∫ p, pderiv f i (interpPath m t p) * (p.2 i - m i) ∂(μ.prod ν) =
      √t * ∑ j, covMatrix ν i j *
        ∫ p, fderiv ℝ (pderiv f i) (interpPath m t p) (Pi.single j 1) ∂(μ.prod ν) := by
  set c : (Fin n → ℝ) → Fin n → ℝ := fun x k ↦ √(1 - t) * (x k - m k) + m k
  have hZ : ∀ x y, interpPath m t (x, y) = √t • (y - m) + c x := fun x y ↦ by
    funext k
    simp only [interpPath, c, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hint2 := integrable_fderiv_pderiv_interp μ ν (m := m) hf t i
  calc ∫ p, pderiv f i (interpPath m t p) * (p.2 i - m i) ∂(μ.prod ν)
      = ∫ x, ∫ y, pderiv f i (√t • (y - m) + c x) * (y i - m i) ∂ν ∂μ := by
        rw [integral_prod _ (integrable_pderiv_interp_mul_snd μ ν (m := m) hf t i)]
        simp only [hZ]
    _ = ∫ x, √t * ∑ j, covMatrix ν i j *
          ∫ y, fderiv ℝ (pderiv f i) (√t • (y - m) + c x) (Pi.single j 1) ∂ν ∂μ :=
        integral_congr_ae (ae_of_all _ fun x ↦ integral_comp_affine_mul ν hm
          (hf.contDiff_pderiv i) (hf.norm_fderiv_pderiv_le i) _ _ i)
    _ = √t * ∑ j, covMatrix ν i j *
          ∫ x, ∫ y, fderiv ℝ (pderiv f i) (√t • (y - m) + c x) (Pi.single j 1) ∂ν ∂μ := by
        rw [integral_const_mul, integral_finsetSum]
        · simp_rw [integral_const_mul]
        · intro j _
          have := ((hint2 j).integral_prod_left).const_mul (covMatrix ν i j)
          simpa only [hZ] using this
    _ = _ := by
        congr 1
        refine sum_congr rfl fun j _ ↦ ?_
        rw [integral_prod _ (hint2 j)]
        simp only [hZ]

/-- **Gaussian interpolation formula**: `φ'(t) = (1 / 2) ∑ᵢⱼ (C_ν - C_μ)ᵢⱼ 𝔼[∂ᵢ∂ⱼ f(Z_t)]`. -/
lemma hasDerivAt_interpInt_interpDeriv (hmμ : ∫ x, x ∂μ = m) (hmν : ∫ y, y ∂ν = m)
    (hf : HasBoundedDerivs f M₁ M₂) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    HasDerivAt (interpInt μ ν m f) (interpDeriv μ ν m f t) t := by
  convert hasDerivAt_interpInt μ ν hf ht using 1
  have hst : 0 < √t := Real.sqrt_pos.2 ht.1
  have hst' : 0 < √(1 - t) := Real.sqrt_pos.2 (by linarith [ht.2])
  symm
  calc ∫ p, ∑ i, pderiv f i (interpPath m t p) *
          ((p.2 i - m i) / (2 * √t) - (p.1 i - m i) / (2 * √(1 - t))) ∂(μ.prod ν)
      = ∑ i, ((∫ p, pderiv f i (interpPath m t p) * (p.2 i - m i) ∂(μ.prod ν)) / (2 * √t) -
          (∫ p, pderiv f i (interpPath m t p) * (p.1 i - m i) ∂(μ.prod ν)) /
            (2 * √(1 - t))) := by
        rw [integral_finsetSum]
        · refine sum_congr rfl fun i _ ↦ ?_
          rw [← integral_div, ← integral_div, ← integral_sub]
          · exact integral_congr_ae (ae_of_all _ fun p ↦ by ring)
          · exact (integrable_pderiv_interp_mul_snd μ ν (m := m) hf t i).div_const _
          · exact (integrable_pderiv_interp_mul_fst μ ν (m := m) hf t i).div_const _
        · intro i _
          refine (((integrable_pderiv_interp_mul_snd μ ν (m := m) hf t i).div_const
            (2 * √t)).sub ((integrable_pderiv_interp_mul_fst μ ν (m := m) hf t i).div_const
              (2 * √(1 - t)))).congr (ae_of_all _ fun p ↦ ?_)
          simp only [Pi.sub_apply]
          ring
    _ = interpDeriv μ ν m f t := by
        rw [interpDeriv, mul_sum]
        refine sum_congr rfl fun i _ ↦ ?_
        rw [integral_pderiv_interpPath_mul_snd μ ν hmν hf t i,
          integral_pderiv_interpPath_mul_fst μ ν hmμ hf t i, mul_comm 2 √t,
          mul_div_mul_left _ _ hst.ne', mul_comm 2 √(1 - t), mul_div_mul_left _ _ hst'.ne',
          ← sub_div, ← sum_sub_distrib, sum_div, mul_sum]
        refine sum_congr rfl fun j _ ↦ ?_
        ring

/-- If `interpDeriv` is nonnegative on `(0, 1)`, then `∫ f dμ ≤ ∫ f dν`. -/
lemma integral_le_integral_of_interpDeriv_nonneg (hmμ : ∫ x, x ∂μ = m)
    (hmν : ∫ y, y ∂ν = m) (hf : HasBoundedDerivs f M₁ M₂)
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ interpDeriv μ ν m f t) :
    ∫ x, f x ∂μ ≤ ∫ y, f y ∂ν := by
  rw [← interpInt_zero μ ν m f, ← interpInt_one μ ν m f]
  have hmono : MonotoneOn (interpInt μ ν m f) (Set.Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (continuousOn_interpInt μ ν hf)
      (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    · rw [interior_Icc] at ht
      exact (hasDerivAt_interpInt_interpDeriv μ ν hmμ hmν hf ht).differentiableAt
        |>.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hasDerivAt_interpInt_interpDeriv μ ν hmμ hmν hf ht).deriv]
      exact h t ht
  exact hmono (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one

/-- If `|interpDeriv| ≤ K` on `(0, 1)`, then `|∫ f dμ - ∫ f dν| ≤ K`. -/
lemma abs_integral_sub_le_of_abs_interpDeriv_le (hmμ : ∫ x, x ∂μ = m)
    (hmν : ∫ y, y ∂ν = m) (hf : HasBoundedDerivs f M₁ M₂) {K : ℝ}
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |interpDeriv μ ν m f t| ≤ K) :
    |∫ x, f x ∂μ - ∫ y, f y ∂ν| ≤ K := by
  rw [← interpInt_zero μ ν m f, ← interpInt_one μ ν m f, abs_sub_comm]
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (interpInt μ ν m f) _ zero_lt_one
    (continuousOn_interpInt μ ν hf) fun t ht ↦ hasDerivAt_interpInt_interpDeriv μ ν hmμ hmν hf ht
  rw [sub_zero, div_one] at hslope
  rw [← hslope]
  exact h c hc

/-- **Kahane's comparison inequality.** Let `μ` and `ν` be Gaussian measures on `ℝⁿ` with the
same mean and the same variances. If `(C_μ - C_ν)ᵢⱼ ∂ᵢ∂ⱼ f ≤ 0` everywhere for `i ≠ j`, then
`∫ f dμ ≤ ∫ f dν`. -/
theorem integral_le_integral_kahane (hmμ : ∫ x, x ∂μ = m) (hmν : ∫ y, y ∂ν = m)
    (hf : HasBoundedDerivs f M₁ M₂) (hdiag : ∀ i, covMatrix μ i i = covMatrix ν i i)
    (hoff : ∀ i j, i ≠ j → ∀ x,
      (covMatrix μ i j - covMatrix ν i j) * fderiv ℝ (pderiv f i) x (Pi.single j 1) ≤ 0) :
    ∫ x, f x ∂μ ≤ ∫ y, f y ∂ν := by
  refine integral_le_integral_of_interpDeriv_nonneg μ ν hmμ hmν hf fun t _ ↦ ?_
  refine mul_nonneg (by norm_num) (sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ ?_)
  rcases eq_or_ne i j with rfl | hij
  · rw [hdiag, sub_self, zero_mul]
  · rw [← integral_const_mul]
    refine integral_nonneg fun p ↦ ?_
    have := hoff i j hij (interpPath m t p)
    have heq : (covMatrix ν i j - covMatrix μ i j) *
        fderiv ℝ (pderiv f i) (interpPath m t p) (Pi.single j 1) =
        -((covMatrix μ i j - covMatrix ν i j) *
          fderiv ℝ (pderiv f i) (interpPath m t p) (Pi.single j 1)) := by ring
    show 0 ≤ (covMatrix ν i j - covMatrix μ i j) *
      fderiv ℝ (pderiv f i) (interpPath m t p) (Pi.single j 1)
    rw [heq]
    exact neg_nonneg.2 this

end Interpolation

section Transport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Relabel coordinates along `e : ι ≃ Fin N`: `x ↦ x ∘ e.symm`. -/
noncomputable def relabel {N : ℕ} (e : ι ≃ Fin N) : (ι → ℝ) ≃L[ℝ] (Fin N → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ e.symm).toContinuousLinearEquiv

omit [DecidableEq ι] in
lemma relabel_apply {N : ℕ} (e : ι ≃ Fin N) (x : ι → ℝ) (k : Fin N) :
    relabel e x k = x (e.symm k) := rfl

omit [DecidableEq ι] in
lemma relabel_symm_apply {N : ℕ} (e : ι ≃ Fin N) (y : Fin N → ℝ) (i : ι) :
    (relabel e).symm y i = y (e i) := by
  obtain ⟨x, rfl⟩ := (relabel e).surjective y
  simp [relabel_apply]

lemma relabel_symm_single {N : ℕ} (e : ι ≃ Fin N) (k : Fin N) :
    (relabel e).symm (Pi.single k 1) = Pi.single (e.symm k) 1 := by
  funext i
  rw [relabel_symm_apply]
  simp only [Pi.single_apply, Equiv.eq_symm_apply]

omit [DecidableEq ι] in
lemma norm_relabel_symm_le {N : ℕ} (e : ι ≃ Fin N) :
    ‖((relabel e).symm : (Fin N → ℝ) →L[ℝ] (ι → ℝ))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ by
    rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun i ↦ ?_
    rw [ContinuousLinearEquiv.coe_coe, relabel_symm_apply]
    exact norm_le_pi_norm y (e i)

lemma pderiv_comp_relabel_symm {N : ℕ} (e : ι ≃ Fin N) {f : (ι → ℝ) → ℝ}
    (hf : Differentiable ℝ f) (k : Fin N) :
    pderiv (f ∘ (relabel e).symm) k = pderiv f (e.symm k) ∘ (relabel e).symm := by
  funext y
  simp only [pderiv, Function.comp_apply]
  rw [((hf _).hasFDerivAt.comp y ((relabel e).symm.hasFDerivAt)).fderiv]
  simp [relabel_symm_single]

lemma HasBoundedDerivs.comp_relabel_symm {N : ℕ} (e : ι ≃ Fin N) {f : (ι → ℝ) → ℝ}
    {M₁ M₂ : ℝ} (hf : HasBoundedDerivs f M₁ M₂) :
    HasBoundedDerivs (f ∘ (relabel e).symm) M₁ M₂ := by
  set L := (relabel e).symm
  have hcomp : ∀ {g : (ι → ℝ) → ℝ}, Differentiable ℝ g → ∀ y,
      fderiv ℝ (g ∘ L) y = (fderiv ℝ g (L y)).comp (L : (Fin N → ℝ) →L[ℝ] (ι → ℝ)) :=
    fun hg y ↦ ((hg _).hasFDerivAt.comp y L.hasFDerivAt).fderiv
  have hnorm : ∀ {g : (ι → ℝ) → ℝ} {M : ℝ}, Differentiable ℝ g →
      (∀ x, ‖fderiv ℝ g x‖ ≤ M) → ∀ y, ‖fderiv ℝ (g ∘ L) y‖ ≤ M := by
    intro g M hg hM y
    rw [hcomp hg]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    calc ‖fderiv ℝ _ (L y)‖ * ‖(L : (Fin N → ℝ) →L[ℝ] (ι → ℝ))‖ ≤ M * 1 :=
          mul_le_mul (hM _) (norm_relabel_symm_le e) (norm_nonneg _) hM0
      _ = M := mul_one M
  have hpd : ∀ i, Differentiable ℝ (pderiv f i) := fun i ↦
    (hf.contDiff_pderiv i).differentiable one_ne_zero
  refine ⟨hf.differentiable.comp L.differentiable, hnorm hf.differentiable hf.norm_fderiv_le,
    fun k ↦ ?_, fun k y ↦ ?_⟩
  · rw [pderiv_comp_relabel_symm e hf.differentiable]
    exact (hf.contDiff_pderiv _).comp L.contDiff
  · rw [pderiv_comp_relabel_symm e hf.differentiable]
    exact hnorm (hpd _) (hf.norm_fderiv_pderiv_le _) y

/-- **Kahane's comparison inequality** for Gaussian measures on `ι → ℝ` with `ι` any finite
type. Let `μ` and `ν` have the same mean and the same variances. If
`(cov_μ(xᵢ, xⱼ) - cov_ν(xᵢ, xⱼ)) ∂ᵢ∂ⱼ f ≤ 0` everywhere for `i ≠ j`, then `∫ f dμ ≤ ∫ f dν`. -/
theorem integral_le_integral_kahane_of_fintype {μ ν : Measure (ι → ℝ)} [IsGaussian μ]
    [IsGaussian ν] {m : ι → ℝ} (hmμ : ∫ x, x ∂μ = m) (hmν : ∫ y, y ∂ν = m)
    {f : (ι → ℝ) → ℝ} {M₁ M₂ : ℝ} (hf : HasBoundedDerivs f M₁ M₂)
    (hdiag : ∀ i, cov[fun x ↦ x i, fun x ↦ x i; μ] = cov[fun x ↦ x i, fun x ↦ x i; ν])
    (hoff : ∀ i j, i ≠ j → ∀ x,
      (cov[fun x ↦ x i, fun x ↦ x j; μ] - cov[fun x ↦ x i, fun x ↦ x j; ν]) *
        fderiv ℝ (pderiv f i) x (Pi.single j 1) ≤ 0) :
    ∫ x, f x ∂μ ≤ ∫ y, f y ∂ν := by
  set e := Fintype.equivFin ι
  set L := relabel e
  have hLm : Measurable L := L.continuous.measurable
  -- transported means
  have hmean : ∀ (ρ : Measure (ι → ℝ)) [IsGaussian ρ], ∫ x, x ∂ρ = m →
      ∫ y, y ∂(ρ.map L) = L m := by
    intro ρ _ hm
    rw [integral_map (f := fun y ↦ y) hLm.aemeasurable aestronglyMeasurable_id, ← hm]
    exact L.integral_comp_comm _
  -- transported covariances
  have hcov : ∀ (ρ : Measure (ι → ℝ)) (k l : Fin (Fintype.card ι)),
      covMatrix (ρ.map L) k l = cov[fun x ↦ x (e.symm k), fun x ↦ x (e.symm l); ρ] := by
    intro ρ k l
    rw [covMatrix_apply, covariance_map_fun (measurable_pi_apply k).aestronglyMeasurable
      (measurable_pi_apply l).aestronglyMeasurable hLm.aemeasurable]
    rfl
  -- transported integrals
  have hint : ∀ ρ : Measure (ι → ℝ), ∫ y, (f ∘ L.symm) y ∂(ρ.map L) = ∫ x, f x ∂ρ := by
    intro ρ
    rw [integral_map hLm.aemeasurable
      (hf.differentiable.continuous.comp L.symm.continuous).aestronglyMeasurable]
    simp
  have hpd : ∀ i, Differentiable ℝ (pderiv f i) := fun i ↦
    ((hf.contDiff_pderiv i).differentiable one_ne_zero)
  have hsecond : ∀ k l y, fderiv ℝ (pderiv (f ∘ L.symm) k) y (Pi.single l 1) =
      fderiv ℝ (pderiv f (e.symm k)) (L.symm y) (Pi.single (e.symm l) 1) := by
    intro k l y
    rw [pderiv_comp_relabel_symm e hf.differentiable,
      ((hpd _ _).hasFDerivAt.comp y L.symm.hasFDerivAt).fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, relabel_symm_single]
  rw [← hint μ, ← hint ν]
  refine integral_le_integral_kahane (μ.map L) (ν.map L) (hmean μ hmμ) (hmean ν hmν)
    (hf.comp_relabel_symm e) (fun k ↦ ?_) (fun k l hkl y ↦ ?_)
  · rw [hcov, hcov]
    exact hdiag _
  · rw [hcov, hcov, hsecond]
    exact hoff _ _ (e.symm.injective.ne hkl) _

end Transport

end GaussianMeasure
