/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Gaussian.Representation
import StatsMLlib.Probability.Concentration.EfronStein
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian integration by parts

This file proves Gaussian integration by parts (Stein's lemma) for the standard Gaussian on `ℝ`,
its coordinatewise version on the standard Gaussian product measure `stdGaussianPi n`, and the
multivariate version for an arbitrary Gaussian measure on `Fin n → ℝ`. The last one is reduced to
the standard case through the representation `ρ = (stdGaussianPi n).map (√C · ·)`.

## Main results

* `GaussianMeasure.integral_mul_gaussianReal_eq_integral_deriv`: if `h : ℝ → ℝ` has derivative
  `h'` everywhere and `h'` is bounded, then `𝔼[X h(X)] = 𝔼[h'(X)]` for `X ∼ N(0, 1)`.
* `GaussianMeasure.integral_eval_mul_stdGaussianPi`: if `H : (Fin n → ℝ) → ℝ` is `C¹` with
  bounded derivative, then `𝔼[W_k H(W)] = 𝔼[∂_k H(W)]` for `W ∼ N(0, I_n)`.
* `GaussianMeasure.integral_eval_mul_eq_sum_covMatrix`: for a centered Gaussian measure with
  covariance matrix `C`, `𝔼[Wᵢ H(W)] = ∑ⱼ Cᵢⱼ 𝔼[∂ⱼ H(W)]`.
* `GaussianMeasure.integral_sub_mul_eq_sum_covMatrix`: the same identity for a Gaussian measure
  with mean `m`, with `Wᵢ` replaced by `Wᵢ - mᵢ`.
-/

open MeasureTheory ProbabilityTheory Real

namespace GaussianMeasure

/-- The standard Gaussian density satisfies `φ'(x) = -x φ(x)`. -/
lemma hasDerivAt_gaussianPDFReal_zero_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hφ : gaussianPDFReal 0 1 = fun y ↦ (√(2 * π))⁻¹ * rexp (-y ^ 2 / 2) := by
    funext y
    simp [gaussianPDFReal]
  have h : HasDerivAt (fun y : ℝ ↦ -y ^ 2 / 2) (-x) x := by
    convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
    ring
  rw [hφ]
  convert (h.exp.const_mul (√(2 * π))⁻¹) using 1
  ring

/-- Transfer integrability from `gaussianReal 0 1` to Lebesgue measure with the density. -/
lemma integrable_gaussianPDFReal_mul {g : ℝ → ℝ} (hg : Integrable g (gaussianReal 0 1)) :
    Integrable (fun x ↦ gaussianPDFReal 0 1 x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)] at hg
  simpa using hg

/-- **Gaussian integration by parts** (Stein's lemma) in dimension one. -/
theorem integral_mul_gaussianReal_eq_integral_deriv {h h' : ℝ → ℝ}
    (hh : ∀ x, HasDerivAt h (h' x) x) {M : ℝ} (hM : ∀ x, |h' x| ≤ M) :
    ∫ x, x * h x ∂(gaussianReal 0 1) = ∫ x, h' x ∂(gaussianReal 0 1) := by
  set φ := gaussianPDFReal 0 1 with hφ_def
  have hderiv : h' = deriv h := funext fun x ↦ (hh x).deriv.symm
  have hmeas' : Measurable h' := hderiv ▸ measurable_deriv h
  have hcont : Continuous h := continuous_iff_continuousAt.2 fun x ↦ (hh x).continuousAt
  have hgrowth : ∀ x, |h x| ≤ |h 0| + M * |x| := by
    intro x
    have hmv := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ ↦ (hh y).hasDerivWithinAt) (fun y _ ↦ by simpa [Real.norm_eq_abs] using hM y)
      (Set.mem_univ 0) (Set.mem_univ x)
    simp only [Real.norm_eq_abs, sub_zero] at hmv
    have := abs_sub_abs_le_abs_sub (h x) (h 0)
    linarith
  have hx1 : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hx2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have h_int : Integrable h (gaussianReal 0 1) :=
    ((integrable_const |h 0|).add (hx1.abs.const_mul M)).mono' hcont.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hgrowth x)
  have hxh_int : Integrable (fun x ↦ x * h x) (gaussianReal 0 1) := by
    refine ((hx1.abs.const_mul |h 0|).add (hx2.const_mul M)).mono'
      (continuous_id.mul hcont).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have := mul_le_mul_of_nonneg_left (hgrowth x) (abs_nonneg x)
    simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
    nlinarith [sq_abs x]
  have h'_int : Integrable h' (gaussianReal 0 1) :=
    (integrable_const M).mono' hmeas'.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hM x)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := h) (v := fun x ↦ -φ x)
    (u' := h') (v' := fun x ↦ x * φ x) (fun x _ ↦ hh x)
    (fun x _ ↦ by
      have := (hasDerivAt_gaussianPDFReal_zero_one x).neg
      rwa [neg_mul, neg_neg] at this)
    (by convert integrable_gaussianPDFReal_mul hxh_int using 1; funext x; simp; ring)
    (by convert (integrable_gaussianPDFReal_mul h'_int).neg using 1; funext x; simp; ring)
    (by convert (integrable_gaussianPDFReal_mul h_int).neg using 1; funext x; simp; ring)
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  calc ∫ x, φ x * (x * h x) = ∫ x, h x * (x * φ x) := by congr 1; funext x; ring
    _ = -∫ x, h' x * (-φ x) := key
    _ = ∫ x, φ x * h' x := by rw [← integral_neg]; congr 1; funext x; ring

/-- Disintegrate `stdGaussianPi n` along coordinate `k`: integrate first over the `k`-th
coordinate (resampled from `gaussianReal 0 1`), then over the product measure. -/
lemma integral_stdGaussianPi_eq_integral_update {n : ℕ} (k : Fin n)
    {G : (Fin n → ℝ) → ℝ} (hG : Integrable G (stdGaussianPi n)) :
    ∫ w, G w ∂(stdGaussianPi n) =
      ∫ x, ∫ y, G (Function.update x k y) ∂(gaussianReal 0 1) ∂(stdGaussianPi n) := by
  have hmeas : Measurable fun p : ℝ × (Fin n → ℝ) ↦ Function.update p.2 k p.1 :=
    (measurable_update' (a := k)).comp measurable_swap
  have hmap : Measure.map (fun p : ℝ × (Fin n → ℝ) ↦ Function.update p.2 k p.1)
      ((gaussianReal 0 1).prod (stdGaussianPi n)) = stdGaussianPi n :=
    map_update_prod_pi (μs := fun _ ↦ gaussianReal 0 1) k
  have hmp : MeasurePreserving (fun p : ℝ × (Fin n → ℝ) ↦ Function.update p.2 k p.1)
      ((gaussianReal 0 1).prod (stdGaussianPi n)) (stdGaussianPi n) := ⟨hmeas, hmap⟩
  have hint := (hmp.integrable_comp hG.aestronglyMeasurable).mpr hG
  conv_lhs => rw [← hmap]
  rw [integral_map hmeas.aemeasurable (by rw [hmap]; exact hG.aestronglyMeasurable)]
  exact integral_prod_symm _ hint

/-- If `H` is `C¹` with bounded derivative, then `w ↦ w k * H w` is integrable under
`stdGaussianPi n`. -/
lemma integrable_eval_mul_stdGaussianPi {n : ℕ} {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ 1 H)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ H x‖ ≤ M) (k : Fin n) :
    Integrable (fun w : Fin n → ℝ ↦ w k * H w) (stdGaussianPi n) := by
  have hdiff : Differentiable ℝ H := hH.differentiable one_ne_zero
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hgrowth : ∀ w, |H w| ≤ |H 0| + M * ∑ i, |w i| := by
    intro w
    have hmv := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun x _ ↦ hdiff x)
      (fun x _ ↦ hM x) (Set.mem_univ 0) (Set.mem_univ w)
    have hnorm : ‖w‖ ≤ ∑ i, |w i| :=
      (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg (w i))).2 fun i ↦ by
        simpa [Real.norm_eq_abs] using
          Finset.single_le_sum (f := fun i ↦ |w i|) (fun j _ ↦ abs_nonneg (w j))
            (Finset.mem_univ i)
    simp only [Real.norm_eq_abs, sub_zero] at hmv
    have := abs_sub_abs_le_abs_sub (H w) (H 0)
    nlinarith [mul_le_mul_of_nonneg_left hnorm hM0]
  have hsum : Integrable (fun w : Fin n → ℝ ↦ ∑ i, (w k ^ 2 + w i ^ 2)) (stdGaussianPi n) :=
    integrable_finsetSum (f := fun i (w : Fin n → ℝ) ↦ w k ^ 2 + w i ^ 2) Finset.univ
      fun i _ ↦ (integrable_sq_eval_stdGaussianPi k).add (integrable_sq_eval_stdGaussianPi i)
  refine (((integrable_eval_stdGaussianPi k).abs.const_mul |H 0|).add
    (hsum.const_mul M)).mono'
    ((continuous_apply k).mul hdiff.continuous).aestronglyMeasurable
    (ae_of_all _ fun w ↦ ?_)
  have hprod : |w k| * ∑ i, |w i| ≤ ∑ i, (w k ^ 2 + w i ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    nlinarith [sq_abs (w k), sq_abs (w i), sq_nonneg (|w k| - |w i|)]
  have := mul_le_mul_of_nonneg_left (hgrowth w) (abs_nonneg (w k))
  simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left hprod hM0]

/-- **Gaussian integration by parts** on the standard Gaussian product measure, coordinatewise. -/
theorem integral_eval_mul_stdGaussianPi {n : ℕ} {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ 1 H)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ H x‖ ≤ M) (k : Fin n) :
    ∫ w, w k * H w ∂(stdGaussianPi n) = ∫ w, fderiv ℝ H w (Pi.single k 1) ∂(stdGaussianPi n) := by
  have hdiff : Differentiable ℝ H := hH.differentiable one_ne_zero
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsingle : ‖(Pi.single k 1 : Fin n → ℝ)‖ = 1 := by simp [Pi.norm_single]
  have hbound : ∀ w, |fderiv ℝ H w (Pi.single k 1)| ≤ M := by
    intro w
    have := (fderiv ℝ H w).le_opNorm (Pi.single k 1)
    rw [hsingle, mul_one] at this
    simpa [Real.norm_eq_abs] using this.trans (hM w)
  have hF := integrable_eval_mul_stdGaussianPi hH hM k
  -- integrability of the partial derivative
  have hcont' : Continuous fun w ↦ fderiv ℝ H w (Pi.single k 1) :=
    (hH.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hG : Integrable (fun w ↦ fderiv ℝ H w (Pi.single k 1)) (stdGaussianPi n) :=
    (integrable_const M).mono' hcont'.aestronglyMeasurable
      (ae_of_all _ fun w ↦ by simpa [Real.norm_eq_abs] using hbound w)
  rw [integral_stdGaussianPi_eq_integral_update k hF,
    integral_stdGaussianPi_eq_integral_update k hG]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [Function.update_self]
  refine integral_mul_gaussianReal_eq_integral_deriv (fun y ↦ ?_) (fun y ↦ hbound _)
  exact (hdiff (Function.update x k y)).hasFDerivAt.comp_hasDerivAt y (hasDerivAt_update x k y)

/-- **Gaussian integration by parts** for a centered Gaussian measure on `Fin n → ℝ`:
`𝔼[Wᵢ H(W)] = ∑ⱼ Cᵢⱼ 𝔼[∂ⱼ H(W)]`, where `C` is the covariance matrix. -/
theorem integral_eval_mul_eq_sum_covMatrix {n : ℕ} (ρ : Measure (Fin n → ℝ)) [IsGaussian ρ]
    (hρ : ∫ x, x ∂ρ = 0) {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ 1 H) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ H x‖ ≤ M) (i : Fin n) :
    ∫ w, w i * H w ∂ρ = ∑ j, covMatrix ρ i j * ∫ w, fderiv ℝ H w (Pi.single j 1) ∂ρ := by
  set A := covSqrt ρ
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  have hL : ∀ g, L g = A.mulVec g := fun g ↦ rfl
  have hdiff : Differentiable ℝ H := hH.differentiable one_ne_zero
  have hHL : ContDiff ℝ 1 (fun g ↦ H (L g)) := hH.comp L.contDiff
  have hfd : ∀ g, HasFDerivAt (fun g ↦ H (L g)) ((fderiv ℝ H (L g)).comp L) g := fun g ↦
    (hdiff (L g)).hasFDerivAt.comp g L.hasFDerivAt
  have hMHL : ∀ g, ‖fderiv ℝ (fun g ↦ H (L g)) g‖ ≤ M * ‖L‖ := fun g ↦ by
    rw [(hfd g).fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
  have hLsingle : ∀ k, L (Pi.single k 1) = ∑ j, A j k • (Pi.single j 1 : Fin n → ℝ) := by
    intro k
    ext j'
    simp [hL, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
  have hsingle_bound : ∀ j w, |fderiv ℝ H w (Pi.single j 1)| ≤ M := fun j w ↦ by
    have := (fderiv ℝ H w).le_opNorm (Pi.single j 1)
    rw [show ‖(Pi.single j 1 : Fin n → ℝ)‖ = 1 by simp [Pi.norm_single], mul_one] at this
    simpa [Real.norm_eq_abs] using this.trans (hM w)
  -- move both sides to the standard Gaussian
  have hcontH : Continuous H := hdiff.continuous
  have hcont' : ∀ j, Continuous fun w ↦ fderiv ℝ H w (Pi.single j 1) := fun j ↦
    (hH.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hLHS : ∫ w, w i * H w ∂ρ = ∫ g, (L g) i * H (L g) ∂(stdGaussianPi n) :=
    integral_eq_integral_stdGaussianPi ρ hρ
      ((continuous_apply i).mul hcontH).aestronglyMeasurable
  have hRHS : ∀ j, ∫ w, fderiv ℝ H w (Pi.single j 1) ∂ρ =
      ∫ g, fderiv ℝ H (L g) (Pi.single j 1) ∂(stdGaussianPi n) := fun j ↦
    integral_eq_integral_stdGaussianPi ρ hρ (hcont' j).aestronglyMeasurable
  -- expand `(A g)ᵢ` and apply the coordinatewise identity
  have hexpand : ∫ g, (L g) i * H (L g) ∂(stdGaussianPi n) =
      ∑ k, A i k * ∫ g, g k * H (L g) ∂(stdGaussianPi n) := by
    have hpt : ∀ g, (L g) i * H (L g) = ∑ k, A i k * (g k * H (L g)) := fun g ↦ by
      rw [hL, Matrix.mulVec, dotProduct, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun k _ ↦
      (integrable_eval_mul_stdGaussianPi hHL hMHL k).const_mul (A i k)]
    simp_rw [integral_const_mul]
  have hstein : ∀ k, ∫ g, g k * H (L g) ∂(stdGaussianPi n) =
      ∑ j, A j k * ∫ g, fderiv ℝ H (L g) (Pi.single j 1) ∂(stdGaussianPi n) := by
    intro k
    rw [integral_eval_mul_stdGaussianPi hHL hMHL k]
    have hpt : ∀ g, fderiv ℝ (fun g ↦ H (L g)) g (Pi.single k 1) =
        ∑ j, A j k * fderiv ℝ H (L g) (Pi.single j 1) := fun g ↦ by
      rw [(hfd g).fderiv, ContinuousLinearMap.comp_apply, hLsingle, map_sum]
      simp_rw [map_smul, smul_eq_mul]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ ↦ ?_]
    · simp_rw [integral_const_mul]
    · refine ((integrable_const M).mono' ((hcont' j).comp L.continuous).aestronglyMeasurable
        (ae_of_all _ fun g ↦ ?_)).const_mul (A j k)
      simpa [Real.norm_eq_abs] using hsingle_bound j (L g)
  rw [hLHS, hexpand]
  simp_rw [hstein, hRHS, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← sum_covSqrt_mul_covSqrt ρ (IsGaussian.memLp_two_id) i j, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- Coordinates of a Gaussian measure on `Fin n → ℝ` are integrable. -/
lemma integrable_eval_of_isGaussian {n : ℕ} (ν : Measure (Fin n → ℝ)) [IsGaussian ν]
    (i : Fin n) : Integrable (fun x : Fin n → ℝ ↦ x i) ν :=
  IsGaussian.integrable_dual ν (ContinuousLinearMap.proj i)

/-- The covariance matrix is invariant under translation. -/
lemma covMatrix_map_sub {n : ℕ} (ν : Measure (Fin n → ℝ)) [IsGaussian ν] (m : Fin n → ℝ) :
    covMatrix (ν.map (fun x ↦ x - m)) = covMatrix ν := by
  ext i j
  have hmeas : Measurable fun x : Fin n → ℝ ↦ x - m := measurable_id.sub_const m
  rw [covMatrix_apply, covMatrix_apply, covariance_map_fun
    (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable
    hmeas.aemeasurable]
  simp only [Pi.sub_apply]
  rw [covariance_sub_const_left (integrable_eval_of_isGaussian ν i),
    covariance_sub_const_right (integrable_eval_of_isGaussian ν j)]

/-- **Gaussian integration by parts** for a Gaussian measure with mean `m` on `Fin n → ℝ`:
`𝔼[(Xᵢ - mᵢ) H(X)] = ∑ⱼ Cᵢⱼ 𝔼[∂ⱼ H(X)]`. -/
theorem integral_sub_mul_eq_sum_covMatrix {n : ℕ} (ν : Measure (Fin n → ℝ)) [IsGaussian ν]
    {m : Fin n → ℝ} (hm : ∫ x, x ∂ν = m) {H : (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ 1 H)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ H x‖ ≤ M) (i : Fin n) :
    ∫ x, (x i - m i) * H x ∂ν = ∑ j, covMatrix ν i j * ∫ x, fderiv ℝ H x (Pi.single j 1) ∂ν := by
  set ρ := ν.map (fun x ↦ x - m) with hρ_def
  have hmeas : Measurable fun x : Fin n → ℝ ↦ x - m := measurable_id.sub_const m
  have hρ : ∫ x, x ∂ρ = 0 := by
    rw [hρ_def, integral_map (f := fun x : Fin n → ℝ ↦ x) hmeas.aemeasurable
      aestronglyMeasurable_id,
      integral_sub (f := fun x : Fin n → ℝ ↦ x) IsGaussian.integrable_id (integrable_const m), hm,
      integral_const]
    simp
  have hH' : ContDiff ℝ 1 (fun w ↦ H (w + m)) := hH.comp (contDiff_id.add contDiff_const)
  have hfd : ∀ w, fderiv ℝ (fun w ↦ H (w + m)) w = fderiv ℝ H (w + m) := fun w ↦ by
    rw [fderiv_comp_add_right]
  have hM' : ∀ w, ‖fderiv ℝ (fun w ↦ H (w + m)) w‖ ≤ M := fun w ↦ by rw [hfd]; exact hM _
  have key := integral_eval_mul_eq_sum_covMatrix ρ hρ hH' hM' i
  rw [covMatrix_map_sub] at key
  have hcont : Continuous H := (hH.differentiable one_ne_zero).continuous
  have hcont' : ∀ j, Continuous fun w ↦ fderiv ℝ H w (Pi.single j 1) := fun j ↦
    (hH.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [hρ_def, integral_map hmeas.aemeasurable] at key
  · simp_rw [hfd, sub_add_cancel, Pi.sub_apply] at key
    rw [key]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_map hmeas.aemeasurable]
    · simp_rw [sub_add_cancel]
    · exact ((hcont' j).comp (continuous_id.add continuous_const)).aestronglyMeasurable
  · exact ((continuous_apply i).mul (hcont.comp
      (continuous_id.add continuous_const))).aestronglyMeasurable

end GaussianMeasure
