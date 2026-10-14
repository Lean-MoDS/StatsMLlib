/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Analysis.LogSumExp
import StatsMLlib.Probability.Gaussian.Kahane

/-!
# The Sudakov–Fernique inequality

Let `ν_X` and `ν_Y` be Gaussian measures on `ℝⁿ` with the same mean, and write
`γ^X_ij = ∫ (xᵢ - xⱼ)² dν_X` and `γ^Y_ij = ∫ (yᵢ - yⱼ)² dν_Y` for their increment second moments.
This file compares the expected maxima `∫ max x dν_X` and `∫ max y dν_Y`:

* if `γ^X_ij ≤ γ^Y_ij` for all `i, j`, then `∫ max dν_X ≤ ∫ max dν_Y` (Sudakov–Fernique);
* in general, `|∫ max dν_X - ∫ max dν_Y| ≤ √(γ log n)` whenever `|γ^X_ij - γ^Y_ij| ≤ γ` for all
  `i, j`.

The proof follows [Chatterjee2005]. The maximum is replaced by the log-sum-exp function `F_β`.
The Gaussian interpolation formula of `StatsMLlib.Probability.Gaussian.Kahane` expresses the
derivative of `t ↦ 𝔼[F_β(Z_t)]` through the Hessian of `F_β`; contracting that Hessian gives
`(β / 4) 𝔼[∑ᵢⱼ pᵢ(Z_t) pⱼ(Z_t) (γ^Y_ij - γ^X_ij)]`, where `p` is the softmax vector.

## Main definitions

* `GaussianMeasure.incrSq ν i j`: the increment second moment `∫ (xᵢ - xⱼ)² dν`.
* `GaussianMeasure.hessLSE β z i j`: the Hessian `β (δᵢⱼ pᵢ - pᵢ pⱼ)` of log-sum-exp.

## Main results

* `GaussianMeasure.hasBoundedDerivs_logSumExp`: log-sum-exp satisfies the regularity hypotheses
  of the interpolation formula.
* `GaussianMeasure.interpDeriv_logSumExp`: the interpolation derivative for log-sum-exp.
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

/-- The Hessian of log-sum-exp, `β (δᵢⱼ pᵢ - pᵢ pⱼ)`. -/
noncomputable def hessLSE (β : ℝ) (z : Fin n → ℝ) (i j : Fin n) : ℝ :=
  β * (softmax β z i * (if i = j then 1 else 0) - softmax β z i * softmax β z j)

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

section LogSumExp

variable [NeZero n] {β : ℝ}

/-- The partial derivatives of log-sum-exp are the softmax weights. -/
lemma pderiv_logSumExp (hβ : β ≠ 0) (i : Fin n) :
    pderiv (logSumExp β) i = fun z ↦ softmax β z i :=
  funext fun z ↦ fderiv_logSumExp_single hβ z i

lemma fderiv_pderiv_logSumExp_single (hβ : β ≠ 0) (z : Fin n → ℝ) (i j : Fin n) :
    fderiv ℝ (pderiv (logSumExp β) i) z (Pi.single j 1) = hessLSE β z i j := by
  rw [pderiv_logSumExp hβ, fderiv_softmax_single hβ, hessLSE]

/-- Log-sum-exp has gradient bounded by `1` and Hessian entries bounded by `2 |β|`. -/
lemma hasBoundedDerivs_logSumExp (hβ : β ≠ 0) :
    HasBoundedDerivs (logSumExp (ι := Fin n) β) 1 (2 * |β|) where
  differentiable x := (hasFDerivAt_logSumExp hβ x).differentiableAt
  norm_fderiv_le := norm_fderiv_logSumExp_le hβ
  contDiff_pderiv i := by
    rw [pderiv_logSumExp hβ]
    exact contDiff_softmax β i
  norm_fderiv_pderiv_le i x := by
    rw [pderiv_logSumExp hβ]
    exact norm_fderiv_softmax_le hβ x i

/-- The interpolation derivative for log-sum-exp, after contracting its Hessian. -/
lemma interpDeriv_logSumExp (νX νY : Measure (Fin n → ℝ)) [IsGaussian νX] [IsGaussian νY]
    {m : Fin n → ℝ} (hmX : ∫ x, x ∂νX = m) (hmY : ∫ y, y ∂νY = m) (hβ : β ≠ 0) (t : ℝ) :
    interpDeriv νX νY m (logSumExp β) t =
      β / 4 * ∫ p, ∑ i, ∑ j, softmax β (interpPath m t p) i * softmax β (interpPath m t p) j *
        (incrSq νY i j - incrSq νX i j) ∂(νX.prod νY) := by
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
      (νX.prod νY) := fun i j ↦
    ((integrable_const (2 * |β|)).mono'
      ((continuous_hessLSE β i j).comp (continuous_interpPath_right m t)).aestronglyMeasurable
      (ae_of_all _ fun p ↦ by
        rw [Real.norm_eq_abs]
        exact abs_hessLSE_le β _ i j)).mul_const _
  calc interpDeriv νX νY m (logSumExp β) t
      = (1 / 2) * ∑ i, ∑ j, ∫ p, hessLSE β (interpPath m t p) i j * Δ i j ∂(νX.prod νY) := by
        rw [interpDeriv]
        simp_rw [fderiv_pderiv_logSumExp_single hβ, integral_mul_const, hΔ, mul_comm]
    _ = (1 / 2) * ∫ p, ∑ i, ∑ j, hessLSE β (interpPath m t p) i j * Δ i j ∂(νX.prod νY) := by
        rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hI i j]
        congr 1
        refine sum_congr rfl fun i _ ↦ ?_
        rw [integral_finsetSum _ fun j _ ↦ hI i j]
    _ = _ := by
        simp_rw [hpt]
        rw [integral_const_mul]
        ring

end LogSumExp

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
  refine integral_le_integral_of_interpDeriv_nonneg νX νY hmX hmY
    (hasBoundedDerivs_logSumExp hβ.ne') fun t _ ↦ ?_
  rw [interpDeriv_logSumExp νX νY hmX hmY hβ.ne']
  refine mul_nonneg (by positivity) (integral_nonneg fun p ↦ ?_)
  refine sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ ?_
  exact mul_nonneg (mul_nonneg (softmax_pos β _ i).le (softmax_pos β _ j).le)
    (sub_nonneg.2 (h i j))

/-- For every `β > 0`, `|∫ F_β dν_X - ∫ F_β dν_Y| ≤ β γ / 4`. -/
lemma abs_integral_logSumExp_sub_le (hmX : ∫ x, x ∂νX = m) (hmY : ∫ y, y ∂νY = m)
    {γ : ℝ} (h : ∀ i j, |incrSq νX i j - incrSq νY i j| ≤ γ) {β : ℝ} (hβ : 0 < β) :
    |∫ x, logSumExp β x ∂νX - ∫ y, logSumExp β y ∂νY| ≤ β * γ / 4 := by
  refine abs_integral_sub_le_of_abs_interpDeriv_le νX νY hmX hmY
    (hasBoundedDerivs_logSumExp hβ.ne') fun c _ ↦ ?_
  rw [interpDeriv_logSumExp νX νY hmX hmY hβ.ne', abs_mul,
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
