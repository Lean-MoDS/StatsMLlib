/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Log-sum-exp and softmax

The log-sum-exp function `F_β(x) = β⁻¹ log ∑ᵢ exp (β xᵢ)` is a smooth surrogate for the
maximum of the coordinates of `x`. Its gradient is the softmax vector
`pᵢ(x) = exp (β xᵢ) / ∑ⱼ exp (β xⱼ)`, a probability vector.

## Main definitions

* `logSumExp β x`: the log-sum-exp function at inverse temperature `β`.
* `softmax β x i`: the softmax weights.

## Main results

* `sup'_le_logSumExp`, `logSumExp_le_sup'_add`: `max x ≤ F_β(x) ≤ max x + log |ι| / β`.
* `abs_logSumExp_le`: `|F_β(x)| ≤ ∑ᵢ |xᵢ| + log |ι| / β`.
* `hasFDerivAt_logSumExp`: the gradient of log-sum-exp is softmax.
* `hasFDerivAt_softmax`: `∂ⱼ pᵢ = β (δᵢⱼ pᵢ - pᵢ pⱼ)`.
* `sum_mul_sub_sum_mul_eq`: contraction of the log-sum-exp Hessian with a matrix.
-/

open Real Finset

variable {ι : Type*} [Fintype ι]

/-- The log-sum-exp function `β⁻¹ log ∑ᵢ exp (β xᵢ)`. -/
noncomputable def logSumExp (β : ℝ) (x : ι → ℝ) : ℝ :=
  β⁻¹ * log (∑ i, exp (β * x i))

/-- The softmax weights `exp (β xᵢ) / ∑ⱼ exp (β xⱼ)`. -/
noncomputable def softmax (β : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  exp (β * x i) / ∑ j, exp (β * x j)

section Basic

variable [Nonempty ι]

lemma sum_exp_mul_pos (β : ℝ) (x : ι → ℝ) : 0 < ∑ i, exp (β * x i) :=
  sum_pos (fun _ _ ↦ exp_pos _) univ_nonempty

lemma softmax_pos (β : ℝ) (x : ι → ℝ) (i : ι) : 0 < softmax β x i :=
  div_pos (exp_pos _) (sum_exp_mul_pos β x)

lemma sum_softmax (β : ℝ) (x : ι → ℝ) : ∑ i, softmax β x i = 1 := by
  simp only [softmax, ← sum_div]
  exact div_self (sum_exp_mul_pos β x).ne'

lemma softmax_le_one (β : ℝ) (x : ι → ℝ) (i : ι) : softmax β x i ≤ 1 := by
  rw [← sum_softmax β x]
  exact single_le_sum (fun j _ ↦ (softmax_pos β x j).le) (mem_univ i)

end Basic

section Bounds

variable [Nonempty ι] {β : ℝ}

lemma sup'_le_logSumExp (hβ : 0 < β) (x : ι → ℝ) :
    univ.sup' univ_nonempty x ≤ logSumExp β x := by
  obtain ⟨k, -, hk⟩ := exists_mem_eq_sup' univ_nonempty x
  have h : exp (β * x k) ≤ ∑ i, exp (β * x i) :=
    single_le_sum (f := fun i ↦ exp (β * x i)) (fun _ _ ↦ (exp_pos _).le) (mem_univ k)
  have hlog : β * x k ≤ log (∑ i, exp (β * x i)) := by
    rw [← log_exp (β * x k)]
    exact log_le_log (exp_pos _) h
  rw [hk, logSumExp, le_inv_mul_iff₀ hβ]
  exact hlog

lemma logSumExp_le_sup'_add (hβ : 0 < β) (x : ι → ℝ) :
    logSumExp β x ≤ univ.sup' univ_nonempty x + log (Fintype.card ι) / β := by
  set M := univ.sup' univ_nonempty x
  have hterm : ∀ i, exp (β * x i) ≤ exp (β * M) := fun i ↦
    exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_sup' x (mem_univ i)) hβ.le)
  have hsum : ∑ i, exp (β * x i) ≤ Fintype.card ι * exp (β * M) := by
    calc ∑ i, exp (β * x i) ≤ ∑ _i : ι, exp (β * M) := sum_le_sum fun i _ ↦ hterm i
      _ = Fintype.card ι * exp (β * M) := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlog : log (∑ i, exp (β * x i)) ≤ log (Fintype.card ι) + β * M := by
    rw [← log_exp (β * M), ← log_mul hcard.ne' (exp_pos _).ne']
    exact log_le_log (sum_exp_mul_pos β x) hsum
  rw [logSumExp, inv_mul_le_iff₀ hβ]
  calc log (∑ i, exp (β * x i)) ≤ log (Fintype.card ι) + β * M := hlog
    _ = β * (M + log (Fintype.card ι) / β) := by field_simp; ring

lemma abs_logSumExp_le (hβ : 0 < β) (x : ι → ℝ) :
    |logSumExp β x| ≤ ∑ i, |x i| + log (Fintype.card ι) / β := by
  have hsup : |univ.sup' univ_nonempty x| ≤ ∑ i, |x i| := by
    obtain ⟨k, -, hk⟩ := exists_mem_eq_sup' univ_nonempty x
    rw [hk]
    exact single_le_sum (f := fun i ↦ |x i|) (fun i _ ↦ abs_nonneg _) (mem_univ k)
  have hlog : 0 ≤ log (Fintype.card ι) / β :=
    div_nonneg (log_natCast_nonneg _) hβ.le
  have h1 := sup'_le_logSumExp hβ x
  have h2 := logSumExp_le_sup'_add hβ x
  rw [abs_le] at hsup ⊢
  constructor <;> linarith [hsup.1, hsup.2]

end Bounds

section Deriv

variable [Nonempty ι] {β : ℝ}

omit [Nonempty ι] in
/-- The derivative of `y ↦ ∑ i, exp (β yᵢ)`. -/
lemma hasFDerivAt_sum_exp_mul (β : ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ ↦ ∑ i, exp (β * y i))
      (∑ i, exp (β * x i) • β • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) x :=
  HasFDerivAt.fun_sum fun i _ ↦ ((hasFDerivAt_apply i x).const_mul β).exp

/-- The gradient of log-sum-exp is the softmax vector. -/
lemma hasFDerivAt_logSumExp (hβ : β ≠ 0) (x : ι → ℝ) :
    HasFDerivAt (logSumExp β)
      (∑ i, softmax β x i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) x := by
  have hS := sum_exp_mul_pos β x
  have h := ((hasFDerivAt_sum_exp_mul β x).log hS.ne').const_mul β⁻¹
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [softmax]
  simp [mul_sum, smul_eq_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  field_simp

lemma softmax_eq_exp (hβ : β ≠ 0) (y : ι → ℝ) (i : ι) :
    softmax β y i = exp (β * (y i - logSumExp β y)) := by
  have hS := sum_exp_mul_pos β y
  rw [softmax, mul_sub, logSumExp, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul, exp_sub,
    exp_log hS]

/-- The derivative of a softmax weight: `∂ⱼ pᵢ = β (δᵢⱼ pᵢ - pᵢ pⱼ)`. -/
lemma hasFDerivAt_softmax (hβ : β ≠ 0) (x : ι → ℝ) (i : ι) :
    HasFDerivAt (fun y ↦ softmax β y i)
      (softmax β x i • β • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i -
        ∑ j, softmax β x j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j)) x := by
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) i x).sub
    (hasFDerivAt_logSumExp hβ x)).const_mul β).exp
  have hfun : (fun y ↦ softmax β y i) = fun y ↦ exp (β * (y i - logSumExp β y)) :=
    funext fun y ↦ softmax_eq_exp hβ y i
  rw [hfun, softmax_eq_exp hβ x i]
  exact h

lemma fderiv_logSumExp_single (hβ : β ≠ 0) (x : ι → ℝ) (j : ι) [DecidableEq ι] :
    fderiv ℝ (logSumExp β) x (Pi.single j 1) = softmax β x j := by
  rw [(hasFDerivAt_logSumExp hβ x).fderiv]
  simp [Pi.single_apply]

lemma fderiv_softmax_single (hβ : β ≠ 0) (x : ι → ℝ) (i j : ι) [DecidableEq ι] :
    fderiv ℝ (fun y ↦ softmax β y i) x (Pi.single j 1) =
      β * (softmax β x i * (if i = j then 1 else 0) - softmax β x i * softmax β x j) := by
  rw [(hasFDerivAt_softmax hβ x i).fderiv]
  simp [Pi.single_apply, eq_comm]
  split_ifs <;> ring

lemma norm_fderiv_softmax_le (hβ : β ≠ 0) (x : ι → ℝ) (i : ι) :
    ‖fderiv ℝ (fun y ↦ softmax β y i) x‖ ≤ 2 * |β| := by
  rw [(hasFDerivAt_softmax hβ x i).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  have hv : ∀ j, |v j| ≤ ‖v‖ := fun j ↦ norm_le_pi_norm v j
  have hsum : |∑ j, softmax β x j * v j| ≤ ‖v‖ := by
    calc |∑ j, softmax β x j * v j| ≤ ∑ j, softmax β x j * ‖v‖ := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
          rw [abs_mul, abs_of_pos (softmax_pos β x j)]
          exact mul_le_mul_of_nonneg_left (hv j) (softmax_pos β x j).le
      _ = ‖v‖ := by rw [← sum_mul, sum_softmax, one_mul]
  have hp := softmax_pos β x i
  have hp1 := softmax_le_one β x i
  simp only [FunLike.coe_smul, FunLike.coe_sub, FunLike.coe_sum, Pi.smul_apply,
    Pi.sub_apply, Finset.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Real.norm_eq_abs]
  have hdiff : |v i - ∑ j, softmax β x j * v j| ≤ 2 * ‖v‖ := by
    have := abs_sub (v i) (∑ j, softmax β x j * v j)
    linarith [hv i]
  rw [abs_mul, abs_mul, abs_of_pos hp]
  calc softmax β x i * (|β| * |v i - ∑ j, softmax β x j * v j|)
      ≤ 1 * (|β| * (2 * ‖v‖)) := by gcongr
    _ = 2 * |β| * ‖v‖ := by ring

lemma contDiff_softmax (β : ℝ) (i : ι) : ContDiff ℝ 1 (fun y : ι → ℝ ↦ softmax β y i) := by
  have hnum : ContDiff ℝ 1 (fun y : ι → ℝ ↦ exp (β * y i)) :=
    (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp
  have hden : ContDiff ℝ 1 (fun y : ι → ℝ ↦ ∑ j, exp (β * y j)) :=
    ContDiff.sum fun j _ ↦ (contDiff_const.mul (contDiff_apply ℝ ℝ j)).exp
  exact hnum.div hden fun y ↦ (sum_exp_mul_pos β y).ne'

end Deriv

/-- Contracting the log-sum-exp Hessian `β (δᵢⱼ pᵢ - pᵢ pⱼ)` with a matrix `Δ`, for a
probability vector `p`. -/
lemma sum_mul_sub_sum_mul_eq (p : ι → ℝ) (hp : ∑ i, p i = 1) (Δ : ι → ι → ℝ) :
    ∑ i, p i * Δ i i - ∑ i, ∑ j, p i * p j * Δ i j =
      (1 / 2) * ∑ i, ∑ j, p i * p j * (Δ i i + Δ j j - 2 * Δ i j) := by
  have hdiag : ∑ i, ∑ j, p i * p j * Δ i i = ∑ i, p i * Δ i i := by
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_mul, ← mul_sum, hp, mul_one]
  have hdiag' : ∑ i, ∑ j, p i * p j * Δ j j = ∑ j, p j * Δ j j := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [← sum_mul, ← sum_mul, hp, one_mul]
  have h2 : ∑ i, ∑ j, p i * p j * (2 * Δ i j) = 2 * ∑ i, ∑ j, p i * p j * Δ i j := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ ↦ by ring
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, hdiag, hdiag', h2]
  ring
