/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Analysis.LogSumExp

/-!
# Soft min-max

For a finite array `x : S × T → ℝ`, the min-max value `min_s max_t x (s, t)` is approximated by
the smooth function
`G_β(x) = -logSumExp β (fun s ↦ -logSumExp β (fun t ↦ x (s, t)))`,
a soft minimum over rows of the soft maximum over columns. Writing
`p t|s = softmax β (fun t ↦ x (s, t)) t` for the row weights and
`w s = softmax β (fun s ↦ -logSumExp β (fun t ↦ x (s, t))) s` for the row-mixing weights, the
gradient of `G_β` is the probability vector `w s * p t|s`, and its second partial derivatives have
a definite sign: nonpositive within a row (off the diagonal), nonnegative across rows.

## Main definitions

* `minMax x`: the value `min_s max_t x (s, t)`.
* `softMinMax β x`: the smooth surrogate `G_β(x)`.

## Main results

* `minMax_sub_le_softMinMax`, `softMinMax_le_minMax_add`: two-sided approximation of `minMax`.
* `abs_minMax_le`, `abs_softMinMax_le`: linear growth bounds.
* `hasFDerivAt_softMinMax`, `differentiable_softMinMax`, `norm_fderiv_softMinMax_le`: the gradient
  is the probability vector `w s * p t|s`, of operator norm at most one.
* `fderiv_softMinMax_single`: the first partial derivatives.
* `contDiff_fderiv_softMinMax_single`: the first partial derivatives are `C¹`.
* `norm_fderiv_fderiv_softMinMax_single_le`: the second derivative is bounded by `4 * |β|`.
* `fderiv_fderiv_softMinMax_single`: an explicit formula for the second partial derivatives.
* `fderiv_fderiv_softMinMax_single_same_row_nonpos`,
  `fderiv_fderiv_softMinMax_single_diff_row_nonneg`: signs of the second partial derivatives.
-/

open Real Finset

variable {S T : Type*} [Fintype S] [Fintype T]

/-- `min_s max_t x (s, t)`. -/
noncomputable def minMax [Nonempty S] [Nonempty T] (x : S × T → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun s ↦
    Finset.univ.sup' Finset.univ_nonempty fun t ↦ x (s, t)

/-- Soft-min over rows of the soft-max over columns:
`G_β(x) = -logSumExp β (fun s ↦ -logSumExp β (fun t ↦ x (s, t)))`. -/
noncomputable def softMinMax (β : ℝ) (x : S × T → ℝ) : ℝ :=
  -logSumExp β fun s ↦ -logSumExp β fun t ↦ x (s, t)

section Bounds

variable [Nonempty S] [Nonempty T] {β : ℝ}

lemma minMax_sub_le_softMinMax (hβ : 0 < β) (x : S × T → ℝ) :
    minMax x - log (Fintype.card S) / β ≤ softMinMax β x := by
  set R : S → ℝ := fun s ↦ -logSumExp β fun t ↦ x (s, t)
  obtain ⟨s, -, hs⟩ := exists_mem_eq_sup' univ_nonempty R
  have h1 := logSumExp_le_sup'_add hβ R
  have h2 := sup'_le_logSumExp hβ fun t ↦ x (s, t)
  have h3 : minMax x ≤ univ.sup' univ_nonempty fun t ↦ x (s, t) :=
    inf'_le (fun s ↦ univ.sup' univ_nonempty fun t ↦ x (s, t)) (mem_univ s)
  rw [hs] at h1
  simp only [softMinMax]
  simp only [R] at h1
  linarith

lemma softMinMax_le_minMax_add (hβ : 0 < β) (x : S × T → ℝ) :
    softMinMax β x ≤ minMax x + log (Fintype.card T) / β := by
  set R : S → ℝ := fun s ↦ -logSumExp β fun t ↦ x (s, t)
  obtain ⟨s, -, hs⟩ :=
    exists_mem_eq_inf' univ_nonempty fun s ↦ univ.sup' univ_nonempty fun t ↦ x (s, t)
  have h1 := sup'_le_logSumExp hβ R
  have h2 : R s ≤ univ.sup' univ_nonempty R := le_sup' R (mem_univ s)
  have h3 := logSumExp_le_sup'_add hβ fun t ↦ x (s, t)
  have h4 : minMax x = univ.sup' univ_nonempty fun t ↦ x (s, t) := hs
  simp only [softMinMax]
  simp only [R] at h1 h2
  linarith

lemma abs_minMax_le (x : S × T → ℝ) : |minMax x| ≤ ∑ i, |x i| := by
  obtain ⟨s, -, hs⟩ :=
    exists_mem_eq_inf' univ_nonempty fun s ↦ univ.sup' univ_nonempty fun t ↦ x (s, t)
  obtain ⟨t, -, ht⟩ := exists_mem_eq_sup' univ_nonempty fun t ↦ x (s, t)
  have h : minMax x = x (s, t) := hs.trans ht
  rw [h]
  exact single_le_sum (f := fun i ↦ |x i|) (fun i _ ↦ abs_nonneg _) (mem_univ (s, t))

lemma abs_softMinMax_le (hβ : 0 < β) (x : S × T → ℝ) :
    |softMinMax β x| ≤
      ∑ i, |x i| + (log (Fintype.card S) + log (Fintype.card T)) / β := by
  have h1 := minMax_sub_le_softMinMax hβ x
  have h2 := softMinMax_le_minMax_add hβ x
  have h3 := abs_le.mp (abs_minMax_le x)
  have hS : 0 ≤ log (Fintype.card S) / β := div_nonneg (log_natCast_nonneg _) hβ.le
  have hT : 0 ≤ log (Fintype.card T) / β := div_nonneg (log_natCast_nonneg _) hβ.le
  rw [add_div, abs_le]
  constructor <;> linarith [h3.1, h3.2]

end Bounds

section Deriv

/-- The continuous linear map extracting row `s` of an array. -/
private noncomputable def rowCLM (s : S) : (S × T → ℝ) →L[ℝ] (T → ℝ) :=
  ContinuousLinearMap.pi fun t ↦ ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S × T ↦ ℝ) (s, t)

omit [Fintype S] [Fintype T] in
private lemma rowCLM_apply (s : S) (y : S × T → ℝ) : rowCLM s y = fun t ↦ y (s, t) := rfl

private lemma norm_rowCLM_le (s : S) : ‖(rowCLM s : (S × T → ℝ) →L[ℝ] (T → ℝ))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  exact fun t ↦ norm_le_pi_norm v (s, t)

variable [Nonempty T] {β : ℝ}

/-- The derivative of the row map `y ↦ fun s ↦ -logSumExp β (fun t ↦ y (s, t))`. -/
private noncomputable def rowsDeriv (β : ℝ) (x : S × T → ℝ) : (S × T → ℝ) →L[ℝ] (S → ℝ) :=
  ContinuousLinearMap.pi fun s ↦ -(fderiv ℝ (logSumExp β) (fun t ↦ x (s, t))).comp (rowCLM s)

private lemma hasFDerivAt_rows (β : ℝ) (x : S × T → ℝ) :
    HasFDerivAt (fun y : S × T → ℝ ↦ fun s ↦ -logSumExp β fun t ↦ y (s, t))
      (rowsDeriv β x) x :=
  hasFDerivAt_pi.2 fun s ↦
    (((contDiff_logSumExp β (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x
      (rowCLM s).hasFDerivAt).neg

private lemma contDiff_rows (β : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y : S × T → ℝ ↦ fun s ↦ -logSumExp β fun t ↦ y (s, t)) :=
  contDiff_pi.2 fun s ↦
    ((contDiff_logSumExp β (n := n)).comp (rowCLM (T := T) s).contDiff).neg

private lemma norm_rowsDeriv_le (hβ : β ≠ 0) (x : S × T → ℝ) : ‖rowsDeriv β x‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro s
  simp only [rowsDeriv, ContinuousLinearMap.pi_apply, neg_apply,
    ContinuousLinearMap.comp_apply, norm_neg]
  calc ‖fderiv ℝ (logSumExp β) (fun t ↦ x (s, t)) (rowCLM s v)‖
      ≤ ‖fderiv ℝ (logSumExp β) (fun t ↦ x (s, t))‖ * ‖rowCLM s v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * (1 * ‖v‖) := by
        gcongr
        · exact norm_fderiv_logSumExp_le hβ _
        · exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (norm_rowCLM_le s) (norm_nonneg v))
    _ = ‖v‖ := by ring

variable [Nonempty S]

private lemma hasFDerivAt_softMinMax' (x : S × T → ℝ) :
    HasFDerivAt (softMinMax β)
      (-(fderiv ℝ (logSumExp β) (fun s ↦ -logSumExp β fun t ↦ x (s, t))).comp
        (rowsDeriv β x)) x :=
  (((contDiff_logSumExp β (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x
    (hasFDerivAt_rows β x)).neg

lemma contDiff_softMinMax (β : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (softMinMax β : (S × T → ℝ) → ℝ) :=
  ((contDiff_logSumExp β (n := n)).comp (contDiff_rows (S := S) (T := T) β)).neg

lemma differentiable_softMinMax (β : ℝ) : Differentiable ℝ (softMinMax β : (S × T → ℝ) → ℝ) :=
  (contDiff_softMinMax β (n := 1)).differentiable one_ne_zero

/-- The gradient of `softMinMax` is the probability vector `w s * p t|s`. -/
lemma hasFDerivAt_softMinMax (hβ : β ≠ 0) (x : S × T → ℝ) :
    HasFDerivAt (softMinMax β)
      (∑ i : S × T, (softmax β (fun r ↦ -logSumExp β fun u ↦ x (r, u)) i.1 *
          softmax β (fun u ↦ x (i.1, u)) i.2) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S × T ↦ ℝ) i) x := by
  refine (hasFDerivAt_softMinMax' x).congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [rowsDeriv, (hasFDerivAt_logSumExp hβ _).fderiv]
  simp [rowCLM_apply, Fintype.sum_prod_type, mul_sum, smul_eq_mul, mul_assoc]

lemma norm_fderiv_softMinMax_le (hβ : β ≠ 0) (x : S × T → ℝ) :
    ‖fderiv ℝ (softMinMax β) x‖ ≤ 1 := by
  rw [(hasFDerivAt_softMinMax' x).fderiv, norm_neg]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  simpa using mul_le_mul (norm_fderiv_logSumExp_le hβ _) (norm_rowsDeriv_le hβ x)
    (norm_nonneg _) zero_le_one

variable [DecidableEq S] [DecidableEq T]

lemma fderiv_softMinMax_single (hβ : β ≠ 0) (x : S × T → ℝ) (s : S) (t : T) :
    fderiv ℝ (softMinMax β) x (Pi.single (s, t) 1) =
      softmax β (fun r ↦ -logSumExp β fun u ↦ x (r, u)) s * softmax β (fun u ↦ x (s, u)) t := by
  rw [(hasFDerivAt_softMinMax hβ x).fderiv]
  simp [Pi.single_apply]

/-- The first partial derivative of `softMinMax` as an explicit function. -/
private lemma fderiv_softMinMax_single_eq (hβ : β ≠ 0) (i : S × T) :
    (fun y ↦ fderiv ℝ (softMinMax β) y (Pi.single i 1)) = fun y ↦
      softmax β (fun r ↦ -logSumExp β fun u ↦ y (r, u)) i.1 *
        softmax β (fun u ↦ y (i.1, u)) i.2 :=
  funext fun y ↦ fderiv_softMinMax_single hβ y i.1 i.2

omit [DecidableEq S] [DecidableEq T] in
private lemma hasFDerivAt_partial (x : S × T → ℝ) (s : S) (t : T) :
    HasFDerivAt (fun y ↦ softmax β (fun r ↦ -logSumExp β fun u ↦ y (r, u)) s *
        softmax β (fun u ↦ y (s, u)) t)
      (softmax β (fun r ↦ -logSumExp β fun u ↦ x (r, u)) s •
          (fderiv ℝ (fun z ↦ softmax β z t) (fun u ↦ x (s, u))).comp (rowCLM s) +
        softmax β (fun u ↦ x (s, u)) t •
          (fderiv ℝ (fun z ↦ softmax β z s) (fun r ↦ -logSumExp β fun u ↦ x (r, u))).comp
            (rowsDeriv β x)) x :=
  (((contDiff_softmax β s).differentiable one_ne_zero _).hasFDerivAt.comp x
    (hasFDerivAt_rows β x)).mul
    (((contDiff_softmax β t).differentiable one_ne_zero _).hasFDerivAt.comp x
      (rowCLM s).hasFDerivAt)

lemma contDiff_fderiv_softMinMax_single (hβ : β ≠ 0) (i : S × T) :
    ContDiff ℝ 1 (fun x ↦ fderiv ℝ (softMinMax β) x (Pi.single i 1)) := by
  rw [fderiv_softMinMax_single_eq hβ i]
  exact ((contDiff_softmax β i.1).comp (contDiff_rows β)).mul
    ((contDiff_softmax β i.2).comp (rowCLM (T := T) i.1).contDiff)

/-- The second derivative of `softMinMax` is bounded by `4 * |β|`. -/
lemma norm_fderiv_fderiv_softMinMax_single_le (hβ : β ≠ 0) (x : S × T → ℝ) (i : S × T) :
    ‖fderiv ℝ (fun y ↦ fderiv ℝ (softMinMax β) y (Pi.single i 1)) x‖ ≤ 4 * |β| := by
  rw [fderiv_softMinMax_single_eq hβ i, (hasFDerivAt_partial x i.1 i.2).fderiv]
  set w := softmax β (fun r ↦ -logSumExp β fun u ↦ x (r, u)) i.1
  set p := softmax β (fun u ↦ x (i.1, u)) i.2
  have hw0 : 0 ≤ w := (softmax_pos _ _ _).le
  have hp0 : 0 ≤ p := (softmax_pos _ _ _).le
  have hw1 : w ≤ 1 := softmax_le_one _ _ _
  have hp1 : p ≤ 1 := softmax_le_one _ _ _
  have hDp : ‖(fderiv ℝ (fun z ↦ softmax β z i.2) (fun u ↦ x (i.1, u))).comp
      (rowCLM i.1)‖ ≤ 2 * |β| := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    simpa using mul_le_mul (norm_fderiv_softmax_le hβ _ i.2) (norm_rowCLM_le i.1)
      (norm_nonneg _) (by positivity)
  have hDw : ‖(fderiv ℝ (fun z ↦ softmax β z i.1)
      (fun r ↦ -logSumExp β fun u ↦ x (r, u))).comp (rowsDeriv β x)‖ ≤ 2 * |β| := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    simpa using mul_le_mul (norm_fderiv_softmax_le hβ _ i.1) (norm_rowsDeriv_le hβ x)
      (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hw0, Real.norm_of_nonneg hp0]
  have hβ0 : 0 ≤ |β| := abs_nonneg β
  nlinarith [norm_nonneg ((fderiv ℝ (fun z ↦ softmax β z i.2) (fun u ↦ x (i.1, u))).comp
      (rowCLM i.1)), norm_nonneg ((fderiv ℝ (fun z ↦ softmax β z i.1)
      (fun r ↦ -logSumExp β fun u ↦ x (r, u))).comp (rowsDeriv β x))]

/-- The second partial derivatives of `softMinMax`. -/
lemma fderiv_fderiv_softMinMax_single (hβ : β ≠ 0) (x : S × T → ℝ) (s s' : S) (t t' : T) :
    fderiv ℝ (fun y ↦ fderiv ℝ (softMinMax β) y (Pi.single (s, t) 1)) x
        (Pi.single (s', t') 1) =
      β * softmax β (fun r ↦ -logSumExp β fun u ↦ x (r, u)) s *
        softmax β (fun u ↦ x (s, u)) t *
        ((if s = s' then (if t = t' then 1 else 0) - softmax β (fun u ↦ x (s, u)) t' else 0) +
          (softmax β (fun r ↦ -logSumExp β fun u ↦ x (r, u)) s' - if s = s' then 1 else 0) *
            softmax β (fun u ↦ x (s', u)) t') := by
  rw [fderiv_softMinMax_single_eq hβ (s, t), (hasFDerivAt_partial x s t).fderiv,
    (hasFDerivAt_softmax hβ _ t).fderiv, (hasFDerivAt_softmax hβ _ s).fderiv]
  simp only [rowsDeriv, (hasFDerivAt_logSumExp hβ _).fderiv]
  simp [rowCLM_apply, Pi.single_apply, ite_and]
  split_ifs <;> subst_vars <;> ring

/-- Within a row, the off-diagonal second partial derivatives are nonpositive. -/
lemma fderiv_fderiv_softMinMax_single_same_row_nonpos (hβ : 0 < β) (x : S × T → ℝ) (s : S)
    {t t' : T} (htt' : t ≠ t') :
    fderiv ℝ (fun y ↦ fderiv ℝ (softMinMax β) y (Pi.single (s, t) 1)) x
      (Pi.single (s, t') 1) ≤ 0 := by
  rw [fderiv_fderiv_softMinMax_single hβ.ne' x s s t t']
  simp only [↓reduceIte, htt', zero_sub]
  have hw0 := softmax_pos β (fun r ↦ -logSumExp β fun u ↦ x (r, u)) s
  have hw1 := softmax_le_one β (fun r ↦ -logSumExp β fun u ↦ x (r, u)) s
  have hp0 := softmax_pos β (fun u ↦ x (s, u)) t
  have hp0' := softmax_pos β (fun u ↦ x (s, u)) t'
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_
  nlinarith

/-- Across rows, the second partial derivatives are nonnegative. -/
lemma fderiv_fderiv_softMinMax_single_diff_row_nonneg (hβ : 0 < β) (x : S × T → ℝ)
    {s s' : S} (hss' : s ≠ s') (t t' : T) :
    0 ≤ fderiv ℝ (fun y ↦ fderiv ℝ (softMinMax β) y (Pi.single (s, t) 1)) x
      (Pi.single (s', t') 1) := by
  rw [fderiv_fderiv_softMinMax_single hβ.ne' x s s' t t']
  simp only [hss', ↓reduceIte, sub_zero, zero_add]
  have := softmax_pos β (fun r ↦ -logSumExp β fun u ↦ x (r, u)) s
  have := softmax_pos β (fun r ↦ -logSumExp β fun u ↦ x (r, u)) s'
  have := softmax_pos β (fun u ↦ x (s, u)) t
  have := softmax_pos β (fun u ↦ x (s', u)) t'
  positivity

end Deriv
