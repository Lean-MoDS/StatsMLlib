/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Concentration.Influence.Martingale
import Mathlib.Algebra.Order.Chebyshev

/-!
# Influences of Boolean functions and the KKL theorem

For a function `f` on the uniform hypercube `{±1}^n`, the influence of coordinate `i` is the
probability that flipping coordinate `i` changes the value of `f`. Combining the Bernoulli
log-Sobolev inequality with the martingale decomposition of `Influence.Martingale`, we prove a
lower bound on the sum of squared influences of a Boolean function, and deduce the
Kahn–Kalai–Linial theorem.

## Main definitions

* `Influence.influence f i`: `P{f(X) ≠ f(X with coordinate i flipped)}`.
* `Influence.totalInfluence f`: `∑ᵢ influence f i`.

## Main results

* `Influence.sq_expect_mul_log_le_dirichletForm`: for `f ≥ 0`,
  `E[f²] log(E[f²] / (E f)²) ≤ 2 𝓔(f)`.
* `Influence.variance_mul_log_le_dirichletForm`:
  `Var f · log(Var f / ∑ᵢ (E|Δᵢ|)²) ≤ 2 𝓔(f)`.
* `Influence.four_variance_mul_exp_le_sum_influence_sq`: for Boolean `f` with `Var f > 0`,
  `4 Var f · exp(-I(f) / (2 Var f)) ≤ ∑ᵢ Iᵢ(f)²`.
* `Influence.sum_influence_sq_ge`: for Boolean `f` and `n ≥ 2`,
  `Var(f)² (log n)² / n ≤ ∑ᵢ Iᵢ(f)²`.
* `Influence.exists_influence_ge` (KKL): some coordinate has `Var f · log n / n ≤ Iᵢ(f)`.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of
  Independence*, Oxford University Press, 2013][BLM], Chapter 9. Numbered results cited as
  `BLM …` refer to this book.
-/

open Real BernoulliLSI

noncomputable section

namespace Influence

variable {n : ℕ}

/-- The influence of coordinate `i` on `f`: the probability that flipping it changes `f`. -/
def influence (f : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  expect (fun x ↦ if f x = f (flipCoord i x) then 0 else 1)

/-- The total influence `I(f) = ∑ᵢ Iᵢ(f)`. -/
def totalInfluence (f : (Fin n → Bool) → ℝ) : ℝ := ∑ i, influence f i

lemma influence_nonneg (f : (Fin n → Bool) → ℝ) (i : Fin n) : 0 ≤ influence f i :=
  expect_nonneg fun x ↦ by split_ifs <;> norm_num

/-! ### BLM Lemma 9.3 -/

/-- The rescaled form of `a² log(1/(ac)) ≤ a/c - a²`. -/
private lemma sq_mul_log_le (A m : ℝ) (hA : 0 < A) (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 * log A - t ^ 2 * log t - t ^ 2 * log m ≤ A / m * t - t ^ 2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hlog : log A - log t - log m = log (A / (t * m)) := by
    rw [log_div hA.ne' (by positivity), log_mul ht.ne' hm.ne']
    ring
  have hle := log_le_sub_one_of_pos (show 0 < A / (t * m) by positivity)
  have key : t ^ 2 * (log A - log t - log m) ≤ t ^ 2 * (A / (t * m) - 1) := by
    rw [hlog]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hrhs : t ^ 2 * (A / (t * m) - 1) = A / m * t - t ^ 2 := by
    field_simp
  linarith

/-- BLM Lemma 9.3: for `f ≥ 0`, `E[f²] log(E[f²] / (E f)²) ≤ 2 𝓔(f)`. -/
theorem sq_expect_mul_log_le_dirichletForm (f : (Fin n → Bool) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    expect (fun x ↦ f x ^ 2) * log (expect (fun x ↦ f x ^ 2) / expect f ^ 2) ≤
      2 * dirichletForm f f := by
  set A := expect (fun x ↦ f x ^ 2) with hA_def
  set m := expect f with hm_def
  have hE := dirichletForm_self_nonneg f
  have hA0 : 0 ≤ A := expect_nonneg fun x ↦ sq_nonneg _
  have hm0 : 0 ≤ m := expect_nonneg hf
  rcases hA0.eq_or_lt with hA | hA
  · rw [← hA, zero_mul]
    linarith
  rcases hm0.eq_or_lt with hm | hm
  · rw [← hm]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, log_zero,
      mul_zero]
    linarith
  refine le_trans ?_ (ent_sq_le_two_mul_dirichletForm f)
  have hpt : A * log A - expect (fun x ↦ f x ^ 2 * log (f x)) - A * log m ≤ A / m * m - A := by
    have h := expect_mono fun x ↦ sq_mul_log_le A m hA hm (hf x)
    simp only [expect_sub, expect_mul_const, expect_const_mul] at h
    exact h
  have hent : ent (fun x ↦ f x ^ 2) =
      2 * expect (fun x ↦ f x ^ 2 * log (f x)) - A * log A := by
    rw [ent, ← hA_def, ← expect_const_mul]
    congr 1
    exact expect_congr fun x ↦ by rw [log_pow]; push_cast; ring
  rw [hent, log_div hA.ne' (by positivity), log_pow]
  have hmm : A / m * m = A := by field_simp
  push_cast
  linarith

/-! ### BLM Theorem 9.4 -/

/-- L2: taking absolute values decreases the Dirichlet form. -/
lemma dirichletForm_abs_le (u : (Fin n → Bool) → ℝ) :
    dirichletForm (fun x ↦ |u x|) (fun x ↦ |u x|) ≤ dirichletForm u u := by
  unfold dirichletForm
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ expect_mono fun x ↦ ?_)
    (by norm_num)
  rw [← abs_mul_abs_self (|u x| - |u (flipCoord i x)|), ← abs_mul_abs_self (u x - _)]
  exact mul_self_le_mul_self (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub _ _)

/-- L3: the log-sum inequality `A log(A/B) ≤ ∑ⱼ aⱼ log(aⱼ/bⱼ)`. -/
lemma mul_log_div_sum_le_sum_mul_log_div {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hab : ∀ i ∈ s, 0 < a i → 0 < b i)
    (hA : 0 < ∑ i ∈ s, a i) (hB : 0 < ∑ i ∈ s, b i) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤
      ∑ i ∈ s, a i * log (a i / b i) := by
  set A := ∑ i ∈ s, a i
  set B := ∑ i ∈ s, b i
  have hpt : ∀ i ∈ s, a i * log (A / B) - a i * log (a i / b i) ≤ A * b i / B - a i := by
    intro i hi
    rcases (ha i hi).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [zero_mul, sub_zero]
      exact div_nonneg (mul_nonneg hA.le (hb i hi)) hB.le
    have hbpos := hab i hi hpos
    have hlog : log (A / B) - log (a i / b i) = log (A * b i / (B * a i)) := by
      rw [← log_div (by positivity) (by positivity)]
      congr 1
      field_simp
    have hle := log_le_sub_one_of_pos (show 0 < A * b i / (B * a i) by positivity)
    have key : a i * (log (A / B) - log (a i / b i)) ≤ a i * (A * b i / (B * a i) - 1) := by
      rw [hlog]
      exact mul_le_mul_of_nonneg_left hle hpos.le
    have hrhs : a i * (A * b i / (B * a i) - 1) = A * b i / B - a i := by
      field_simp
    linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div,
    ← Finset.mul_sum, mul_div_assoc, div_self hB.ne', mul_one, sub_self] at hsum
  linarith

/-- If `E|Δᵢ| = 0`, then `E[Δᵢ²] = 0`. -/
private lemma expect_sq_eq_zero_of_expect_abs_eq_zero {g : (Fin n → Bool) → ℝ}
    (h : expect (fun x ↦ |g x|) = 0) : expect (fun x ↦ g x ^ 2) = 0 := by
  have hz := eq_zero_of_expect_eq_zero (fun x ↦ abs_nonneg (g x)) h
  rw [expect_congr (h := fun _ ↦ 0) fun x ↦ by simp [abs_eq_zero.mp (hz x)], expect_const]

/-- L4: if `Var f > 0`, then `∑ᵢ (E|Δᵢ|)² > 0`. -/
lemma sum_sq_expect_abs_martingaleDiff_pos (f : (Fin n → Bool) → ℝ) (hV : 0 < variance f) :
    0 < ∑ i : Fin n, expect (fun x ↦ |martingaleDiff f i x|) ^ 2 := by
  refine (Finset.sum_nonneg fun i _ ↦ sq_nonneg _).lt_of_ne fun h ↦ hV.ne' ?_
  rw [variance_eq_sum_expect_martingaleDiff_sq]
  refine Finset.sum_eq_zero fun i hi ↦ expect_sq_eq_zero_of_expect_abs_eq_zero ?_
  exact pow_eq_zero_iff two_ne_zero |>.mp <|
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg _).mp h.symm i hi

/-- BLM Theorem 9.4: `Var f · log(Var f / ∑ᵢ (E|Δᵢ|)²) ≤ 2 𝓔(f)`. -/
theorem variance_mul_log_le_dirichletForm (f : (Fin n → Bool) → ℝ) (hV : 0 < variance f) :
    variance f * log (variance f / ∑ i : Fin n, expect (fun x ↦ |martingaleDiff f i x|) ^ 2) ≤
      2 * dirichletForm f f := by
  set a : Fin n → ℝ := fun i ↦ expect (fun x ↦ martingaleDiff f i x ^ 2)
  set b : Fin n → ℝ := fun i ↦ expect (fun x ↦ |martingaleDiff f i x|) ^ 2
  have hVa : variance f = ∑ i, a i := variance_eq_sum_expect_martingaleDiff_sq f
  have ha : ∀ i ∈ Finset.univ, 0 ≤ a i := fun i _ ↦ expect_nonneg fun x ↦ sq_nonneg _
  have hb : ∀ i ∈ Finset.univ, 0 ≤ b i := fun i _ ↦ sq_nonneg _
  have hab : ∀ i ∈ Finset.univ, 0 < a i → 0 < b i := by
    intro i _ hai
    refine (sq_nonneg _).lt_of_ne fun h ↦ hai.ne' ?_
    exact expect_sq_eq_zero_of_expect_abs_eq_zero (pow_eq_zero_iff two_ne_zero |>.mp h.symm)
  have hlogsum := mul_log_div_sum_le_sum_mul_log_div Finset.univ a b ha hb hab (hVa ▸ hV)
    (sum_sq_expect_abs_martingaleDiff_pos f hV)
  rw [← hVa] at hlogsum
  refine hlogsum.trans ?_
  rw [dirichletForm_eq_sum_martingaleDiff, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h93 := sq_expect_mul_log_le_dirichletForm (fun x ↦ |martingaleDiff f i x|)
    fun x ↦ abs_nonneg _
  simp only [sq_abs] at h93
  exact h93.trans (by linarith [dirichletForm_abs_le (martingaleDiff f i)])

/-! ### Boolean functions -/

section Boolean

variable {f : (Fin n → Bool) → ℝ}

private lemma sq_sub_eq_ite (hf : ∀ x, f x = 0 ∨ f x = 1) (x y : Fin n → Bool) :
    (f x - f y) ^ 2 = if f x = f y then 0 else 1 := by
  rcases hf x with hx | hx <;> rcases hf y with hy | hy <;> simp [hx, hy]

private lemma abs_sub_eq_ite (hf : ∀ x, f x = 0 ∨ f x = 1) (x y : Fin n → Bool) :
    |f x - f y| = if f x = f y then 0 else 1 := by
  rcases hf x with hx | hx <;> rcases hf y with hy | hy <;> simp [hx, hy]

/-- B1: for Boolean `f`, `𝓔(f) = I(f) / 4`. -/
lemma dirichletForm_eq_totalInfluence_div_four (hf : ∀ x, f x = 0 ∨ f x = 1) :
    dirichletForm f f = totalInfluence f / 4 := by
  simp only [dirichletForm, totalInfluence, influence, ← sq, sq_sub_eq_ite hf]
  ring

/-- B2: `E|f - flipAvg i f| = Iᵢ(f) / 2`. -/
lemma expect_abs_sub_flipAvg (hf : ∀ x, f x = 0 ∨ f x = 1) (i : Fin n) :
    expect (fun x ↦ |f x - flipAvg i f x|) = influence f i / 2 := by
  rw [influence, ← expect_div_const]
  refine expect_congr fun x ↦ ?_
  rw [show f x - flipAvg i f x = (f x - f (flipCoord i x)) / 2 by simp only [flipAvg]; ring,
    abs_div, abs_two, abs_sub_eq_ite hf]

/-- B3: `E|Δᵢ| ≤ E|f - flipAvg i f|`. -/
lemma expect_abs_martingaleDiff_le (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    expect (fun x ↦ |martingaleDiff f i x|) ≤ expect (fun x ↦ |f x - flipAvg i f x|) := by
  set h : (Fin n → Bool) → ℝ := fun x ↦ f x - flipAvg i f x
  have hΔ : ∀ x, martingaleDiff f i x = condFirst h (i + 1) x := by
    intro x
    rw [martingaleDiff, ← condFirst_flipAvg f i x, condFirst, condFirst, condFirst, ← expect_sub]
  calc expect (fun x ↦ |martingaleDiff f i x|)
      ≤ expect (condFirst (fun x ↦ |h x|) (i + 1)) := expect_mono fun x ↦ by
        rw [hΔ]
        exact abs_expect_le _
    _ = expect (fun x ↦ |h x|) := expect_condFirst _ _ i.isLt

/-- ★: for Boolean `f` with `Var f > 0`, `4 Var f · exp(-I(f) / (2 Var f)) ≤ ∑ᵢ Iᵢ(f)²`. -/
theorem four_variance_mul_exp_le_sum_influence_sq (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hV : 0 < variance f) :
    4 * variance f * exp (-(totalInfluence f / (2 * variance f))) ≤
      ∑ i, influence f i ^ 2 := by
  set B := ∑ i : Fin n, expect (fun x ↦ |martingaleDiff f i x|) ^ 2
  set S := ∑ i, influence f i ^ 2 / 4
  have hB := sum_sq_expect_abs_martingaleDiff_pos f hV
  have hBS : B ≤ S := Finset.sum_le_sum fun i _ ↦ by
    have h1 := (expect_abs_martingaleDiff_le f i).trans_eq (expect_abs_sub_flipAvg hf i)
    have h0 : 0 ≤ expect (fun x ↦ |martingaleDiff f i x|) := expect_nonneg fun x ↦ abs_nonneg _
    calc expect (fun x ↦ |martingaleDiff f i x|) ^ 2 ≤ (influence f i / 2) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = influence f i ^ 2 / 4 := by ring
  have hS : 0 < S := hB.trans_le hBS
  have h94 := variance_mul_log_le_dirichletForm f hV
  rw [dirichletForm_eq_totalInfluence_div_four hf] at h94
  have hlog : log (variance f / S) ≤ totalInfluence f / (2 * variance f) := by
    have hmono : log (variance f / S) ≤ log (variance f / B) :=
      log_le_log (by positivity) (div_le_div_of_nonneg_left hV.le hB hBS)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [log_le_iff_le_exp (by positivity), div_le_iff₀ hS] at hlog
  have hS' : S = (∑ i, influence f i ^ 2) / 4 := by rw [Finset.sum_div]
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
  rw [hS'] at hlog
  linarith

/-- C1: a Boolean function has variance at most `1/4`. -/
lemma variance_le_quarter (hf : ∀ x, f x = 0 ∨ f x = 1) : variance f ≤ 1 / 4 := by
  have hsq : expect (fun x ↦ f x ^ 2) = expect f :=
    expect_congr fun x ↦ by rcases hf x with hx | hx <;> simp [hx]
  rw [variance, hsq]
  nlinarith [sq_nonneg (expect f - 1 / 2)]

/-- C2: `(log x)⁴ ≤ 256 x` for `x ≥ 1`. -/
lemma log_pow_four_le {x : ℝ} (hx1 : 1 ≤ x) : log x ^ 4 ≤ 256 * x := by
  have hx : 0 ≤ x := zero_le_one.trans hx1
  have h := log_le_rpow_div hx (show (0 : ℝ) < 1 / 4 by norm_num)
  have hpow : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
    rw [← rpow_natCast, ← rpow_mul hx]
    norm_num
  calc log x ^ 4 ≤ (x ^ (1 / 4 : ℝ) / (1 / 4)) ^ 4 := pow_le_pow_left₀ (log_nonneg hx1) h 4
    _ = 256 * x := by rw [div_pow, hpow]; norm_num; ring

/-- BLM Theorem 9.5: for Boolean `f` and `n ≥ 2`, `Var(f)² (log n)² / n ≤ ∑ᵢ Iᵢ(f)²`. -/
theorem sum_influence_sq_ge (hn : 2 ≤ n) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    variance f ^ 2 * log n ^ 2 / n ≤ ∑ i, influence f i ^ 2 := by
  have hsum0 : 0 ≤ ∑ i, influence f i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  rcases (variance_nonneg f).eq_or_lt with hV | hV
  · rw [← hV]
    simpa using hsum0
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  set V := variance f
  set L := log n
  set I := totalInfluence f
  have hL : 0 < L := log_pos hn1
  set K := V * L ^ 2 / 4
  have hK : 0 < K := by positivity
  set c := 2 - 2 * log K / L
  -- `c ≥ 1`, i.e. `2 log K ≤ log n`, i.e. `K² ≤ n`.
  have hKn : K ^ 2 ≤ n := by
    have hV4 := variance_le_quarter hf
    have hL4 := log_pow_four_le hn1.le
    have hV2 : V ^ 2 ≤ 1 / 16 := by nlinarith
    calc K ^ 2 = V ^ 2 * L ^ 4 / 16 := by ring
      _ ≤ (1 / 16) * L ^ 4 / 16 := by gcongr
      _ ≤ n := by nlinarith
  have hc : 1 ≤ c := by
    have h2 : 2 * log K ≤ L := by
      have hlog2 : log (K ^ 2) = 2 * log K := by rw [log_pow]; norm_num
      rw [← hlog2]
      exact log_le_log (by positivity) (by exact_mod_cast hKn)
    have : 2 * log K / L ≤ 1 := (div_le_one hL).mpr h2
    linarith
  by_cases hI : c * V * L ≤ I
  · -- Case 1: Cauchy–Schwarz.
    have hCS : I ^ 2 ≤ n * ∑ i, influence f i ^ 2 := by
      simpa [I, totalInfluence] using
        sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := influence f)
    have hVL0 : 0 ≤ V * L := mul_nonneg hV.le hL.le
    have hVL : V * L ≤ I := le_trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hc) hVL0]) hI
    have hsq := pow_le_pow_left₀ hVL0 hVL 2
    rw [div_le_iff₀ hn0]
    nlinarith
  · -- Case 2: inequality ★.
    rw [not_le] at hI
    have hstar := four_variance_mul_exp_le_sum_influence_sq hf hV
    have hexp : exp (-(c * L / 2)) ≤ exp (-(I / (2 * V))) := by
      refine exp_le_exp.mpr (neg_le_neg ?_)
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    have hcL : -(c * L / 2) = log K - L := by
      simp only [c]
      field_simp
      ring
    have hval : exp (-(c * L / 2)) = K / n := by
      rw [hcL, exp_sub, exp_log hK, exp_log hn0]
    calc V ^ 2 * L ^ 2 / n = 4 * V * (K / n) := by simp only [K]; ring
      _ = 4 * V * exp (-(c * L / 2)) := by rw [hval]
      _ ≤ 4 * V * exp (-(I / (2 * V))) := mul_le_mul_of_nonneg_left hexp (by linarith)
      _ ≤ ∑ i, influence f i ^ 2 := hstar

/-- The Kahn–Kalai–Linial theorem: for Boolean `f` and `n ≥ 2`, some coordinate has influence
at least `Var f · log n / n`. -/
theorem exists_influence_ge (hn : 2 ≤ n) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    ∃ i, variance f * log n / n ≤ influence f i := by
  by_contra! h
  have hn0 : (0 : ℝ) < n := by positivity
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hlt : ∑ i, influence f i ^ 2 < ∑ _i : Fin n, (variance f * log n / n) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty hne fun i _ ↦
      pow_lt_pow_left₀ (h i) (influence_nonneg f i) two_ne_zero
  have hconst : ∑ _i : Fin n, (variance f * log n / n) ^ 2 = variance f ^ 2 * log n ^ 2 / n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  linarith [sum_influence_sq_ge hn hf]

end Boolean

/-- The KKL bound applied to a concrete Boolean function on `{±1}^4`. -/
example (f : (Fin 4 → Bool) → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    ∃ i, variance f * log 4 / 4 ≤ influence f i := by
  simpa using exists_influence_ge (by norm_num) hf

end Influence
