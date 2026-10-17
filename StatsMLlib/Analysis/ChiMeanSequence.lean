/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Increments of sequences with `c k * c (k + 1) = k`

Let `c : ℕ → ℝ` be positive on `k ≥ 1`, satisfy `c k * c (k + 1) = k` and `c k ≤ √k` for
`k ≥ 1`. Such a sequence grows at least as fast as `√k`: every increment `c (k + 1) - c k` is at
least `√(k + 1) - √k`, so `k ↦ √k - c k` is antitone on `k ≥ 1`.

The motivating example is `c k = 𝔼 ‖g‖` for a standard Gaussian vector `g` in `ℝ^k`; the
statements here are purely real-analytic.

## Main statements

* `sqrt_succ_sub_sqrt_le_sub_of_mul_succ_eq`: `√(k + 1) - √k ≤ c (k + 1) - c k` for `k ≥ 1`.
* `sqrt_sub_sqrt_le_sub_of_mul_succ_eq`: `√n - √d ≤ c n - c d` for `1 ≤ d ≤ n`.

## Implementation notes

The proof compares `c k ^ 2` with `B k = k - 1 / 2 + 3 / (20 * k)`. The ratio `c k ^ 2 / B k`
is nondecreasing along `k, k + 2, k + 4, …` and its limsup is at most `1`, so `c k ^ 2 ≤ B k`.
The increment `c (k + 1) - c k = k / c k - c k` is decreasing in `c k`, and the value at
`c k = √(B k)` already dominates `√(k + 1) - √k`.
-/

namespace ChiMeanSequence

/-- The comparison value `x - 1 / 2 + 3 / (20 * x)` for `c k ^ 2`. -/
private noncomputable def bsq (x : ℝ) : ℝ := x - 1 / 2 + 3 / (20 * x)

private lemma bsq_ge {x : ℝ} (hx : 1 ≤ x) : x - 1 / 2 ≤ bsq x := by
  unfold bsq
  have : 0 < 3 / (20 * x) := by positivity
  linarith

private lemma bsq_pos {x : ℝ} (hx : 1 ≤ x) : 0 < bsq x := by
  have := bsq_ge hx
  linarith

/-- The polynomial inequality behind the monotonicity of `c k ^ 2 / bsq k` along `k + 2 * m`. -/
private lemma bsq_add_two {x : ℝ} (hx : 1 ≤ x) :
    x ^ 2 * bsq (x + 2) ≤ (x + 1) ^ 2 * bsq x := by
  unfold bsq
  have hx0 : 0 < x := by linarith
  rw [← sub_nonneg]
  have h : (x + 1) ^ 2 * (x - 1 / 2 + 3 / (20 * x)) -
      x ^ 2 * (x + 2 - 1 / 2 + 3 / (20 * (x + 2))) =
      (2 * x ^ 2 - 5 * x + 6) / (20 * x * (x + 2)) := by
    field_simp
    ring
  rw [h]
  apply div_nonneg _ (by positivity)
  nlinarith [sq_nonneg (x - 5 / 4)]

/-- The polynomial inequality behind the final increment estimate. -/
private lemma bsq_le_sub_sq_mul {x : ℝ} (hx : 1 ≤ x) :
    bsq x ≤ (x - bsq x) ^ 2 * ((8 * x ^ 2 + 8 * x + 1) / (2 * x + 1)) := by
  unfold bsq
  have hx0 : 0 < x := by linarith
  rw [← sub_nonneg]
  have h : (x - (x - 1 / 2 + 3 / (20 * x))) ^ 2 * ((8 * x ^ 2 + 8 * x + 1) / (2 * x + 1)) -
      (x - 1 / 2 + 3 / (20 * x)) =
      (320 * x ^ 3 - 228 * x ^ 2 - 48 * x + 9) / (400 * x ^ 2 * (2 * x + 1)) := by
    field_simp
    ring
  rw [h]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg (mul_nonneg hx0.le hx0.le) (sub_nonneg.mpr hx)]

/-- If `0 < x` and `x ^ 2 ≤ bsq K`, then `K / x - x ≥ √(K + 1) - √K`. -/
private lemma sqrt_succ_sub_sqrt_le_div_sub {K x : ℝ} (hK : 1 ≤ K) (hx : 0 < x)
    (hx2 : x ^ 2 ≤ bsq K) :
    √(K + 1) - √K ≤ K / x - x := by
  have hK0 : 0 < K := by linarith
  have hb := bsq_pos hK
  have hB : 0 < √(bsq K) := Real.sqrt_pos.mpr hb
  have hB2 : √(bsq K) ^ 2 = bsq K := Real.sq_sqrt hb.le
  have hxB : x ≤ √(bsq K) := Real.le_sqrt_of_sq_le hx2
  have h1 : K / √(bsq K) - √(bsq K) ≤ K / x - x := by
    have : K / √(bsq K) ≤ K / x := div_le_div_of_nonneg_left hK0.le hx hxB
    linarith
  refine le_trans ?_ h1
  have hu : √K ^ 2 = K := Real.sq_sqrt hK0.le
  have hv : √(K + 1) ^ 2 = K + 1 := Real.sq_sqrt (by linarith)
  have hu0 : 0 < √K := Real.sqrt_pos.mpr hK0
  have hv0 : 0 < √(K + 1) := Real.sqrt_pos.mpr (by linarith)
  -- `√K * √(K + 1) ≥ 2K(K + 1) / (2K + 1)`
  have hw : 2 * K * (K + 1) ≤ √K * √(K + 1) * (2 * K + 1) := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero]
    have h : (√K * √(K + 1) * (2 * K + 1)) ^ 2 = √K ^ 2 * √(K + 1) ^ 2 * (2 * K + 1) ^ 2 := by
      ring
    rw [h, hu, hv]
    nlinarith
  have hs : (8 * K ^ 2 + 8 * K + 1) / (2 * K + 1) ≤ (√K + √(K + 1)) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have ha : 0 ≤ K - bsq K := by
    have : 3 / (20 * K) ≤ 3 / 20 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by linarith)
    unfold bsq
    linarith
  have hkey : √(bsq K) ≤ (K - bsq K) * (√K + √(K + 1)) := by
    rw [← pow_le_pow_iff_left₀ hB.le (by positivity) two_ne_zero, hB2, mul_pow]
    calc bsq K ≤ (K - bsq K) ^ 2 * ((8 * K ^ 2 + 8 * K + 1) / (2 * K + 1)) :=
          bsq_le_sub_sq_mul hK
      _ ≤ (K - bsq K) ^ 2 * (√K + √(K + 1)) ^ 2 := by gcongr
  have hdiff : (√(K + 1) - √K) * (√K + √(K + 1)) = 1 := by
    nlinarith
  have hvu : 0 ≤ √(K + 1) - √K := sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  rw [le_sub_iff_add_le, le_div_iff₀ hB]
  nlinarith [mul_le_mul_of_nonneg_left hkey hvu]

variable {c : ℕ → ℝ}

private lemma succ_eq_div (hpos : ∀ k, 1 ≤ k → 0 < c k)
    (hmul : ∀ k, 1 ≤ k → c k * c (k + 1) = k) {k : ℕ} (hk : 1 ≤ k) :
    c (k + 1) = k / c k := by
  rw [eq_div_iff (hpos k hk).ne', mul_comm]
  exact hmul k hk

private lemma add_two_eq (hpos : ∀ k, 1 ≤ k → 0 < c k)
    (hmul : ∀ k, 1 ≤ k → c k * c (k + 1) = k) {k : ℕ} (hk : 1 ≤ k) :
    c (k + 2) = (k + 1) / k * c k := by
  have h1 := succ_eq_div hpos hmul hk
  have h2 := succ_eq_div hpos hmul (k := k + 1) (by omega)
  have hck := (hpos k hk).ne'
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [h2, h1]
  push_cast
  field_simp

private lemma ratio_le_ratio_add_two (hpos : ∀ k, 1 ≤ k → 0 < c k)
    (hmul : ∀ k, 1 ≤ k → c k * c (k + 1) = k) {k : ℕ} (hk : 1 ≤ k) :
    c k ^ 2 / bsq k ≤ c (k + 2) ^ 2 / bsq ((k + 2 : ℕ) : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  rw [add_two_eq hpos hmul hk, div_le_div_iff₀ (bsq_pos hk1) (bsq_pos (by push_cast; linarith))]
  push_cast
  have h := bsq_add_two hk1
  calc c k ^ 2 * bsq (k + 2) = c k ^ 2 / k ^ 2 * (k ^ 2 * bsq (k + 2)) := by
        field_simp
    _ ≤ c k ^ 2 / k ^ 2 * ((k + 1) ^ 2 * bsq k) := by gcongr
    _ = ((k + 1) / k * c k) ^ 2 * bsq k := by
        field_simp

private lemma ratio_le_ratio_add_two_mul (hpos : ∀ k, 1 ≤ k → 0 < c k)
    (hmul : ∀ k, 1 ≤ k → c k * c (k + 1) = k) {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    c k ^ 2 / bsq k ≤ c (k + 2 * m) ^ 2 / bsq ((k + 2 * m : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    refine ih.trans ?_
    have h := ratio_le_ratio_add_two hpos hmul (k := k + 2 * m) (by omega)
    rwa [show k + 2 * m + 2 = k + 2 * (m + 1) by ring] at h

private lemma sq_le_bsq (hpos : ∀ k, 1 ≤ k → 0 < c k)
    (hmul : ∀ k, 1 ≤ k → c k * c (k + 1) = k)
    (hle : ∀ k, 1 ≤ k → c k ≤ √k) {k : ℕ} (hk : 1 ≤ k) :
    c k ^ 2 ≤ bsq k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  by_contra h
  rw [not_le] at h
  have hq : 1 < c k ^ 2 / bsq k := by rwa [one_lt_div (bsq_pos hk1)]
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (c k ^ 2 / bsq k - 1))
  have hN' : 1 < N * (c k ^ 2 / bsq k - 1) := by
    rwa [div_lt_iff₀ (by linarith)] at hN
  have hj : 1 ≤ k + 2 * N := by omega
  have hj1 : (1 : ℝ) ≤ ((k + 2 * N : ℕ) : ℝ) := by exact_mod_cast hj
  have hqj := ratio_le_ratio_add_two_mul hpos hmul hk N
  have hcj : c (k + 2 * N) ^ 2 ≤ ((k + 2 * N : ℕ) : ℝ) := by
    calc c (k + 2 * N) ^ 2 ≤ √((k + 2 * N : ℕ) : ℝ) ^ 2 :=
          pow_le_pow_left₀ (hpos _ hj).le (hle _ hj) 2
      _ = _ := Real.sq_sqrt (by positivity)
  have hbj := bsq_ge hj1
  have hbj0 := bsq_pos hj1
  have hqj' : c (k + 2 * N) ^ 2 / bsq ((k + 2 * N : ℕ) : ℝ) * bsq ((k + 2 * N : ℕ) : ℝ) =
      c (k + 2 * N) ^ 2 := div_mul_cancel₀ _ hbj0.ne'
  have hcast : ((k + 2 * N : ℕ) : ℝ) = k + 2 * N := by push_cast; ring
  rw [hcast] at hbj hcj hqj' hqj
  set q := c k ^ 2 / bsq k
  set r := c (k + 2 * N) ^ 2 / bsq ((k : ℝ) + 2 * N)
  nlinarith [mul_le_mul_of_nonneg_right hqj (show (0 : ℝ) ≤ k + 2 * N - 1 / 2 by linarith),
    mul_le_mul_of_nonneg_left hbj (show (0 : ℝ) ≤ r by linarith)]

end ChiMeanSequence

open ChiMeanSequence

/-- Let `c : ℕ → ℝ` be positive on `k ≥ 1` with `c k * c (k + 1) = k` and `c k ≤ √k`. Then
every increment of `c` dominates the corresponding increment of `√k`. -/
theorem sqrt_succ_sub_sqrt_le_sub_of_mul_succ_eq (c : ℕ → ℝ)
    (hpos : ∀ k, 1 ≤ k → 0 < c k)
    (hmul : ∀ k, 1 ≤ k → c k * c (k + 1) = k)
    (hle : ∀ k, 1 ≤ k → c k ≤ √k) (k : ℕ) (hk : 1 ≤ k) :
    √(k + 1 : ℝ) - √k ≤ c (k + 1) - c k := by
  rw [succ_eq_div hpos hmul hk]
  exact sqrt_succ_sub_sqrt_le_div_sub (by exact_mod_cast hk) (hpos k hk)
    (sq_le_bsq hpos hmul hle hk)

/-- Let `c : ℕ → ℝ` be positive on `k ≥ 1` with `c k * c (k + 1) = k` and `c k ≤ √k`. Then
`k ↦ √k - c k` is antitone on `k ≥ 1`: `√n - √d ≤ c n - c d` whenever `1 ≤ d ≤ n`. -/
theorem sqrt_sub_sqrt_le_sub_of_mul_succ_eq (c : ℕ → ℝ)
    (hpos : ∀ k, 1 ≤ k → 0 < c k)
    (hmul : ∀ k, 1 ≤ k → c k * c (k + 1) = k)
    (hle : ∀ k, 1 ≤ k → c k ≤ √k) {d n : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    √(n : ℝ) - √d ≤ c n - c d := by
  induction n, hdn using Nat.le_induction with
  | base => simp
  | succ n hdn ih =>
    have h := sqrt_succ_sub_sqrt_le_sub_of_mul_succ_eq c hpos hmul hle n (by omega)
    push_cast
    linarith
