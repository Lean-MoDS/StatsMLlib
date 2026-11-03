/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Concentration.Influence.Monotone

/-!
# Threshold phenomena and Russo's lemma

On the `p`-biased hypercube, encoded as `Fin n → Bool`, each coordinate is `true` with weight `p`
and `false` with weight `1 - p`, independently. For a monotone Boolean function `f`, Russo's lemma
identifies the derivative of `p ↦ P_p(f = 1)` with the total `p`-influence of `f`. As a
corollary, the total `p`-influence is controlled by `√(n P_p(f = 1) / (p (1 - p)))`.

All expectations are finite sums against the product weight, so the derivative is that of a
polynomial in `p`; no coupling is needed. Russo's lemma holds as a polynomial identity for every
real `p`.

## Main definitions

* `Influence.weightP p x`: the product weight `∏ⱼ w_p(xⱼ)`.
* `Influence.expectP p g`: the `p`-biased expectation `∑ₓ g x · weightP p x`.
* `Influence.influenceP p f i`, `Influence.totalInfluenceP p f`: the `p`-influences.

## Main results

* `Influence.hasDerivAt_expectP` (Russo's lemma, BLM Theorem 9.15): for monotone Boolean `f`,
  `d/dp E_p[f] = I^p(f)`.
* `Influence.totalInfluenceP_eq` (BLM Corollary 9.16):
  `I^p(f) = E_p[(‖X‖ - n p) f] / (p (1 - p))`.
* `Influence.totalInfluenceP_le` (BLM Corollary 9.16): for `p ∈ (0, 1)`,
  `I^p(f) ≤ √(n E_p[f] / (p (1 - p)))`.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of
  Independence*, Oxford University Press, 2013][BLM], Chapter 9. Numbered results cited as
  `BLM …` refer to this book.
-/

open BernoulliLSI

noncomputable section

namespace Influence

variable {n : ℕ}

/-! ### The `p`-biased weights -/

/-- The weight of a single coordinate: `p` for `true`, `1 - p` for `false`. -/
def coordWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- The derivative in `p` of `coordWeight p b`: `1` for `true`, `-1` for `false`. -/
def coordSign (b : Bool) : ℝ := if b then 1 else -1

/-- The product weight of a point of the hypercube. -/
def weightP (p : ℝ) (x : Fin n → Bool) : ℝ := ∏ j, coordWeight p (x j)

/-- The product weight of all coordinates but `i`. -/
def offWeight (p : ℝ) (i : Fin n) (x : Fin n → Bool) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, coordWeight p (x j)

/-- The `p`-biased expectation, as a finite sum. -/
def expectP (p : ℝ) (g : (Fin n → Bool) → ℝ) : ℝ := ∑ x, g x * weightP p x

/-- The `p`-influence of coordinate `i` on `f`. -/
def influenceP (p : ℝ) (f : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  expectP p (fun x ↦ if f x = f (flipCoord i x) then 0 else 1)

/-- The total `p`-influence. -/
def totalInfluenceP (p : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ := ∑ i, influenceP p f i

lemma coordWeight_add_not (p : ℝ) (b : Bool) : coordWeight p b + coordWeight p (!b) = 1 := by
  cases b <;> simp [coordWeight]

lemma coordWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ coordWeight p b := by
  cases b <;> simp [coordWeight] <;> linarith

lemma weightP_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Fin n → Bool) :
    0 ≤ weightP p x :=
  Finset.prod_nonneg fun j _ ↦ coordWeight_nonneg hp0 hp1 (x j)

/-- The product weights sum to one. -/
lemma sum_weightP (p : ℝ) : ∑ x : Fin n → Bool, weightP p x = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset Bool))
    (fun _ b ↦ coordWeight p b)
  rw [Fintype.piFinset_univ] at h
  rw [show ∑ x : Fin n → Bool, weightP p x = ∑ x : Fin n → Bool, ∏ j, coordWeight p (x j) from rfl,
    ← h]
  simp [coordWeight]

lemma weightP_eq_mul_offWeight (p : ℝ) (i : Fin n) (x : Fin n → Bool) :
    weightP p x = coordWeight p (x i) * offWeight p i x :=
  (Finset.mul_prod_erase _ (fun j ↦ coordWeight p (x j)) (Finset.mem_univ i)).symm

lemma offWeight_flipCoord (p : ℝ) (i : Fin n) (x : Fin n → Bool) :
    offWeight p i (flipCoord i x) = offWeight p i x :=
  Finset.prod_congr rfl fun j hj ↦ by
    rw [flipCoord_noteq i j x (Finset.ne_of_mem_erase hj)]

/-! ### Pairing by a flip -/

lemma sum_comp_flipCoord (i : Fin n) (F : (Fin n → Bool) → ℝ) :
    ∑ x, F (flipCoord i x) = ∑ x, F x :=
  Equiv.sum_comp (Function.Involutive.toPerm _ fun x ↦ flipCoord_flipCoord i x) F

lemma sum_eq_half_sum_add_flipCoord (i : Fin n) (F : (Fin n → Bool) → ℝ) :
    ∑ x, F x = (1 / 2) * ∑ x, (F x + F (flipCoord i x)) := by
  rw [Finset.sum_add_distrib, sum_comp_flipCoord]
  ring

/-- The `p`-biased expectation, computed pair by pair over `{x, flipᵢ x}`. -/
lemma expectP_eq_pair (p : ℝ) (i : Fin n) (g : (Fin n → Bool) → ℝ) :
    expectP p g = (1 / 2) * ∑ x, (g x * coordWeight p (x i) +
      g (flipCoord i x) * coordWeight p (!x i)) * offWeight p i x := by
  rw [expectP, sum_eq_half_sum_add_flipCoord i]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [weightP_eq_mul_offWeight p i x, weightP_eq_mul_offWeight p i (flipCoord i x),
    offWeight_flipCoord, flipCoord_same]
  ring

/-- The expectation of a flip-invariant function. -/
lemma expectP_of_flipCoord_invariant (p : ℝ) (i : Fin n) {g : (Fin n → Bool) → ℝ}
    (hg : ∀ x, g (flipCoord i x) = g x) :
    expectP p g = (1 / 2) * ∑ x, g x * offWeight p i x := by
  rw [expectP_eq_pair p i]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [hg, ← mul_add, coordWeight_add_not, mul_one]

lemma half_sum_offWeight (p : ℝ) (i : Fin n) :
    (1 / 2) * ∑ x : Fin n → Bool, offWeight p i x = 1 := by
  have h := expectP_of_flipCoord_invariant p i (g := fun _ ↦ (1 : ℝ)) fun _ ↦ rfl
  simpa [expectP, sum_weightP] using h.symm

/-! ### Linearity of the `p`-biased expectation -/

lemma expectP_sum {ι : Type*} (p : ℝ) (s : Finset ι) (g : ι → (Fin n → Bool) → ℝ) :
    expectP p (fun x ↦ ∑ j ∈ s, g j x) = ∑ j ∈ s, expectP p (g j) := by
  simp only [expectP, Finset.sum_mul]
  exact Finset.sum_comm

/-- A centred coordinate is orthogonal to every function not depending on that coordinate. -/
lemma expectP_centered_mul (p : ℝ) (j : Fin n) {h : (Fin n → Bool) → ℝ}
    (hh : ∀ x, h (flipCoord j x) = h x) :
    expectP p (fun x ↦ (boolToReal (x j) - p) * h x) = 0 := by
  rw [expectP_eq_pair p j]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ ↦ ?_)
  rw [flipCoord_same, hh]
  cases x j <;> simp only [coordWeight, boolToReal_true, boolToReal_false, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;> ring

lemma expectP_centered_sq (p : ℝ) (j : Fin n) :
    expectP p (fun x ↦ (boolToReal (x j) - p) ^ 2) = p * (1 - p) := by
  rw [expectP_eq_pair p j]
  have h : ∀ x : Fin n → Bool, ((boolToReal (x j) - p) ^ 2 * coordWeight p (x j) +
      (boolToReal ((flipCoord j x) j) - p) ^ 2 * coordWeight p (!x j)) * offWeight p j x =
      p * (1 - p) * offWeight p j x := by
    intro x
    rw [flipCoord_same]
    cases x j <;> simp only [coordWeight, boolToReal_true, boolToReal_false, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;> ring
  rw [Finset.sum_congr rfl fun x _ ↦ h x, ← Finset.mul_sum, ← mul_assoc, mul_comm (1 / 2 : ℝ),
    mul_assoc, half_sum_offWeight, mul_one]

lemma weight_sub_eq_sum (p : ℝ) (x : Fin n → Bool) :
    weight x - n * p = ∑ j, (boolToReal (x j) - p) := by
  simp [weight, Finset.sum_sub_distrib]

/-- The variance of the binomial count `‖X‖`. -/
lemma expectP_sq_weight_sub (p : ℝ) :
    expectP p (fun x : Fin n → Bool ↦ (weight x - n * p) ^ 2) = n * (p * (1 - p)) := by
  have hexp : ∀ x : Fin n → Bool, (weight x - n * p) ^ 2 =
      ∑ j, ∑ k, (boolToReal (x j) - p) * (boolToReal (x k) - p) := by
    intro x
    rw [weight_sub_eq_sum, sq, Finset.sum_mul_sum]
  have hterm : ∀ j k : Fin n,
      expectP p (fun x ↦ (boolToReal (x j) - p) * (boolToReal (x k) - p)) =
        if j = k then p * (1 - p) else 0 := by
    intro j k
    split_ifs with hjk
    · subst hjk
      simpa [sq] using expectP_centered_sq p j
    · exact expectP_centered_mul p j fun x ↦ by rw [flipCoord_noteq j k x (Ne.symm hjk)]
  simp only [hexp, expectP_sum, hterm, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The derivative of the weights -/

lemma hasDerivAt_coordWeight (p : ℝ) (b : Bool) :
    HasDerivAt (fun q ↦ coordWeight q b) (coordSign b) p := by
  cases b
  · simpa [coordWeight, coordSign] using (hasDerivAt_id p).const_sub 1
  · simpa [coordWeight, coordSign] using hasDerivAt_id' p

/-- The derivative of the product weight. -/
lemma hasDerivAt_weightP (p : ℝ) (x : Fin n → Bool) :
    HasDerivAt (fun q ↦ weightP q x) (∑ i, coordSign (x i) * offWeight p i x) p := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun j q ↦ coordWeight q (x j))
    fun j _ ↦ hasDerivAt_coordWeight p (x j)
  simpa [weightP, offWeight, smul_eq_mul, mul_comm] using h

/-- The derivative of the weight, multiplied by `p (1 - p)`. -/
lemma mul_sum_coordSign_offWeight (p : ℝ) (x : Fin n → Bool) :
    p * (1 - p) * ∑ i, coordSign (x i) * offWeight p i x = (weight x - n * p) * weightP p x := by
  rw [weight_sub_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [weightP_eq_mul_offWeight p i x]
  cases x i <;> simp [coordWeight, coordSign] <;> ring

/-! ### Russo's lemma -/

section Monotone

variable {f : (Fin n → Bool) → ℝ}

lemma flipCoord_le_self {i : Fin n} {x : Fin n → Bool} (hx : x i = true) : flipCoord i x ≤ x := by
  intro k
  by_cases hk : k = i
  · subst hk
    simp [hx]
  · rw [flipCoord_noteq i k x hk]

lemma le_flipCoord_self {i : Fin n} {x : Fin n → Bool} (hx : x i = false) : x ≤ flipCoord i x := by
  intro k
  by_cases hk : k = i
  · subst hk
    simp [hx]
  · rw [flipCoord_noteq i k x hk]

/-- For a monotone Boolean function, the signed difference across a flip is the
indicator that the flip changes the value. -/
lemma coordSign_mul_sub_eq (hf : ∀ x, f x = 0 ∨ f x = 1) (hmono : Monotone f) (i : Fin n)
    (x : Fin n → Bool) :
    coordSign (x i) * (f x - f (flipCoord i x)) = if f x = f (flipCoord i x) then 0 else 1 := by
  cases hx : x i
  · have hle := hmono (le_flipCoord_self hx)
    rcases hf x with h1 | h1 <;> rcases hf (flipCoord i x) with h2 | h2 <;>
      simp_all [coordSign]
    all_goals norm_num at hle
  · have hle := hmono (flipCoord_le_self hx)
    rcases hf x with h1 | h1 <;> rcases hf (flipCoord i x) with h2 | h2 <;>
      simp_all [coordSign]
    all_goals norm_num at hle

/-- The total `p`-influence of a monotone Boolean function, as the termwise derivative. -/
lemma totalInfluenceP_eq_sum (hf : ∀ x, f x = 0 ∨ f x = 1) (hmono : Monotone f) (p : ℝ) :
    totalInfluenceP p f = ∑ x, f x * ∑ i, coordSign (x i) * offWeight p i x := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, totalInfluenceP]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hind : ∀ x, (if f (flipCoord i x) = f (flipCoord i (flipCoord i x)) then (0 : ℝ) else 1) =
      if f x = f (flipCoord i x) then 0 else 1 := by
    intro x
    simp only [flipCoord_flipCoord, eq_comm]
  rw [influenceP, expectP_of_flipCoord_invariant p i hind]
  conv_rhs => rw [sum_eq_half_sum_add_flipCoord i]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← coordSign_mul_sub_eq hf hmono i x, offWeight_flipCoord, flipCoord_same]
  cases x i <;> simp [coordSign] <;> ring

/-- **Russo's lemma (BLM Theorem 9.15).** For a monotone Boolean function `f`, the derivative of
`p ↦ E_p[f]` is the total `p`-influence of `f`. -/
theorem hasDerivAt_expectP (hf : ∀ x, f x = 0 ∨ f x = 1) (hmono : Monotone f) (p : ℝ) :
    HasDerivAt (fun q ↦ expectP q f) (totalInfluenceP p f) p := by
  rw [totalInfluenceP_eq_sum hf hmono]
  exact HasDerivAt.fun_sum fun x _ ↦ (hasDerivAt_weightP p x).const_mul (f x)

/-! ### BLM Corollary 9.16 -/

lemma mul_totalInfluenceP_eq (hf : ∀ x, f x = 0 ∨ f x = 1) (hmono : Monotone f) (p : ℝ) :
    p * (1 - p) * totalInfluenceP p f = expectP p (fun x ↦ (weight x - n * p) * f x) := by
  rw [totalInfluenceP_eq_sum hf hmono, expectP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [mul_left_comm, mul_sum_coordSign_offWeight]
  ring

/-- **BLM Corollary 9.16**, the identity. -/
theorem totalInfluenceP_eq (hf : ∀ x, f x = 0 ∨ f x = 1) (hmono : Monotone f) {p : ℝ}
    (hp : p * (1 - p) ≠ 0) :
    totalInfluenceP p f = expectP p (fun x ↦ (weight x - n * p) * f x) / (p * (1 - p)) := by
  rw [← mul_totalInfluenceP_eq hf hmono, mul_div_cancel_left₀ _ hp]

/-- **BLM Corollary 9.16**, the inequality. -/
theorem totalInfluenceP_le (hf : ∀ x, f x = 0 ∨ f x = 1) (hmono : Monotone f) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    totalInfluenceP p f ≤ √(n * expectP p f / (p * (1 - p))) := by
  have hc : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  have hw : ∀ x : Fin n → Bool, 0 ≤ weightP p x := weightP_nonneg hp0.le hp1.le
  have hf0 : ∀ x, 0 ≤ f x := fun x ↦ by rcases hf x with h | h <;> simp [h]
  have hff : ∀ x, f x ^ 2 = f x := fun x ↦ by rcases hf x with h | h <;> simp [h]
  set E := expectP p (fun x ↦ (weight x - n * p) * f x)
  -- Weighted Cauchy–Schwarz, using `f² = f`.
  have hCS : E ^ 2 ≤ (n * (p * (1 - p))) * expectP p f := by
    rw [← expectP_sq_weight_sub p]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun x _ ↦ mul_nonneg (sq_nonneg _) (hw x)) (fun x _ ↦ mul_nonneg (hf0 x) (hw x))
      fun x _ ↦ le_of_eq ?_
    rw [← hff x]
    ring
  have hI : totalInfluenceP p f = E / (p * (1 - p)) := totalInfluenceP_eq hf hmono hc.ne'
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  rw [hI, div_pow, div_le_div_iff₀ (by positivity) hc]
  nlinarith

end Monotone

/-! ### The uniform case -/

lemma expectP_half (g : (Fin n → Bool) → ℝ) : expectP (1 / 2) g = expect g := by
  simp only [expectP, expect, weightP, coordWeight]
  have h : ∀ x : Fin n → Bool, ∏ j, (if x j = true then (1 / 2 : ℝ) else 1 - 1 / 2) =
      (2 ^ n : ℝ)⁻¹ := by
    intro x
    norm_num [Finset.prod_ite_eq]
  simp only [h, ← Finset.sum_mul]
  ring

lemma influenceP_half (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    influenceP (1 / 2) f i = influence f i :=
  expectP_half _

example (f : (Fin 3 → Bool) → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) (hmono : Monotone f) (p : ℝ) :
    HasDerivAt (fun q ↦ expectP q f) (totalInfluenceP p f) p :=
  hasDerivAt_expectP hf hmono p

end Influence
