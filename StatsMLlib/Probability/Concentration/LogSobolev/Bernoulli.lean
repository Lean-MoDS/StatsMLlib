/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import StatsMLlib.Probability.Entropy.Basic
import StatsMLlib.Probability.Entropy.Conditional.Subadditivity
import StatsMLlib.Probability.Concentration.LogSobolev.TwoPoint
import StatsMLlib.Probability.Gaussian.Poincare.Limit
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Logic.Function.Basic

/-!
# Bernoulli Log-Sobolev Inequality

This file proves the Bernoulli log-Sobolev inequality on the hypercube {±1}^n.

## Main definitions

* `flipCoord j ε`: Flip the j-th coordinate of ε, replacing ε_j with -ε_j
* `bernoulliUniform n`: The uniform measure on {±1}^n (balanced Bernoulli product)
* `boolUniform`: The uniform probability measure on `Bool`
* `signValue`: Maps Bool to ±1 ∈ ℝ

## Main results

* `bernoulliUniform_eq_pi`: `bernoulliUniform n` is the product of `n` copies of `boolUniform`.
* `condEntExceptCoord_sq_eq_twoPointEntropyCoord`: on the hypercube, the conditional entropy of
  `h²` given all coordinates but `j` is the two-point entropy of `h²` along coordinate `j`.
* `bernoulli_logSobolev`: For any h : {±1}^n → ℝ,
  Ent_μ(h²) ≤ (1/2) · E_μ[Σⱼ (h(ε) - h(flip_j ε))²]
* `bernoulli_logSobolev_app`: Application to compactly supported smooth functions f:
  Ent_{S_n}(f²) ≤ (1/2) · Σᵢ E[(f(S_n) - f(S_n with coord i flipped))²]

## Proof approach

Since `bernoulliUniform n` is a product measure, the subadditivity of entropy
(`SubAddEnt.entropy_subadditive`) bounds `Ent_μ(h²)` by the sum over coordinates of the expected
conditional entropies. Each conditional entropy is a two-point entropy, which the Rothaus lemma
(`LogSobolev.rothaus_lemma`) bounds by half the squared difference across the flip.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Function
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

namespace BernoulliLSI

/-!
## Part 1: Sign values and coordinate flips
-/

/-- Map Bool to ±1 ∈ ℝ: True ↦ +1, False ↦ -1 -/
def signValue (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem signValue_true : signValue true = 1 := rfl
@[simp] theorem signValue_false : signValue false = -1 := rfl

/-- Sign values are ±1, so their square is 1 -/
@[simp] theorem signValue_sq (b : Bool) : (signValue b)^2 = 1 := by
  cases b <;> simp [signValue]

/-- The sign of the negated value -/
@[simp] theorem signValue_not (b : Bool) : signValue (!b) = -signValue b := by
  cases b <;> simp [signValue]

variable {n : ℕ}

/-- Flip the j-th coordinate: ε^(j) has ε_j replaced by ¬ε_j -/
def flipCoord (j : Fin n) (ε : Fin n → Bool) : Fin n → Bool :=
  update ε j (!ε j)

/-- Flipping the same coordinate twice returns the original -/
theorem flipCoord_involutive (j : Fin n) : flipCoord j ∘ flipCoord j = id := by
  ext ε i
  simp only [comp_apply, id_eq, flipCoord]
  by_cases h : i = j
  · subst h; simp only [update_self, Bool.not_not]
  · rw [update_of_ne h, update_of_ne h]

/-- The j-th coordinate after flip -/
@[simp] theorem flipCoord_same (j : Fin n) (ε : Fin n → Bool) :
    (flipCoord j ε) j = !ε j := by
  simp [flipCoord]

/-- Other coordinates are unchanged after flip -/
theorem flipCoord_noteq (j i : Fin n) (ε : Fin n → Bool) (h : i ≠ j) :
    (flipCoord j ε) i = ε i := by
  simp only [flipCoord, update_of_ne h]

/-!
## Part 2: Bernoulli measure on the hypercube

The uniform measure on {±1}^n is the counting measure normalized by 2^n.
-/

/-- The uniform measure on Fin n → Bool (representing {±1}^n).
    Each point has probability 1/2^n. -/
def bernoulliUniform (n : ℕ) : Measure (Fin n → Bool) :=
  ((Finset.univ : Finset (Fin n → Bool)).card : ℝ≥0∞)⁻¹ • Measure.count

/-- The number of elements in Fin n → Bool is 2^n -/
theorem card_fin_bool (n : ℕ) : Finset.card (Finset.univ : Finset (Fin n → Bool)) = 2^n := by
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- The Bernoulli uniform measure is a probability measure -/
instance (n : ℕ) : IsProbabilityMeasure (bernoulliUniform n) := by
  constructor
  unfold bernoulliUniform
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.count_apply_finite Set.univ Set.finite_univ]
  simp only [Set.Finite.toFinset_univ, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  rw [ENNReal.inv_mul_cancel]
  · -- 2^n ≠ 0
    apply pow_ne_zero
    norm_num
  · -- 2^n ≠ ⊤
    exact ENNReal.pow_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

/-- The measure is invariant under coordinate flips -/
theorem bernoulli_flip_invariance (j : Fin n) :
    (bernoulliUniform n).map (flipCoord j) = bernoulliUniform n := by
  -- flipCoord j is a bijection (involutive) and count is invariant under bijections
  unfold bernoulliUniform
  have hinv : (flipCoord j).Involutive := fun ε => by
    simp only [flipCoord]
    ext i
    by_cases h : i = j
    · subst h; simp only [update_self, Bool.not_not]
    · rw [update_of_ne h, update_of_ne h]
  have hmeas : Measurable (flipCoord j) := measurable_of_finite _
  rw [Measure.map_smul _ hmeas.aemeasurable]
  congr 1
  -- Show count measure is invariant under bijection
  ext s hs
  rw [Measure.map_apply hmeas hs]
  have hs1 : (flipCoord j ⁻¹' s).Finite := Set.toFinite _
  have hs2 : s.Finite := Set.toFinite _
  rw [Measure.count_apply_finite _ hs1]
  rw [Measure.count_apply_finite _ hs2]
  -- Need: hs1.toFinset.card = hs2.toFinset.card
  -- This follows from bijection: preimage of s under bijection has same cardinality
  have h_eq : hs1.toFinset = hs2.toFinset.image (flipCoord j) := by
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_image]
    constructor
    · intro hx
      exact ⟨flipCoord j x, hx, hinv x⟩
    · rintro ⟨y, hy, rfl⟩
      convert hy using 1
      exact hinv y
  rw [h_eq, Finset.card_image_of_injective _ hinv.injective]

/-- Integral over bernoulliUniform equals sum divided by 2^n.
    This is the fundamental property of the uniform measure on finite types. -/
theorem bernoulli_integral_eq_sum {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    ∫ ε, f ε ∂(bernoulliUniform n) = (∑ ε : Fin n → Bool, f ε) / 2^n := by
  unfold bernoulliUniform
  rw [integral_smul_measure]
  rw [MeasureTheory.integral_fintype (Integrable.of_finite : Integrable f Measure.count)]
  rw [card_fin_bool n]
  simp only [Nat.cast_pow, Nat.cast_ofNat, smul_eq_mul, count_real_singleton, one_mul]
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  ring

/-- The uniform probability measure on `Bool`. -/
def boolUniform : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

lemma boolUniform_singleton (b : Bool) : boolUniform {b} = (2 : ℝ≥0∞)⁻¹ := by
  simp [boolUniform]

instance : IsProbabilityMeasure boolUniform := by
  constructor
  rw [boolUniform, Measure.smul_apply, Measure.count_apply_finite Set.univ Set.finite_univ]
  simp only [Set.Finite.toFinset_univ, Finset.card_univ, Fintype.card_bool, Nat.cast_ofNat,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma integral_boolUniform (g : Bool → ℝ) :
    ∫ b, g b ∂boolUniform = (g true + g false) / 2 := by
  rw [integral_fintype (Integrable.of_finite : Integrable g boolUniform)]
  simp [measureReal_def, boolUniform_singleton, Fintype.univ_bool]
  ring

lemma bernoulliUniform_singleton (ε : Fin n → Bool) :
    bernoulliUniform n {ε} = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [bernoulliUniform, Measure.smul_apply, Measure.count_singleton, card_fin_bool]
  simp

/-- The uniform measure on the hypercube is the product of uniform measures on `Bool`. -/
theorem bernoulliUniform_eq_pi (n : ℕ) :
    bernoulliUniform n = Measure.pi fun _ : Fin n ↦ boolUniform := by
  refine Measure.ext_of_singleton fun ε ↦ ?_
  rw [← Set.univ_pi_singleton, Measure.pi_pi, Set.univ_pi_singleton, bernoulliUniform_singleton]
  simp [boolUniform_singleton, ENNReal.inv_pow]

/-- Sum over Fin (n+1) → Bool decomposes as sum over slices by the last coordinate. -/
theorem sum_fin_succ_bool_eq_sum_snoc {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    ∑ ε : Fin (n+1) → Bool, f ε =
    ∑ ε' : Fin n → Bool, (f (Fin.snoc ε' true) + f (Fin.snoc ε' false)) := by
  -- Use Fin.snocEquiv: (Fin (n+1) → α) ≃ α × (Fin n → α) at last position
  -- But we need (Fin n → α) × α, so use Prod.swap
  let h_equiv : (Fin (n+1) → Bool) ≃ (Fin n → Bool) × Bool :=
    (Fin.snocEquiv (fun _ => Bool)).symm.trans (Equiv.prodComm _ _)
  calc ∑ ε : Fin (n+1) → Bool, f ε
      = ∑ p : (Fin n → Bool) × Bool, f (h_equiv.symm p) := by
          rw [Fintype.sum_equiv h_equiv.symm]
          simp
    _ = ∑ ε' : Fin n → Bool, ∑ b : Bool, f (h_equiv.symm (ε', b)) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ ε' : Fin n → Bool, (f (h_equiv.symm (ε', true)) + f (h_equiv.symm (ε', false))) := by
          congr 1
          ext ε'
          simp only [Fintype.sum_bool]
    _ = ∑ ε' : Fin n → Bool, (f (Fin.snoc ε' true) + f (Fin.snoc ε' false)) := by
          congr 1

/-- Integral over bernoulliUniform (n+1) splits into average over slices.
    This expresses that summing over (Fin (n+1) → Bool) equals summing over
    pairs (ε', b) with ε' : Fin n → Bool and b : Bool, weighted by 1/2 each. -/
theorem bernoulli_integral_succ_split {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    ∫ ε, f ε ∂(bernoulliUniform (n+1)) =
    ∫ ε', (f (Fin.snoc ε' true) + f (Fin.snoc ε' false)) / 2 ∂(bernoulliUniform n) := by
  rw [bernoulli_integral_eq_sum, bernoulli_integral_eq_sum]
  rw [sum_fin_succ_bool_eq_sum_snoc]
  rw [pow_succ]
  rw [Finset.sum_div]
  -- Goal: ∑ i, (f true + f false) / (2^n * 2) = (∑ i, (f true + f false) / 2) / 2^n
  -- Rewrite RHS: (∑ (x/2)) / 2^n = ∑ (x / (2 * 2^n)) = ∑ (x / (2^n * 2))
  rw [Finset.sum_div]
  congr 1
  ext i
  ring

/-! ## Part 3: Entropy on the hypercube -/

/-- The sum over all coordinate differences -/
def gradientNormSq (n : ℕ) (h : (Fin n → Bool) → ℝ) (ε : Fin n → Bool) : ℝ :=
  ∑ j : Fin n, (h ε - h (flipCoord j ε))^2

/-! ## Part 4: Coordinate flips and integrals on the hypercube -/

/-- Flipping the last coordinate swaps true/false -/
theorem flipCoord_last_snoc {n : ℕ} (ε' : Fin n → Bool) (b : Bool) :
    flipCoord (Fin.last n) (Fin.snoc ε' b) = Fin.snoc ε' (!b) := by
  ext i
  by_cases h : i = Fin.last n
  · simp only [h, flipCoord_same, Fin.snoc_last]
  · have hi : i.val < n := by
      have hlt := i.isLt
      have hne : i.val ≠ n := by
        intro heq
        apply h; ext; simp [Fin.last, heq]
      omega
    have hne' : i ≠ Fin.last n := fun heq => h heq
    rw [flipCoord_noteq (Fin.last n) i _ hne']
    simp only [Fin.snoc, hi, ↓reduceDIte]

/-- Flipping a coordinate in the first n doesn't affect the last coordinate -/
theorem flipCoord_castSucc_snoc {n : ℕ} (j : Fin n) (ε' : Fin n → Bool) (b : Bool) :
    flipCoord (Fin.castSucc j) (Fin.snoc ε' b) = Fin.snoc (flipCoord j ε') b := by
  ext i
  by_cases hi_last : i = Fin.last n
  · -- i is the last index
    simp only [hi_last, Fin.snoc_last]
    have hne : Fin.last n ≠ Fin.castSucc j := by
      intro heq
      have hval : (Fin.last n).val = (Fin.castSucc j).val := congrArg Fin.val heq
      simp only [Fin.last, Fin.val_castSucc] at hval
      omega
    rw [flipCoord_noteq (Fin.castSucc j) (Fin.last n) _ hne]
    simp [Fin.snoc]
  · -- i is not the last index
    have hi : i.val < n := by
      have hlt := i.isLt
      have hne : i.val ≠ n := by
        intro heq
        apply hi_last; ext; simp [Fin.last, heq]
      omega
    by_cases hj : i = Fin.castSucc j
    · -- i = castSucc j
      subst hj
      simp only [flipCoord_same, Fin.snoc]
      have hi' : (Fin.castSucc j).val < n := by simp [Fin.val_castSucc]
      simp only [hi', ↓reduceDIte]
      -- Need to show !ε'(castLT (castSucc j)) = flipCoord j ε' (castLT (castSucc j))
      have hcast_eq : Fin.castLT (Fin.castSucc j) hi' = j := by
        ext; simp [Fin.castLT, Fin.castSucc]
      simp only [hcast_eq, flipCoord_same, cast_eq]
    · -- i ≠ castSucc j
      have hne' : i ≠ Fin.castSucc j := hj
      rw [flipCoord_noteq (Fin.castSucc j) i _ hne']
      simp only [Fin.snoc, hi, ↓reduceDIte]
      have hj' : Fin.castLT i hi ≠ j := by
        intro heq
        apply hj
        ext
        simp only [Fin.val_castSucc]
        exact congrArg Fin.val heq
      rw [flipCoord_noteq j (Fin.castLT i hi) _ hj']

/-- Entropy equals ∫ f log f - (∫ f) log(∫ f) by definition -/
theorem entropy_def' {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    LogSobolev.entropy μ f = ∫ ω, f ω * log (f ω) ∂μ - (∫ ω, f ω ∂μ) * log (∫ ω, f ω ∂μ) := rfl

/-- For the Bernoulli uniform measure, integral is a weighted sum -/
theorem bernoulli_integral {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    ∫ ε, f ε ∂(bernoulliUniform n) =
    (2^n : ℝ)⁻¹ * ∑ ε : Fin n → Bool, f ε := by
  unfold bernoulliUniform
  rw [integral_smul_measure, card_fin_bool]
  simp only [Nat.cast_pow, Nat.cast_ofNat, smul_eq_mul]
  rw [ENNReal.toReal_inv]
  congr 1
  rw [integral_count]

/-- The gradient sum splits into individual coordinate contributions -/
theorem integral_gradientNormSq_eq_sum {n : ℕ} (h : (Fin n → Bool) → ℝ) :
    ∫ ε, gradientNormSq n h ε ∂(bernoulliUniform n) =
    ∑ j : Fin n, ∫ ε, (h ε - h (flipCoord j ε))^2 ∂(bernoulliUniform n) := by
  simp only [gradientNormSq]
  rw [integral_finsetSum]
  intro j _
  apply Integrable.of_finite

/-!
## Part 5: The two-point entropy

Conditioning on all coordinates but one leaves a two-point distribution. Its entropy is bounded
by the Rothaus lemma from `TwoPoint.lean`.
-/

/-- The two-point entropy for coordinate j given all other coordinates.
    This is the entropy of the function (h(ε_{-j}, true)², h(ε_{-j}, false)²)
    under the uniform distribution on {true, false}. -/
def twoPointEntropyCoord {n : ℕ} (j : Fin n) (h : (Fin n → Bool) → ℝ)
    (ε : Fin n → Bool) : ℝ :=
  let a := (h ε)^2
  let b := (h (flipCoord j ε))^2
  (a * log a + b * log b) / 2 - (a + b) / 2 * log ((a + b) / 2)

/-- The two-point entropy is bounded by the squared difference via Rothaus -/
theorem twoPointEntropyCoord_le_gradientTerm {n : ℕ} (j : Fin n)
    (h : (Fin n → Bool) → ℝ) (ε : Fin n → Bool) :
    twoPointEntropyCoord j h ε ≤ (h ε - h (flipCoord j ε))^2 / 2 := by
  unfold twoPointEntropyCoord
  set a := (h ε)^2 with ha_def
  set b := (h (flipCoord j ε))^2 with hb_def
  have ha_nn : 0 ≤ a := sq_nonneg _
  have hb_nn : 0 ≤ b := sq_nonneg _
  by_cases ha_pos : 0 < a
  · by_cases hb_pos : 0 < b
    · -- Both positive: apply Rothaus lemma
      have hrothaus := LogSobolev.rothaus_lemma ha_pos hb_pos
      -- √a = |h(ε)| and √b = |h(flip ε)| (using sqrt_sq_eq_abs, no nonnegativity needed)
      have hsqrt_a : sqrt a = |h ε| := sqrt_sq_eq_abs (h ε)
      have hsqrt_b : sqrt b = |h (flipCoord j ε)| := sqrt_sq_eq_abs (h (flipCoord j ε))
      -- Use reverse triangle inequality: ||x| - |y|| ≤ |x - y|, then square both sides
      have h_rev_tri : (|h ε| - |h (flipCoord j ε)|)^2 ≤ (h ε - h (flipCoord j ε))^2 := by
        rw [sq_le_sq]
        exact abs_abs_sub_abs_le_abs_sub (h ε) (h (flipCoord j ε))
      calc (a * log a + b * log b) / 2 - (a + b) / 2 * log ((a + b) / 2)
          ≤ (sqrt a - sqrt b)^2 / 2 := hrothaus
        _ = (|h ε| - |h (flipCoord j ε)|)^2 / 2 := by rw [hsqrt_a, hsqrt_b]
        _ ≤ (h ε - h (flipCoord j ε))^2 / 2 := by linarith [h_rev_tri]
    · -- b = 0
      have hb_zero : b = 0 := le_antisymm (not_lt.mp hb_pos) hb_nn
      simp only [hb_zero, add_zero, mul_zero, log_zero]
      by_cases ha_zero : a = 0
      · simp [ha_zero]; positivity
      · have h_lhs : a * log a / 2 - a / 2 * log (a / 2) = a / 2 * log 2 := by
          rw [log_div ha_zero (by norm_num : (2 : ℝ) ≠ 0)]
          ring
        rw [h_lhs]
        have h_flip_zero : h (flipCoord j ε) = 0 := sq_eq_zero_iff.mp hb_zero
        rw [h_flip_zero, sub_zero, sq]
        have hlog2_le : log 2 ≤ 1 := by
          have h1 : (2 : ℝ) < exp 1 := by
            have : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
            linarith
          have h2 : log 2 < log (exp 1) := log_lt_log (by norm_num : (0 : ℝ) < 2) h1
          simp only [log_exp] at h2
          linarith
        calc a / 2 * log 2 ≤ a / 2 * 1 := by nlinarith [hlog2_le, ha_nn]
          _ = a / 2 := by ring
          _ = h ε * h ε / 2 := by rw [ha_def]; ring_nf
  · -- a = 0
    have ha_zero : a = 0 := le_antisymm (not_lt.mp ha_pos) ha_nn
    simp only [ha_zero, zero_add, zero_mul, log_zero]
    by_cases hb_zero : b = 0
    · simp [hb_zero]; positivity
    · have h_lhs : b * log b / 2 - b / 2 * log (b / 2) = b / 2 * log 2 := by
        rw [log_div hb_zero (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      rw [h_lhs]
      have h_ε_zero : h ε = 0 := sq_eq_zero_iff.mp ha_zero
      rw [h_ε_zero, zero_sub, neg_sq]
      have hlog2_le : log 2 ≤ 1 := by
        have h1 : (2 : ℝ) < exp 1 := by
          have : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
          linarith
        have h2 : log 2 < log (exp 1) := log_lt_log (by norm_num : (0 : ℝ) < 2) h1
        simp only [log_exp] at h2
        linarith
      calc b / 2 * log 2 ≤ b / 2 * 1 := by nlinarith [hlog2_le, hb_nn]
        _ = b / 2 := by ring
        _ = h (flipCoord j ε) ^ 2 / 2 := by rw [hb_def]

/-- φ(x) = x log x is convex on [0, ∞), so φ((a+b)/2) ≤ (φ(a) + φ(b))/2 -/
theorem phi_convex_avg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 * log ((a + b) / 2) ≤ (a * log a + b * log b) / 2 := by
  by_cases hab : a + b = 0
  · -- If a + b = 0, then a = b = 0
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · -- Otherwise, use convexity of x log x
    have hconv := Real.convexOn_mul_log
    have ha_mem : a ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr ha
    have hb_mem : b ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hb
    have h12 : (0 : ℝ) ≤ 1/2 := by norm_num
    have h12' : (1/2 : ℝ) + 1/2 = 1 := by norm_num
    have hkey := hconv.2 ha_mem hb_mem h12 h12 h12'
    simp only [smul_eq_mul] at hkey
    have hmid_eq : (1/2 : ℝ) * a + (1/2) * b = (a + b) / 2 := by ring
    rw [hmid_eq] at hkey
    calc (a + b) / 2 * log ((a + b) / 2)
        ≤ (1/2) * (a * log a) + (1/2) * (b * log b) := hkey
      _ = (a * log a + b * log b) / 2 := by ring

/-- The two-point entropy is always nonnegative (consequence of Jensen) -/
theorem twoPointEntropyCoord_nonneg {n : ℕ} (j : Fin n) (h : (Fin n → Bool) → ℝ)
    (ε : Fin n → Bool) :
    0 ≤ twoPointEntropyCoord j h ε := by
  unfold twoPointEntropyCoord
  set a := (h ε)^2
  set b := (h (flipCoord j ε))^2
  have ha_nn : 0 ≤ a := sq_nonneg _
  have hb_nn : 0 ≤ b := sq_nonneg _
  -- By Jensen: (a+b)/2 * log((a+b)/2) ≤ (a log a + b log b)/2
  have hconv := phi_convex_avg a b ha_nn hb_nn
  linarith

/-- The average two-point entropy over all ε is bounded by the average gradient term -/
theorem avg_twoPointEntropyCoord_le {n : ℕ} (j : Fin n)
    (h : (Fin n → Bool) → ℝ) :
    ∫ ε, twoPointEntropyCoord j h ε ∂(bernoulliUniform n) ≤
    ∫ ε, (h ε - h (flipCoord j ε))^2 / 2 ∂(bernoulliUniform n) := by
  apply integral_mono_of_nonneg
  · -- The two-point entropy is nonneg (a.e.)
    filter_upwards with ε
    exact twoPointEntropyCoord_nonneg j h ε
  · -- The RHS is integrable
    apply Integrable.of_finite
  · -- Pointwise bound
    apply Eventually.of_forall
    intro ε
    exact twoPointEntropyCoord_le_gradientTerm j h ε

/-!
### Subadditivity of entropy on the hypercube

The uniform measure on the hypercube is a product measure, so the general subadditivity of entropy
applies, and its conditional entropies are the two-point entropies above.
-/

/-- The conditional entropy of `h²` given all coordinates but `j` is the two-point entropy. -/
lemma condEntExceptCoord_sq_eq_twoPointEntropyCoord (j : Fin n) (h : (Fin n → Bool) → ℝ)
    (ε : Fin n → Bool) :
    SubAddEnt.condEntExceptCoord (μs := fun _ ↦ boolUniform) j (fun ε ↦ h ε ^ 2) ε =
      twoPointEntropyCoord j h ε := by
  simp only [SubAddEnt.condEntExceptCoord, condExpExceptCoord, integral_boolUniform,
    twoPointEntropyCoord, flipCoord]
  cases hε : ε j
  · have h1 : update ε j false = ε := by rw [← hε, update_eq_self]
    rw [h1, Bool.not_false]
    ring_nf
  · have h1 : update ε j true = ε := by rw [← hε, update_eq_self]
    rw [h1, Bool.not_true]

/-- The main bound: subadditivity of entropy reduces `Ent(h²)` to two-point entropies, each of
which is bounded by the Rothaus inequality. -/
theorem entropy_le_half_gradient {n : ℕ} (h : (Fin n → Bool) → ℝ) :
    LogSobolev.entropy (bernoulliUniform n) (fun ε => (h ε)^2) ≤
    (1/2) * ∫ ε, gradientNormSq n h ε ∂(bernoulliUniform n) := by
  calc LogSobolev.entropy (bernoulliUniform n) (fun ε => (h ε)^2)
      ≤ ∑ j : Fin n, ∫ ε, twoPointEntropyCoord j h ε ∂(bernoulliUniform n) := by
        rw [bernoulliUniform_eq_pi]
        refine (SubAddEnt.entropy_subadditive (μs := fun _ ↦ boolUniform) _
          (measurable_of_finite _) (ae_of_all _ fun ε ↦ sq_nonneg (h ε)) Integrable.of_finite
          Integrable.of_finite).trans_eq ?_
        simp_rw [condEntExceptCoord_sq_eq_twoPointEntropyCoord]
    _ ≤ ∑ j : Fin n, ∫ ε, (h ε - h (flipCoord j ε))^2 / 2 ∂(bernoulliUniform n) := by
        apply Finset.sum_le_sum
        intro j _
        exact avg_twoPointEntropyCoord_le j h
    _ = ∫ ε, ∑ j : Fin n, (h ε - h (flipCoord j ε))^2 / 2 ∂(bernoulliUniform n) := by
        rw [← integral_finsetSum]
        intro j _
        exact Integrable.of_finite
    _ = ∫ ε, (∑ j : Fin n, (h ε - h (flipCoord j ε))^2) / 2 ∂(bernoulliUniform n) := by
        congr 1
        ext ε
        rw [Finset.sum_div]
    _ = (1/2) * ∫ ε, ∑ j : Fin n, (h ε - h (flipCoord j ε))^2 ∂(bernoulliUniform n) := by
        rw [← integral_const_mul]
        congr 1
        ext ε
        ring
    _ = (1/2) * ∫ ε, gradientNormSq n h ε ∂(bernoulliUniform n) := by
        rfl

/-!
## Part 6: Main Theorem - Bernoulli Log-Sobolev Inequality
-/

/-- The Bernoulli log-Sobolev inequality.

For any function h : {±1}^n → ℝ,
  Ent_μ(h²) ≤ (1/2) · E_μ[Σⱼ (h(ε) - h(flip_j ε))²]

where μ is the uniform measure on the hypercube.

Note: The nonnegativity hypothesis was removed using the reverse triangle inequality
to show that (|h(ε)| - |h(flip_j ε)|)² ≤ (h(ε) - h(flip_j ε))². -/
theorem bernoulli_logSobolev (n : ℕ) (h : (Fin n → Bool) → ℝ) :
    LogSobolev.entropy (bernoulliUniform n) (fun ε => (h ε)^2) ≤
    (1/2) * ∫ ε, gradientNormSq n h ε ∂(bernoulliUniform n) :=
  -- Direct application of entropy_le_half_gradient
  entropy_le_half_gradient h

/-!
## Part 7: Application to Compactly Supported Smooth Functions

This section connects the Bernoulli log-Sobolev inequality on the Boolean hypercube
to compactly supported smooth functions via the Rademacher sum formulation.
-/

open EfronSteinApp GaussianPoincare

/-- Map from Boolean hypercube to Rademacher space: True ↦ 1, False ↦ -1. -/
def toRademacher {n : ℕ} (ε : Fin n → Bool) : RademacherSpace n :=
  fun i => signValue (ε i)

/-- The inverse map: 1 ↦ True, -1 ↦ False (partial, defined on support). -/
def fromRademacher {n : ℕ} (x : RademacherSpace n)
    (_hx : ∀ i, x i = 1 ∨ x i = -1) : Fin n → Bool :=
  fun i => (x i = 1)

/-- toRademacher is injective -/
theorem toRademacher_injective (n : ℕ) : Function.Injective (toRademacher (n := n)) := by
  intro ε₁ ε₂ h
  ext i
  have hi : signValue (ε₁ i) = signValue (ε₂ i) := congrFun h i
  cases hb₁ : ε₁ i <;> cases hb₂ : ε₂ i <;> simp_all [signValue]
  · norm_num at hi
  · norm_num at hi

/-- Flipping coordinate j on Bool corresponds to negating coordinate j on Rademacher space -/
theorem toRademacher_flipCoord {n : ℕ} (j : Fin n) (ε : Fin n → Bool) :
    toRademacher (flipCoord j ε) = Function.update (toRademacher ε) j (-(toRademacher ε j)) := by
  ext i
  simp only [toRademacher, Function.update]
  by_cases h : i = j
  · subst h
    simp only [flipCoord_same, signValue_not, dite_eq_left]
  · simp only [dite_eq_right h]
    rw [flipCoord_noteq j i ε h]

/-- The Rademacher sum after coordinate flip equals the shifted sum -/
theorem rademacherSumProd_flip_eq_shifted {n : ℕ} [NeZero n] (j : Fin n)
    (x : RademacherSpace n) (_hx : x j = 1 ∨ x j = -1) :
    rademacherSumProd n (Function.update x j (-x j)) = rademacherSumShifted n j x := by
  unfold rademacherSumProd rademacherSumShifted
  have hsum : ∑ i : Fin n, Function.update x j (-x j) i =
      (∑ i : Fin n, x i) - 2 * x j := by
    have h1 : Function.update x j (-x j) j = -x j := Function.update_self j (-x j) x
    have h2 : ∀ i ∈ Finset.univ, i ≠ j → Function.update x j (-x j) i = x i :=
      fun i _ hi => Function.update_of_ne hi (-x j) x
    calc ∑ i : Fin n, Function.update x j (-x j) i
        = Function.update x j (-x j) j +
            ∑ i ∈ Finset.univ.erase j, Function.update x j (-x j) i := by
          exact (Finset.add_sum_erase Finset.univ
            (fun i : Fin n => Function.update x j (-x j) i) (Finset.mem_univ j)).symm
      _ = -x j + ∑ i ∈ Finset.univ.erase j, x i := by
          rw [h1]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact h2 i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
      _ = -x j + (∑ i : Fin n, x i - x j) := by
          have hsum_erase : ∑ i ∈ Finset.univ.erase j, x i = ∑ i : Fin n, x i - x j := by
            have hsplit := Finset.add_sum_erase Finset.univ (fun i : Fin n => x i) (Finset.mem_univ j)
            linarith
          rw [hsum_erase]
      _ = (∑ i : Fin n, x i) - 2 * x j := by ring
  rw [hsum]
  unfold rademacherSumProd
  ring

/-- toRademacher is measurable since Fin n → Bool is finite -/
theorem measurable_toRademacher {n : ℕ} : Measurable (toRademacher (n := n)) :=
  measurable_of_finite _

/-- rademacherSumProd is continuous since it's a linear combination of coordinate functions. -/
theorem continuous_rademacherSumProd (n : ℕ) : Continuous (rademacherSumProd n) := by
  unfold rademacherSumProd
  have hsum : Continuous (fun x : RademacherSpace n => ∑ i : Fin n, x i) := by
    apply continuous_finsetSum
    intro i _
    exact continuous_apply i
  exact hsum.const_smul ((√n)⁻¹)

/-- Key lemma: The bernoulliUniform measure pushes forward to rademacherProductMeasure via toRademacher. -/
theorem bernoulliUniform_map_toRademacher {n : ℕ} :
    (bernoulliUniform n).map toRademacher = rademacherProductMeasure n := by
  -- Both measures are probability measures supported on {±1}^n with equal weights
  -- We prove equality by showing they agree on all measurable rectangles
  ext s hs
  -- Use induction on n via product measure structure
  induction n with
  | zero =>
    -- For n = 0, both spaces are singletons
    simp only [bernoulliUniform, rademacherProductMeasure, Measure.map_apply measurable_toRademacher hs]
    -- Simplify LHS: (1⁻¹ • count) = count since 1⁻¹ = 1 in ENNReal
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      pow_zero, Nat.cast_one, inv_one, one_smul]
    -- For n = 0, Measure.pi of empty gives Dirac at the unique point
    rw [Measure.pi_of_empty (fun _ : Fin 0 => RademacherApprox.rademacherMeasure)]
    -- Now: count (toRademacher⁻¹' s) = dirac (fun _ => 1) s
    -- The unique element of Fin 0 → Bool maps to fun _ => 1 under toRademacher
    have huniq : ∀ ε : Fin 0 → Bool, toRademacher ε = fun _ : Fin 0 => (1 : ℝ) := by
      intro ε; ext i; exact Fin.elim0 i
    -- The unique element of Fin 0 → ℝ
    have helem : (fun _ : Fin 0 => (1 : ℝ)) = (fun a : Fin 0 => isEmptyElim a) := by
      ext i; exact Fin.elim0 i
    by_cases h : (fun _ : Fin 0 => (1 : ℝ)) ∈ s
    · have hpre : toRademacher⁻¹' s = Set.univ := by
        ext ε; simp only [Set.mem_preimage, Set.mem_univ, huniq ε, h]
      rw [hpre]
      simp only [Measure.count_univ]
      rw [Measure.dirac_apply' _ hs]
      have hmem : (fun a : Fin 0 => isEmptyElim a) ∈ s := by rw [← helem]; exact h
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool, pow_zero, Nat.cast_one]
      norm_cast
    · have hpre : toRademacher⁻¹' s = ∅ := by
        ext ε; simp only [Set.mem_preimage, Set.mem_empty_iff_false, huniq ε, h]
      rw [hpre, measure_empty]
      rw [Measure.dirac_apply' _ hs]
      have hnotmem : (fun a : Fin 0 => isEmptyElim a) ∉ s := by rw [← helem]; exact h
      simp only [Set.indicator_of_notMem hnotmem]
  | succ n ih =>
    -- Both measures are discrete probability measures with equal weights on {±1}^{n+1}
    -- Expand the LHS using map_apply
    simp only [Measure.map_apply measurable_toRademacher hs]
    -- Now: bernoulliUniform (n+1) (toRademacher⁻¹' s) = rademacherProductMeasure (n+1) s
    unfold bernoulliUniform
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      Measure.smul_apply, smul_eq_mul]
    -- Rewrite using count on finite preimage
    rw [Measure.count_apply (measurable_toRademacher hs)]
    -- Step 1: Show (rademacherProductMeasure (n+1)) {toRademacher ε} = 2^{-(n+1)} for each ε
    have hsingleton : ∀ ε : Fin (n+1) → Bool,
        (rademacherProductMeasure (n+1)) {toRademacher ε} = ((2 : ℝ≥0∞)^(n+1))⁻¹ := by
      intro ε
      rw [← Set.univ_pi_singleton (toRademacher ε)]
      unfold rademacherProductMeasure
      rw [Measure.pi_pi (fun _ => RademacherApprox.rademacherMeasure)]
      -- Each factor is rademacherMeasure {toRademacher ε i} = 1/2
      have h_each : ∀ i : Fin (n+1), RademacherApprox.rademacherMeasure {toRademacher ε i} = 1/2 := by
        intro i
        unfold toRademacher signValue RademacherApprox.rademacherMeasure
        simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
        rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
        simp only [Set.indicator_apply, Set.mem_singleton_iff]
        by_cases hb : ε i
        · -- Case ε i = true, so value is 1
          simp only [hb]
          norm_num
        · -- Case ε i = false, so value is -1
          simp only [hb]
          norm_num
      simp_rw [h_each]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      -- (1/2)^(n+1) = (2^{n+1})⁻¹
      simp only [one_div, ENNReal.inv_pow]
    -- Key: Show that toRademacher is a bijection onto the support of rademacherProductMeasure
    -- and both measures assign weight 2^{-(n+1)} to each point
    have hrange_char : ∀ x : RademacherSpace (n+1),
        x ∈ Set.range toRademacher ↔ ∀ i, x i = 1 ∨ x i = -1 := by
      intro x
      constructor
      · rintro ⟨ε, rfl⟩ i
        unfold toRademacher signValue
        by_cases h : ε i <;> simp [h]
      · intro hx
        -- Construct the preimage
        use fun i => x i = 1
        ext i
        unfold toRademacher signValue
        simp only []
        cases hx i with
        | inl h => simp [h]
        | inr h => simp only [h, decide_eq_false (by linarith : ¬(-1 : ℝ) = 1)]; rfl
    -- The measure is concentrated on the range
    have hsupp : (rademacherProductMeasure (n+1)) (Set.range toRademacher)ᶜ = 0 := by
      -- Every coordinate is ±1 a.e., so a.e. x is in range
      have hae : ∀ᵐ x ∂(rademacherProductMeasure (n+1)), x ∈ Set.range toRademacher := by
        -- Use hrange_char: x ∈ range ↔ ∀ i, x i = 1 ∨ x i = -1
        simp only [hrange_char]
        -- Need to show: ∀ᵐ x, ∀ i, x i = 1 ∨ x i = -1
        rw [ae_all_iff]
        intro i
        exact coord_values_ae (n+1) i
      -- If a.e. x ∈ S, then μ(Sᶜ) = 0
      exact mem_ae_iff.mp hae
    have hsum : (rademacherProductMeasure (n+1)) s =
        ∑ ε : Fin (n+1) → Bool, (rademacherProductMeasure (n+1)) (s ∩ {toRademacher ε}) := by
      -- μ s = μ (s ∩ range) = ∑_{ε} μ (s ∩ {toRademacher ε})
      have heq : (rademacherProductMeasure (n+1)) s =
          (rademacherProductMeasure (n+1)) (s ∩ Set.range toRademacher) := by
        rw [← measure_inter_add_sdiff s (Set.finite_range toRademacher).measurableSet]
        have h0 : (rademacherProductMeasure (n+1)) (s \ Set.range toRademacher) = 0 := by
          apply measure_mono_null (Set.sdiff_subset_compl _ _) hsupp
        rw [h0, add_zero]
      rw [heq]
      -- range toRademacher = ⋃ ε, {toRademacher ε}
      have hrange_eq : Set.range toRademacher =
          ⋃ ε : Fin (n+1) → Bool, {toRademacher ε} := by
        ext x; simp only [Set.mem_range, Set.mem_iUnion, Set.mem_singleton_iff, eq_comm]
      rw [hrange_eq, Set.inter_iUnion]
      rw [measure_iUnion]
      · exact tsum_fintype _
      · -- Disjoint singletons
        intro i j hij
        simp only [Set.disjoint_iff]
        intro x ⟨h1, h2⟩
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff] at h1 h2
        have heq : toRademacher i = toRademacher j := h1.2.symm.trans h2.2
        exact hij (toRademacher_injective (n+1) heq)
      · -- Measurable singletons
        intro i
        exact hs.inter (measurableSet_singleton _)
    -- Now compute each term: μ(s ∩ {toRademacher ε}) = indicator(toRademacher ε ∈ s) * 2^{-(n+1)}
    have hterm : ∀ ε : Fin (n+1) → Bool, (rademacherProductMeasure (n+1)) (s ∩ {toRademacher ε}) =
        Set.indicator s (fun _ => ((2 : ℝ≥0∞)^(n+1))⁻¹) (toRademacher ε) := by
      intro ε
      by_cases h : toRademacher ε ∈ s
      · have heq : s ∩ {toRademacher ε} = {toRademacher ε} := by
          ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
          constructor
          · exact And.right
          · intro hx; exact ⟨hx ▸ h, hx⟩
        rw [heq, hsingleton, Set.indicator_of_mem h]
      · have heq : s ∩ {toRademacher ε} = ∅ := by
          ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro hx hxs; exact h (hxs ▸ hx)
        rw [heq, measure_empty, Set.indicator_of_notMem h]
    simp_rw [hsum, hterm]
    -- ∑ ε, indicator s _ (toRademacher ε) = 2^{-(n+1)} * |toRademacher⁻¹' s|
    have : DecidablePred fun i => toRademacher i ∈ s := Classical.decPred _
    rw [Finset.sum_indicator_eq_sum_filter, Finset.sum_const]
    -- Convert nsmul to mul and relate cardinalities
    rw [nsmul_eq_mul, mul_comm]
    congr 1
    -- Show (toRademacher ⁻¹' s).encard = ↑(filter card)
    · -- The filter is equivalent to the preimage
      have hfinite : (toRademacher ⁻¹' s).Finite := Set.toFinite _
      have heq_card : (Finset.filter (fun i => toRademacher i ∈ s) Finset.univ).card =
          hfinite.toFinset.card := by
        congr 1
        ext ε
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.Finite.mem_toFinset,
          Set.mem_preimage]
      rw [heq_card, hfinite.encard_eq_coe_toFinset_card]
      simp only [ENat.toENNReal_coe]
    -- Show (↑(2 ^ (n + 1)))⁻¹ = (2 ^ (n + 1))⁻¹
    · simp only [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]

/-- Key lemma: The integral of f(S_n(toRademacher ε)) over bernoulliUniform equals
    the integral of f(S_n(x)) over rademacherProductMeasure. -/
theorem bernoulli_integral_eq_rademacher_integral {n : ℕ} [NeZero n]
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ ε, f (rademacherSumProd n (toRademacher ε)) ∂(bernoulliUniform n) =
    ∫ x, f (rademacherSumProd n x) ∂(rademacherProductMeasure n) := by
  -- Use the measure equality and integral_map
  rw [← bernoulliUniform_map_toRademacher]
  rw [integral_map measurable_toRademacher.aemeasurable]
  -- f ∘ rademacherSumProd is continuous hence AEStronglyMeasurable
  exact (hf.comp (continuous_rademacherSumProd n)).aestronglyMeasurable

/-- Key lemma: Entropy is preserved under the measure isomorphism. -/
theorem entropy_bernoulli_eq_rademacher {n : ℕ} [NeZero n]
    {g : RademacherSpace n → ℝ} (hg : Continuous g) :
    LogSobolev.entropy (bernoulliUniform n) (fun ε => (g (toRademacher ε))^2) =
    LogSobolev.entropy (rademacherProductMeasure n) (fun x => (g x)^2) := by
  -- Use the measure isomorphism: bernoulliUniform.map toRademacher = rademacherProductMeasure
  unfold LogSobolev.entropy
  -- The function g² is continuous, hence strongly measurable
  have hgsq : Continuous (fun x => (g x)^2) := hg.pow 2
  have hglog : Continuous (fun x => (g x)^2 * log ((g x)^2)) := hgsq.mul_log
  -- We show each integral part is equal using integral_map
  have h1 : ∫ x, (g x)^2 * log ((g x)^2) ∂(rademacherProductMeasure n) =
            ∫ ε, (g (toRademacher ε))^2 * log ((g (toRademacher ε))^2) ∂(bernoulliUniform n) := by
    rw [← bernoulliUniform_map_toRademacher]
    rw [integral_map measurable_toRademacher.aemeasurable hglog.aestronglyMeasurable]
  have h2 : ∫ x, (g x)^2 ∂(rademacherProductMeasure n) =
            ∫ ε, (g (toRademacher ε))^2 ∂(bernoulliUniform n) := by
    rw [← bernoulliUniform_map_toRademacher]
    rw [integral_map measurable_toRademacher.aemeasurable hgsq.aestronglyMeasurable]
  rw [h1, h2]

/-- Key lemma: The gradient term transforms correctly. -/
theorem gradient_eq_sum_shifted {n : ℕ} [NeZero n] {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ ε, gradientNormSq n (fun ε' => f (rademacherSumProd n (toRademacher ε'))) ε
      ∂(bernoulliUniform n) =
    ∑ j : Fin n, ∫ x, (f (rademacherSumProd n x) - f (rademacherSumShifted n j x))^2
      ∂(rademacherProductMeasure n) := by
  -- Step 1: Expand gradientNormSq
  simp only [gradientNormSq]
  -- Step 2: Exchange integral and sum (integral of sum = sum of integrals for finite sums)
  rw [integral_finsetSum Finset.univ (fun j _ => Integrable.of_finite)]
  -- Step 3: For each term, show the integrand is the same after using flip-to-shifted correspondence
  congr 1
  ext j
  have hflip : ∀ ε, rademacherSumProd n (toRademacher (flipCoord j ε)) =
                   rademacherSumShifted n j (toRademacher ε) := by
    intro ε
    rw [toRademacher_flipCoord]
    apply rademacherSumProd_flip_eq_shifted
    -- Need to show toRademacher ε j = 1 ∨ toRademacher ε j = -1
    unfold toRademacher signValue
    simp only [ite_eq_left_iff, ite_eq_right_iff]
    by_cases h : ε j
    · left; simp [h]
    · right; simp [h]
  -- Rewrite the integrand
  have heq : ∀ ε, (f (rademacherSumProd n (toRademacher ε)) -
                  f (rademacherSumProd n (toRademacher (flipCoord j ε))))^2 =
                 (f (rademacherSumProd n (toRademacher ε)) -
                  f (rademacherSumShifted n j (toRademacher ε)))^2 := by
    intro ε; rw [hflip]
  simp_rw [heq]
  -- Step 4: Transfer integral from bernoulliUniform to rademacherProductMeasure
  -- Use bernoulliUniform_map_toRademacher and integral_map (in symmetric form)
  symm
  rw [← bernoulliUniform_map_toRademacher]
  -- The integrand is continuous, hence AEStronglyMeasurable
  have hcont_sum : Continuous (rademacherSumProd n) := continuous_rademacherSumProd n
  have hcont_shifted : Continuous (rademacherSumShifted n j) := by
    unfold rademacherSumShifted
    apply Continuous.sub hcont_sum
    apply Continuous.div_const
    exact continuous_const.mul (continuous_apply j)
  have hcont_integrand : Continuous (fun x => (f (rademacherSumProd n x) -
                                               f (rademacherSumShifted n j x))^2) := by
    apply Continuous.pow
    apply Continuous.sub (hf.comp hcont_sum) (hf.comp hcont_shifted)
  rw [integral_map measurable_toRademacher.aemeasurable hcont_integrand.aestronglyMeasurable]

/-- Key lemma: Entropy under pushforward for continuous functions. -/
theorem entropy_map_eq {n : ℕ} [NeZero n] {f : ℝ → ℝ} (hf : Continuous f) :
    LogSobolev.entropy (rademacherLaw n).toMeasure (fun x => (f x)^2) =
    LogSobolev.entropy (rademacherProductMeasure n) (fun x => (f (rademacherSumProd n x))^2) := by
  -- The law of S_n is the pushforward of the product measure
  -- Entropy(μ.map g)(φ) = Entropy(μ)(φ ∘ g) by the pushforward property
  unfold rademacherLaw LogSobolev.entropy
  simp only [ProbabilityMeasure.coe_mk]
  have hmeas : Measurable (rademacherSumProd n) := measurable_rademacherSumProd n
  have haem : AEMeasurable (rademacherSumProd n) (rademacherProductMeasure n) := hmeas.aemeasurable
  -- For the integrands, we need AEStronglyMeasurable
  have hfsq : Continuous (fun x => (f x)^2) := hf.pow 2
  have hlog : Continuous (fun x => (f x)^2 * Real.log ((f x)^2)) :=
    hfsq.mul_log
  -- Both integrals are over finite measures, so use integral_map
  congr 1
  · -- The f*log(f) integral
    rw [integral_map haem hlog.aestronglyMeasurable]
  · -- The mean integral
    congr 1
    · rw [integral_map haem hfsq.aestronglyMeasurable]
    · rw [integral_map haem hfsq.aestronglyMeasurable]

/-- **Application of Bernoulli Log-Sobolev to Compactly Supported Smooth Functions**

For f ∈ C_c²(ℝ) (compactly supported, twice continuously differentiable), the entropy
of f² under the law of the Rademacher sum S_{n+1} is bounded by half the expected
sum of squared differences:

  Ent_{S_{n+1}}(f²) ≤ (1/2) · ∑ᵢ E[(f(S_{n+1}) - f(S_{n+1} with coord i flipped))²]

This is the continuous-function version of the Bernoulli log-Sobolev inequality,
which serves as a key intermediate step toward the Gaussian log-Sobolev inequality
via the central limit theorem. -/
theorem bernoulli_logSobolev_app {f : ℝ → ℝ} (hf : CompactlySupportedSmooth f) (n : ℕ) :
    LogSobolev.entropy (rademacherLaw (n + 1)).toMeasure (fun x => (f x)^2) ≤
    (1/2) * ∑ i : Fin (n + 1), ∫ x,
        (f (rademacherSumProd (n + 1) x) - f (rademacherSumShifted (n + 1) i x))^2
          ∂rademacherProductMeasure (n + 1) := by
  -- Step 1: Transfer entropy from rademacherLaw to rademacherProductMeasure
  rw [entropy_map_eq hf.continuous]
  -- Step 2: Transfer from rademacherProductMeasure to bernoulliUniform via toRademacher
  have hg_cont : Continuous (fun x => f (rademacherSumProd (n + 1) x)) :=
    hf.continuous.comp (continuous_rademacherSumProd (n + 1))
  rw [← entropy_bernoulli_eq_rademacher hg_cont]
  -- Step 3: Apply the discrete Bernoulli log-Sobolev inequality
  have hbound := bernoulli_logSobolev (n + 1)
    (fun ε => f (rademacherSumProd (n + 1) (toRademacher ε)))
  -- Step 4: Transform the RHS to the sum of squared differences
  calc LogSobolev.entropy (bernoulliUniform (n + 1))
        (fun ε => (f (rademacherSumProd (n + 1) (toRademacher ε)))^2)
      ≤ (1/2) * ∫ ε, gradientNormSq (n + 1)
          (fun ε' => f (rademacherSumProd (n + 1) (toRademacher ε'))) ε
          ∂(bernoulliUniform (n + 1)) := hbound
    _ = (1/2) * ∑ i : Fin (n + 1), ∫ x,
          (f (rademacherSumProd (n + 1) x) - f (rademacherSumShifted (n + 1) i x))^2
            ∂rademacherProductMeasure (n + 1) := by
        rw [gradient_eq_sum_shifted hf.continuous]

end BernoulliLSI

end
