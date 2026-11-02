/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Concentration.LogSobolev.Bernoulli

/-!
# Martingale decomposition on the Boolean hypercube

On the uniform hypercube `{±1}^n`, encoded as `Fin n → Bool`, every expectation is a finite average.
This file develops the Doob martingale `f_j = E[f | X_1, …, X_j]` of a function `f` and shows that
both the variance and the Dirichlet form split along its increments.

## Main definitions

* `Influence.expect g`: the uniform average `2⁻ⁿ ∑ₓ g x`.
* `Influence.variance f`, `Influence.ent g`: variance and entropy as finite averages.
* `Influence.dirichletForm u v`: the Dirichlet form
  `𝓔(u, v) = (1/4) ∑ᵢ E[(u - u ∘ flipᵢ) (v - v ∘ flipᵢ)]`.
* `Influence.condFirst f j`: the average of `f` over all but the first `j` coordinates.
* `Influence.martingaleDiff f i`: the increment `condFirst f (i + 1) - condFirst f i`.

## Main results

* `Influence.variance_eq_sum_expect_martingaleDiff_sq`: `Var f = ∑ᵢ E[Δᵢ²]`.
* `Influence.dirichletForm_eq_sum_martingaleDiff`: `𝓔(f) = ∑ᵢ 𝓔(Δᵢ)`.
* `Influence.ent_sq_le_two_mul_dirichletForm`: the Bernoulli log-Sobolev inequality
  `Ent(f²) ≤ 2 𝓔(f)` in finite-average form.
-/

open Real BernoulliLSI

noncomputable section

namespace Influence

variable {n : ℕ}

/-! ### Uniform averages -/

/-- The expectation under the uniform measure on the hypercube, as a finite average. -/
def expect (g : (Fin n → Bool) → ℝ) : ℝ := (2 ^ n : ℝ)⁻¹ * ∑ x, g x

/-- The variance under the uniform measure on the hypercube. -/
def variance (f : (Fin n → Bool) → ℝ) : ℝ := expect (fun x ↦ f x ^ 2) - expect f ^ 2

/-- The entropy `E[g log g] - E[g] log E[g]` under the uniform measure on the hypercube. -/
def ent (g : (Fin n → Bool) → ℝ) : ℝ :=
  expect (fun x ↦ g x * log (g x)) - expect g * log (expect g)

lemma expect_add (g h : (Fin n → Bool) → ℝ) :
    expect (fun x ↦ g x + h x) = expect g + expect h := by
  simp only [expect, Finset.sum_add_distrib, mul_add]

lemma expect_sub (g h : (Fin n → Bool) → ℝ) :
    expect (fun x ↦ g x - h x) = expect g - expect h := by
  simp only [expect, Finset.sum_sub_distrib, mul_sub]

lemma expect_const_mul (c : ℝ) (g : (Fin n → Bool) → ℝ) :
    expect (fun x ↦ c * g x) = c * expect g := by
  simp only [expect, ← Finset.mul_sum]
  ring

lemma expect_div_const (g : (Fin n → Bool) → ℝ) (c : ℝ) :
    expect (fun x ↦ g x / c) = expect g / c := by
  simp only [expect, ← Finset.sum_div]
  ring

lemma expect_sum {ι : Type*} (s : Finset ι) (g : ι → (Fin n → Bool) → ℝ) :
    expect (fun x ↦ ∑ i ∈ s, g i x) = ∑ i ∈ s, expect (g i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

@[simp] lemma expect_const (c : ℝ) : expect (fun _ : Fin n → Bool ↦ c) = c := by
  simp only [expect, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

lemma expect_congr {g h : (Fin n → Bool) → ℝ} (hgh : ∀ x, g x = h x) : expect g = expect h := by
  simp only [expect, hgh]

lemma expect_mono {g h : (Fin n → Bool) → ℝ} (hgh : ∀ x, g x ≤ h x) : expect g ≤ expect h :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ ↦ hgh x) (by positivity)

lemma expect_nonneg {g : (Fin n → Bool) → ℝ} (hg : ∀ x, 0 ≤ g x) : 0 ≤ expect g := by
  have h := expect_mono (g := fun _ ↦ (0 : ℝ)) (h := g) hg
  rwa [expect_const] at h

lemma expect_mul_const (g : (Fin n → Bool) → ℝ) (c : ℝ) :
    expect (fun x ↦ g x * c) = expect g * c := by
  rw [← mul_comm c, ← expect_const_mul]
  exact expect_congr fun x ↦ mul_comm _ _

lemma abs_expect_le (g : (Fin n → Bool) → ℝ) : |expect g| ≤ expect (fun x ↦ |g x|) := by
  simp only [expect, abs_mul, abs_inv, abs_pow, abs_two]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- A nonnegative function with zero expectation vanishes. -/
lemma eq_zero_of_expect_eq_zero {g : (Fin n → Bool) → ℝ} (hg : ∀ x, 0 ≤ g x)
    (h0 : expect g = 0) (x : Fin n → Bool) : g x = 0 := by
  have hsum : ∑ y, g y = 0 := by
    simpa [expect] using h0
  exact (Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦ hg y).mp hsum x (Finset.mem_univ x)

/-! ### Coordinate flips -/

@[simp] lemma flipCoord_flipCoord (i : Fin n) (x : Fin n → Bool) :
    flipCoord i (flipCoord i x) = x :=
  congrFun (flipCoord_involutive i) x

lemma flipCoord_comm {i k : Fin n} (hik : i ≠ k) (x : Fin n → Bool) :
    flipCoord i (flipCoord k x) = flipCoord k (flipCoord i x) := by
  ext j
  simp only [flipCoord, Function.update_apply]
  split_ifs <;> simp_all

/-- Flipping a coordinate preserves the uniform measure. -/
lemma expect_comp_flipCoord (i : Fin n) (g : (Fin n → Bool) → ℝ) :
    expect (fun x ↦ g (flipCoord i x)) = expect g := by
  simp only [expect]
  congr 1
  exact Equiv.sum_comp (Function.Involutive.toPerm _ fun x ↦ flipCoord_flipCoord i x) g

/-- The average of `g` and `g ∘ flipᵢ`. -/
def flipAvg (i : Fin n) (g : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : ℝ :=
  (g x + g (flipCoord i x)) / 2

lemma expect_flipAvg (i : Fin n) (g : (Fin n → Bool) → ℝ) :
    expect (flipAvg i g) = expect g := by
  unfold flipAvg
  rw [expect_div_const, expect_add, expect_comp_flipCoord]
  ring

/-- If `h` is invariant under `flipᵢ`, then `E[g h] = E[(flipAvg i g) h]`. -/
lemma expect_mul_eq_expect_flipAvg_mul (i : Fin n) (g : (Fin n → Bool) → ℝ)
    {h : (Fin n → Bool) → ℝ} (hh : ∀ x, h (flipCoord i x) = h x) :
    expect (fun x ↦ g x * h x) = expect (fun x ↦ flipAvg i g x * h x) := by
  rw [← expect_flipAvg i]
  exact expect_congr fun x ↦ by simp only [flipAvg, hh]; ring

/-! ### The Dirichlet form -/

/-- The Dirichlet form `𝓔(u, v) = (1/4) ∑ᵢ E[(u - u ∘ flipᵢ) (v - v ∘ flipᵢ)]`. -/
def dirichletForm (u v : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / 4) * ∑ i, expect (fun x ↦ (u x - u (flipCoord i x)) * (v x - v (flipCoord i x)))

lemma dirichletForm_self_nonneg (u : (Fin n → Bool) → ℝ) : 0 ≤ dirichletForm u u := by
  unfold dirichletForm
  exact mul_nonneg (by norm_num) <| Finset.sum_nonneg fun i _ ↦
    expect_nonneg fun x ↦ mul_self_nonneg _

lemma dirichletForm_const_left (c : ℝ) (v : (Fin n → Bool) → ℝ) :
    dirichletForm (fun _ ↦ c) v = 0 := by
  simp [dirichletForm]

/-- Expanding the Dirichlet form of a sum. -/
lemma dirichletForm_add_self (a b : (Fin n → Bool) → ℝ) :
    dirichletForm (fun x ↦ a x + b x) (fun x ↦ a x + b x) =
      dirichletForm a a + 2 * dirichletForm b a + dirichletForm b b := by
  have key : ∀ i : Fin n,
      expect (fun x ↦ (a x + b x - (a (flipCoord i x) + b (flipCoord i x))) *
        (a x + b x - (a (flipCoord i x) + b (flipCoord i x)))) =
      expect (fun x ↦ (a x - a (flipCoord i x)) * (a x - a (flipCoord i x))) +
        2 * expect (fun x ↦ (b x - b (flipCoord i x)) * (a x - a (flipCoord i x))) +
        expect (fun x ↦ (b x - b (flipCoord i x)) * (b x - b (flipCoord i x))) := by
    intro i
    rw [← expect_const_mul, ← expect_add, ← expect_add]
    exact expect_congr fun x ↦ by ring
  simp only [dirichletForm, key, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- One coordinate of the Dirichlet form: `E[(u - u∘σ)(v - v∘σ)] = 2 E[u (v - v∘σ)]`. -/
lemma expect_flip_diff_mul (i : Fin n) (u v : (Fin n → Bool) → ℝ) :
    expect (fun x ↦ (u x - u (flipCoord i x)) * (v x - v (flipCoord i x))) =
      2 * expect (fun x ↦ u x * (v x - v (flipCoord i x))) := by
  have hswap : expect (fun x ↦ u (flipCoord i x) * (v x - v (flipCoord i x))) =
      -expect (fun x ↦ u x * (v x - v (flipCoord i x))) := by
    rw [← expect_comp_flipCoord i (fun x ↦ u x * (v x - v (flipCoord i x))),
      eq_neg_iff_add_eq_zero, ← expect_add]
    refine (expect_congr (h := fun _ ↦ (0 : ℝ)) fun x ↦ ?_).trans (expect_const 0)
    simp only [flipCoord_flipCoord]
    ring
  have hsplit : expect (fun x ↦ (u x - u (flipCoord i x)) * (v x - v (flipCoord i x))) =
      expect (fun x ↦ u x * (v x - v (flipCoord i x))) -
        expect (fun x ↦ u (flipCoord i x) * (v x - v (flipCoord i x))) := by
    rw [← expect_sub]
    exact expect_congr fun x ↦ by ring
  rw [hsplit, hswap]
  ring

/-! ### The martingale decomposition -/

/-- The point that agrees with `x` on the first `j` coordinates and with `y` on the rest. -/
def mix (j : ℕ) (x y : Fin n → Bool) : Fin n → Bool :=
  fun k ↦ if (k : ℕ) < j then x k else y k

/-- The conditional expectation `E[f | X_1, …, X_j]`: average `f` over the last `n - j`
coordinates. -/
def condFirst (f : (Fin n → Bool) → ℝ) (j : ℕ) (x : Fin n → Bool) : ℝ :=
  expect (fun y ↦ f (mix j x y))

/-- The martingale increment `Δᵢ = f_{i+1} - f_i` (0-indexed). -/
def martingaleDiff (f : (Fin n → Bool) → ℝ) (i : ℕ) (x : Fin n → Bool) : ℝ :=
  condFirst f (i + 1) x - condFirst f i x

/-- M1: `f_n = f`. -/
lemma condFirst_n (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : condFirst f n x = f x := by
  have hmix : ∀ y, mix n x y = x := fun y ↦ funext fun k ↦ by simp [mix]
  simp only [condFirst, hmix, expect_const]

/-- M1: `f_0 = E f`. -/
lemma condFirst_zero (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    condFirst f 0 x = expect f := by
  have hmix : ∀ y, mix 0 x y = y := fun y ↦ funext fun k ↦ by simp [mix]
  simp only [condFirst, hmix]

/-- M2: `f_j` only depends on the first `j` coordinates. -/
lemma condFirst_flipCoord_of_le (f : (Fin n → Bool) → ℝ) {j : ℕ} {i : Fin n} (hji : j ≤ i)
    (x : Fin n → Bool) : condFirst f j (flipCoord i x) = condFirst f j x := by
  have hmix : ∀ y, mix j (flipCoord i x) y = mix j x y := by
    intro y
    funext k
    simp only [mix]
    split_ifs with hk
    · exact flipCoord_noteq i k x fun h ↦ by subst h; omega
    · rfl
  simp only [condFirst, hmix]

@[simp] lemma mix_apply_self (i : Fin n) (x y : Fin n → Bool) : mix i x y i = y i := by
  simp [mix]

lemma mix_flipCoord_left (i : Fin n) (x y : Fin n → Bool) :
    mix i (flipCoord i x) y = mix i x y := by
  funext k
  simp only [mix]
  split_ifs with hk
  · exact flipCoord_noteq i k x fun h ↦ by subst h; omega
  · rfl

lemma mix_flipCoord_right (i : Fin n) (x y : Fin n → Bool) :
    mix i x (flipCoord i y) = Function.update (mix i x y) i (!y i) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [mix, flipCoord]
  · simp only [mix, Function.update_of_ne hk, flipCoord_noteq i k y hk]

lemma mix_succ (i : Fin n) (a z : Fin n → Bool) :
    mix (i + 1) a z = Function.update (mix i a z) i (a i) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [mix]
  · have hk' : (k : ℕ) ≠ i := fun h ↦ hk (Fin.ext h)
    simp only [mix, Function.update_of_ne hk]
    split_ifs <;> first | rfl | omega

lemma mix_flip_sum (f : (Fin n → Bool) → ℝ) (i : Fin n) (x y : Fin n → Bool) :
    f (mix i x y) + f (mix i x (flipCoord i y)) =
      f (mix (i + 1) x y) + f (mix (i + 1) (flipCoord i x) y) := by
  rw [mix_succ, mix_succ, mix_flipCoord_left, mix_flipCoord_right, flipCoord_same]
  have hM : Function.update (mix i x y) i (y i) = mix i x y := by
    conv_lhs => rw [← mix_apply_self i x y]
    exact Function.update_eq_self _ _
  by_cases h : x i = y i
  · rw [h, hM]
  · have h' : x i = !y i := by cases hx : x i <;> cases hy : y i <;> simp_all
    rw [h', Bool.not_not, hM, add_comm]

/-- M3: averaging `f_{i+1}` over coordinate `i` gives `f_i`. -/
lemma flipAvg_condFirst_succ (f : (Fin n → Bool) → ℝ) (i : Fin n) (x : Fin n → Bool) :
    flipAvg i (condFirst f (i + 1)) x = condFirst f i x := by
  rw [condFirst, ← expect_flipAvg i]
  unfold flipAvg
  simp only [mix_flip_sum]
  rw [expect_div_const, expect_add]
  rfl

/-- M3, corollary: `flipAvg i Δᵢ = 0`. -/
lemma flipAvg_martingaleDiff (f : (Fin n → Bool) → ℝ) (i : Fin n) (x : Fin n → Bool) :
    flipAvg i (martingaleDiff f i) x = 0 := by
  have h3 := flipAvg_condFirst_succ f i x
  have h2 := condFirst_flipCoord_of_le f (le_refl (i : ℕ)) x
  simp only [flipAvg, martingaleDiff] at h3 ⊢
  linarith

/-- `Δᵢ` is invariant under flips of later coordinates. -/
lemma martingaleDiff_flipCoord (f : (Fin n → Bool) → ℝ) {i : ℕ} {k : Fin n} (hik : i < k)
    (x : Fin n → Bool) : martingaleDiff f i (flipCoord k x) = martingaleDiff f i x := by
  simp only [martingaleDiff, condFirst_flipCoord_of_le f hik, condFirst_flipCoord_of_le f hik.le]

/-- M4: `Δᵢ` is orthogonal to every function invariant under `flipᵢ`. -/
lemma expect_martingaleDiff_mul_eq_zero (f : (Fin n → Bool) → ℝ) (i : Fin n)
    {h : (Fin n → Bool) → ℝ} (hh : ∀ x, h (flipCoord i x) = h x) :
    expect (fun x ↦ martingaleDiff f i x * h x) = 0 := by
  rw [expect_mul_eq_expect_flipAvg_mul i _ hh]
  simp [flipAvg_martingaleDiff]

lemma flipCoord_mix_succ (i : Fin n) (x y : Fin n → Bool) :
    flipCoord i (mix (i + 1) x y) = mix (i + 1) (flipCoord i x) y := by
  rw [mix_succ, mix_succ, mix_flipCoord_left, flipCoord_same]
  simp [flipCoord]

/-- Averaging `flipAvg i g` over the coordinates after `i` gives `condFirst g i`. -/
lemma condFirst_flipAvg (g : (Fin n → Bool) → ℝ) (i : Fin n) (x : Fin n → Bool) :
    condFirst (flipAvg i g) (i + 1) x = condFirst g i x := by
  rw [← flipAvg_condFirst_succ]
  simp only [condFirst, flipAvg, flipCoord_mix_succ]
  rw [expect_div_const, expect_add]

/-- The tower property `E[f_j] = E[f]`. -/
lemma expect_condFirst (g : (Fin n → Bool) → ℝ) :
    ∀ j ≤ n, expect (condFirst g j) = expect g
  | 0, _ => by
    rw [show condFirst g 0 = fun _ ↦ expect g from funext (condFirst_zero g), expect_const]
  | j + 1, hj => by
    rw [← expect_flipAvg ⟨j, hj⟩, ← expect_condFirst g j (by omega)]
    exact expect_congr fun x ↦ flipAvg_condFirst_succ g ⟨j, hj⟩ x

/-- Telescoping: `f - E f = ∑ᵢ Δᵢ`. -/
lemma sum_martingaleDiff (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    ∑ i : Fin n, martingaleDiff f i x = f x - expect f := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ martingaleDiff f i x)]
  simp only [martingaleDiff]
  rw [Finset.sum_range_sub (fun j ↦ condFirst f j x), condFirst_n, condFirst_zero]

lemma variance_eq_expect_sub_sq (f : (Fin n → Bool) → ℝ) :
    variance f = expect (fun x ↦ (f x - expect f) ^ 2) := by
  have : (fun x ↦ (f x - expect f) ^ 2) =
      fun x ↦ (f x ^ 2 + (-2 * expect f) * f x) + expect f ^ 2 := by
    funext x
    ring
  rw [this, expect_add, expect_add, expect_const_mul, expect_const, variance]
  ring

lemma expect_martingaleDiff_mul_martingaleDiff (f : (Fin n → Bool) → ℝ) {i j : Fin n}
    (hij : i ≠ j) :
    expect (fun x ↦ martingaleDiff f i x * martingaleDiff f j x) = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [← expect_martingaleDiff_mul_eq_zero f j (h := martingaleDiff f i)
      (fun x ↦ martingaleDiff_flipCoord f h x)]
    exact expect_congr fun x ↦ mul_comm _ _
  · exact expect_martingaleDiff_mul_eq_zero f i fun x ↦ martingaleDiff_flipCoord f h x

lemma variance_nonneg (f : (Fin n → Bool) → ℝ) : 0 ≤ variance f := by
  rw [variance_eq_expect_sub_sq]
  exact expect_nonneg fun x ↦ sq_nonneg _

/-- M5: `Var f = ∑ᵢ E[Δᵢ²]`. -/
theorem variance_eq_sum_expect_martingaleDiff_sq (f : (Fin n → Bool) → ℝ) :
    variance f = ∑ i : Fin n, expect (fun x ↦ martingaleDiff f i x ^ 2) := by
  rw [variance_eq_expect_sub_sq]
  have hsq : ∀ x, (f x - expect f) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, martingaleDiff f i x * martingaleDiff f j x := by
    intro x
    rw [← sum_martingaleDiff, sq, Finset.sum_mul_sum]
  rw [expect_congr hsq, expect_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [expect_sum, Finset.sum_eq_single i
    (fun j _ hji ↦ expect_martingaleDiff_mul_martingaleDiff f (Ne.symm hji))
    (fun h ↦ absurd (Finset.mem_univ i) h)]
  exact expect_congr fun x ↦ (sq _).symm

/-- M6: `𝓔(Δᵢ, f_i) = 0`. -/
lemma dirichletForm_martingaleDiff_condFirst (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    dirichletForm (martingaleDiff f i) (condFirst f i) = 0 := by
  unfold dirichletForm
  rw [Finset.sum_eq_zero, mul_zero]
  intro k _
  rw [expect_flip_diff_mul]
  by_cases hik : (i : ℕ) ≤ k
  · simp [condFirst_flipCoord_of_le f hik]
  · have hki : k ≠ i := fun h ↦ hik (h ▸ le_refl _)
    rw [expect_martingaleDiff_mul_eq_zero f i, mul_zero]
    intro x
    rw [flipCoord_comm hki, condFirst_flipCoord_of_le f (le_refl (i : ℕ)),
      condFirst_flipCoord_of_le f (le_refl (i : ℕ))]

/-- M7: `𝓔(f) = ∑ᵢ 𝓔(Δᵢ)`. -/
theorem dirichletForm_eq_sum_martingaleDiff (f : (Fin n → Bool) → ℝ) :
    dirichletForm f f = ∑ i : Fin n, dirichletForm (martingaleDiff f i) (martingaleDiff f i) := by
  have hstep : ∀ i : Fin n, dirichletForm (condFirst f (i + 1)) (condFirst f (i + 1)) -
      dirichletForm (condFirst f i) (condFirst f i) =
        dirichletForm (martingaleDiff f i) (martingaleDiff f i) := by
    intro i
    have hsucc : condFirst f (i + 1) = fun x ↦ condFirst f i x + martingaleDiff f i x := by
      funext x
      simp only [martingaleDiff]
      ring
    rw [hsucc, dirichletForm_add_self, dirichletForm_martingaleDiff_condFirst]
    ring
  simp only [← hstep]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ dirichletForm (condFirst f (i + 1))
      (condFirst f (i + 1)) - dirichletForm (condFirst f i) (condFirst f i)),
    Finset.sum_range_sub (fun j ↦ dirichletForm (condFirst f j) (condFirst f j))]
  have hn : condFirst f n = f := funext (condFirst_n f)
  have h0 : condFirst f 0 = fun _ ↦ expect f := funext (condFirst_zero f)
  rw [hn, h0, dirichletForm_const_left, sub_zero]

/-! ### Log-Sobolev in finite-average form -/

/-- The Bernoulli log-Sobolev inequality (`bernoulli_logSobolev`) in the form
`Ent(f²) ≤ 2 𝓔(f)`. -/
theorem ent_sq_le_two_mul_dirichletForm (f : (Fin n → Bool) → ℝ) :
    ent (fun x ↦ f x ^ 2) ≤ 2 * dirichletForm f f := by
  have h := bernoulli_logSobolev n f
  rw [entropy_def'] at h
  simp only [bernoulli_integral, gradientNormSq] at h
  have hrhs : (1 / 2 : ℝ) * ((2 ^ n : ℝ)⁻¹ *
      ∑ ε, ∑ j, (f ε - f (flipCoord j ε)) ^ 2) = 2 * dirichletForm f f := by
    simp only [dirichletForm, expect, ← sq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun ε _ ↦ ?_
    ring
  rw [hrhs] at h
  exact h

end Influence
