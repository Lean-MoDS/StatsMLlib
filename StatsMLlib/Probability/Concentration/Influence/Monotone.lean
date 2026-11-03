/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Concentration.Influence.Basic

/-!
# Reduction to monotone Boolean functions

On the uniform hypercube `{±1}^n`, encoded as `Fin n → Bool`, the shift operator `Sᵢ` pushes
the mass of a Boolean function towards `xᵢ = 1`: on each pair `{x, flipᵢ x}` it puts the larger
value on the point with `xᵢ = 1`. It preserves the expectation and does not increase the total
influence. A maximal-potential argument then shows that every Boolean function can be replaced by
a monotone one with the same expectation and no larger total influence.

## Main definitions

* `Influence.boolToReal b`: the embedding `false ↦ 0`, `true ↦ 1` of `Bool` into `ℝ`.
* `Influence.shift i g`: the shift operator `Sᵢ` on Boolean functions.

## Main results

* `Influence.expect_shift`: `E[Sᵢ g] = E[g]`.
* `Influence.totalInfluence_shift_le`: `I(Sᵢ g) ≤ I(g)`.
* `Influence.exists_monotone` (BLM Theorem 9.10): for every Boolean `f` there is a monotone Boolean
  `g` with `E[g] = E[f]` and `I(g) ≤ I(f)`.

## Implementation notes

Instead of iterating the shifts until the function becomes monotone, we take a function of
maximal potential `φ(g) = E[g(x) ‖x‖]` among those with the right expectation and total
influence; a non-monotone function would be improved by some shift.
-/

open BernoulliLSI

noncomputable section

namespace Influence

variable {n : ℕ}

/-! ### The embedding of `Bool` into `ℝ` -/

/-- The embedding `false ↦ 0`, `true ↦ 1`. -/
def boolToReal (b : Bool) : ℝ := if b then 1 else 0

@[simp] lemma boolToReal_true : boolToReal true = 1 := rfl

@[simp] lemma boolToReal_false : boolToReal false = 0 := rfl

@[simp] lemma boolToReal_inj {a b : Bool} : boolToReal a = boolToReal b ↔ a = b := by
  cases a <;> cases b <;> simp

lemma monotone_boolToReal : Monotone boolToReal := by
  intro a b hab
  cases a <;> cases b <;> simp_all [Bool.le_iff_imp]

/-! ### Symmetrization over a flip -/

/-- Comparing two averages pair by pair over `{x, flipᵢ x}`. -/
lemma expect_le_of_pair (i : Fin n) {h k : (Fin n → Bool) → ℝ}
    (hhk : ∀ x, h x + h (flipCoord i x) ≤ k x + k (flipCoord i x)) : expect h ≤ expect k := by
  have H := expect_mono hhk
  rw [expect_add, expect_add, expect_comp_flipCoord, expect_comp_flipCoord] at H
  linarith

lemma expect_eq_of_pair (i : Fin n) {h k : (Fin n → Bool) → ℝ}
    (hhk : ∀ x, h x + h (flipCoord i x) = k x + k (flipCoord i x)) : expect h = expect k :=
  le_antisymm (expect_le_of_pair i fun x ↦ (hhk x).le)
    (expect_le_of_pair i fun x ↦ (hhk x).ge)

lemma expect_lt_of_pair (i : Fin n) {h k : (Fin n → Bool) → ℝ}
    (hhk : ∀ x, h x + h (flipCoord i x) ≤ k x + k (flipCoord i x))
    {x₀ : Fin n → Bool} (hx₀ : h x₀ + h (flipCoord i x₀) < k x₀ + k (flipCoord i x₀)) :
    expect h < expect k := by
  have H : expect (fun x ↦ h x + h (flipCoord i x)) <
      expect (fun x ↦ k x + k (flipCoord i x)) := by
    simp only [expect]
    exact mul_lt_mul_of_pos_left (Finset.sum_lt_sum (fun x _ ↦ hhk x)
      ⟨x₀, Finset.mem_univ _, hx₀⟩) (by positivity)
  rw [expect_add, expect_add, expect_comp_flipCoord, expect_comp_flipCoord] at H
  linarith

/-! ### The shift operator -/

/-- The shift `Sᵢ g`: on each pair `{x, flipᵢ x}`, the point with `xᵢ = true` receives
`g x ∨ g (flipᵢ x)` and the other one receives `g x ∧ g (flipᵢ x)`. -/
def shift (i : Fin n) (g : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  if x i then g x || g (flipCoord i x) else g x && g (flipCoord i x)

lemma shift_flipCoord (i : Fin n) (g : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    shift i g (flipCoord i x) =
      if x i then g (flipCoord i x) && g x else g (flipCoord i x) || g x := by
  cases hx : x i <;> simp [shift, hx]

/-- The shift preserves the expectation. -/
lemma expect_shift (i : Fin n) (g : (Fin n → Bool) → Bool) :
    expect (fun x ↦ boolToReal (shift i g x)) = expect (fun x ↦ boolToReal (g x)) := by
  refine expect_eq_of_pair i fun x ↦ ?_
  rw [shift_flipCoord]
  unfold shift
  cases x i <;> cases g x <;> cases g (flipCoord i x) <;> simp

/-- The shift preserves the influence of its own coordinate. -/
lemma influence_shift_self (i : Fin n) (g : (Fin n → Bool) → Bool) :
    influence (fun x ↦ boolToReal (shift i g x)) i = influence (fun x ↦ boolToReal (g x)) i := by
  refine expect_congr fun x ↦ ?_
  simp only [boolToReal_inj]
  rw [shift_flipCoord]
  unfold shift
  cases x i <;> cases g x <;> cases g (flipCoord i x) <;> simp

/-- The shift does not increase the influence of the other coordinates. -/
lemma influence_shift_le {i j : Fin n} (hij : i ≠ j) (g : (Fin n → Bool) → Bool) :
    influence (fun x ↦ boolToReal (shift i g x)) j ≤ influence (fun x ↦ boolToReal (g x)) j := by
  refine expect_le_of_pair i fun x ↦ ?_
  simp only [boolToReal_inj]
  rw [shift_flipCoord, flipCoord_comm hij.symm, shift_flipCoord]
  unfold shift
  rw [flipCoord_noteq j i x hij, flipCoord_comm hij]
  cases x i <;> cases g x <;> cases g (flipCoord i x) <;> cases g (flipCoord j x) <;>
    cases g (flipCoord j (flipCoord i x)) <;> norm_num

/-- The shift does not increase the total influence. -/
lemma totalInfluence_shift_le (i : Fin n) (g : (Fin n → Bool) → Bool) :
    totalInfluence (fun x ↦ boolToReal (shift i g x)) ≤
      totalInfluence (fun x ↦ boolToReal (g x)) := by
  unfold totalInfluence
  refine Finset.sum_le_sum fun j _ ↦ ?_
  by_cases hij : i = j
  · subst hij
    exact (influence_shift_self i g).le
  · exact influence_shift_le hij g

/-! ### The potential -/

/-- The number of coordinates equal to `true`. -/
def weight (x : Fin n → Bool) : ℝ := ∑ k, boolToReal (x k)

lemma weight_eq_weight_flipCoord_add_one {i : Fin n} {x : Fin n → Bool} (hx : x i = true) :
    weight x = weight (flipCoord i x) + 1 := by
  have h : weight x - weight (flipCoord i x) = 1 := by
    rw [weight, weight, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp [hx]
    · intro k _ hk
      rw [flipCoord_noteq i k x hk, sub_self]
    · simp
  linarith

/-- The potential `φ(g) = E[g(x) ‖x‖]`, which strictly increases under a shift that changes `g`. -/
def potential (g : (Fin n → Bool) → Bool) : ℝ := expect (fun x ↦ boolToReal (g x) * weight x)

lemma potential_lt_potential_shift (i : Fin n) (g : (Fin n → Bool) → Bool)
    {x₀ : Fin n → Bool} (hx₀ : x₀ i = true) (hg₀ : g x₀ = false)
    (hg₁ : g (flipCoord i x₀) = true) : potential g < potential (shift i g) := by
  refine expect_lt_of_pair i (fun x ↦ ?_) (x₀ := x₀) ?_
  · rw [shift_flipCoord]
    unfold shift
    cases hx : x i
    · have hw := weight_eq_weight_flipCoord_add_one (i := i) (x := flipCoord i x) (by simp [hx])
      rw [flipCoord_flipCoord] at hw
      rw [hw]
      cases g x <;> cases g (flipCoord i x) <;> simp
    · rw [weight_eq_weight_flipCoord_add_one hx]
      cases g x <;> cases g (flipCoord i x) <;> simp
  · rw [shift_flipCoord]
    unfold shift
    rw [weight_eq_weight_flipCoord_add_one hx₀, hx₀, hg₀, hg₁]
    simp

/-! ### Coordinatewise monotonicity -/

/-- A Boolean function that never decreases when a coordinate is switched from `false` to `true`
is monotone. -/
lemma monotone_of_forall_flipCoord {g : (Fin n → Bool) → Bool}
    (hg : ∀ i x, x i = true → g (flipCoord i x) ≤ g x) : Monotone g := by
  intro x y hxy
  have key : ∀ j ≤ n, g x ≤ g (mix j y x) := by
    intro j
    induction j with
    | zero =>
      intro _
      have : mix 0 y x = x := funext fun k ↦ by simp [mix]
      rw [this]
    | succ j ih =>
      intro hj
      refine (ih (by omega)).trans ?_
      set i : Fin n := ⟨j, by omega⟩
      have hsucc : mix (j + 1) y x = Function.update (mix j y x) i (y i) := mix_succ i y x
      by_cases hxyi : x i = y i
      · rw [hsucc, ← hxyi, ← mix_apply_self i y x, Function.update_eq_self]
      · have hxi : x i = false := by
          have := hxy i
          cases hx : x i <;> cases hy : y i <;> simp_all [Bool.le_iff_imp]
        have hyi : y i = true := by
          cases hy : y i <;> simp_all
        have hflip : flipCoord i (mix (j + 1) y x) = mix j y x := by
          rw [hsucc, flipCoord]
          simp only [Function.update_self, Function.update_idem, hyi, Bool.not_true]
          rw [← hxi, ← mix_apply_self i y x, Function.update_eq_self]
        have := hg i (mix (j + 1) y x) (by rw [hsucc, Function.update_self, hyi])
        rwa [hflip] at this
  have hy : mix n y x = y := funext fun k ↦ by simp [mix]
  simpa [hy] using key n le_rfl

/-! ### BLM Theorem 9.10 -/

private lemma exists_monotone_bool (f : (Fin n → Bool) → Bool) :
    ∃ g : (Fin n → Bool) → Bool, Monotone g ∧
      expect (fun x ↦ boolToReal (g x)) = expect (fun x ↦ boolToReal (f x)) ∧
      totalInfluence (fun x ↦ boolToReal (g x)) ≤ totalInfluence (fun x ↦ boolToReal (f x)) := by
  classical
  set C : Finset ((Fin n → Bool) → Bool) := Finset.univ.filter fun g ↦
    expect (fun x ↦ boolToReal (g x)) = expect (fun x ↦ boolToReal (f x)) ∧
      totalInfluence (fun x ↦ boolToReal (g x)) ≤ totalInfluence (fun x ↦ boolToReal (f x))
  have hf : f ∈ C := by simp [C]
  obtain ⟨g, hgC, hmax⟩ := C.exists_max_image potential ⟨f, hf⟩
  have hg := (Finset.mem_filter.mp hgC).2
  refine ⟨g, monotone_of_forall_flipCoord fun i x hx ↦ ?_, hg⟩
  by_contra hlt
  have hg₀ : g x = false := by cases h : g x <;> simp_all
  have hg₁ : g (flipCoord i x) = true := by cases h : g (flipCoord i x) <;> simp_all
  have hS : shift i g ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(expect_shift i g).trans hg.1, (totalInfluence_shift_le i g).trans hg.2⟩
  exact (hmax _ hS).not_gt (potential_lt_potential_shift i g hx hg₀ hg₁)

/-- **BLM Theorem 9.10.** Every Boolean function on the hypercube can be replaced by a monotone
Boolean function with the same expectation and no larger total influence. -/
theorem exists_monotone {f : (Fin n → Bool) → ℝ} (hf : ∀ x, f x = 0 ∨ f x = 1) :
    ∃ g : (Fin n → Bool) → ℝ, (∀ x, g x = 0 ∨ g x = 1) ∧ Monotone g ∧
      expect g = expect f ∧ totalInfluence g ≤ totalInfluence f := by
  have hfb : (fun x ↦ boolToReal (decide (f x = 1))) = f := by
    funext x
    rcases hf x with h | h <;> simp [h]
  obtain ⟨g, hmono, hexp, hinf⟩ := exists_monotone_bool fun x ↦ decide (f x = 1)
  rw [hfb] at hexp hinf
  refine ⟨fun x ↦ boolToReal (g x), fun x ↦ ?_, monotone_boolToReal.comp hmono, hexp, hinf⟩
  cases h : g x <;> simp [h]

example (f : (Fin 3 → Bool) → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    ∃ g : (Fin 3 → Bool) → ℝ, (∀ x, g x = 0 ∨ g x = 1) ∧ Monotone g ∧
      expect g = expect f ∧ totalInfluence g ≤ totalInfluence f :=
  exists_monotone hf

end Influence
