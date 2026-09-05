/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Topology.MetricSpace.CoveringNumber.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval

/-!
# Covering numbers of the Lipschitz ball on `[0, 1]`

Let `F_L` be the set of `L`-Lipschitz functions on `[0, 1]` vanishing at `0`, viewed inside
`C(unitInterval, ℝ)` with the supremum metric.  This file bounds its covering number below by
exhibiting an explicit exponentially large separated family.

The family is indexed by sign vectors `β : Fin n → Bool`.  The associated sawtooth `sawtooth`
has slope `±L` on each of the `n` cells `[k/n, (k+1)/n]`, so two sawtooths whose sign vectors
first differ in cell `k` are exactly `2 * L / n` apart at the grid point `(k+1)/n`.

Sawtooths are defined as integrals of their piecewise constant slope rather than as sums of
ramps.  The Lipschitz bound is then a single application of
`intervalIntegral.norm_integral_le_of_norm_le_const`, with no gluing across cells; what remains
is to evaluate the integral on one cell, which is `sawtooth_sub_sawtooth_of_mem_cell`.

## Main definitions

* `sawtoothSlope`, `sawtooth`: the piecewise constant slope and its primitive.
* `signVector`: the `±1`-valued sign sequence attached to a `Bool` vector.
* `lipschitzBall`, `sawtoothMap`: the Lipschitz ball and the sawtooth family inside it.

## Main results

* `sawtooth_sub_sawtooth_of_mem_cell`: the sawtooth is affine with slope `L * s k` on cell `k`.
* `sawtooth_grid`: the sawtooth at a grid point is `L / n` times a partial sign sum.
* `isPacking_sawtoothFamily`: the sawtooth family is an `L / n`-packing of the Lipschitz ball.
* `le_coveringNumber_lipschitzBall`: `2 ^ n ≤ N(L / (2 * n), F_L)`.
-/

noncomputable section

open Set MeasureTheory unitInterval
open scoped Interval

namespace LipschitzBall

/-!
## The sawtooth primitive
-/

variable (L : ℝ) (n : ℕ) (s : ℕ → ℝ)

/-- The piecewise constant slope of a sawtooth: `L * s k` on the cell `[k/n, (k+1)/n)`. -/
def sawtoothSlope (t : ℝ) : ℝ := L * s ⌊t * n⌋₊

/-- The sawtooth attached to a sign sequence `s`, as the primitive of `sawtoothSlope`
vanishing at `0`. -/
def sawtooth (y : ℝ) : ℝ := ∫ t in (0 : ℝ)..y, sawtoothSlope L n s t

variable {L n s}

lemma sawtoothSlope_intervalIntegrable (hs : ∀ i, |s i| ≤ 1) (a b : ℝ) :
    IntervalIntegrable (sawtoothSlope L n s) volume a b := by
  have hm : Measurable (sawtoothSlope L n s) := by unfold sawtoothSlope; fun_prop
  refine ⟨?_, ?_⟩ <;>
  · refine Measure.integrableOn_of_bounded (M := |L|) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable (.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, sawtoothSlope, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg L) (hs _)

@[simp] lemma sawtooth_zero : sawtooth L n s 0 = 0 := by
  simp [sawtooth]

/-- The sawtooth is `|L|`-Lipschitz, directly from the bound on its slope. -/
lemma abs_sawtooth_sub_sawtooth_le (hs : ∀ i, |s i| ≤ 1) (x y : ℝ) :
    |sawtooth L n s y - sawtooth L n s x| ≤ |L| * |y - x| := by
  have hsub : sawtooth L n s y - sawtooth L n s x = ∫ t in x..y, sawtoothSlope L n s t :=
    intervalIntegral.integral_interval_sub_left (sawtoothSlope_intervalIntegrable hs 0 y)
      (sawtoothSlope_intervalIntegrable hs 0 x)
  rw [hsub, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => ?_
  rw [Real.norm_eq_abs, sawtoothSlope, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg L) (hs _)

lemma lipschitzWith_sawtooth (hs : ∀ i, |s i| ≤ 1) :
    LipschitzWith (Real.toNNReal |L|) (sawtooth L n s) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (abs_nonneg L)]
  exact abs_sawtooth_sub_sawtooth_le hs y x

lemma continuous_sawtooth (hs : ∀ i, |s i| ≤ 1) : Continuous (sawtooth L n s) :=
  (lipschitzWith_sawtooth hs).continuous

/-- On the cell `[k/n, (k+1)/n]` the sawtooth is affine with slope `L * s k`. -/
lemma sawtooth_sub_sawtooth_of_mem_cell (hs : ∀ i, |s i| ≤ 1) (hn : 0 < n) (k : ℕ) {x y : ℝ}
    (hx : (k : ℝ) / n ≤ x) (hxy : x ≤ y) (hy : y ≤ ((k : ℝ) + 1) / n) :
    sawtooth L n s y - sawtooth L n s x = L * s k * (y - x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : sawtooth L n s y - sawtooth L n s x = ∫ t in x..y, sawtoothSlope L n s t :=
    intervalIntegral.integral_interval_sub_left (sawtoothSlope_intervalIntegrable hs 0 y)
      (sawtoothSlope_intervalIntegrable hs 0 x)
  have hae : ∀ᵐ t : ℝ, t ∈ Ι x y → sawtoothSlope L n s t = L * s k := by
    have hne : ∀ᵐ t : ℝ, t ≠ ((k : ℝ) + 1) / n := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
      exact measure_singleton _
    filter_upwards [hne] with t ht htmem
    rw [Set.uIoc_of_le hxy, Set.mem_Ioc] at htmem
    have h1 : (k : ℝ) / n ≤ t := hx.trans htmem.1.le
    have h2 : t < ((k : ℝ) + 1) / n := lt_of_le_of_ne (htmem.2.trans hy) ht
    have hfloor : ⌊t * n⌋₊ = k := by
      have ht0 : (0 : ℝ) ≤ t := le_trans (by positivity) h1
      rw [Nat.floor_eq_iff (by positivity)]
      rw [div_le_iff₀ hn'] at h1
      rw [lt_div_iff₀ hn'] at h2
      exact ⟨h1, by linarith⟩
    rw [sawtoothSlope, hfloor]
  rw [hsub, intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const,
    smul_eq_mul, mul_comm]

/-- The value of a sawtooth at a grid point is `L / n` times the partial sum of its signs. -/
lemma sawtooth_grid (hs : ∀ i, |s i| ≤ 1) (hn : 0 < n) (k : ℕ) :
    sawtooth L n s ((k : ℝ) / n) = (L / n) * ∑ j ∈ Finset.range k, s j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : sawtooth L n s (((k : ℝ) + 1) / n) - sawtooth L n s ((k : ℝ) / n) =
        L * s k * (((k : ℝ) + 1) / n - (k : ℝ) / n) :=
      sawtooth_sub_sawtooth_of_mem_cell hs hn k le_rfl
        (by gcongr; linarith) le_rfl
    rw [Finset.sum_range_succ]
    push_cast
    rw [← sub_add_cancel (sawtooth L n s (((k : ℝ) + 1) / n)) (sawtooth L n s ((k : ℝ) / n)),
      hstep, ih]
    field_simp
    ring

/-!
## The sawtooth family inside the Lipschitz ball
-/

/-- The `±1`-valued sign sequence attached to a `Bool` vector, extended by `1` past `n`. -/
def signVector (n : ℕ) (β : Fin n → Bool) (i : ℕ) : ℝ :=
  if h : i < n then (if β ⟨i, h⟩ then 1 else -1) else 1

lemma abs_signVector_le_one (n : ℕ) (β : Fin n → Bool) (i : ℕ) :
    |signVector n β i| ≤ 1 := by
  unfold signVector
  split
  · split <;> norm_num
  · norm_num

lemma signVector_of_lt {n : ℕ} (β : Fin n → Bool) {i : ℕ} (h : i < n) :
    signVector n β i = if β ⟨i, h⟩ then 1 else -1 := by
  rw [signVector, dif_pos h]

lemma signVector_congr {n : ℕ} {β β' : Fin n → Bool} {i : ℕ} (h : i < n)
    (hβ : β ⟨i, h⟩ = β' ⟨i, h⟩) : signVector n β i = signVector n β' i := by
  rw [signVector_of_lt β h, signVector_of_lt β' h, hβ]

lemma abs_signVector_sub_of_ne {n : ℕ} {β β' : Fin n → Bool} {i : ℕ} (h : i < n)
    (hβ : β ⟨i, h⟩ ≠ β' ⟨i, h⟩) : |signVector n β i - signVector n β' i| = 2 := by
  rw [signVector_of_lt β h, signVector_of_lt β' h]
  cases hb : β ⟨i, h⟩ <;> cases hb' : β' ⟨i, h⟩ <;>
    simp_all <;> norm_num

/-- The Lipschitz ball `F_L`: continuous functions on `[0, 1]` that vanish at `0` and are
`L`-Lipschitz. -/
def lipschitzBall (L : ℝ) : Set C(I, ℝ) :=
  {f | f 0 = 0 ∧ ∀ x y : I, |f x - f y| ≤ L * |(x : ℝ) - (y : ℝ)|}

/-- The member of the sawtooth family attached to a sign vector. -/
def sawtoothMap (L : ℝ) (n : ℕ) (β : Fin n → Bool) : C(I, ℝ) :=
  ⟨fun x => sawtooth L n (signVector n β) x,
    (continuous_sawtooth (abs_signVector_le_one n β)).comp continuous_subtype_val⟩

@[simp] lemma sawtoothMap_apply (L : ℝ) (n : ℕ) (β : Fin n → Bool) (x : I) :
    sawtoothMap L n β x = sawtooth L n (signVector n β) x := rfl

lemma sawtoothMap_mem_lipschitzBall {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (β : Fin n → Bool) :
    sawtoothMap L n β ∈ lipschitzBall L := by
  refine ⟨by simp, fun x y => ?_⟩
  simpa [abs_of_nonneg hL] using
    abs_sawtooth_sub_sawtooth_le (L := L) (n := n) (abs_signVector_le_one n β) (y : ℝ) (x : ℝ)

/-- The grid point `(k + 1) / n` of the unit interval, for `k < n`. -/
private def gridPoint {n : ℕ} (k : Fin n) : I :=
  ⟨((k : ℕ) + 1 : ℕ) / n, by
    have hk : ((k : ℕ) + 1 : ℕ) ≤ n := k.2
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.lt_of_lt_of_le (Nat.succ_pos (k : ℕ)) hk
    exact ⟨by positivity, by rw [div_le_one hnpos]; exact_mod_cast hk⟩⟩

/-- Two sawtooths whose sign vectors differ are at supremum distance at least `2 * L / n`:
they agree up to the first cell where the signs differ, and separate by `2 * L / n` there. -/
lemma le_dist_sawtoothMap {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n) {β β' : Fin n → Bool}
    (hne : β ≠ β') : 2 * L / n ≤ dist (sawtoothMap L n β) (sawtoothMap L n β') := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set S : Finset (Fin n) := Finset.univ.filter fun i => β i ≠ β' i with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    exact ⟨i, by simp [hS, hi]⟩
  set k : Fin n := S.min' hSne with hk
  have hkmem : β k ≠ β' k := by
    have := S.min'_mem hSne
    simpa [hS] using this
  have hbelow : ∀ j ∈ Finset.range (k : ℕ),
      signVector n β j = signVector n β' j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjn : j < n := hj.trans k.2
    refine signVector_congr hjn ?_
    by_contra hcon
    have : k ≤ (⟨j, hjn⟩ : Fin n) := S.min'_le _ (by simp [hS, hcon])
    exact absurd (this.trans_lt (by exact_mod_cast hj)) (lt_irrefl _)
  have hgrid : ∀ γ : Fin n → Bool, sawtoothMap L n γ (gridPoint k) =
      (L / n) * ∑ j ∈ Finset.range ((k : ℕ) + 1), signVector n γ j := by
    intro γ
    have := sawtooth_grid (L := L) (n := n) (abs_signVector_le_one n γ) hn ((k : ℕ) + 1)
    simpa [gridPoint, sawtoothMap] using this
  have hsums : (∑ j ∈ Finset.range ((k : ℕ) + 1), signVector n β j) -
      ∑ j ∈ Finset.range ((k : ℕ) + 1), signVector n β' j =
      signVector n β (k : ℕ) - signVector n β' (k : ℕ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_congr rfl hbelow]
    ring
  have hdiff : |sawtoothMap L n β (gridPoint k) - sawtoothMap L n β' (gridPoint k)| =
      2 * L / n := by
    rw [hgrid, hgrid, ← mul_sub, hsums, abs_mul,
      abs_signVector_sub_of_ne k.2 (by simpa using hkmem), abs_of_nonneg (by positivity)]
    ring
  have := ContinuousMap.dist_apply_le_dist (f := sawtoothMap L n β) (g := sawtoothMap L n β')
    (gridPoint k)
  rwa [Real.dist_eq, hdiff] at this

lemma sawtoothMap_injective {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    Function.Injective (sawtoothMap L n) := by
  intro β β' h
  by_contra hne
  have hpos : 0 < 2 * L / n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have := le_dist_sawtoothMap hL.le hn hne
  rw [h, dist_self] at this
  linarith

open Classical in
/-- The sawtooth family: `2 ^ n` functions in the Lipschitz ball, pairwise `L / n`-separated. -/
def sawtoothFamily (L : ℝ) (n : ℕ) : Finset C(I, ℝ) :=
  Finset.univ.image (sawtoothMap L n)

open Classical in
lemma mem_sawtoothFamily {L : ℝ} {n : ℕ} {f : C(I, ℝ)} :
    f ∈ sawtoothFamily L n ↔ ∃ β : Fin n → Bool, sawtoothMap L n β = f := by
  simp [sawtoothFamily]

lemma card_sawtoothFamily {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    (sawtoothFamily L n).card = 2 ^ n := by
  classical
  rw [sawtoothFamily, Finset.card_image_of_injective _ (sawtoothMap_injective hL hn)]
  simp

lemma isPacking_sawtoothFamily {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    IsPacking (sawtoothFamily L n) (L / n) (lipschitzBall L) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rintro f hf
    obtain ⟨β, rfl⟩ := mem_sawtoothFamily.1 (Finset.mem_coe.1 hf)
    exact sawtoothMap_mem_lipschitzBall hL.le n β
  · rintro f hf g hg hfg
    obtain ⟨β, rfl⟩ := mem_sawtoothFamily.1 (Finset.mem_coe.1 hf)
    obtain ⟨β', rfl⟩ := mem_sawtoothFamily.1 (Finset.mem_coe.1 hg)
    have hne : β ≠ β' := fun h => hfg (by rw [h])
    have hsep := le_dist_sawtoothMap hL.le hn hne
    have : L / n < 2 * L / n := by
      rw [div_lt_div_iff_of_pos_right hn']
      linarith
    linarith

/-- The lower bound on the covering number of the Lipschitz ball: `n` cells of width `1 / n`
give `2 ^ n` functions that no `L / (2 * n)`-net can separate fewer than `2 ^ n` times. -/
theorem le_coveringNumber_lipschitzBall {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    (2 ^ n : WithTop ℕ) ≤ coveringNumber (L / (2 * n)) (lipschitzBall L) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf : 2 * (L / (2 * n)) = L / n := by field_simp
  have hpack : ((sawtoothFamily L n).card : WithTop ℕ) ≤
      packingNumber (L / n) (lipschitzBall L) :=
    le_sSup ⟨sawtoothFamily L n, isPacking_sawtoothFamily hL hn, rfl⟩
  rw [card_sawtoothFamily hL hn] at hpack
  refine le_trans ?_ (le_trans (hhalf ▸ hpack) packingNumber_two_mul_le_coveringNumber)
  norm_cast

/-- A concrete instance: four cells of the unit interval give sixteen `1`-Lipschitz functions
no `1 / 8`-net can cover with fewer centres. -/
example : (16 : WithTop ℕ) ≤ coveringNumber (1 / 8 : ℝ) (lipschitzBall 1) := by
  have := le_coveringNumber_lipschitzBall (L := 1) one_pos (n := 4) (by norm_num)
  norm_num at this
  exact this

end LipschitzBall
