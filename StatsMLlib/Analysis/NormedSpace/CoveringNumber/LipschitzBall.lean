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
* `greedyLevel`, `greedyVector`: the sign choice that tracks a given member of the ball.

## Main results

* `sawtooth_sub_sawtooth_of_mem_cell`: the sawtooth is affine with slope `L * s k` on cell `k`.
* `sawtooth_grid`: the sawtooth at a grid point is `L / n` times a partial sign sum.
* `isPacking_sawtoothFamily`: the sawtooth family is an `L / n`-packing of the Lipschitz ball.
* `isENet_sawtoothFamily`: the same family is an `L / n`-net of the Lipschitz ball.
* `le_coveringNumber_lipschitzBall`: `2 ^ n ≤ N(L / (2 * n), F_L)`.
* `coveringNumber_lipschitzBall_le`: `N(L / n, F_L) ≤ 2 ^ n`.
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

/-!
## The greedy cover
-/

open Classical in
/-- The greedy grid level.  `L / n * greedyLevel L n g k` is the sawtooth value at `k / n`
produced by always moving the sawtooth toward the next grid value of `g`. -/
def greedyLevel (L : ℝ) (n : ℕ) (g : ℝ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => greedyLevel L n g k +
      (if 0 ≤ g (((k : ℝ) + 1) / n) - L / n * greedyLevel L n g k then 1 else -1)

open Classical in
/-- The sign the greedy choice uses on cell `k`. -/
def greedySign (L : ℝ) (n : ℕ) (g : ℝ → ℝ) (k : ℕ) : Bool :=
  if 0 ≤ g (((k : ℝ) + 1) / n) - L / n * greedyLevel L n g k then true else false

/-- The sign vector of the greedy choice, as an index of the sawtooth family. -/
def greedyVector (L : ℝ) (n : ℕ) (g : ℝ → ℝ) : Fin n → Bool :=
  fun i => greedySign L n g i

lemma greedyLevel_succ (L : ℝ) (n : ℕ) (g : ℝ → ℝ) (k : ℕ) :
    greedyLevel L n g (k + 1) =
      greedyLevel L n g k + (if greedySign L n g k then (1 : ℝ) else -1) := by
  classical
  rw [greedyLevel, greedySign]
  split_ifs <;> simp_all

lemma signVector_greedyVector {L : ℝ} {n : ℕ} {g : ℝ → ℝ} {k : ℕ} (hk : k < n) :
    signVector n (greedyVector L n g) k = if greedySign L n g k then (1 : ℝ) else -1 := by
  rw [signVector_of_lt _ hk, greedyVector]

/-- The sawtooth of the greedy sign vector reaches exactly the greedy levels. -/
lemma sum_signVector_greedyVector {L : ℝ} {n : ℕ} {g : ℝ → ℝ} {k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ Finset.range k, signVector n (greedyVector L n g) j = greedyLevel L n g k := by
  induction k with
  | zero => simp [greedyLevel]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hk), greedyLevel_succ,
      signVector_greedyVector (Nat.lt_of_succ_le hk)]

/-- The greedy invariant: at every grid point the greedy sawtooth stays within `L / n`
of `g`.  Each step overshoots by at most `L / n` because the gap it has to close is at
most `2 * L / n`. -/
lemma abs_sub_greedyLevel_le {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ}
    (hg0 : g 0 = 0) (hglip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|) (k : ℕ) :
    |g ((k : ℝ) / n) - L / n * greedyLevel L n g k| ≤ L / n := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hLn : 0 ≤ L / n := by positivity
  induction k with
  | zero => simpa [greedyLevel, hg0] using hLn
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hgrid : |g (((k : ℝ) + 1) / n) - g ((k : ℝ) / n)| ≤ L / n := by
      have h := hglip (((k : ℝ) + 1) / n) ((k : ℝ) / n)
      rwa [show |((k : ℝ) + 1) / n - (k : ℝ) / n| = 1 / n by
        rw [div_sub_div_same, add_sub_cancel_left, abs_of_nonneg (by positivity)],
        mul_one_div] at h
    have hdle : |g (((k : ℝ) + 1) / n) - L / n * greedyLevel L n g k| ≤ 2 * (L / n) :=
      calc |g (((k : ℝ) + 1) / n) - L / n * greedyLevel L n g k|
          ≤ |g (((k : ℝ) + 1) / n) - g ((k : ℝ) / n)|
            + |g ((k : ℝ) / n) - L / n * greedyLevel L n g k| := abs_sub_le _ _ _
        _ ≤ L / n + L / n := add_le_add hgrid ih
        _ = 2 * (L / n) := by ring
    rw [abs_le] at hdle
    rw [hcast, greedyLevel, mul_add, abs_le]
    split_ifs with hpos
    · constructor <;> linarith
    · rw [not_le] at hpos
      constructor <;> linarith

/-- Every point of `[0, 1]` lies in one of the `n` cells. -/
lemma exists_cell {n : ℕ} (hn : 0 < n) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∃ k : ℕ, k < n ∧ (k : ℝ) / n ≤ y ∧ y ≤ ((k : ℝ) + 1) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hfl : ⌊y * n⌋₊ < n
  · refine ⟨⌊y * n⌋₊, hfl, ?_, ?_⟩
    · rw [div_le_iff₀ hn']
      exact Nat.floor_le (by positivity)
    · rw [le_div_iff₀ hn']
      exact (Nat.lt_floor_add_one (y * n)).le
  · rw [not_lt] at hfl
    have hy : y = 1 := by
      by_contra hne
      have hlt : y < 1 := lt_of_le_of_ne hy1 hne
      have hfloor : ⌊y * n⌋₊ < n := by
        rw [Nat.floor_lt (by positivity)]
        calc y * (n : ℝ) < 1 * n := by gcongr
          _ = n := one_mul _
      omega
    subst hy
    have hone : (1 : ℕ) ≤ n := hn
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hone, Nat.cast_one]
    refine ⟨n - 1, Nat.sub_lt hn one_pos, ?_, ?_⟩
    · rw [hcast, div_le_one hn']
      linarith
    · rw [hcast, le_div_iff₀ hn']
      linarith

/-- On a cell the difference between an `L`-Lipschitz function and a sawtooth of slope `±L`
is monotone, so it is largest at the endpoints of the cell. -/
lemma abs_sub_sawtooth_le_of_mem_cell {L : ℝ} {n : ℕ} {s : ℕ → ℝ} (hn : 0 < n)
    (hs : ∀ i, |s i| ≤ 1) {k : ℕ} (hsk : s k = 1 ∨ s k = -1) {g : ℝ → ℝ}
    (hglip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|) {y : ℝ}
    (hy1 : (k : ℝ) / n ≤ y) (hy2 : y ≤ ((k : ℝ) + 1) / n)
    (hA : |g ((k : ℝ) / n) - sawtooth L n s ((k : ℝ) / n)| ≤ L / n)
    (hB : |g (((k : ℝ) + 1) / n) - sawtooth L n s (((k : ℝ) + 1) / n)| ≤ L / n) :
    |g y - sawtooth L n s y| ≤ L / n := by
  have hstepA : sawtooth L n s y - sawtooth L n s ((k : ℝ) / n) = L * s k * (y - (k : ℝ) / n) :=
    sawtooth_sub_sawtooth_of_mem_cell hs hn k le_rfl hy1 hy2
  have hstepB : sawtooth L n s (((k : ℝ) + 1) / n) - sawtooth L n s y =
      L * s k * (((k : ℝ) + 1) / n - y) :=
    sawtooth_sub_sawtooth_of_mem_cell hs hn k hy1 hy2 le_rfl
  have hgA : |g y - g ((k : ℝ) / n)| ≤ L * (y - (k : ℝ) / n) := by
    simpa [abs_of_nonneg (sub_nonneg.2 hy1)] using hglip y ((k : ℝ) / n)
  have hgB : |g (((k : ℝ) + 1) / n) - g y| ≤ L * (((k : ℝ) + 1) / n - y) := by
    simpa [abs_of_nonneg (sub_nonneg.2 hy2)] using hglip (((k : ℝ) + 1) / n) y
  rw [abs_le] at hA hB hgA hgB ⊢
  rcases hsk with hsk | hsk <;> rw [hsk] at hstepA hstepB
  · exact ⟨by nlinarith [hstepB, hB.2, hgB.2], by nlinarith [hstepA, hA.1, hgA.2]⟩
  · exact ⟨by nlinarith [hstepA, hA.1, hgA.1], by nlinarith [hstepB, hB.2, hgB.1]⟩

/-- The sawtooth family is an `L / n`-net of the Lipschitz ball: the greedy sign choice
tracks any member of the ball to within `L / n`. -/
lemma isENet_sawtoothFamily {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    IsENet (sawtoothFamily L n) (L / n) (lipschitzBall L) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  intro f hf
  obtain ⟨hf0, hflip⟩ := hf
  set g : ℝ → ℝ := fun y => f (Set.projIcc 0 1 zero_le_one y) with hg
  have hgproj : ∀ x : I, g (x : ℝ) = f x := by
    intro x
    rw [hg]
    simp [Set.projIcc_of_mem _ x.2]
  have hg0 : g 0 = 0 := by
    have h0 := hgproj 0
    rw [hf0, show ((0 : I) : ℝ) = 0 by norm_num] at h0
    exact h0
  have hglip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y| := by
    intro x y
    have hproj : |((Set.projIcc 0 1 zero_le_one x : I) : ℝ) -
        ((Set.projIcc 0 1 zero_le_one y : I) : ℝ)| ≤ |x - y| := by
      have h := (LipschitzWith.projIcc (a := (0 : ℝ)) (b := 1) zero_le_one).dist_le_mul x y
      simpa [Subtype.dist_eq, Real.dist_eq] using h
    exact le_trans (hflip _ _) (mul_le_mul_of_nonneg_left hproj hL.le)
  set β : Fin n → Bool := greedyVector L n g with hβ
  set s : ℕ → ℝ := signVector n β with hs
  have hsbound : ∀ i, |s i| ≤ 1 := abs_signVector_le_one n β
  have hgridclose : ∀ k : ℕ, k ≤ n →
      |g ((k : ℝ) / n) - sawtooth L n s ((k : ℝ) / n)| ≤ L / n := by
    intro k hk
    rw [sawtooth_grid hsbound hn k, hs, sum_signVector_greedyVector hk]
    exact abs_sub_greedyLevel_le hL.le hn hg0 hglip k
  refine Set.mem_iUnion₂.2 ⟨sawtoothMap L n β, mem_sawtoothFamily.2 ⟨β, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, ContinuousMap.dist_le (by positivity)]
  intro x
  obtain ⟨k, hkn, hk1, hk2⟩ := exists_cell hn x.2.1 x.2.2
  have hsk : s k = 1 ∨ s k = -1 := by
    rw [hs, signVector_of_lt β hkn]
    split <;> simp
  have hkn1 : ((k : ℕ) + 1 : ℕ) ≤ n := hkn
  have hgridA := hgridclose k (Nat.le_of_succ_le hkn1)
  have hgridB : |g (((k : ℝ) + 1) / n) - sawtooth L n s (((k : ℝ) + 1) / n)| ≤ L / n := by
    have := hgridclose (k + 1) hkn1
    rwa [Nat.cast_add, Nat.cast_one] at this
  have hclose := abs_sub_sawtooth_le_of_mem_cell hn hsbound hsk hglip hk1 hk2 hgridA hgridB
  rw [Real.dist_eq, sawtoothMap_apply, ← hs, ← hgproj x, abs_sub_comm]
  exact hclose

/-- The upper bound on the covering number of the Lipschitz ball: the same `2 ^ n`
sawtooths that separate the ball also cover it at radius `L / n`. -/
theorem coveringNumber_lipschitzBall_le {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    coveringNumber (L / n) (lipschitzBall L) ≤ (2 ^ n : ℕ) := by
  have := coveringNumber_le_card (isENet_sawtoothFamily hL hn)
  rwa [card_sawtoothFamily hL hn] at this

/-- A concrete instance: four cells of the unit interval give sixteen `1`-Lipschitz functions
that cover the unit ball at radius `1 / 4` and that no `1 / 8`-net can cover with fewer
centres. -/
example : coveringNumber (1 / 4 : ℝ) (lipschitzBall 1) ≤ 16 ∧
    (16 : WithTop ℕ) ≤ coveringNumber (1 / 8 : ℝ) (lipschitzBall 1) := by
  constructor
  · have h := coveringNumber_lipschitzBall_le (L := 1) one_pos (n := 4) (by norm_num)
    norm_num at h
    exact h
  · have h := le_coveringNumber_lipschitzBall (L := 1) one_pos (n := 4) (by norm_num)
    norm_num at h
    exact h

end LipschitzBall
