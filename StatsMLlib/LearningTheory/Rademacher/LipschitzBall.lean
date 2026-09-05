/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Analysis.NormedSpace.CoveringNumber.LipschitzBall
import StatsMLlib.LearningTheory.Rademacher.OneStep

/-!
# Rademacher complexity of the Lipschitz ball

The `L`-Lipschitz functions on `[0, 1]` vanishing at `0` have metric entropy linear in `1 / eps`,
so the Dudley entropy integral diverges and the one-step discretization bound is what applies.
Optimizing the number of cells gives the rate `m ^ (-1/3)`, linear in `L`.

The sawtooth net is built in the supremum metric, and transfers to the empirical `L²` metric
because the latter is dominated by the former on any sample.

## Main definitions

* `lipschitzBallClass`: the Lipschitz ball as an indexed family of functions on `[0, 1]`.

## Main results

* `empiricalDist_le_dist`: the empirical metric is dominated by the supremum metric.
* `empiricalRademacherComplexity_lipschitzBall_le`: the bound for a fixed number of cells.
* `empiricalRademacherComplexity_lipschitzBall_le_rate`: the resulting `m ^ (-1/3)` rate.
-/

noncomputable section

open MeasureTheory Real unitInterval ProbabilityTheory

namespace LipschitzBall

variable {L : ℝ} {m n : ℕ}

/-- The Lipschitz ball as an indexed function class on the unit interval. -/
def lipschitzBallClass (L : ℝ) : ↥(lipschitzBall L) → I → ℝ := fun f x => (f : C(I, ℝ)) x

lemma zero_mem_lipschitzBall (hL : 0 ≤ L) : (0 : C(I, ℝ)) ∈ lipschitzBall L :=
  ⟨rfl, fun x y => by simpa using mul_nonneg hL (abs_nonneg _)⟩

lemma neg_mem_lipschitzBall {f : C(I, ℝ)} (hf : f ∈ lipschitzBall L) : -f ∈ lipschitzBall L := by
  refine ⟨by simp [hf.1], fun x y => ?_⟩
  have h := hf.2 y x
  rw [abs_sub_comm (y : ℝ) (x : ℝ)] at h
  rw [show ((-f) x - (-f) y) = f y - f x by simp only [ContinuousMap.neg_apply]; ring]
  exact h

lemma isNegClosed_lipschitzBallClass (L : ℝ) : IsNegClosed (lipschitzBallClass L) := by
  intro i
  exact ⟨⟨-(i : C(I, ℝ)), neg_mem_lipschitzBall i.2⟩, rfl⟩

lemma abs_lipschitzBallClass_le (i : ↥(lipschitzBall L)) (x : I) :
    |lipschitzBallClass L i x| ≤ L :=
  abs_le_of_mem_lipschitzBall i.2 x

/-- The empirical metric on a sample is dominated by the supremum metric. -/
lemma empiricalDist_le_dist (hm : 0 < m) (S : Fin m → I) (f g : C(I, ℝ)) :
    empiricalDist S (fun x => f x) (fun x => g x) ≤ dist f g := by
  refine empiricalNorm_le_of_abs_le hm S _ dist_nonneg fun k => ?_
  simpa [Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) (S k)

/-- The sawtooth family, read as a finite subfamily of the Lipschitz ball, is an `L / n`-net
for the empirical metric of any sample. -/
lemma exists_finset_net (hL : 0 < L) (hn : 0 < n) (hm : 0 < m) (S : Fin m → I) :
    ∃ t : Finset ↥(lipschitzBall L), t.Nonempty ∧ t.card = 2 ^ n ∧
      ∀ i : ↥(lipschitzBall L), ∃ j ∈ t,
        empiricalDist S (lipschitzBallClass L i) (lipschitzBallClass L j) ≤ L / n := by
  classical
  set emb : (Fin n → Bool) → ↥(lipschitzBall L) := fun β =>
    ⟨sawtoothMap L n β, sawtoothMap_mem_lipschitzBall hL.le n β⟩ with hemb
  have hinj : Function.Injective emb := by
    intro β β' h
    exact sawtoothMap_injective hL hn (congrArg Subtype.val h)
  refine ⟨Finset.univ.image emb, ?_, ?_, ?_⟩
  · exact (Finset.univ_nonempty (α := Fin n → Bool)).image emb
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · rintro ⟨f, hf⟩
    obtain ⟨h, hh, hball⟩ := Set.mem_iUnion₂.1 (isENet_sawtoothFamily hL hn hf)
    obtain ⟨β, rfl⟩ := mem_sawtoothFamily.1 hh
    refine ⟨emb β, Finset.mem_image.2 ⟨β, Finset.mem_univ β, rfl⟩, ?_⟩
    exact le_trans (empiricalDist_le_dist hm S f (sawtoothMap L n β))
      (Metric.mem_closedBall.1 hball)

/-- The one-step bound for the Lipschitz ball with `n` cells. -/
theorem empiricalRademacherComplexity_lipschitzBall_le (hL : 0 < L) (hn : 0 < n) (hm : 0 < m)
    (S : Fin m → I) :
    empiricalRademacherComplexity m (lipschitzBallClass L) S
      ≤ L / n + L * Real.sqrt (2 * n * Real.log 2) / Real.sqrt m := by
  have : Nonempty ↥(lipschitzBall L) := ⟨⟨0, zero_mem_lipschitzBall hL.le⟩⟩
  obtain ⟨t, ht, hcard, hnet⟩ := exists_finset_net hL hn hm S
  have habs : empiricalRademacherComplexity m (lipschitzBallClass L) S
      = empiricalRademacherComplexity_without_abs m (lipschitzBallClass L) S :=
    empiricalRademacherComplexity_eq_without_abs_of_neg_closed m (lipschitzBallClass L) S L hL.le
      (fun i k => abs_lipschitzBallClass_le i (S k)) (isNegClosed_lipschitzBallClass L)
  have hone := empiricalRademacherComplexity_without_abs_le_of_net (lipschitzBallClass L) S hm ht
    hL.le (fun j _ k => abs_lipschitzBallClass_le j (S k)) hnet
  rw [habs]
  refine hone.trans ?_
  rw [hcard]
  have hlog : Real.log ((2 ^ n : ℕ) : ℝ) = n * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
  rw [hlog, show 2 * ((n : ℝ) * Real.log 2) = 2 * n * Real.log 2 by ring]

/-- Choosing `⌈m ^ (1/3)⌉` cells gives the `m ^ (-1/3)` rate, linear in `L`. -/
theorem empiricalRademacherComplexity_lipschitzBall_le_rate (hL : 0 < L) (hm : 0 < m)
    (S : Fin m → I) :
    empiricalRademacherComplexity m (lipschitzBallClass L) S
      ≤ (1 + 2 * Real.sqrt (Real.log 2)) * L / (m : ℝ) ^ ((1 : ℝ) / 3) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set x : ℝ := (m : ℝ) ^ ((1 : ℝ) / 3) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hmR _
  have hx1 : 1 ≤ x := Real.one_le_rpow hm1 (by norm_num)
  set N : ℕ := ⌈x⌉₊ with hN
  have hNx : x ≤ (N : ℝ) := Nat.le_ceil x
  have hN0 : 0 < N := by
    have : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hx0 hNx
    exact_mod_cast this
  have hN2 : (N : ℝ) ≤ 2 * x := by
    have hlt : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    linarith
  refine (empiricalRademacherComplexity_lipschitzBall_le hL hN0 hm S).trans ?_
  -- the two terms at the chosen number of cells
  have hterm1 : L / (N : ℝ) ≤ L / x := by
    gcongr
  have hsqrtx : Real.sqrt x / Real.sqrt m = 1 / x := by
    have h1 : Real.sqrt ((m : ℝ) ^ ((1 : ℝ) / 3)) = (m : ℝ) ^ ((1 : ℝ) / 6) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hmR.le]
      norm_num
    rw [hx, h1, Real.sqrt_eq_rpow, ← Real.rpow_sub hmR,
      show (1 : ℝ) / 6 - 1 / 2 = -(1 / 3) by norm_num, Real.rpow_neg hmR.le]
    exact (one_div _).symm
  have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hterm2 : L * Real.sqrt (2 * N * Real.log 2) / Real.sqrt m
      ≤ 2 * Real.sqrt (Real.log 2) * L / x := by
    have hstep : Real.sqrt (2 * N * Real.log 2) ≤ 2 * Real.sqrt x * Real.sqrt (Real.log 2) := by
      rw [show (2 : ℝ) * Real.sqrt x * Real.sqrt (Real.log 2)
          = Real.sqrt (4 * x * Real.log 2) by
        rw [show (4 : ℝ) * x * Real.log 2 = 2 ^ 2 * (x * Real.log 2) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), Real.sqrt_mul hx0.le]
        ring]
      exact Real.sqrt_le_sqrt (by nlinarith)
    calc L * Real.sqrt (2 * N * Real.log 2) / Real.sqrt m
        ≤ L * (2 * Real.sqrt x * Real.sqrt (Real.log 2)) / Real.sqrt m := by
          gcongr
      _ = 2 * Real.sqrt (Real.log 2) * L * (Real.sqrt x / Real.sqrt m) := by ring
      _ = 2 * Real.sqrt (Real.log 2) * L * (1 / x) := by rw [hsqrtx]
      _ = 2 * Real.sqrt (Real.log 2) * L / x := by ring
  rw [show (1 + 2 * Real.sqrt (Real.log 2)) * L / x = L / x + 2 * Real.sqrt (Real.log 2) * L / x by
    ring]
  exact add_le_add hterm1 hterm2

/-- A concrete instance: the unit Lipschitz ball has empirical Rademacher complexity at most
`3 / m ^ (1/3)` on every sample. -/
example (hm : 0 < m) (S : Fin m → I) :
    empiricalRademacherComplexity m (lipschitzBallClass 1) S
      ≤ 3 / (m : ℝ) ^ ((1 : ℝ) / 3) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : Real.sqrt (Real.log 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by linarith [Real.log_two_lt_d9])
  refine (empiricalRademacherComplexity_lipschitzBall_le_rate one_pos hm S).trans ?_
  gcongr
  linarith

end LipschitzBall
