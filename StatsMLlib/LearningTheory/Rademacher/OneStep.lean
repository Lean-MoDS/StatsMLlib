/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.LearningTheory.Rademacher.Massart
import StatsMLlib.LearningTheory.EmpiricalProcess.FunctionClass

/-!
# One-step discretization of the Rademacher complexity

Replacing a function class by a finite `eps`-net of it in the empirical metric costs `eps`,
and the net is then handled by Massart's finite-class lemma.  The result is

`Rhat_n(F; S) ≤ eps + b * sqrt (2 * log N) / sqrt n`

for a net of cardinality `N` whose members are bounded by `b` on the sample.

This uses the covering number at a single scale, so it is weaker than the Dudley entropy
integral whenever that integral converges.  It is what one wants for classes whose entropy
grows like `1 / eps`, where the integral diverges.

## Main results

* `signed_sum_le_mul_empiricalDist`: a signed sample sum is bounded by the empirical distance.
* `empiricalRademacherComplexity_without_abs_le_of_net`: the one-step estimate.
-/

noncomputable section

universe u v

open MeasureTheory Real

namespace ProbabilityTheory

variable {n : ℕ} {ι : Type u} {𝒳 : Type v}

/-- A signed sample sum of `f - g` is at most `n` times their empirical distance.  This is
Cauchy-Schwarz against the sign vector, whose coordinates are all `±1`. -/
lemma signed_sum_le_mul_empiricalDist (S : Fin n → 𝒳) (f g : 𝒳 → ℝ) (σ : Signs n) :
    ∑ k : Fin n, ((σ k : ℤ) : ℝ) * (f (S k) - g (S k)) ≤ n * empiricalDist S f g := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : ∀ k : Fin n, (((σ k : ℤ) : ℝ)) ^ 2 = 1 := by
    intro k
    have hmem := (σ k).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h <;> rw [h] <;> norm_num
  have hsum : ∑ k : Fin n, (((σ k : ℤ) : ℝ)) ^ 2 = (n : ℝ) := by
    rw [Finset.sum_congr rfl fun k _ => hsq k]
    simp
  have hcs : (∑ k : Fin n, ((σ k : ℤ) : ℝ) * (f (S k) - g (S k))) ^ 2
      ≤ (n : ℝ) * ∑ k : Fin n, (f (S k) - g (S k)) ^ 2 := by
    refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _) ?_
    rw [hsum]
  have hdist : (n : ℝ) * empiricalDist S f g
      = Real.sqrt ((n : ℝ) * ∑ k : Fin n, (f (S k) - g (S k)) ^ 2) := by
    rw [empiricalDist_def, empiricalNorm_def]
    simp only [Pi.sub_apply]
    rw [show ((n : ℝ) * Real.sqrt (1 / n * ∑ k : Fin n, (f (S k) - g (S k)) ^ 2))
        = Real.sqrt ((n : ℝ) ^ 2) * Real.sqrt (1 / n * ∑ k : Fin n, (f (S k) - g (S k)) ^ 2) by
      rw [Real.sqrt_sq hnR.le]]
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  calc ∑ k : Fin n, ((σ k : ℤ) : ℝ) * (f (S k) - g (S k))
      ≤ |∑ k : Fin n, ((σ k : ℤ) : ℝ) * (f (S k) - g (S k))| := le_abs_self _
    _ = Real.sqrt ((∑ k : Fin n, ((σ k : ℤ) : ℝ) * (f (S k) - g (S k))) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((n : ℝ) * ∑ k : Fin n, (f (S k) - g (S k)) ^ 2) := Real.sqrt_le_sqrt hcs
    _ = (n : ℝ) * empiricalDist S f g := hdist.symm

/-- The approximation step, for a single sign vector: passing from the class to a net costs
the radius of the net. -/
private lemma sup_le_add_sup_of_net [Nonempty ι] (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) (hn : 0 < n)
    {t : Finset ι} (ht : t.Nonempty) {eps : ℝ}
    (hnet : ∀ i : ι, ∃ j ∈ t, empiricalDist S (F i) (F j) ≤ eps) (σ : Signs n) :
    (⨆ i : ι, (n : ℝ)⁻¹ * ∑ k : Fin n, ((σ k : ℤ) : ℝ) * F i (S k))
      ≤ eps + ⨆ j : {j // j ∈ t},
          (n : ℝ)⁻¹ * ∑ k : Fin n, ((σ k : ℤ) : ℝ) * F_on F t j (S k) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : Nonempty {j // j ∈ t} := ⟨⟨ht.choose, ht.choose_spec⟩⟩
  have hbdd : BddAbove (Set.range fun j : {j // j ∈ t} =>
      (n : ℝ)⁻¹ * ∑ k : Fin n, ((σ k : ℤ) : ℝ) * F_on F t j (S k)) :=
    Set.Finite.bddAbove (Set.finite_range _)
  refine ciSup_le fun i => ?_
  obtain ⟨j, hj, hij⟩ := hnet i
  have hle : (n : ℝ)⁻¹ * ∑ k : Fin n, ((σ k : ℤ) : ℝ) * F j (S k)
      ≤ ⨆ j' : {j' // j' ∈ t},
          (n : ℝ)⁻¹ * ∑ k : Fin n, ((σ k : ℤ) : ℝ) * F_on F t j' (S k) :=
    le_ciSup hbdd ⟨j, hj⟩
  have hdiff : ∑ k : Fin n, ((σ k : ℤ) : ℝ) * (F i (S k) - F j (S k)) ≤ (n : ℝ) * eps :=
    le_trans (signed_sum_le_mul_empiricalDist S (F i) (F j) σ)
      (by gcongr)
  have hsplit : ∑ k : Fin n, ((σ k : ℤ) : ℝ) * F i (S k)
      = (∑ k : Fin n, ((σ k : ℤ) : ℝ) * F j (S k))
        + ∑ k : Fin n, ((σ k : ℤ) : ℝ) * (F i (S k) - F j (S k)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, mul_add]
  have hscale : (n : ℝ)⁻¹ * ∑ k : Fin n, ((σ k : ℤ) : ℝ) * (F i (S k) - F j (S k)) ≤ eps := by
    rw [inv_mul_le_iff₀ hnR]
    linarith
  linarith

/-- The one-step discretization bound: an `eps`-net of cardinality `N` whose members are
bounded by `b` on the sample controls the Rademacher complexity by
`eps + b * sqrt (2 * log N) / sqrt n`. -/
theorem empiricalRademacherComplexity_without_abs_le_of_net
    [Nonempty ι] (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) (hn : 0 < n)
    {t : Finset ι} (ht : t.Nonempty) {eps b : ℝ} (hb : 0 ≤ b)
    (hbdd : ∀ j ∈ t, ∀ k, |F j (S k)| ≤ b)
    (hnet : ∀ i : ι, ∃ j ∈ t, empiricalDist S (F i) (F j) ≤ eps) :
    empiricalRademacherComplexity_without_abs n F S
      ≤ eps + b * Real.sqrt (2 * Real.log t.card) / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (0 : ℝ) < (Fintype.card (Signs n) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Signs n)
  -- the approximation step, averaged over the sign vectors
  have hstep : empiricalRademacherComplexity_without_abs n F S
      ≤ eps + empiricalRademacherComplexity_without_abs n (F_on F t) S := by
    have hsum := Finset.sum_le_sum
      (fun σ (_ : σ ∈ (Finset.univ : Finset (Signs n))) =>
        sup_le_add_sup_of_net F S hn ht hnet σ)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    have hscaled := mul_le_mul_of_nonneg_left hsum
      (le_of_lt (inv_pos.2 hcard))
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul] at hscaled
    exact hscaled
  -- Massart's lemma on the net
  have hmass : empiricalRademacherComplexity_without_abs n (F_on F t) S
      ≤ b * Real.sqrt (2 * Real.log t.card) / Real.sqrt n := by
    have hbridge :=
      empiricalRademacherComplexity_without_abs_eq_empiricalRademacherComplexity_pmf_without_abs
        (n := n) (f := F_on F t) (S := S)
    have hm := massart_lemma_pmf F S t ht hn b hbdd
    rw [← hbridge] at hm
    refine hm.trans ?_
    have hsup : (t.sup' ht fun j =>
        Real.sqrt (∑ i : Fin n, ((n : ℝ)⁻¹ * |F j (S i)|) ^ 2)) ≤ b / Real.sqrt n := by
      refine Finset.sup'_le _ _ fun j hj => ?_
      have hle : ∑ i : Fin n, ((n : ℝ)⁻¹ * |F j (S i)|) ^ 2 ≤ b ^ 2 / n := by
        calc ∑ i : Fin n, ((n : ℝ)⁻¹ * |F j (S i)|) ^ 2
            ≤ ∑ _i : Fin n, ((n : ℝ)⁻¹ * b) ^ 2 := by
              refine Finset.sum_le_sum fun i _ => ?_
              gcongr
              exact hbdd j hj i
          _ = b ^ 2 / n := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp
      refine le_trans (Real.sqrt_le_sqrt hle) ?_
      rw [show b ^ 2 / (n : ℝ) = b ^ 2 * (n : ℝ)⁻¹ by ring, Real.sqrt_mul (sq_nonneg b),
        Real.sqrt_sq hb, Real.sqrt_inv, ← div_eq_mul_inv]
    have hlog : 0 ≤ Real.sqrt (2 * Real.log t.card) := Real.sqrt_nonneg _
    calc (t.sup' ht fun j => Real.sqrt (∑ i : Fin n, ((n : ℝ)⁻¹ * |F j (S i)|) ^ 2))
          * Real.sqrt (2 * Real.log t.card)
        ≤ (b / Real.sqrt n) * Real.sqrt (2 * Real.log t.card) :=
          mul_le_mul_of_nonneg_right hsup hlog
      _ = b * Real.sqrt (2 * Real.log t.card) / Real.sqrt n := by ring
  linarith

end ProbabilityTheory
