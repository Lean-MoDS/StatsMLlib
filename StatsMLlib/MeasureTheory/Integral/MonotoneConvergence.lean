/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Monotone convergence with bounded integrals

Mathlib's `integral_tendsto_of_tendsto_of_monotone` assumes that the limit is integrable. This file
derives that integrability, and the a.e. boundedness of the sequence, from a uniform bound on the
integrals of the sequence.

## Main results

* `MeasureTheory.ae_bddAbove_of_monotone_of_integral_le`: a monotone sequence of integrable
  functions with integrals bounded above is a.e. bounded above;
  `MeasureTheory.ae_bddBelow_of_antitone_of_le_integral` is the antitone counterpart.
* `MeasureTheory.integrable_of_tendsto_of_monotone_of_integral_le`: the a.e. limit of a monotone
  sequence of integrable functions with integrals bounded above is integrable.
* `MeasureTheory.integrable_of_tendsto_of_antitone_of_le_integral`: the antitone counterpart.
-/

open Filter Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}

/-- For a monotone sequence with integrals bounded by `C`, the Lebesgue integrals of the
increments `f n - f 0` are bounded by `C - ∫ f 0`. -/
lemma lintegral_ofReal_sub_le {C : ℝ} (hf : ∀ n, Integrable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x) (hC : ∀ n, ∫ x, f n x ∂μ ≤ C) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (f n x - f 0 x) ∂μ ≤ ENNReal.ofReal (C - ∫ x, f 0 x ∂μ) := by
  have hnn : 0 ≤ᵐ[μ] fun x ↦ f n x - f 0 x := by
    filter_upwards [h_mono] with x hx
    exact sub_nonneg.2 (hx (Nat.zero_le n))
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x ↦ f n x - f 0 x)
    ((hf n).sub (hf 0)) hnn, integral_sub (hf n) (hf 0)]
  exact ENNReal.ofReal_le_ofReal (sub_le_sub_right (hC n) _)

/-- A monotone sequence of integrable functions whose integrals are bounded above is a.e. bounded
above. -/
lemma ae_bddAbove_of_monotone_of_integral_le {C : ℝ} (hf : ∀ n, Integrable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x) (hC : ∀ n, ∫ x, f n x ∂μ ≤ C) :
    ∀ᵐ x ∂μ, BddAbove (Set.range fun n ↦ f n x) := by
  set g : ℕ → α → ENNReal := fun n x ↦ ENNReal.ofReal (f n x - f 0 x)
  have hgm : ∀ n, AEMeasurable (g n) μ :=
    fun n ↦ ((hf n).sub (hf 0)).aemeasurable.ennreal_ofReal
  have hgmono : ∀ᵐ x ∂μ, Monotone fun n ↦ g n x := by
    filter_upwards [h_mono] with x hx n m hnm
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_right (hx hnm) _)
  have hfin : ∫⁻ x, ⨆ n, g n x ∂μ ≠ ⊤ := by
    rw [lintegral_iSup' hgm hgmono]
    exact ((iSup_le (lintegral_ofReal_sub_le hf h_mono hC)).trans_lt ENNReal.ofReal_lt_top).ne
  filter_upwards [ae_lt_top' (AEMeasurable.iSup hgm) hfin] with x hx
  refine ⟨f 0 x + (⨆ n, g n x).toReal, Set.forall_mem_range.2 fun n ↦ ?_⟩
  have h := (ENNReal.ofReal_le_iff_le_toReal hx.ne).1 (le_iSup (fun n ↦ g n x) n)
  linarith

/-- An antitone sequence of integrable functions whose integrals are bounded below is a.e. bounded
below. -/
lemma ae_bddBelow_of_antitone_of_le_integral {C : ℝ} (hf : ∀ n, Integrable (f n) μ)
    (h_anti : ∀ᵐ x ∂μ, Antitone fun n ↦ f n x) (hC : ∀ n, C ≤ ∫ x, f n x ∂μ) :
    ∀ᵐ x ∂μ, BddBelow (Set.range fun n ↦ f n x) := by
  have h := ae_bddAbove_of_monotone_of_integral_le (f := fun n x ↦ -f n x) (C := -C)
    (fun n ↦ (hf n).neg) ?_ fun n ↦ by rw [integral_neg]; exact neg_le_neg (hC n)
  · filter_upwards [h] with x hx
    obtain ⟨b, hb⟩ := hx
    exact ⟨-b, Set.forall_mem_range.2 fun n ↦ neg_le.1 (hb ⟨n, rfl⟩)⟩
  · filter_upwards [h_anti] with x hx n m hnm
    exact neg_le_neg (hx hnm)

/-- The a.e. limit of a monotone sequence of integrable functions whose integrals are bounded above
is integrable. -/
lemma integrable_of_tendsto_of_monotone_of_integral_le {C : ℝ} (hf : ∀ n, Integrable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x)))
    (hC : ∀ n, ∫ x, f n x ∂μ ≤ C) : Integrable F μ := by
  have hFm : AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n ↦ (hf n).1) h_tendsto
  have hF_ge : 0 ≤ᵐ[μ] fun x ↦ F x - f 0 x := by
    filter_upwards [h_tendsto, h_mono] with x hx hm
    exact sub_nonneg.2 (ge_of_tendsto' hx fun n ↦ hm (Nat.zero_le n))
  have hlim : Tendsto (fun n ↦ ∫⁻ x, ENNReal.ofReal (f n x - f 0 x) ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (F x - f 0 x) ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n ↦ ((hf n).sub (hf 0)).aemeasurable.ennreal_ofReal) ?_ ?_
    · filter_upwards [h_mono] with x hx n m hnm
      exact ENNReal.ofReal_le_ofReal (sub_le_sub_right (hx hnm) _)
    · filter_upwards [h_tendsto] with x hx
      exact (ENNReal.continuous_ofReal.tendsto _).comp (hx.sub tendsto_const_nhds)
  have hfin : ∫⁻ x, ENNReal.ofReal (F x - f 0 x) ∂μ < ⊤ :=
    (le_of_tendsto' hlim (lintegral_ofReal_sub_le hf h_mono hC)).trans_lt ENNReal.ofReal_lt_top
  have hsub : Integrable (fun x ↦ F x - f 0 x) μ := by
    refine ⟨hFm.sub (hf 0).1, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hF_ge]
    exact hfin
  refine (hsub.add (hf 0)).congr (Eventually.of_forall fun x ↦ ?_)
  simp

/-- The a.e. limit of an antitone sequence of integrable functions whose integrals are bounded
below is integrable. -/
lemma integrable_of_tendsto_of_antitone_of_le_integral {C : ℝ} (hf : ∀ n, Integrable (f n) μ)
    (h_anti : ∀ᵐ x ∂μ, Antitone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x)))
    (hC : ∀ n, C ≤ ∫ x, f n x ∂μ) : Integrable F μ := by
  have h := integrable_of_tendsto_of_monotone_of_integral_le (f := fun n x ↦ -f n x) (F := -F)
    (C := -C) (fun n ↦ (hf n).neg) ?_ ?_ ?_
  · simpa using h.neg
  · filter_upwards [h_anti] with x hx n m hnm
    exact neg_le_neg (hx hnm)
  · filter_upwards [h_tendsto] with x hx
    exact hx.neg
  · intro n
    rw [integral_neg]
    exact neg_le_neg (hC n)

end MeasureTheory
