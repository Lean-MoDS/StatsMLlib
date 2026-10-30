/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Concentration.McDiarmid
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Concentration of the L¹ error of kernel density estimators

For a kernel `K : ℝ → ℝ` and a bandwidth `h > 0`, the kernel density estimator built from a sample
`x : Fin n → ℝ` is
`kde K h x t = (n * h)⁻¹ * ∑ i, K ((t - x i) / h)`,
and its L¹ error against a target `f` is `kdeL1Error K h f x = ∫ t, |kde K h x t - f t|`.

Replacing one sample point moves the estimator by at most `2 / n` in L¹, so the L¹ error has
bounded differences and McDiarmid's inequality gives a sub-Gaussian upper tail.

The sample is a deterministic point `x : Fin n → ℝ`; probabilities are taken under a product
measure `Measure.pi μ`. Only independence of the coordinates is used: the coordinate laws `μ i`
need not be equal, and `f` need not be their density. Neither `K` nor `f` is assumed measurable;
measurability of the L¹ error is recovered from a.e.-strong measurability.

## Main definitions

* `kde`: the kernel density estimator.
* `kdeL1Error`: its L¹ distance to a target function.

## Main results

* `integral_kernel_shift`: `∫ t, K ((t - a) / h) = h`.
* `integral_abs_kde_sub_kde_update_le`: replacing one sample point moves `kde` by at most `2 / n`
  in L¹.
* `abs_kdeL1Error_sub_update_le`: the bounded-difference property of `kdeL1Error`.
* `measurable_kdeL1Error`: the L¹ error is a measurable function of the sample.
* `kdeL1Error_tail_bound`: `P[F ≥ E F + δ] ≤ exp (-(n * δ ^ 2) / 2)`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The kernel density estimator with kernel `K` and bandwidth `h` at the sample `x`. -/
def kde (K : ℝ → ℝ) (h : ℝ) {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((n : ℝ) * h)⁻¹ * ∑ i, K ((t - x i) / h)

/-- The L¹ distance between the kernel density estimator at the sample `x` and `f`. -/
def kdeL1Error (K : ℝ → ℝ) (h : ℝ) (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∫ t, |kde K h x t - f t|

variable {K : ℝ → ℝ} {h : ℝ}

theorem integrable_kernel_shift (hh : h ≠ 0) (hK : Integrable K) (a : ℝ) :
    Integrable fun t ↦ K ((t - a) / h) :=
  (hK.comp_div hh).comp_sub_right a

/-- A rescaled translate of a kernel integrates to the bandwidth. -/
theorem integral_kernel_shift (hh : 0 < h) (hK_one : ∫ t, K t = 1) (a : ℝ) :
    ∫ t, K ((t - a) / h) = h := by
  have := integral_sub_right_eq_self (μ := volume) (fun s ↦ K (s / h)) a
  rw [this, Measure.integral_comp_div, hK_one, abs_of_pos hh, smul_eq_mul, mul_one]

theorem integrable_kde (hh : h ≠ 0) (hK : Integrable K) {n : ℕ} (x : Fin n → ℝ) :
    Integrable (kde K h x) :=
  (integrable_finsetSum _ fun i _ ↦ integrable_kernel_shift hh hK (x i)).const_mul _

theorem kde_sub_kde_update {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (y t : ℝ) :
    kde K h x t - kde K h (Function.update x i y) t =
      ((n : ℝ) * h)⁻¹ * (K ((t - x i) / h) - K ((t - y) / h)) := by
  rw [kde, kde, ← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Function.update_of_ne hj]
  · simp

/-- Replacing one sample point moves the kernel density estimator by at most `2 / n` in L¹. -/
theorem integral_abs_kde_sub_kde_update_le (hh : 0 < h) (hK_nonneg : ∀ t, 0 ≤ K t)
    (hK : Integrable K) (hK_one : ∫ t, K t = 1) {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (y : ℝ) :
    ∫ t, |kde K h x t - kde K h (Function.update x i y) t| ≤ 2 / n := by
  have hn : (0 : ℝ) < n := by
    have := i.pos
    exact_mod_cast this
  have hc : 0 < ((n : ℝ) * h)⁻¹ := by positivity
  have hA := integrable_kernel_shift hh.ne' hK (x i)
  have hB := integrable_kernel_shift hh.ne' hK y
  calc
    _ = ∫ t, ((n : ℝ) * h)⁻¹ * |K ((t - x i) / h) - K ((t - y) / h)| := by
      simp_rw [kde_sub_kde_update, abs_mul, abs_of_pos hc]
    _ ≤ ∫ t, ((n : ℝ) * h)⁻¹ * (K ((t - x i) / h) + K ((t - y) / h)) := by
      refine integral_mono ((hA.sub hB).abs.const_mul _) ((hA.add hB).const_mul _) fun t ↦ ?_
      refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨?_, ?_⟩) hc.le
      · linarith [hK_nonneg ((t - x i) / h)]
      · linarith [hK_nonneg ((t - y) / h)]
    _ = 2 / n := by
      rw [integral_const_mul, integral_add hA hB, integral_kernel_shift hh hK_one,
        integral_kernel_shift hh hK_one]
      field_simp
      ring

/-- Reverse triangle inequality for L¹ distances to a common function. -/
theorem abs_integral_abs_sub_sub_integral_abs_sub_le {g₁ g₂ f : ℝ → ℝ}
    (h₁ : Integrable fun t ↦ g₁ t - f t) (h₂ : Integrable fun t ↦ g₂ t - f t) :
    |(∫ t, |g₁ t - f t|) - (∫ t, |g₂ t - f t|)| ≤ ∫ t, |g₁ t - g₂ t| := by
  have h₁₂ : Integrable fun t ↦ g₁ t - g₂ t := by
    convert h₁.sub h₂ using 2 with t
    simp only [Pi.sub_apply]
    ring
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
  · rw [← integral_sub h₁.abs h₂.abs]
    refine integral_mono (h₁.abs.sub h₂.abs) h₁₂.abs fun t ↦ ?_
    simpa using abs_sub_abs_le_abs_sub (g₁ t - f t) (g₂ t - f t)
  · rw [← integral_sub h₂.abs h₁.abs]
    refine integral_mono (h₂.abs.sub h₁.abs) h₁₂.abs fun t ↦ ?_
    simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub (g₂ t - f t) (g₁ t - f t)

/-- The L¹ error of the kernel density estimator has bounded differences. -/
theorem abs_kdeL1Error_sub_update_le {f : ℝ → ℝ} (hh : 0 < h) (hK_nonneg : ∀ t, 0 ≤ K t)
    (hK : Integrable K) (hK_one : ∫ t, K t = 1) (hf : Integrable f) {n : ℕ}
    (x : Fin n → ℝ) (i : Fin n) (y : ℝ) :
    |kdeL1Error K h f x - kdeL1Error K h f (Function.update x i y)| ≤ 2 / n :=
  (abs_integral_abs_sub_sub_integral_abs_sub_le ((integrable_kde hh.ne' hK x).sub hf)
    ((integrable_kde hh.ne' hK _).sub hf)).trans
    (integral_abs_kde_sub_kde_update_le hh hK_nonneg hK hK_one x i y)

/-- The L¹ error of the kernel density estimator is a measurable function of the sample. -/
theorem measurable_kdeL1Error {f : ℝ → ℝ} (hh : h ≠ 0) (hK : Integrable K) (hf : Integrable f)
    {n : ℕ} : Measurable (kdeL1Error K h f (n := n)) := by
  set K' := hK.1.mk K
  set f' := hf.1.mk f
  have hK' : Measurable K' := hK.1.stronglyMeasurable_mk.measurable
  have hf' : Measurable f' := hf.1.stronglyMeasurable_mk.measurable
  -- The map `t ↦ (t - a) / h` does not charge null sets, so `K` may be replaced by `K'`.
  have hshift (a : ℝ) : ∀ᵐ t, K ((t - a) / h) = K' ((t - a) / h) := by
    have hφ : Measure.QuasiMeasurePreserving (fun t : ℝ ↦ h⁻¹ • (t - a)) volume volume :=
      (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hh)).comp
        (measurePreserving_sub_right volume a).quasiMeasurePreserving
    filter_upwards [hφ.ae_eq_comp hK.1.ae_eq_mk] with t ht
    simpa [smul_eq_mul, div_eq_inv_mul] using ht
  have heq : kdeL1Error K h f (n := n) = kdeL1Error K' h f' := by
    funext x
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 fun i ↦ hshift (x i), hf.1.ae_eq_mk] with t ht hft
    simp only [kde, ht, hft]
    rfl
  rw [heq]
  refine (StronglyMeasurable.integral_prod_right (f := fun x t ↦ |kde K' h x t - f' t|)
    ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  simp only [kde, Function.uncurry_def]
  fun_prop

/-- **Concentration of the L¹ error of a kernel density estimator.** Under any product law of the
sample, the L¹ error exceeds its mean by `δ` with probability at most `exp (-(n * δ ^ 2) / 2)`. -/
theorem kdeL1Error_tail_bound {f : ℝ → ℝ} {n : ℕ} (hn : 0 < n) (hh : 0 < h)
    (hK_nonneg : ∀ t, 0 ≤ K t) (hK : Integrable K) (hK_one : ∫ t, K t = 1) (hf : Integrable f)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] {δ : ℝ} (hδ : 0 ≤ δ) :
    (Measure.pi μ {x | (Measure.pi μ)[kdeL1Error K h f] + δ ≤ kdeL1Error K h f x}).toReal ≤
      Real.exp (-(n * δ ^ 2) / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set F := kdeL1Error K h f (n := n)
  set X : Fin n → (Fin n → ℝ) → ℝ := fun i ω ↦ ω i
  have hX : ∀ i, Measurable (X i) := measurable_pi_apply
  have hind : iIndepFun X (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id
  have hsum : ∑ _i : Fin n, (2 / (n : ℝ)) ^ 2 = (4 : ℝ) / n := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have key := mcdiarmid_inequality_pos_of_sum_sq_pos (μ := Measure.pi μ) X hX hind
    (c := fun _ ↦ 2 / (n : ℝ))
    (fun i x y ↦ abs_kdeL1Error_sub_update_le hh hK_nonneg hK hK_one hf x i y)
    (measurable_kdeL1Error hh.ne' hK hf) hδ (by rw [hsum]; positivity)
  have hFX : F ∘ Function.swap X = F := rfl
  rw [hFX] at key
  have hset : {x | (Measure.pi μ)[F] + δ ≤ F x} =
      fun ω ↦ F ω - (Measure.pi μ)[F] ≥ δ := by
    ext x
    change (Measure.pi μ)[F] + δ ≤ F x ↔ F x - (Measure.pi μ)[F] ≥ δ
    constructor <;> intro hx <;> linarith
  rw [hset]
  refine key.trans (le_of_eq ?_)
  rw [hsum]
  congr 1
  field_simp
  ring

/-- The setting of the textbook exercise: an i.i.d. sample from the density `f`. -/
example {f : ℝ → ℝ} {n : ℕ} (hn : 0 < n) (hh : 0 < h) (hK_nonneg : ∀ t, 0 ≤ K t)
    (hK : Integrable K) (hK_one : ∫ t, K t = 1) (hf : Integrable f)
    [IsProbabilityMeasure (volume.withDensity fun t ↦ ENNReal.ofReal (f t))] {δ : ℝ}
    (hδ : 0 ≤ δ) :
    let P := Measure.pi fun _ : Fin n ↦ volume.withDensity fun t ↦ ENNReal.ofReal (f t)
    (P {x | P[kdeL1Error K h f] + δ ≤ kdeL1Error K h f x}).toReal ≤
      Real.exp (-(n * δ ^ 2) / 2) :=
  kdeL1Error_tail_bound hn hh hK_nonneg hK hK_one hf _ hδ

end
