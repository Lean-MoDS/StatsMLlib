/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic

/-!
# Chebyshev's association inequality and Harris' inequality

Two nondecreasing functions of the same real random variable are positively correlated
(Chebyshev's association inequality, BLM Theorem 2.14). Harris' inequality (BLM Theorem 2.15)
extends this to coordinatewise nondecreasing functions of independent real random variables.

## Main results

* `Harris.integral_mul_integral_le`: for `Y ≥ 0` and nondecreasing `f, g : ℝ → ℝ`,
  `E[Y f(X)] E[Y g(X)] ≤ E[Y] E[Y f(X) g(X)]`.
* `Harris.integral_mul_le_integral_mul_of_antitone`: the reverse inequality for nonincreasing `f`.
* `Harris.harris`: for a product `μ = μ₁ ⊗ ⋯ ⊗ μₙ` of probability measures on `ℝ` and bounded
  measurable nondecreasing `f, g : ℝⁿ → ℝ`, `∫ f dμ ∫ g dμ ≤ ∫ f g dμ`.
* `Harris.harris_of_antitone`: the reverse inequality for nonincreasing `f`.
* `Harris.harris_of_iIndepFun`, `Harris.harris_of_iIndepFun_of_antitone`: the same statements for
  functions of independent real random variables.

## Implementation notes

* Instead of an independent copy `(X', Y')`, Theorem 2.14 is proved on `P.prod P`.
* In Harris' inequality, the functions are assumed measurable and bounded:
  * a coordinatewise monotone function on `ℝⁿ` need not be Borel measurable for `n ≥ 2`;
  * boundedness makes every section `t ↦ f (t, u)` integrable, for every `u` rather than almost
    every `u`, which the monotonicity of the averaged function needs.
* The induction step splits off the first coordinate through
  `MeasurableEquiv.piFinSuccAbove _ 0`, and replaces the conditional expectation
  `E[f(X) | X₂, …, Xₙ]` by the explicit average `u ↦ ∫ f (Fin.cons t u) dμ₁(t)`.
-/

open MeasureTheory ProbabilityTheory

namespace Harris

/-! ### Chebyshev's association inequality -/

/-- The pointwise inequality behind Chebyshev's association inequality. -/
lemma mul_sub_nonneg_of_monotone {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) (x x' : ℝ) :
    0 ≤ (f x - f x') * (g x - g x') := by
  rcases le_total x x' with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf h)) (sub_nonpos.mpr (hg h))
  · exact mul_nonneg (sub_nonneg.mpr (hf h)) (sub_nonneg.mpr (hg h))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SigmaFinite P]

/-- **Chebyshev's association inequality** (BLM Theorem 2.14). For `Y ≥ 0` and nondecreasing
`f, g`, `E[Y f(X)] E[Y g(X)] ≤ E[Y] E[Y f(X) g(X)]`. The variables `X` and `Y` need not be
independent. -/
theorem integral_mul_integral_le {X Y : Ω → ℝ} {f g : ℝ → ℝ} (hf : Monotone f)
    (hg : Monotone g) (hY : 0 ≤ᵐ[P] Y) (hY₁ : Integrable Y P)
    (hYf : Integrable (fun ω ↦ Y ω * f (X ω)) P) (hYg : Integrable (fun ω ↦ Y ω * g (X ω)) P)
    (hYfg : Integrable (fun ω ↦ Y ω * (f (X ω) * g (X ω))) P) :
    (∫ ω, Y ω * f (X ω) ∂P) * ∫ ω, Y ω * g (X ω) ∂P ≤
      (∫ ω, Y ω ∂P) * ∫ ω, Y ω * (f (X ω) * g (X ω)) ∂P := by
  set A := fun ω ↦ Y ω * (f (X ω) * g (X ω))
  set B := fun ω ↦ Y ω * f (X ω)
  set D := fun ω ↦ Y ω * g (X ω)
  have hZ : ∀ᵐ p ∂P.prod P,
      0 ≤ Y p.1 * Y p.2 * ((f (X p.1) - f (X p.2)) * (g (X p.1) - g (X p.2))) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hY,
      Measure.quasiMeasurePreserving_snd.ae hY] with p h1 h2
    exact mul_nonneg (mul_nonneg h1 h2) (mul_sub_nonneg_of_monotone hf hg _ _)
  have hexp : (fun p : Ω × Ω ↦
      Y p.1 * Y p.2 * ((f (X p.1) - f (X p.2)) * (g (X p.1) - g (X p.2)))) =
      fun p ↦ A p.1 * Y p.2 - B p.1 * D p.2 - D p.1 * B p.2 + Y p.1 * A p.2 := by
    funext p
    simp only [A, B, D]
    ring
  have h1 := hYfg.mul_prod hY₁
  have h2 := hYf.mul_prod hYg
  have h3 := hYg.mul_prod hYf
  have h4 := hY₁.mul_prod hYfg
  have hint := integral_nonneg_of_ae hZ
  rw [hexp, integral_add (f := fun p : Ω × Ω ↦ A p.1 * Y p.2 - B p.1 * D p.2 - D p.1 * B p.2)
      (g := fun p : Ω × Ω ↦ Y p.1 * A p.2) ((h1.sub h2).sub h3) h4,
    integral_sub (f := fun p : Ω × Ω ↦ A p.1 * Y p.2 - B p.1 * D p.2)
      (g := fun p : Ω × Ω ↦ D p.1 * B p.2)
      (h1.sub h2) h3,
    integral_sub (f := fun p : Ω × Ω ↦ A p.1 * Y p.2) (g := fun p : Ω × Ω ↦ B p.1 * D p.2) h1 h2,
    integral_prod_mul A Y, integral_prod_mul B D, integral_prod_mul D B,
    integral_prod_mul Y A] at hint
  simp only [A, B, D] at hint ⊢
  nlinarith

/-- **Chebyshev's association inequality** (BLM Theorem 2.14), for nonincreasing `f` and
nondecreasing `g`. -/
theorem integral_mul_le_integral_mul_of_antitone {X Y : Ω → ℝ} {f g : ℝ → ℝ} (hf : Antitone f)
    (hg : Monotone g) (hY : 0 ≤ᵐ[P] Y) (hY₁ : Integrable Y P)
    (hYf : Integrable (fun ω ↦ Y ω * f (X ω)) P) (hYg : Integrable (fun ω ↦ Y ω * g (X ω)) P)
    (hYfg : Integrable (fun ω ↦ Y ω * (f (X ω) * g (X ω))) P) :
    (∫ ω, Y ω ∂P) * ∫ ω, Y ω * (f (X ω) * g (X ω)) ∂P ≤
      (∫ ω, Y ω * f (X ω) ∂P) * ∫ ω, Y ω * g (X ω) ∂P := by
  have h := integral_mul_integral_le (X := X) (f := fun x ↦ -f x) hf.neg hg hY hY₁
    (by simpa only [mul_neg] using hYf.fun_neg)
    hYg (by simpa only [neg_mul, mul_neg] using hYfg.fun_neg)
  simp only [mul_neg, neg_mul, integral_neg] at h
  linarith

/-- Chebyshev's association inequality for a probability measure on `ℝ`. -/
theorem integral_mul_integral_le_of_monotone {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) (hfi : Integrable f ν)
    (hgi : Integrable g ν) (hfgi : Integrable (fun x ↦ f x * g x) ν) :
    (∫ x, f x ∂ν) * ∫ x, g x ∂ν ≤ ∫ x, f x * g x ∂ν := by
  have h := integral_mul_integral_le (P := ν) (X := id) (Y := fun _ ↦ 1) hf hg
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one) (integrable_const 1)
    (by simpa using hfi) (by simpa using hgi) (by simpa using hfgi)
  simpa using h

/-! ### Harris' inequality -/

section Pi

variable {n : ℕ}

lemma measurable_cons :
    Measurable fun p : ℝ × (Fin n → ℝ) ↦ (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) :=
  measurable_pi_iff.mpr fun i ↦ Fin.cases (by simpa using measurable_fst)
    (fun j ↦ by simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd) i

/-- Splitting off the first coordinate of a product measure. -/
lemma integral_pi_succ (μ : Fin (n + 1) → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (F : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ x, F x ∂Measure.pi μ =
      ∫ p, F (Fin.cons p.1 p.2) ∂((μ 0).prod (Measure.pi fun j ↦ μ j.succ)) := by
  rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
  simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
    Equiv.coe_fn_mk]
  rfl

lemma integrable_of_bound {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {F : α → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) : Integrable F ν :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- **Harris' inequality** (BLM Theorem 2.15). For a product of probability measures on `ℝ` and
bounded measurable nondecreasing `f, g : ℝⁿ → ℝ`, `∫ f ∫ g ≤ ∫ f g`. -/
theorem harris (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f g : (Fin n → ℝ) → ℝ} (hf : Monotone f) (hg : Monotone g) (hfm : Measurable f)
    (hgm : Measurable g) {C : ℝ} (hfC : ∀ x, |f x| ≤ C) (hgC : ∀ x, |g x| ≤ C) :
    (∫ x, f x ∂Measure.pi μ) * ∫ x, g x ∂Measure.pi μ ≤ ∫ x, f x * g x ∂Measure.pi μ := by
  induction n with
  | zero =>
    have hf0 : f = fun _ ↦ f 0 := funext fun x ↦ congrArg f (Subsingleton.elim x 0)
    have hg0 : g = fun _ ↦ g 0 := funext fun x ↦ congrArg g (Subsingleton.elim x 0)
    rw [hf0, hg0]
    simp
  | succ n ih =>
    set ν := (μ 0).prod (Measure.pi fun j : Fin n ↦ μ j.succ)
    set F : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ f (Fin.cons p.1 p.2)
    set G : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ g (Fin.cons p.1 p.2)
    have hFm : Measurable F := hfm.comp measurable_cons
    have hGm : Measurable G := hgm.comp measurable_cons
    -- The averaged functions `f'`, `g'` on the remaining coordinates.
    set f' : (Fin n → ℝ) → ℝ := fun u ↦ ∫ t, f (Fin.cons t u) ∂μ 0
    set g' : (Fin n → ℝ) → ℝ := fun u ↦ ∫ t, g (Fin.cons t u) ∂μ 0
    have hsec_mono : ∀ {h : (Fin (n + 1) → ℝ) → ℝ}, Monotone h → ∀ u : Fin n → ℝ,
        Monotone fun t ↦ h (Fin.cons t u) :=
      fun hh u _ _ hst ↦ hh (Fin.cons_le_cons.mpr ⟨hst, le_rfl⟩)
    have hsec_int : ∀ {h : (Fin (n + 1) → ℝ) → ℝ}, Monotone h → (∀ x, |h x| ≤ C) →
        ∀ u : Fin n → ℝ, Integrable (fun t ↦ h (Fin.cons t u)) (μ 0) :=
      fun hh hC u ↦ integrable_of_bound (hsec_mono hh u).measurable fun t ↦ hC _
    have havg_mono : ∀ {h : (Fin (n + 1) → ℝ) → ℝ}, Monotone h → (∀ x, |h x| ≤ C) →
        Monotone fun u ↦ ∫ t, h (Fin.cons t u) ∂μ 0 :=
      fun hh hC u v huv ↦ integral_mono (hsec_int hh hC u) (hsec_int hh hC v)
        fun t ↦ hh (Fin.cons_le_cons.mpr ⟨le_rfl, huv⟩)
    have havg_bound : ∀ {h : (Fin (n + 1) → ℝ) → ℝ}, (∀ x, |h x| ≤ C) →
        ∀ u : Fin n → ℝ, |∫ t, h (Fin.cons t u) ∂μ 0| ≤ C := by
      intro h hC u
      have := norm_integral_le_of_norm_le_const (μ := μ 0) (C := C)
        (f := fun t ↦ h (Fin.cons t u)) (Filter.Eventually.of_forall fun t ↦ hC _)
      simpa using this
    have hf'm : Measurable f' :=
      (hFm.stronglyMeasurable.integral_prod_left' (μ := μ 0)).measurable
    have hg'm : Measurable g' :=
      (hGm.stronglyMeasurable.integral_prod_left' (μ := μ 0)).measurable
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hfC 0)
    have hFi : Integrable F ν := integrable_of_bound hFm fun p ↦ hfC _
    have hGi : Integrable G ν := integrable_of_bound hGm fun p ↦ hgC _
    have hFGi : Integrable (fun p ↦ F p * G p) ν :=
      integrable_of_bound (hFm.mul hGm) (C := C * C) fun p ↦ by
        rw [abs_mul]
        exact mul_le_mul (hfC _) (hgC _) (abs_nonneg _) hC0
    -- Step B: the one-dimensional inequality on each section.
    have hB : ∀ u, f' u * g' u ≤ ∫ t, f (Fin.cons t u) * g (Fin.cons t u) ∂μ 0 := fun u ↦
      integral_mul_integral_le_of_monotone (hsec_mono hf u) (hsec_mono hg u)
        (hsec_int hf hfC u) (hsec_int hg hgC u)
        (integrable_of_bound ((hsec_mono hf u).measurable.mul (hsec_mono hg u).measurable)
          (C := C * C) fun t ↦ by
            rw [abs_mul]
            exact mul_le_mul (hfC _) (hgC _) (abs_nonneg _) hC0)
    -- Step D: the induction hypothesis.
    have hD := ih (fun j ↦ μ j.succ) (havg_mono hf hfC) (havg_mono hg hgC) hf'm hg'm
      (havg_bound hfC) (havg_bound hgC)
    -- Steps C and E: Fubini.
    have hfE : ∫ x, f x ∂Measure.pi μ = ∫ u, f' u ∂Measure.pi fun j ↦ μ j.succ := by
      rw [integral_pi_succ, integral_prod_symm _ hFi]
    have hgE : ∫ x, g x ∂Measure.pi μ = ∫ u, g' u ∂Measure.pi fun j ↦ μ j.succ := by
      rw [integral_pi_succ, integral_prod_symm _ hGi]
    have hfgE : ∫ x, f x * g x ∂Measure.pi μ =
        ∫ u, ∫ t, f (Fin.cons t u) * g (Fin.cons t u) ∂μ 0 ∂Measure.pi fun j ↦ μ j.succ := by
      rw [integral_pi_succ, integral_prod_symm _ hFGi]
    have hC : ∫ u, f' u * g' u ∂Measure.pi (fun j ↦ μ j.succ) ≤
        ∫ u, ∫ t, f (Fin.cons t u) * g (Fin.cons t u) ∂μ 0 ∂Measure.pi fun j ↦ μ j.succ :=
      integral_mono (integrable_of_bound (hf'm.mul hg'm) (C := C * C) fun u ↦ by
          rw [abs_mul]
          exact mul_le_mul (havg_bound hfC u) (havg_bound hgC u) (abs_nonneg _) hC0)
        hFGi.integral_prod_right hB
    rw [hfE, hgE, hfgE]
    exact hD.trans hC

/-- **Harris' inequality** (BLM Theorem 2.15), for nonincreasing `f` and nondecreasing `g`. -/
theorem harris_of_antitone (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f g : (Fin n → ℝ) → ℝ} (hf : Antitone f) (hg : Monotone g) (hfm : Measurable f)
    (hgm : Measurable g) {C : ℝ} (hfC : ∀ x, |f x| ≤ C) (hgC : ∀ x, |g x| ≤ C) :
    ∫ x, f x * g x ∂Measure.pi μ ≤ (∫ x, f x ∂Measure.pi μ) * ∫ x, g x ∂Measure.pi μ := by
  have h := harris μ (f := fun x ↦ -f x) hf.neg hg hfm.neg hgm (C := C)
    (fun x ↦ by rw [abs_neg]; exact hfC x) hgC
  simp only [neg_mul, integral_neg] at h
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integral_comp_eq_integral_pi {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {h : (Fin n → ℝ) → ℝ} (hh : Measurable h) :
    ∫ ω, h (fun i ↦ X i ω) ∂P = ∫ x, h x ∂Measure.pi fun i ↦ P.map (X i) := by
  rw [← (iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hX i).aemeasurable).mp hind,
    integral_map (measurable_pi_iff.mpr hX).aemeasurable hh.aestronglyMeasurable]

/-- **Harris' inequality** (BLM Theorem 2.15) for independent real random variables. -/
theorem harris_of_iIndepFun {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {f g : (Fin n → ℝ) → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hfm : Measurable f) (hgm : Measurable g) {C : ℝ} (hfC : ∀ x, |f x| ≤ C)
    (hgC : ∀ x, |g x| ≤ C) :
    (∫ ω, f (fun i ↦ X i ω) ∂P) * ∫ ω, g (fun i ↦ X i ω) ∂P ≤
      ∫ ω, f (fun i ↦ X i ω) * g (fun i ↦ X i ω) ∂P := by
  have : ∀ i, IsProbabilityMeasure (P.map (X i)) :=
    fun i ↦ (Measure.isProbabilityMeasure_map_iff (hX i).aemeasurable).mpr inferInstance
  rw [integral_comp_eq_integral_pi hX hind hfm, integral_comp_eq_integral_pi hX hind hgm,
    integral_comp_eq_integral_pi hX hind (h := fun x ↦ f x * g x) (hfm.mul hgm)]
  exact harris _ hf hg hfm hgm hfC hgC

/-- **Harris' inequality** (BLM Theorem 2.15) for independent real random variables, for
nonincreasing `f` and nondecreasing `g`. -/
theorem harris_of_iIndepFun_of_antitone {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) {f g : (Fin n → ℝ) → ℝ} (hf : Antitone f) (hg : Monotone g)
    (hfm : Measurable f) (hgm : Measurable g) {C : ℝ} (hfC : ∀ x, |f x| ≤ C)
    (hgC : ∀ x, |g x| ≤ C) :
    ∫ ω, f (fun i ↦ X i ω) * g (fun i ↦ X i ω) ∂P ≤
      (∫ ω, f (fun i ↦ X i ω) ∂P) * ∫ ω, g (fun i ↦ X i ω) ∂P := by
  have : ∀ i, IsProbabilityMeasure (P.map (X i)) :=
    fun i ↦ (Measure.isProbabilityMeasure_map_iff (hX i).aemeasurable).mpr inferInstance
  rw [integral_comp_eq_integral_pi hX hind hfm, integral_comp_eq_integral_pi hX hind hgm,
    integral_comp_eq_integral_pi hX hind (h := fun x ↦ f x * g x) (hfm.mul hgm)]
  exact harris_of_antitone _ hf hg hfm hgm hfC hgC

end Pi

example (μ : Fin 3 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f g : (Fin 3 → ℝ) → ℝ} (hf : Monotone f) (hg : Monotone g) (hfm : Measurable f)
    (hgm : Measurable g) (hfC : ∀ x, |f x| ≤ 1) (hgC : ∀ x, |g x| ≤ 1) :
    (∫ x, f x ∂Measure.pi μ) * ∫ x, g x ∂Measure.pi μ ≤ ∫ x, f x * g x ∂Measure.pi μ :=
  harris μ hf hg hfm hgm hfC hgC

end Harris
