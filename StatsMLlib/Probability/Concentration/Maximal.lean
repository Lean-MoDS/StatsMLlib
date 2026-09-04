/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
import StatsMLlib.Probability.Concentration.Hoeffding
import StatsMLlib.Probability.Process.FiniteMaximum
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Independence.Integration

/-!
# Maximal Inequalities

Finite and supremum-form maximal inequalities derived from sub-Gaussian moment bounds.

## Main definitions

This module uses Mathlib's cumulant-generating-function predicates.

## Main results

* `ProbabilityTheory.maximal_inequality_finset`: maximal inequality over a finite index set,
  stated with the sub-Gaussian bound in lower-integral form. It is a corollary of
  `expected_max_subGaussian` in `Probability.Process.FiniteMaximum`, which states the same
  bound with the hypothesis phrased through `ProbabilityTheory.cgf`; the two differ only in
  how sub-Gaussianity is spelled, and this module supplies the translation.
* `ProbabilityTheory.maximal_inequality_supR`: supremum form of the maximal inequality.
-/

open MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory

universe u

variable {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {ι : Type*} [DecidableEq ι]


omit [IsProbabilityMeasure μ] [DecidableEq ι] in
theorem integrable_of_subgaussian (X : ι → Ω → ℝ) (j : ι) (r : ℝ)
  (p : ∀ (t : ℝ), ∫⁻ (ω : Ω), ENNReal.ofReal (rexp (t * X j ω)) ∂μ ≤ ENNReal.ofReal (rexp (t ^ 2 * r ^ 2 / 2)))
  (q : AEMeasurable (X j) μ) : Integrable (X j) μ := by
  constructor
  exact aestronglyMeasurable_iff_aemeasurable.mpr q
  dsimp [HasFiniteIntegral]
  calc
  _ ≤ ∫⁻ (a : Ω), ENNReal.ofReal (rexp (|X j a|)) ∂μ := by
    apply lintegral_mono
    intro a
    simp only
    rw [enorm_eq_ofReal_abs (X j a)]
    rw [ENNReal.ofReal_le_ofReal_iff]
    exact le_trans (by linarith) (add_one_le_exp |X j a|)
    exact exp_nonneg |X j a|
  _ ≤ ∫⁻ (a : Ω), ENNReal.ofReal (rexp (-(X j a)) + rexp (X j a)) ∂μ := by
    apply lintegral_mono
    intro a
    simp only
    rw [ENNReal.ofReal_le_ofReal_iff]
    by_cases h : 0 ≤ X j a
    case pos =>
      rw [(by simp only [abs_eq_self]; exact h : |X j a| = X j a)]
      linarith [exp_nonneg (-X j a)]
    case neg =>
      rw [(by simp only [abs_eq_neg_self]; linarith [h] : |X j a| = - X j a)]
      linarith [exp_nonneg (X j a)]
    refine Left.add_nonneg ?hfg.ha ?hfg.hb
    exact exp_nonneg (-X j a)
    exact exp_nonneg (X j a)
  _ = ∫⁻ (a : Ω), ENNReal.ofReal (rexp (-(X j a))) + ENNReal.ofReal (rexp (X j a)) ∂μ := by
    apply lintegral_congr
    intro a
    refine ENNReal.ofReal_add (exp_nonneg (-X j a)) (exp_nonneg (X j a))
  _ = (∫⁻ (a : Ω), ENNReal.ofReal (rexp (-(X j a))) ∂μ) + ∫⁻ (a : Ω), ENNReal.ofReal (rexp ((X j a))) ∂μ := by
    rw [MeasureTheory.lintegral_add_left']
    refine AEMeasurable.ennreal_ofReal (Measurable.comp_aemeasurable' measurable_exp (AEMeasurable.neg q))
  _ ≤ ENNReal.ofReal (rexp (r ^ 2 / 2)) + ENNReal.ofReal (rexp (r ^ 2 / 2)) := by
    have p0 := p 1
    simp only [one_mul, one_pow] at p0
    have p1 := p (-1)
    simp only [neg_mul, one_mul, even_two, Even.neg_pow, one_pow] at p1
    apply add_le_add p1 p0
  _ < ⊤ := Batteries.compareOfLessAndEq_eq_lt.mp rfl

omit [IsProbabilityMeasure μ] in
private lemma measurable_expt' (X : Ω → ℝ) (t : ℝ) (hX : AEMeasurable X μ) :
    AEStronglyMeasurable (fun ω => rexp (t * (X ω))) μ :=
  aestronglyMeasurable_iff_aemeasurable.mpr <| measurable_exp.comp_aemeasurable' (hX.const_mul t)

omit [IsProbabilityMeasure μ] [DecidableEq ι] in
private theorem integrable_exp_of_subgaussian
  (X : ι → Ω → ℝ) (j : ι) (r : ℝ)
  (p : ∀ (t : ℝ), ∫⁻ (ω : Ω), ENNReal.ofReal (rexp (t * X j ω)) ∂μ ≤ ENNReal.ofReal (rexp (t ^ 2 * r ^ 2 / 2)))
  (t : ℝ) (q : AEMeasurable (X j) μ) :
  Integrable (fun x ↦ rexp (t * X j x)) μ := by
  constructor
  refine measurable_expt' μ (X j) t ?left.hX
  exact q
  dsimp [HasFiniteIntegral]
  rw [lintegral_congr (by intro a; rw [enorm_eq_ofReal_abs]; simp : ∀ a, ‖rexp (t * X j a)‖ₑ = ENNReal.ofReal (rexp (t * X j a)))]
  exact trans (p t) ENNReal.ofReal_lt_top



omit [IsProbabilityMeasure μ] [DecidableEq ι] in
private theorem Finset.aemeasurable_sup' {s : Finset ι} (hs : s.Nonempty) {f : ι → Ω → ℝ}
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (s.sup' hs f) μ  := by
  let p (x : Ω → ℝ) := AEMeasurable x μ
  change p (s.sup' hs f)
  apply Finset.sup'_induction
  intro a_1
  intro r
  intro a_2
  intro r0
  exact AEMeasurable.sup r r0
  exact hf


omit [DecidableEq ι] in
lemma maximal_inequality_finset (n : ℕ) (s : Finset ι) (n_car : s.card = n) (X : ι → Ω → ℝ)
    (r : ℝ) (n_pos : 1 < n) (r_pos : 0 < r) (H : s.Nonempty)
    (p : ∀ j ∈ s, ∀ t, ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (t * ((X j) ω))) ∂μ ≤
      ENNReal.ofReal (Real.exp (t ^ 2 * r ^ 2 / 2)))
    (q7 : ∀ j ∈ s, Measurable (X j)) :
    ∫ (ω : Ω), Finset.sup' s H (fun j => (X j) ω) ∂μ ≤ r * Real.sqrt (2 * Real.log n) := by
  subst n_car
  refine expected_max_subGaussian r_pos H n_pos (fun j hj => q7 j hj)
    (fun j hj => integrable_of_subgaussian μ X j r (p j hj) (q7 j hj).aemeasurable) ?_
    (fun j hj t => integrable_exp_of_subgaussian μ X j r (p j hj) t (q7 j hj).aemeasurable)
  intro j hj t
  have hint := integrable_exp_of_subgaussian μ X j r (p j hj) t (q7 j hj).aemeasurable
  have hmgf : mgf (X j) μ t ≤ Real.exp (t ^ 2 * r ^ 2 / 2) := by
    have h := p j hj t
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).1 h
  calc cgf (X j) μ t = Real.log (mgf (X j) μ t) := rfl
    _ ≤ Real.log (Real.exp (t ^ 2 * r ^ 2 / 2)) := Real.log_le_log (mgf_pos hint) hmgf
    _ = t ^ 2 * r ^ 2 / 2 := Real.log_exp _

omit [DecidableEq ι] in
lemma sup'_pow (s : Finset ι)
    (f : ι → ℝ) (hs) (hf : ∀ a ∈ s, 0 ≤ f a) :
    s.sup' hs f ^ 2 = s.sup' hs fun a ↦ f a ^ 2 := by
  have h_sup : ∀ a ∈ s, f a ≤ s.sup' hs f := fun a ha => Finset.le_sup' f ha
  have h_max : ∃ a ∈ s, s.sup' hs f = f a := Finset.exists_mem_eq_sup' hs f
  obtain ⟨a₀, ha₀, h_eq⟩ := h_max
  rw [h_eq]
  apply le_antisymm
  · -- (f a₀) ^ 2 ≤ s.sup' hs (fun a => f a ^ 2)
    rw [Finset.le_sup'_iff]
    use a₀, ha₀
  · -- s.sup' hs (fun a => f a ^ 2) ≤ (f a₀) ^ 2
    rw [Finset.sup'_le_iff]
    intro b hb
    have hb_nonneg : 0 ≤ f b := hf b hb
    have ha₀_nonneg : 0 ≤ f a₀ := hf a₀ ha₀
    have : f b ≤ f a₀ := by
      rw [← h_eq]
      exact h_sup b hb
    exact (sq_le_sq₀ (hf b hb) (hf a₀ ha₀)).mpr this

lemma maximal_inequality_supR'
  {ι ι' : Type*} [DecidableEq ι']
  (n : ℕ) (s : Finset ι) (s' : Finset ι') (hs' : s'.Nonempty)
  (n_car : s'.card = n)
  (X : ι' → Ω → ℝ)
  (Y : ι → ι' → Ω → ℝ)
  (r : ι → ι' → ℝ)
  (n_pos : 1 < n)
  (r_pos : ∃ j ∈ s', (∃ i ∈ s, r i j > 0))
  (y_pos : ∀ i ∈ s, ∀ j ∈ s', ∀ ω, Y i j ω ≤ r i j)
  (y_neg : ∀ i ∈ s, ∀ j ∈ s', ∀ ω, - r i j ≤ Y i j ω)
  (y_ave : ∀ i ∈ s, ∀ j ∈ s', ∫ ω, Y i j ω ∂μ = 0)
  (y_mea : ∀ i, ∀ j, Measurable (Y i j))
  (s_ind : ∀ j ∈ s', iIndepFun (fun i ↦ Y i j) μ)
  (xy : ∀ j ∈ s', (X j = ∑ i ∈ s, Y i j)) :
  let R : ι' → ℝ := fun j => Real.sqrt (∑ i ∈ s, (r i j) ^ 2)
  ∫ ω, Finset.sup' s' hs' (fun j => X j ω) ∂μ
    ≤ (Finset.sup' s' hs' R) * Real.sqrt (2 * Real.log n) := by
  intro r'
  have p1 : ∀ j ∈ s', ∀ (t : ℝ), ∫⁻ (ω : Ω), ENNReal.ofReal (rexp (t * X j ω)) ∂μ ≤ ENNReal.ofReal (rexp (t ^ 2 * s'.sup' hs' r' ^ 2 / 2)) := by
    intro j hj t
    have w : ∫⁻ (ω : Ω), ENNReal.ofReal (rexp (t * X j ω)) ∂μ = ENNReal.ofReal (∫ (ω : Ω), (rexp (t * X j ω)) ∂μ) := by
      refine Eq.symm (ofReal_integral_eq_lintegral_ofReal ?hfi ?f_nn)
      constructor
      refine measurable_expt' μ (X j) t ?hfi.left.hX
      · subst n_car
        simp_all only [gt_iff_lt]
        apply Finset.aemeasurable_sum
        intro i a
        apply Measurable.aemeasurable
        simp_all only
      dsimp [HasFiniteIntegral]
      have w : ∫⁻ (a : Ω), ↑‖rexp (t * X j a)‖₊ ∂μ < ⊤ := by
        calc
        _ ≤ ∫⁻ (a : Ω), ENNReal.ofReal (rexp (|t * X j a|)) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards
          intro a
          have w' : ↑‖rexp (t * X j a)‖₊ = ENNReal.ofReal (rexp (t * X j a)) := Real.enorm_eq_ofReal (exp_nonneg (t * X j a))
          rw [w']
          refine ENNReal.ofReal_le_ofReal ?h.h.h
          refine exp_le_exp.mpr ?h.h.h.a
          exact le_abs_self (t * X j a)
        _ ≤  ∫⁻ (a : Ω), ENNReal.ofReal (rexp |t * (∑ i ∈ s, r i j)|) ∂μ := by
          rw [xy]
          apply lintegral_mono
          · intro a
            simp
            apply ENNReal.ofReal_le_ofReal
            rw [exp_le_exp]
            rw [←abs_mul, abs_mul]
            apply mul_le_mul_of_nonneg_left
            · calc |∑ c ∈ s, Y c j a|
                ≤ ∑ c ∈ s, |Y c j a| := by exact Finset.abs_sum_le_sum_abs (fun i ↦ Y i j a) s
              _ ≤ ∑ c ∈ s, r c j := by
                  apply Finset.sum_le_sum
                  intro i hi
                  rw [abs_le]
                  constructor
                  · exact y_neg i hi j hj a
                  · exact y_pos i hi j hj a
              _ ≤ |∑ i ∈ s, r i j| := le_abs_self _
            · exact abs_nonneg t
          · exact hj

        _ < ⊤ := by
          refine lintegral_const_lt_top ?_
          exact ENNReal.ofReal_ne_top
      exact w
      filter_upwards
      intro a
      simp only [Pi.zero_apply]
      exact exp_nonneg (t * X j a)
    calc
    _ = ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (t * ((∑ i ∈ s, Y i j) ω))) ∂μ := by
      rw [xy j hj]
    _ = ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (∑ i ∈ s, t * Y i j ω)) ∂μ := by
      have q : ∀ ω : Ω, (t * (∑ i ∈ s, Y i j) ω) = (∑ i ∈ s, t * Y i j ω) := by
        intro ω
        calc
        _ = t * (∑ i ∈ s, Y i j ω) := by
          suffices (∑ i ∈ s, Y i j) ω = ∑ i ∈ s, Y i j ω from by
            rw [this]
          exact Finset.sum_apply ω s fun c ↦ Y c j
        _ = ∑ i ∈ s, t * Y i j ω := Finset.mul_sum s (fun i ↦ Y i j ω) t
      have q' : ∀ (ω : Ω), rexp (t * (∑ i ∈ s, Y i j) ω) = rexp (∑ i ∈ s, t * Y i j ω) := by
        intro ω
        have q0 := q ω
        rw [q0]
      apply lintegral_congr_ae
      filter_upwards with ω
      exact congrArg ENNReal.ofReal (q' ω)
    _ = ∫⁻ (ω : Ω), ENNReal.ofReal (∏ i ∈ s, Real.exp (t * Y i j ω)) ∂μ := by
      have q : ∀ ω : Ω, (rexp (∑ i ∈ s, t * Y i j ω) = ∏ i ∈ s, rexp (t * Y i j ω)) := by
        intro ω
        exact exp_sum s fun x ↦ t * Y x j ω
      apply lintegral_congr_ae
      filter_upwards with ω
      exact congrArg ENNReal.ofReal (q ω)
    _ = ∫⁻ (ω : Ω), ∏ i ∈ s, ENNReal.ofReal (Real.exp (t * Y i j ω)) ∂μ := by
      apply lintegral_congr
      intro a
      refine ENNReal.ofReal_prod_of_nonneg ?h.hf
      intro i hi
      exact exp_nonneg (t * Y i j a)
    _ = ∏ i ∈ s, ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (t * Y i j ω)) ∂μ := by
      apply ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun (s := s) (X := fun i ω ↦ ENNReal.ofReal (Real.exp (t * Y i j ω)))
      · change iIndepFun (fun i ↦ (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (t * x))) ∘ Y i j) μ
        refine ProbabilityTheory.iIndepFun.comp (s_ind j hj) ?_ ?_
        intro i
        refine Measurable.ennreal_ofReal ?_
        refine Continuous.borel_measurable ?_
        refine Continuous.rexp ?_
        exact continuous_const_mul t
      · intro i
        subst n_car
        simp_all only [gt_iff_lt, Finset.sum_apply]
        apply Measurable.coe_nnreal_ennreal
        apply Measurable.real_toNNReal
        apply Measurable.exp
        apply Measurable.const_mul
        simp_all only
    _ ≤ ∏ i ∈ s, ENNReal.ofReal (Real.exp (t ^ 2 * r i j ^ 2 / 2)) := by
      suffices ∀ i ∈ s, ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (t * Y i j ω)) ∂μ ≤ ENNReal.ofReal (Real.exp (t ^ 2 * r i j ^ 2 / 2)) from by
        exact Finset.prod_le_prod' this
      intro i hi
      have : t ^ 2 * r i j ^ 2 / 2 = t ^ 2 * (r i j - (- r i j)) ^ 2 / 8 := by
        simp
        grind
      rw [this]
      rw [<- MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
      apply ENNReal.ofReal_le_ofReal
      apply hoeffding
      · exact Measurable.aemeasurable (y_mea i j)
      · filter_upwards
        intro ω
        constructor
        · apply y_neg
          exact hi
          exact hj
        · apply y_pos
          exact hi
          exact hj
      · apply y_ave
        exact hi
        exact hj
      · constructor
        · subst n_car
          simp_all only [gt_iff_lt, Finset.sum_apply, sub_neg_eq_add]
          apply Measurable.aestronglyMeasurable
          apply Measurable.exp
          apply Measurable.const_mul
          simp_all only
        · by_cases ht : 0 ≤ t
          · apply MeasureTheory.HasFiniteIntegral.of_bounded
            filter_upwards with ω
            change ‖rexp (t * Y i j ω)‖ ≤ ‖rexp (t * r i j)‖
            refine norm_le_norm_of_abs_le_abs ?_
            simp
            exact mul_le_mul_of_nonneg_left (y_pos i hi j hj ω) ht
          · apply MeasureTheory.HasFiniteIntegral.of_bounded
            filter_upwards with ω
            change ‖rexp (t * Y i j ω)‖ ≤ ‖rexp (t * (-r i j))‖
            refine norm_le_norm_of_abs_le_abs ?_
            simp only [abs_exp, exp_le_exp]
            have ht' : t < 0 := not_le.mp ht
            exact mul_le_mul_of_nonpos_left (y_neg i hi j hj ω) (le_of_lt ht')
      · filter_upwards with ω
        apply exp_nonneg
    _ ≤ _ := by
      rw [<- ENNReal.ofReal_prod_of_nonneg]
      apply ENNReal.ofReal_le_ofReal
      have : ∏ i ∈ s, rexp (t ^ 2 * r i j ^ 2 / 2) = rexp (t ^ 2 * ∑ i ∈ s, (r i j ^ 2) / 2) := by
        rw [← exp_sum]
        congr 1
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
      rw [this]
      rw [exp_le_exp]
      have : ∑ i ∈ s, r i j ^ 2 ≤ s'.sup' hs' r' ^ 2 := by
        dsimp [r']
        have : (s'.sup' hs' fun j ↦ √(∑ i ∈ s, r i j ^ 2)) ^ 2 = (s'.sup' hs' fun j ↦ (∑ i ∈ s, r i j ^ 2)) := by
          rw [sup'_pow]
          apply congrArg
          ext j
          apply sq_sqrt
          apply Finset.sum_nonneg
          exact fun i a ↦ sq_nonneg (r i j)
          intro a ha
          simp
        rw [this]
        refine (Finset.le_sup'_iff hs').mpr ?_
        use j
      · rw [<- Finset.sum_div]
        rw [mul_div]
        rw [div_le_div_iff_of_pos_right]
        apply mul_le_mul_of_nonneg_left
        exact this
        exact sq_nonneg t
        simp
      · intro i hi
        apply exp_nonneg
  apply maximal_inequality_finset
  · exact n_car
  · exact n_pos
  · rw [Finset.lt_sup'_iff]
    dsimp [r']
    obtain ⟨b, ⟨hb1, hb2⟩⟩ := r_pos
    use b
    constructor
    · exact hb1
    · obtain ⟨c, ⟨hc1, hc2⟩⟩ := hb2
      apply Real.sqrt_pos.mpr
      apply Finset.sum_pos'
      · intro k hk
        apply sq_nonneg
      · use c
        constructor
        · exact hc1
        · exact sq_pos_of_pos hc2
  · intro j hj t
    apply p1
    exact hj
  · intro j hj
    rw [xy j hj]
    rw [show (∑ i ∈ s, Y i j) = fun ω => ∑ i ∈ s, Y i j ω from
      funext fun ω => Finset.sum_apply ω s (fun i => Y i j)]
    exact Finset.measurable_sum s fun i _ => y_mea i j

lemma maximal_inequality_supR
  {ι ι' : Type*} [DecidableEq ι']
  (n : ℕ) (s : Finset ι) (s' : Finset ι') (hs' : s'.Nonempty)
  (n_car : s'.card = n)
  (X : ι' → Ω → ℝ)
  (Y : ι → ι' → Ω → ℝ)
  (r : ι → ι' → ℝ)
  (y_pos : ∀ i ∈ s, ∀ j ∈ s', ∀ ω, Y i j ω ≤ r i j)
  (y_neg : ∀ i ∈ s, ∀ j ∈ s', ∀ ω, - r i j ≤ Y i j ω)
  (y_ave : ∀ i ∈ s, ∀ j ∈ s', ∫ ω, Y i j ω ∂μ = 0)
  (y_mea : ∀ i, ∀ j, Measurable (Y i j))
  (s_ind : ∀ j ∈ s', iIndepFun (fun i ↦ Y i j) μ)
  (xy : ∀ j ∈ s', (X j = ∑ i ∈ s, Y i j)) :
  let R : ι' → ℝ := fun j => Real.sqrt (∑ i ∈ s, (r i j) ^ 2)
  ∫ ω, Finset.sup' s' hs' (fun j => X j ω) ∂μ
    ≤ (Finset.sup' s' hs' R) * Real.sqrt (2 * Real.log n) := by
  by_cases hn : 1 < n
  case pos =>
    by_cases hr : ∃ j ∈ s', ∃ i ∈ s, r i j > 0
    case pos =>
      apply maximal_inequality_supR' μ n s s' hs' n_car X Y r hn hr y_pos y_neg y_ave y_mea s_ind xy
    case neg =>
      simp at hr
      intro R
      have hX0 : ∀ j ∈ s', ∀ (ω : Ω), X j = 0 := by
        have hX1 : ∀ i ∈ s, ∀ j ∈ s', r i j = 0 := by
          intros i hi j hj
          specialize hr j hj i hi
          have h_ge : 0 ≤ r i j := by
            have : Nonempty Ω := MeasureTheory.Measure.nonempty_of_neZero μ
            obtain ⟨ω⟩ := (inferInstance : Nonempty Ω)
            specialize y_pos i hi j hj ω
            specialize y_neg i hi j hj ω
            linarith
          linarith [hr, h_ge]
        have hX2 : ∀ i ∈ s, ∀ j ∈ s', Y i j = 0 := by
          intro i hi j hj
          ext ω
          have hr_eq := hX1 i hi j hj
          have h_pos := y_pos i hi j hj ω
          have h_neg := y_neg i hi j hj ω
          rw [hr_eq] at h_pos h_neg
          simp only [neg_zero] at h_neg
          simp only [Pi.zero_apply]
          linarith
        intro j hj ω
        have := xy j hj
        rw [this]
        apply Finset.sum_eq_zero
        intro i hi
        have := hX2 i hi j hj
        exact this
      calc
      (∫ (ω : Ω), Finset.sup' s' hs' (fun j => (X j) ω) ∂μ) = ∫ (ω : Ω), 0 ∂μ := by
        congr
        ext ω
        calc
        (s'.sup' hs' (fun j => X j ω)) = s'.sup' hs' (fun j => 0) := by
          apply Finset.sup'_congr
          · rfl
          · exact fun x a ↦ congrFun (hX0 x a ω) ω
        _ = 0 := by
          exact Finset.sup'_const hs' 0
      _ = 0 := by
        simp
      _ ≤ _ := by
        refine Right.mul_nonneg ?_ ?_
        · refine (Finset.le_sup'_iff hs').mpr ?_
          obtain ⟨b, hb⟩ := hs'
          use b, hb
          apply sqrt_nonneg
        · apply sqrt_nonneg
  case neg =>
    have hn' : n = 1 := by
      have : n ≠ 0 := by
        intro hn''
        have : s' = ∅ := by
          apply Finset.card_eq_zero.mp
          exact hn'' ▸ n_car
        exact Finset.not_nonempty_empty (this ▸ hs')
      grind
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (hn' ▸ n_car)
    intro r'
    calc
    (∫ (ω : Ω), Finset.sup' s' hs' (fun j => (X j) ω) ∂μ) = ∫ (ω : Ω), X j ω ∂μ := by
      congr
      ext ω
      calc
      _ = ({j} : Finset ι').sup' (hj ▸ hs') (fun j => X j ω) := by
        congr
      _ = _ := by
        apply Finset.sup'_singleton
    _ = ∑ i ∈ s, ∫ (ω : Ω), Y i j ω ∂μ := by
      rw [xy j (by grind)]
      have q : ∀ i ∈ s, Integrable (Y i j) μ := by
        intro i hi
        constructor
        . apply AEMeasurable.aestronglyMeasurable
          exact Measurable.aemeasurable (y_mea i j)
        . apply MeasureTheory.HasFiniteIntegral.of_bounded
          filter_upwards with ω
          exact abs_le.mpr ⟨y_neg i hi j (by grind) ω, y_pos i hi j (by grind) ω⟩
      convert MeasureTheory.integral_finsetSum s q
      simp
    _ = ∑ i ∈ s, 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact y_ave i hi j (by grind)
    _ = 0 := by simp
    _ ≤ _ := by
      refine Right.mul_nonneg ?_ ?_
      · refine (Finset.le_sup'_iff hs').mpr ?_
        dsimp [r']
        use j
        constructor
        · rw [hj]; simp
        · apply sqrt_nonneg
      · apply sqrt_nonneg

end ProbabilityTheory
