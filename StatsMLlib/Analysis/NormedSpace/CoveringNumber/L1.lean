/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import StatsMLlib.Topology.MetricSpace.CoveringNumber.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Covering Numbers of L1 Balls

We show the standard bound

  N(ε, B₁^d(R), ‖·‖₂) ≤ (2d+1)^{⌈R^2/ε^2⌉₊}.

## Main definitions

* `l1norm`, `l1Ball`: the coordinate L1 norm and its sublevel set.
* `l1Net`: the finite net constructed by Maurey's empirical method.

## Main results

* `coveringNumber_l1Ball_le`: covering-number bound for an L1 ball.
* `l1_peeling_inequality`: comparison of L1 and Euclidean norms after peeling coordinates.
-/

section L1Ball

open Finset BigOperators Real MeasureTheory ProbabilityTheory

variable {d : ℕ}

-- MeasurableSpace for Option (Fin d) using discrete sigma-algebra
instance instMeasurableSpaceOptionFin (d : ℕ) : MeasurableSpace (Option (Fin d)) := ⊤
instance instMeasurableSingletonClassOptionFin (d : ℕ) : MeasurableSingletonClass (Option (Fin d)) :=
  ⟨fun _ => trivial⟩

-- L1 norm on EuclideanSpace ℝ (Fin d)
def l1norm (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∑ i, ‖x i‖

def l1Ball (R : ℝ) : Set (EuclideanSpace ℝ (Fin d)) := {x | l1norm x ≤ R}

-- deterministic sign (+1 for nonnegative, -1 for negative)
noncomputable def sgn (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma abs_mul_sgn (x : ℝ) : |x| * sgn x = x := by
  by_cases hx : 0 ≤ x
  · simp [sgn, hx, abs_of_nonneg hx]
  · have hx' : x < 0 := lt_of_not_ge hx
    simp [sgn, hx, abs_of_neg hx']

lemma sgn_sq (x : ℝ) : sgn x ^ 2 = 1 := by
  by_cases hx : 0 ≤ x <;> simp [sgn, hx]

-- vector-valued random variable depending on θ
noncomputable def vecθ (θ : EuclideanSpace ℝ (Fin d)) (R : ℝ) : Option (Fin d) → EuclideanSpace ℝ (Fin d)
  | none => 0
  | some j => EuclideanSpace.single j (R * sgn (θ j))

-- base sign for the net
def sgnBool (b : Bool) : ℝ := if b then 1 else -1

noncomputable def vec (R : ℝ) : Option (Fin d × Bool) → EuclideanSpace ℝ (Fin d)
  | none => 0
  | some (j, b) => EuclideanSpace.single j (R * sgnBool b)

noncomputable def embed (θ : EuclideanSpace ℝ (Fin d)) : Option (Fin d) → Option (Fin d × Bool)
  | none => none
  | some j => some (j, decide (0 ≤ θ j))

lemma sgnBool_decide (x : ℝ) : sgnBool (decide (0 ≤ x)) = sgn x := by
  by_cases hx : 0 ≤ x <;> simp [sgnBool, sgn, hx]

lemma vec_embed (θ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (o : Option (Fin d)) :
    vec R (embed θ o) = vecθ θ R o := by
  cases o <;> simp [embed, vec, vecθ, sgnBool_decide]

noncomputable def avg (R : ℝ) (k : ℕ) (f : Fin k → Option (Fin d × Bool)) :
    EuclideanSpace ℝ (Fin d) :=
  (1 / (k : ℝ)) • ∑ i, vec R (f i)

noncomputable def avgθ (θ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (k : ℕ) (f : Fin k → Option (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (1 / (k : ℝ)) • ∑ i, vecθ θ R (f i)

lemma avg_embed (θ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (k : ℕ) (f : Fin k → Option (Fin d)) :
    avg R k (fun i => embed θ (f i)) = avgθ θ R k f := by
  simp [avg, avgθ, vec_embed]

-- Finite net built from all averages of k points in {0, ±R e_j}
noncomputable def l1Net (R : ℝ) (k : ℕ) : Finset (EuclideanSpace ℝ (Fin d)) := by
  classical
  exact (Finset.univ.image (avg R k))

lemma l1Net_card_le (R : ℝ) (k : ℕ) :
    (l1Net (d := d) R k).card ≤ (2 * d + 1) ^ k := by
  classical
  have hle : (l1Net (d := d) R k).card ≤
      (Finset.univ : Finset (Fin k → Option (Fin d × Bool))).card := by
    simpa [l1Net] using (Finset.card_image_le : (Finset.univ.image (avg R k)).card ≤ _)
  have hcardS : Fintype.card (Option (Fin d × Bool)) = 2 * d + 1 := by
    simp [Fintype.card_option, Fintype.card_prod, Fintype.card_bool,
      Nat.mul_comm, Nat.add_comm]
  -- card univ for function space
  have hcard_univ :
      (Finset.univ : Finset (Fin k → Option (Fin d × Bool))).card = (2 * d + 1) ^ k := by
    -- card_univ = card_fun
    simp [hcardS]
  simpa [hcard_univ] using hle

-- Probability distribution on Option (Fin d) based on θ
noncomputable def l1pmf (θ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (hθ : l1norm θ ≤ R) :
    PMF (Option (Fin d)) := by
  classical
  refine PMF.ofFintype (fun o : Option (Fin d) => ?_) ?_
  · cases o with
    | none => exact ENNReal.ofReal (1 - l1norm θ / R)
    | some j => exact ENNReal.ofReal (‖θ j‖ / R)
  · -- sum to 1
    -- split option sum
    have hl1nonneg : 0 ≤ l1norm θ := Finset.sum_nonneg (fun i _ => norm_nonneg (θ i))
    have hR : 0 ≤ R := le_trans hl1nonneg hθ
    have hpos : 0 ≤ l1norm θ / R := by
      by_cases hR0 : R = 0
      · simp [hR0]
      · have hRpos : 0 < R := lt_of_le_of_ne hR (fun h => hR0 h.symm)
        exact div_nonneg hl1nonneg (le_of_lt hRpos)
    have hle : l1norm θ / R ≤ 1 := by
      by_cases hR0 : R = 0
      · simp [hR0]
      · have hRpos : 0 < R := lt_of_le_of_ne hR (fun h => hR0 h.symm)
        exact (div_le_one hRpos).2 hθ
    have hnonneg : 0 ≤ 1 - l1norm θ / R := by linarith
    -- evaluate sum over Option using Fintype.sum_option
    rw [Fintype.sum_option]
    by_cases hR0 : R = 0
    · -- R = 0 case: l1norm θ = 0 so θ = 0
      have hl1zero : l1norm θ = 0 := by
        have : l1norm θ ≤ 0 := by simp only [hR0] at hθ; exact hθ
        linarith
      have hcoord_zero : ∀ j : Fin d, ‖θ j‖ = 0 := by
        intro j
        have hsum : ∑ i, ‖θ i‖ = 0 := hl1zero
        exact Finset.sum_eq_zero_iff_of_nonneg (fun i _ => norm_nonneg _) |>.1 hsum j (by simp)
      simp only [hR0, div_zero, ENNReal.ofReal_zero, Finset.sum_const_zero, add_zero,
        sub_zero, ENNReal.ofReal_one]
    · -- R > 0 case
      have hRpos : 0 < R := lt_of_le_of_ne hR (fun h => hR0 h.symm)
      -- Convert to real calculation
      have hsum_real : (1 - l1norm θ / R) + ∑ j, ‖θ j‖ / R = 1 := by
        have : ∑ j : Fin d, ‖θ j‖ / R = l1norm θ / R := by
          simp only [l1norm, Finset.sum_div]
        rw [this]
        ring
      -- Use ENNReal.ofReal properties
      have hcoord_le : ∀ j : Fin d, ‖θ j‖ / R ≤ 1 := fun j => by
        have hjle : ‖θ j‖ ≤ l1norm θ := by
          simp only [l1norm]
          exact Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ j)
        exact (div_le_one hRpos).2 (le_trans hjle hθ)
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg (norm_nonneg _) (le_of_lt hRpos))]
      rw [← ENNReal.ofReal_add hnonneg (Finset.sum_nonneg (fun j _ =>
        div_nonneg (norm_nonneg _) (le_of_lt hRpos)))]
      rw [hsum_real, ENNReal.ofReal_one]

-- expectation of coordinate for base pmf
lemma l1pmf_mean_coord (θ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R)
    (hθ : l1norm θ ≤ R) (j : Fin d) :
    ∫ o, (vecθ θ R o) j ∂(l1pmf θ R hθ).toMeasure = θ j := by
  classical
  -- integral as finite sum using PMF.integral_eq_sum
  rw [PMF.integral_eq_sum]
  -- Split sum over Option using Fintype.sum_option
  rw [Fintype.sum_option]
  -- The none term contributes 0
  simp only [vecθ, WithLp.ofLp_zero, Pi.zero_apply, smul_zero, zero_add]
  -- For EuclideanSpace, use single_apply and collapse the sum
  simp only [PiLp.single_apply, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq Finset.univ j (fun x => _ • (R * sgn (θ x)))]
  simp only [Finset.mem_univ, ite_true]
  -- Now simplify the PMF value and sign
  simp only [l1pmf, PMF.ofFintype_apply]
  have hnorm_nonneg : 0 ≤ ‖θ j‖ := norm_nonneg _
  have hpos : 0 ≤ ‖θ j‖ / R := div_nonneg hnorm_nonneg (le_of_lt hR)
  rw [ENNReal.toReal_ofReal hpos]
  -- Use sgn and norm relationship: |θ j| / R * (R * sgn(θ j)) = |θ j| * sgn(θ j) = θ j
  rw [Real.norm_eq_abs, smul_eq_mul]
  have hRne : R ≠ 0 := ne_of_gt hR
  field_simp
  rw [abs_mul_sgn]

lemma l1pmf_second_moment_coord (θ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R)
    (hθ : l1norm θ ≤ R) (j : Fin d) :
    ∫ o, ((vecθ θ R o) j) ^ 2 ∂(l1pmf θ R hθ).toMeasure = R * ‖θ j‖ := by
  classical
  -- compute by finite sum, only the j term contributes
  rw [PMF.integral_eq_sum]
  rw [Fintype.sum_option]
  -- The none term contributes 0^2 = 0
  simp only [vecθ, WithLp.ofLp_zero, Pi.zero_apply, sq]
  -- Handle EuclideanSpace.single_apply
  simp only [PiLp.single_apply, ite_mul, mul_ite, mul_zero, zero_mul, smul_ite, smul_zero]
  -- Simplify nested if with same condition
  have hsum_simp : ∀ x, (if j = x then (if j = x then ((l1pmf θ R hθ) (some x)).toReal •
      (R * sgn (θ x) * (R * sgn (θ x))) else 0) else 0) =
      (if j = x then ((l1pmf θ R hθ) (some x)).toReal • (R * sgn (θ x) * (R * sgn (θ x))) else 0) := by
    intro x; split_ifs <;> rfl
  simp only [hsum_simp]
  rw [Finset.sum_ite_eq Finset.univ j (fun x => _ • ((R * sgn (θ x)) * (R * sgn (θ x))))]
  simp only [Finset.mem_univ, ite_true]
  -- Simplify (R * sgn(θ j))^2 = R^2
  have hsgn_sq : (R * sgn (θ j)) * (R * sgn (θ j)) = R ^ 2 := by
    rw [← sq, mul_pow, sgn_sq, mul_one]
  rw [hsgn_sq]
  -- Simplify PMF value
  simp only [l1pmf, PMF.ofFintype_apply]
  have hnorm_nonneg : 0 ≤ ‖θ j‖ := norm_nonneg _
  have hpos : 0 ≤ ‖θ j‖ / R := div_nonneg hnorm_nonneg (le_of_lt hR)
  rw [ENNReal.toReal_ofReal hpos]
  rw [Real.norm_eq_abs, smul_eq_mul]
  field_simp
  ring

-- Main bound: existence of close average
lemma exists_avgθ_close (θ : EuclideanSpace ℝ (Fin d)) {R eps : ℝ} (hR : 0 < R)
    (hε : 0 < eps) (hθ : l1norm θ ≤ R) (k : ℕ) (hk : R ^ 2 ≤ (k : ℝ) * eps ^ 2) :
    ∃ f : Fin k → Option (Fin d), dist (avgθ θ R k f) θ ≤ eps := by
  classical
  -- build product measure of k independent samples
  let p := l1pmf θ R hθ
  let μ : Measure (Option (Fin d)) := p.toMeasure
  let ν : Measure (Fin k → Option (Fin d)) := Measure.pi (fun _ : Fin k => μ)
  have hprob : IsProbabilityMeasure ν := by
    infer_instance

  -- expected squared distance bound
  have hbound :
      ∫ ω, dist (avgθ θ R k ω) θ ^ 2 ∂ν ≤ R ^ 2 / (k : ℝ) := by
    -- Express dist² as sum of coordinate squared differences
    have hdist_eq : ∀ ω, dist (avgθ θ R k ω) θ ^ 2 =
        ∑ j, ((avgθ θ R k ω).ofLp j - θ.ofLp j) ^ 2 := by
      intro ω
      rw [PiLp.dist_sq_eq_of_L2]
      congr 1
      ext j
      rw [Real.dist_eq, sq_abs]
    simp_rw [hdist_eq]
    -- Push integral inside sum (finite sum)
    rw [MeasureTheory.integral_finsetSum Finset.univ]
    swap
    · intro j _
      exact Integrable.of_finite
    -- Now bound each coordinate's contribution
    -- The goal is: ∑ j, ∫ ω, ((avgθ θ R k ω).ofLp j - θ.ofLp j) ^ 2 ∂ν ≤ R² / k
    have hcoord_bound : ∀ j : Fin d,
        ∫ ω, ((avgθ θ R k ω).ofLp j - θ.ofLp j) ^ 2 ∂ν ≤ R * ‖θ j‖ / k := by
      intro j
      -- The average at coordinate j: (avgθ θ R k ω).ofLp j = (1/k) * ∑ᵢ (vecθ θ R (ω i)).ofLp j
      have havg_coord : ∀ ω, (avgθ θ R k ω).ofLp j = (k : ℝ)⁻¹ * ∑ i, (vecθ θ R (ω i)).ofLp j := by
        intro ω
        simp only [avgθ, one_div, PiLp.smul_apply, smul_eq_mul]
        congr 1
        simp only [WithLp.ofLp_sum, Finset.sum_apply]
      calc ∫ ω, ((avgθ θ R k ω).ofLp j - θ.ofLp j) ^ 2 ∂ν
          ≤ ∫ ω, ((avgθ θ R k ω).ofLp j - θ.ofLp j) ^ 2 ∂ν := le_refl _
        _ ≤ R * ‖θ j‖ / k := by
            -- Use that for product measure, the variance of sum equals sum of variances
            -- and bound each variance by R * |θ_j| / k
            by_cases hk0 : k = 0
            · -- k = 0 is impossible since R² ≤ k * ε² and R > 0
              exfalso
              simp only [hk0, Nat.cast_zero, zero_mul] at hk
              have : 0 < R ^ 2 := sq_pos_of_pos hR
              linarith
            · have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
              have h2mom := l1pmf_second_moment_coord θ hR hθ j
              have hmean := l1pmf_mean_coord θ hR hθ j
              have hsingle_var : ∫ o, ((vecθ θ R o).ofLp j - θ.ofLp j)^2 ∂μ ≤ R * ‖θ j‖ := by
                -- E[(X - θ_j)²] = E[X²] - 2θ_j·E[X] + θ_j² = E[X²] - θ_j²
                -- = R*|θ_j| - θ_j² ≤ R*|θ_j| (since θ_j² ≥ 0)
                have hexp_sq : ∫ o, ((vecθ θ R o).ofLp j)^2 ∂μ = R * ‖θ j‖ := h2mom
                have hexp : ∫ o, (vecθ θ R o).ofLp j ∂μ = θ.ofLp j := hmean
                -- Use E[(X-μ)²] = E[X²] - μ²
                have hvariance : ∫ o, ((vecθ θ R o).ofLp j - θ.ofLp j)^2 ∂μ =
                    ∫ o, ((vecθ θ R o).ofLp j)^2 ∂μ - (θ.ofLp j)^2 := by
                  calc ∫ o, ((vecθ θ R o).ofLp j - θ.ofLp j)^2 ∂μ
                      = ∫ o, ((vecθ θ R o).ofLp j)^2 - 2 * θ.ofLp j * (vecθ θ R o).ofLp j +
                          (θ.ofLp j)^2 ∂μ := by
                        congr 1; ext o; ring
                    _ = ∫ o, ((vecθ θ R o).ofLp j)^2 ∂μ -
                        2 * θ.ofLp j * ∫ o, (vecθ θ R o).ofLp j ∂μ +
                        ∫ o, (θ.ofLp j)^2 ∂μ := by
                        rw [MeasureTheory.integral_add]
                        rw [MeasureTheory.integral_sub]
                        rw [MeasureTheory.integral_const_mul]
                        all_goals exact Integrable.of_finite
                    _ = ∫ o, ((vecθ θ R o).ofLp j)^2 ∂μ -
                        2 * θ.ofLp j * θ.ofLp j + (θ.ofLp j)^2 := by
                        rw [hexp]
                        rw [MeasureTheory.integral_const]
                        -- μ = PMF.toMeasure, which is a probability measure
                        have hμprob : MeasureTheory.IsProbabilityMeasure μ := by
                          simp only [μ]
                          infer_instance
                        simp only [smul_eq_mul]
                        -- μ.real Set.univ = (μ Set.univ).toReal = 1.toReal = 1
                        have huniv : μ.real Set.univ = 1 := by
                          unfold Measure.real
                          rw [hμprob.measure_univ]
                          rfl
                        rw [huniv, one_mul]
                    _ = ∫ o, ((vecθ θ R o).ofLp j)^2 ∂μ - (θ.ofLp j)^2 := by ring
                rw [hvariance, hexp_sq]
                have hsq_nonneg : 0 ≤ (θ.ofLp j)^2 := sq_nonneg _
                linarith
              calc ∫ ω, ((avgθ θ R k ω).ofLp j - θ.ofLp j) ^ 2 ∂ν
                  ≤ (k : ℝ)⁻¹ * (∫ o, ((vecθ θ R o).ofLp j - θ.ofLp j)^2 ∂μ) := by
                    -- Define centered random variable
                    let Y := fun i (ω : Fin k → Option (Fin d)) => (vecθ θ R (ω i)).ofLp j - θ.ofLp j
                    have havg_Y : ∀ ω, (avgθ θ R k ω).ofLp j - θ.ofLp j = (↑k)⁻¹ * ∑ i, Y i ω := by
                      intro ω
                      rw [havg_coord]
                      simp only [Y]
                      have hsum_eq : ∑ x : Fin k, ((vecθ θ R (ω x)).ofLp j - θ.ofLp j) =
                          ∑ x : Fin k, (vecθ θ R (ω x)).ofLp j - ∑ _x : Fin k, θ.ofLp j := by
                        rw [Finset.sum_sub_distrib]
                      rw [hsum_eq]
                      have hconst : ∑ _x : Fin k, θ.ofLp j = k * θ.ofLp j := by
                        simp only [Finset.sum_const, Finset.card_fin]
                        rw [nsmul_eq_mul]
                      rw [hconst]
                      have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
                      field_simp
                    simp_rw [havg_Y]
                    have hsq_factor : ∀ ω, ((↑k)⁻¹ * ∑ i, Y i ω) ^ 2 = (↑k)⁻¹ ^ 2 * (∑ i, Y i ω) ^ 2 := by intro ω; ring
                    simp_rw [hsq_factor]
                    rw [integral_const_mul]
                    have hexpand_sq : ∀ ω, (∑ i, Y i ω) ^ 2 = ∑ i, ∑ l, Y i ω * Y l ω := by intro ω; rw [sq, Finset.sum_mul_sum]
                    simp_rw [hexpand_sq]
                    rw [integral_finsetSum]; swap; · intro i _; exact Integrable.of_finite
                    simp_rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
                    -- Establish independence of Y_i under ν using iIndepFun_pi
                    have hindep : ProbabilityTheory.iIndepFun (fun i (ω : Fin k → Option (Fin d)) => Y i ω) ν := by
                      simp only [Y]
                      have hμprob : ∀ _ : Fin k, IsProbabilityMeasure μ := fun _ => by simp only [μ]; infer_instance
                      -- First establish that coordinate projections are iIndepFun
                      let f : (i : Fin k) → Option (Fin d) → Option (Fin d) := fun _ => id
                      have hf_meas : ∀ i, AEMeasurable (f i) μ := fun _ => measurable_id.aemeasurable
                      have hid := @ProbabilityTheory.iIndepFun_pi (Fin k) _ (fun _ => Option (Fin d)) _
                        (fun _ => μ) hμprob (fun _ => Option (Fin d)) _ f hf_meas
                      simp only [f, id_eq] at hid
                      -- Now compose with the centering function
                      let g : (i : Fin k) → Option (Fin d) → ℝ := fun _ o => (vecθ θ R o).ofLp j - θ.ofLp j
                      have hg_meas : ∀ i, Measurable (g i) := fun _ => measurable_of_countable _
                      have hcomp := hid.comp g hg_meas
                      simp only [g] at hcomp
                      exact hcomp
                    -- Show each Y_i has mean 0
                    have hY_mean_zero : ∀ i, ∫ ω, Y i ω ∂ν = 0 := by
                      intro i; simp only [Y]
                      have hmeas : AEStronglyMeasurable (fun o : Option (Fin d) => (vecθ θ R o).ofLp j - θ.ofLp j) μ := by
                        exact Measurable.aestronglyMeasurable (measurable_of_countable _)
                      have heq := MeasureTheory.integral_comp_eval (μ := fun _ : Fin k => μ) (i := i) hmeas
                      simp only [μ, ν] at heq ⊢; rw [heq, integral_sub (Integrable.of_finite) (Integrable.of_finite), hmean, integral_const]
                      have hμprob : IsProbabilityMeasure ((l1pmf θ R hθ).toMeasure) := by infer_instance
                      unfold Measure.real
                      rw [hμprob.measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, sub_self]
                    -- Cross terms (i ≠ l) vanish due to independence and zero mean
                    have hcross : ∀ i l, i ≠ l → ∫ ω, Y i ω * Y l ω ∂ν = 0 := by
                      intro i l hil; have hpair := hindep.indepFun hil
                      have hmeas_i : AEStronglyMeasurable (Y i) ν := Measurable.aestronglyMeasurable (measurable_of_countable _)
                      have hmeas_l : AEStronglyMeasurable (Y l) ν := Measurable.aestronglyMeasurable (measurable_of_countable _)
                      rw [ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hpair hmeas_i hmeas_l, hY_mean_zero i, hY_mean_zero l, mul_zero]
                    -- Diagonal terms equal single-sample variance
                    have hdiag : ∀ i, ∫ ω, Y i ω * Y i ω ∂ν = ∫ o, ((vecθ θ R o).ofLp j - θ.ofLp j)^2 ∂μ := by
                      intro i; simp only [Y]
                      have hmeas : AEStronglyMeasurable (fun o : Option (Fin d) => ((vecθ θ R o).ofLp j - θ.ofLp j)^2) μ := by
                        exact Measurable.aestronglyMeasurable (measurable_of_countable _)
                      have heq := MeasureTheory.integral_comp_eval (μ := fun _ : Fin k => μ) (i := i) hmeas
                      simp only [μ, ν] at heq ⊢; convert heq using 2; ext ω; ring
                    -- Simplify sum: only diagonal terms survive
                    have hsum_eq : ∑ i : Fin k, ∑ l : Fin k, ∫ ω, Y i ω * Y l ω ∂ν = ∑ i : Fin k, ∫ o, ((vecθ θ R o).ofLp j - θ.ofLp j)^2 ∂μ := by
                      congr 1; ext i
                      rw [Finset.sum_eq_single (a := i)]
                      · exact hdiag i
                      · intro l _ hli; exact hcross i l (Ne.symm hli)
                      · intro hi; exact (hi (Finset.mem_univ i)).elim
                    rw [hsum_eq, Finset.sum_const, Finset.card_fin]
                    -- Now k⁻² * (k * ∫ ...) = k⁻¹ * ∫ ...
                    have halg : ((↑k)⁻¹ : ℝ) ^ 2 * (↑k * ∫ o, ((vecθ θ R o).ofLp j - θ.ofLp j)^2 ∂μ) =
                                (↑k)⁻¹ * ∫ o, ((vecθ θ R o).ofLp j - θ.ofLp j)^2 ∂μ := by
                      have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
                      field_simp
                    rw [nsmul_eq_mul, halg]
                _ ≤ (k : ℝ)⁻¹ * (R * ‖θ j‖) := by
                    apply mul_le_mul_of_nonneg_left hsingle_var (inv_nonneg.mpr (le_of_lt hkpos))
                _ = R * ‖θ j‖ / k := by rw [mul_comm, div_eq_mul_inv]
    -- Sum the coordinate bounds
    calc ∑ j, ∫ ω, ((avgθ θ R k ω).ofLp j - θ.ofLp j) ^ 2 ∂ν
        ≤ ∑ j, R * ‖θ j‖ / k := Finset.sum_le_sum (fun j _ => hcoord_bound j)
      _ = R / k * ∑ j, ‖θ j‖ := by rw [← Finset.sum_div, ← Finset.mul_sum]; ring
      _ = R / k * l1norm θ := by rfl
      _ ≤ R / k * R := by
          apply mul_le_mul_of_nonneg_left hθ
          by_cases hk0 : k = 0
          · simp [hk0]
          · exact div_nonneg (le_of_lt hR) (Nat.cast_nonneg k)
      _ = R ^ 2 / k := by ring
  -- apply first moment method
  have hint : Integrable (fun ω => dist (avgθ θ R k ω) θ ^ 2) ν := by
    -- finite space integrability
    have : Finite (Fin k → Option (Fin d)) := by
      infer_instance
    exact (Integrable.of_finite (μ := ν))
  obtain ⟨f, hf⟩ :=
    (MeasureTheory.exists_le_integral (μ := ν)
      (f := fun ω => dist (avgθ θ R k ω) θ ^ 2) hint)
  -- compare to eps^2
  have hk' : R ^ 2 / (k : ℝ) ≤ eps ^ 2 := by
    -- from hk
    have hk_rearranged : R ^ 2 ≤ eps ^ 2 * (k : ℝ) := by
      rw [mul_comm]; exact hk
    have hkpos : 0 < (k : ℝ) := by
      by_cases hk0 : k = 0
      · -- if k=0, then hk implies R=0, contradiction with hR
        exfalso
        have hR2 : R ^ 2 ≤ 0 := by
          have : R ^ 2 ≤ (k : ℝ) * eps ^ 2 := hk
          simp only [hk0, Nat.cast_zero, zero_mul] at this
          exact this
        have hRpos2 : 0 < R ^ 2 := sq_pos_of_pos hR
        linarith
      · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
    exact (div_le_iff₀ hkpos).2 hk_rearranged
  have hdist : dist (avgθ θ R k f) θ ^ 2 ≤ eps ^ 2 := by
    exact le_trans hf (le_trans hbound hk')
  have hdist' : dist (avgθ θ R k f) θ ≤ eps := by
    -- take square root
    have hnonneg : 0 ≤ dist (avgθ θ R k f) θ := dist_nonneg
    have hnonneg' : 0 ≤ eps := le_of_lt hε
    exact (sq_le_sq₀ hnonneg hnonneg').1 hdist
  exact ⟨f, hdist'⟩

-- Final covering number bound
theorem coveringNumber_l1Ball_le {R eps : ℝ} (hR : 0 ≤ R) (hε : 0 < eps) :
    coveringNumber eps (l1Ball (d := d) R) ≤ (2 * d + 1) ^ (⌈R ^ 2 / eps ^ 2⌉₊) := by
  classical
  -- handle R = 0 separately
  by_cases hR0 : R = 0
  · subst hR0
    -- l1Ball 0 = {0}
    have hnet : IsENet ({0} : Finset (EuclideanSpace ℝ (Fin d))) eps (l1Ball (d := d) 0) := by
      intro x hx
      have hxeq0 : x = 0 := by
        have hle : l1norm x ≤ 0 := hx
        have hnonneg : 0 ≤ l1norm x := Finset.sum_nonneg (fun i _ => norm_nonneg _)
        have hl1zero : l1norm x = 0 := le_antisymm hle hnonneg
        -- if l1norm x = 0, then x=0
        ext i
        have hcoord : ‖x i‖ = 0 := by
          have hsum : ∑ j, ‖x j‖ = 0 := hl1zero
          exact Finset.sum_eq_zero_iff_of_nonneg (fun j _ => norm_nonneg _) |>.1 hsum i (by simp)
        exact norm_eq_zero.1 hcoord
      subst hxeq0
      exact Set.mem_iUnion₂.mpr ⟨0, by simp, Metric.mem_closedBall_self (by linarith)⟩
    simpa using (coveringNumber_le_card hnet)
  · have hRpos : 0 < R := lt_of_le_of_ne hR (fun h => hR0 h.symm)
    set k : ℕ := ⌈R ^ 2 / eps ^ 2⌉₊ with hk
    -- build the net
    let N : Finset (EuclideanSpace ℝ (Fin d)) := l1Net (d := d) R k
    have hcard : (N.card : WithTop ℕ) ≤ (2 * d + 1) ^ k := by
      exact_mod_cast (l1Net_card_le (d := d) R k)
    -- show N is an eps-net
    have hnet : IsENet N eps (l1Ball (d := d) R) := by
      intro θ hθ
      -- choose f with avg close
      have hk' : R ^ 2 ≤ (k : ℝ) * eps ^ 2 := by
        -- from k = ceil
        have := Nat.le_ceil (R ^ 2 / eps ^ 2)
        -- rearrange
        have hk' : (R ^ 2 / eps ^ 2) ≤ k := by
          simpa [hk] using this
        have hk'' : R ^ 2 ≤ (k : ℝ) * eps ^ 2 := by
          have hε2 : 0 < eps ^ 2 := by nlinarith
          have := (div_le_iff₀ hε2).1 hk'
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        exact hk''
      obtain ⟨f, hf⟩ := exists_avgθ_close (θ := θ) (R := R) (eps := eps) hRpos hε hθ k hk'
      -- map to N using embed
      let g : Fin k → Option (Fin d × Bool) := fun i => embed θ (f i)
      have hmem : avg R k g ∈ N := by
        -- by definition of N
        have : avg R k g ∈ Finset.univ.image (avg R k) := by
          exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
        simp only [N, l1Net, this]
      -- conclude
      have hdist : dist θ (avg R k g) ≤ eps := by
        -- use avg_embed and dist_comm
        have heq : avg R k g = avgθ θ R k f := avg_embed θ R k f
        rw [heq, dist_comm]
        exact hf
      exact Set.mem_iUnion₂.mpr ⟨_, hmem, Metric.mem_closedBall.mpr hdist⟩
    -- finish with coveringNumber_le_card
    exact (coveringNumber_le_card hnet).trans hcard

/-!
## Peeling Inequality for ℓ₁-Balls

For θ in the ℓ₁-ball of radius 2R and τ > 0, we have:
  ‖θ‖₁ ≤ √(2R/τ + 1) · ‖θ‖₂ + 2R

This bounds the ℓ₁ norm in terms of the ℓ₂ norm via a "peeling" argument that
separates coordinates into those with large magnitude (> τ) and small magnitude (≤ τ).
-/

/-- The set of coordinates j where |θ j| > τ -/
noncomputable def largeCoords (θ : EuclideanSpace ℝ (Fin d)) (τ : ℝ) : Finset (Fin d) :=
  Finset.filter (fun j => τ < ‖θ j‖) Finset.univ

/-- The ℓ₁ norm decomposes as sum over large coordinates plus sum over small coordinates -/
lemma l1norm_eq_sum_large_add_small (θ : EuclideanSpace ℝ (Fin d)) (τ : ℝ) :
    l1norm θ = ∑ j ∈ largeCoords θ τ, ‖θ j‖ + ∑ j ∈ (largeCoords θ τ)ᶜ, ‖θ j‖ := by
  unfold l1norm largeCoords
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => τ < ‖θ j‖) (fun j => ‖θ j‖)]
  simp only [Finset.compl_filter]

/-- Sum over small coordinates is at most the full ℓ₁ norm -/
lemma sum_small_coords_le_l1norm (θ : EuclideanSpace ℝ (Fin d)) (τ : ℝ) :
    ∑ j ∈ (largeCoords θ τ)ᶜ, ‖θ j‖ ≤ l1norm θ := by
  unfold l1norm
  apply Finset.sum_le_univ_sum_of_nonneg
  intro x
  exact norm_nonneg _

/-- Sum over small coordinates is bounded by 2R when θ is in the ℓ₁-ball of radius 2R -/
lemma sum_small_coords_le (θ : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (R : ℝ)
    (hθ : l1norm θ ≤ 2 * R) :
    ∑ j ∈ (largeCoords θ τ)ᶜ, ‖θ j‖ ≤ 2 * R :=
  le_trans (sum_small_coords_le_l1norm θ τ) hθ

/-- Cauchy-Schwarz: sum of |θ j| over large coordinates is at most √|S| · ‖θ‖₂ -/
lemma sum_large_coords_le_sqrt_card_mul_norm (θ : EuclideanSpace ℝ (Fin d)) (τ : ℝ) :
    ∑ j ∈ largeCoords θ τ, ‖θ j‖ ≤ Real.sqrt (largeCoords θ τ).card * ‖θ‖ := by
  -- Apply Cauchy-Schwarz: ∑ 1·|θⱼ| ≤ √(∑ 1²) · √(∑ |θⱼ|²)
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (largeCoords θ τ) (fun _ => (1 : ℝ)) (fun j => ‖θ j‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  -- Now we need √(∑_{j∈S} ‖θ j‖²) ≤ ‖θ‖
  have hsub : ∑ j ∈ largeCoords θ τ, ‖θ j‖ ^ 2 ≤ ∑ j : Fin d, ‖θ j‖ ^ 2 := by
    apply Finset.sum_le_univ_sum_of_nonneg
    intro x
    exact sq_nonneg _
  have hnorm_sq : ‖θ‖ ^ 2 = ∑ j : Fin d, ‖θ j‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq θ]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  have hpart_le_whole : Real.sqrt (∑ j ∈ largeCoords θ τ, ‖θ j‖ ^ 2) ≤ ‖θ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg θ), hnorm_sq]
    apply Real.sqrt_le_sqrt
    exact hsub
  calc ∑ j ∈ largeCoords θ τ, ‖θ j‖
      ≤ Real.sqrt ↑(largeCoords θ τ).card * Real.sqrt (∑ j ∈ largeCoords θ τ, ‖θ j‖ ^ 2) := hCS
    _ ≤ Real.sqrt ↑(largeCoords θ τ).card * ‖θ‖ := by
        apply mul_le_mul_of_nonneg_left hpart_le_whole
        exact Real.sqrt_nonneg _

/-- Cardinality of large coordinates satisfies |S| · τ < 2R + τ -/
lemma largeCoords_card_mul_lt (θ : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (R : ℝ)
    (hτ : 0 < τ) (hθ : l1norm θ ≤ 2 * R) :
    (largeCoords θ τ).card * τ < 2 * R + τ := by
  have hsum_large : ∑ j ∈ largeCoords θ τ, τ ≤ ∑ j ∈ largeCoords θ τ, ‖θ j‖ := by
    apply Finset.sum_le_sum
    intro j hj
    simp only [largeCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact le_of_lt hj
  have hsum_large' : ∑ j ∈ largeCoords θ τ, ‖θ j‖ ≤ l1norm θ := by
    unfold l1norm
    apply Finset.sum_le_univ_sum_of_nonneg
    intro x
    exact norm_nonneg _
  have hcard_τ : (largeCoords θ τ).card * τ = ∑ j ∈ largeCoords θ τ, τ := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hcard_τ]
  calc ∑ j ∈ largeCoords θ τ, τ
      ≤ ∑ j ∈ largeCoords θ τ, ‖θ j‖ := hsum_large
    _ ≤ l1norm θ := hsum_large'
    _ ≤ 2 * R := hθ
    _ < 2 * R + τ := by linarith

/-- If |S| · τ < 2R + τ and τ > 0, then |S| < 2R/τ + 1 -/
lemma largeCoords_card_lt_div_add_one (θ : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (R : ℝ)
    (hτ : 0 < τ) (hθ : l1norm θ ≤ 2 * R) :
    ((largeCoords θ τ).card : ℝ) < 2 * R / τ + 1 := by
  have h := largeCoords_card_mul_lt θ τ R hτ hθ
  have hτpos : (0 : ℝ) < τ := hτ
  have h2 : (largeCoords θ τ).card * τ / τ < (2 * R + τ) / τ := by
    exact div_lt_div_of_pos_right h hτpos
  simp only [mul_div_assoc, div_self (ne_of_gt hτpos), mul_one] at h2
  have heq : (2 * R + τ) / τ = 2 * R / τ + 1 := by field_simp
  linarith

/-- Square root of cardinality bound: √|S| ≤ √(2R/τ + 1) -/
lemma sqrt_largeCoords_card_le (θ : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (R : ℝ)
    (hτ : 0 < τ) (hθ : l1norm θ ≤ 2 * R) :
    Real.sqrt (largeCoords θ τ).card ≤ Real.sqrt (2 * R / τ + 1) := by
  apply Real.sqrt_le_sqrt
  have h := largeCoords_card_lt_div_add_one θ τ R hτ hθ
  linarith

/-- Peeling inequality: for θ in B₁(2R) and τ > 0,
    ‖θ‖₁ ≤ √(2R/τ + 1) · ‖θ‖₂ + 2R -/
theorem l1_peeling_inequality (θ : EuclideanSpace ℝ (Fin d)) (τ R : ℝ)
    (hτ : 0 < τ) (hθ : l1norm θ ≤ 2 * R) :
    l1norm θ ≤ Real.sqrt (2 * R / τ + 1) * ‖θ‖ + 2 * R := by
  rw [l1norm_eq_sum_large_add_small θ τ]
  have h1 : ∑ j ∈ largeCoords θ τ, ‖θ j‖ ≤ Real.sqrt (2 * R / τ + 1) * ‖θ‖ := by
    calc ∑ j ∈ largeCoords θ τ, ‖θ j‖
        ≤ Real.sqrt (largeCoords θ τ).card * ‖θ‖ := sum_large_coords_le_sqrt_card_mul_norm θ τ
      _ ≤ Real.sqrt (2 * R / τ + 1) * ‖θ‖ := by
          apply mul_le_mul_of_nonneg_right
          · exact sqrt_largeCoords_card_le θ τ R hτ hθ
          · exact norm_nonneg θ
  have h2 : ∑ j ∈ (largeCoords θ τ)ᶜ, ‖θ j‖ ≤ 2 * R := sum_small_coords_le θ τ R hθ
  linarith

/-- √(a + b) ≤ √a + √b for non-negative a, b -/
lemma sqrt_add_le_peeling {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsum_nonneg : 0 ≤ Real.sqrt a + Real.sqrt b := by
    apply add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  rw [← Real.sqrt_sq hsum_nonneg]
  apply Real.sqrt_le_sqrt
  ring_nf
  have h1 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have h2 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
  have h3 : 0 ≤ 2 * Real.sqrt a * Real.sqrt b := by
    apply mul_nonneg
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg a)
    exact Real.sqrt_nonneg b
  linarith

/-- Alternative form of peeling inequality using τ^(-1/2) notation -/
theorem l1_peeling_inequality' (θ : EuclideanSpace ℝ (Fin d)) (τ R : ℝ)
    (hτ : 0 < τ) (hR : 0 ≤ R) (hθ : l1norm θ ≤ 2 * R) :
    l1norm θ ≤ Real.sqrt (2 * R) * τ ^ (-(1:ℝ)/2) * ‖θ‖ + ‖θ‖ + 2 * R := by
  have h := l1_peeling_inequality θ τ R hτ hθ
  -- We have √(2R/τ + 1) ≤ √(2R/τ) + 1 = √(2R) · τ^(-1/2) + 1
  have hsplit : Real.sqrt (2 * R / τ + 1) ≤ Real.sqrt (2 * R / τ) + 1 := by
    have h1 : 0 ≤ 2 * R / τ := by positivity
    have h2 : Real.sqrt (2 * R / τ + 1) ≤ Real.sqrt (2 * R / τ) + Real.sqrt 1 := by
      exact sqrt_add_le_peeling h1 (by norm_num : (0:ℝ) ≤ 1)
    simp at h2
    exact h2
  have hrewrite : Real.sqrt (2 * R / τ) = Real.sqrt (2 * R) * τ ^ (-(1:ℝ)/2) := by
    rw [Real.sqrt_div' (2 * R) (le_of_lt hτ)]
    rw [div_eq_mul_inv]
    congr 1
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_neg (le_of_lt hτ)]
    norm_num
  calc l1norm θ
      ≤ Real.sqrt (2 * R / τ + 1) * ‖θ‖ + 2 * R := h
    _ ≤ (Real.sqrt (2 * R / τ) + 1) * ‖θ‖ + 2 * R := by gcongr
    _ = Real.sqrt (2 * R / τ) * ‖θ‖ + ‖θ‖ + 2 * R := by ring
    _ = Real.sqrt (2 * R) * τ ^ (-(1:ℝ)/2) * ‖θ‖ + ‖θ‖ + 2 * R := by rw [hrewrite]

end L1Ball
