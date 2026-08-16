/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
import StatsMLlib.LearningTheory.Rademacher.Massart
import StatsMLlib.LearningTheory.Rademacher.Signs
import StatsMLlib.Analysis.NormedSpace.CoveringNumber.L1
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rademacher Complexity of L1 Linear Predictors

The empirical Rademacher bound for L1-bounded predictors on Linfinity-bounded inputs.

## Main definitions

* `l1Norm`: compatibility view of StatsMLlib's canonical `l1norm`.
* `L1Ball`: subtype associated with StatsMLlib's canonical `l1Ball`.
* `LinftyBall`: subtype of inputs with bounded coordinate norm.

## Main results

* `linear_predictor_l1_bound'`: L1/Linfinity linear-predictor complexity bound.
* `linear_predictor_l1_bound`: public form of the same bound.
-/

universe v

open Real
open ProbabilityTheory
open scoped BigOperators ENNReal Classical

variable {ι : Type v} [Nonempty ι]
variable {d n : Nat}

-- Compatibility spelling for the canonical StatsMLlib ℓ1 norm.
noncomputable abbrev l1Norm (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  l1norm w

-- Subtype of the canonical StatsMLlib ℓ1 ball.
def L1Ball (W : ℝ) : Type :=
  ↥(l1Ball (d := d) W)

-- coordinatewise ℓ∞ bound type (|x_j| ≤ X∞)
def LinftyBall (X : ℝ) : Type :=
  { x : EuclideanSpace ℝ (Fin d) // ∀ j : Fin d, |x j| ≤ X }

-- sign as real
noncomputable def boolSign (b : Bool) : ℝ := if b then (1:ℝ) else (-1:ℝ)

lemma abs_boolSign (b : Bool) : |boolSign b| = 1 := by
  by_cases hb : b <;> simp [boolSign, hb]

-- signed coordinate function class: (j,b) ↦ sign(b) * x_j
noncomputable def coordSigned (jb : Fin d × Bool) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  boolSign jb.2 * x jb.1

-- restriction to a finite set via Massart's F_on (we take univ)
abbrev CoordIndex (d : Nat) :=
  { jb : Fin d × Bool // jb ∈ (Finset.univ : Finset (Fin d × Bool)) }

noncomputable def coordSignedOn (x : EuclideanSpace ℝ (Fin d)) :
    CoordIndex d → ℝ :=
  fun jb => coordSigned (d := d) jb.1 x

-- helper: |sum_j w_j z_j| ≤ (∑|w_j|)*M if |z_j|≤M
lemma abs_sum_mul_le_l1_mul {w z : EuclideanSpace ℝ (Fin d)} {M : ℝ}
    (hM : ∀ j : Fin d, |z j| ≤ M) :
    |∑ j : Fin d, w j * z j| ≤ (l1Norm (d := d) w) * M := by
  classical
  -- triangle
  have h1 :
      |∑ j : Fin d, w j * z j| ≤ ∑ j : Fin d, |w j * z j| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin d)))
        (f := fun j => w j * z j))
  -- bound each term
  have h2 :
      (∑ j : Fin d, |w j * z j|) ≤ ∑ j : Fin d, |w j| * M := by
    refine Finset.sum_le_sum (fun j _hj => ?_)
    calc
      |w j * z j| = |w j| * |z j| := by simp [abs_mul]
      _ ≤ |w j| * M := by
        exact mul_le_mul_of_nonneg_left (hM j) (abs_nonneg _)
  -- factor M
  have h3 :
      (∑ j : Fin d, |w j| * M) = (∑ j : Fin d, |w j|) * M := by
    simpa using
      (Finset.sum_mul (s := (Finset.univ : Finset (Fin d)))
        (f := fun j => |w j|) (a := M)).symm
  -- finish
  calc
    |∑ j : Fin d, w j * z j|
        ≤ ∑ j : Fin d, |w j * z j| := h1
    _ ≤ ∑ j : Fin d, |w j| * M := h2
    _ = (∑ j : Fin d, |w j|) * M := h3
    _ = (l1Norm (d := d) w) * M := rfl

/-
Main theorem: Lasso / ℓ1 bound
R_n ≤ X∞ * W * sqrt(2*log(2d)/n)
-/
theorem linear_predictor_l1_bound'
    (Xinf W : ℝ)
    (hX : 0 ≤ Xinf) (hW : 0 ≤ W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Y' : Fin n → LinftyBall (d := d) Xinf)
    (w' : ι → L1Ball (d := d) W) :
    empiricalRademacherComplexity n
      (fun i a => (∑ j : Fin d, (w' i).1 j * a j))
      (Subtype.val ∘ Y') ≤
      (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d)) := by
  classical

  -- (1) coordinate-signed class bound via Massart
  let : Nonempty (Fin d × Bool) := ⟨(⟨0, d_pos⟩, true)⟩
  have hs : (Finset.univ : Finset (Fin d × Bool)).Nonempty :=
    Finset.univ_nonempty

  -- bridge to pmf version
  have hbridge :
      empiricalRademacherComplexity_without_abs n
        (F_on (coordSigned (d := d)) (Finset.univ : Finset (Fin d × Bool)))
        (Subtype.val ∘ Y')
      =
      empiricalRademacherComplexity_pmf_without_abs n
        (F_on (coordSigned (d := d)) (Finset.univ : Finset (Fin d × Bool)))
        (Subtype.val ∘ Y') := by
    simpa using
      (empiricalRademacherComplexity_without_abs_eq_empiricalRademacherComplexity_pmf_without_abs
        (n := n)
        (f := F_on (coordSigned (d := d)) (Finset.univ : Finset (Fin d × Bool)))
        (S := (Subtype.val ∘ Y')))

  -- apply Massart
  have hmass :
      empiricalRademacherComplexity_pmf_without_abs n
        (F_on (coordSigned (d := d)) (Finset.univ : Finset (Fin d × Bool)))
        (Subtype.val ∘ Y')
      ≤
      (Finset.sup' (Finset.univ : Finset (Fin d × Bool)) hs
        (fun jb =>
          Real.sqrt (∑ i : Fin n,
            ((n : ℝ)⁻¹ * |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)|) ^ 2)))
      * Real.sqrt (2 * Real.log ((Finset.univ : Finset (Fin d × Bool)).card)) :=
    massart_lemma_pmf
      (F := coordSigned (d := d))
      (S := (Subtype.val ∘ Y'))
      (f := (Finset.univ : Finset (Fin d × Bool)))
      hs n_pos Xinf
      (by
        intro jb hj i
        -- |sign*x_j| ≤ X∞
        have hx := (Y' i).2 jb.1
        rw [show (Subtype.val ∘ Y') i = (Y' i).1 by rfl]
        simpa [coordSigned, abs_mul, abs_boolSign] using hx)
      hs

  -- (2) bound the sup term by X∞/sqrt(n)
  have hsup :
      (Finset.sup' (Finset.univ : Finset (Fin d × Bool)) hs
        (fun jb =>
          Real.sqrt (∑ i : Fin n,
            ((n : ℝ)⁻¹ * |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)|) ^ 2)))
      ≤ Xinf / Real.sqrt (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast n_pos
    have hconst_nonneg : 0 ≤ (n : ℝ)⁻¹ * Xinf := by
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt hnR)) hX
    have hsqrt_const :
        Real.sqrt ((n : ℝ) * (((n : ℝ)⁻¹ * Xinf) ^ 2)) = Xinf / Real.sqrt (n : ℝ) := by
      calc
        Real.sqrt ((n : ℝ) * (((n : ℝ)⁻¹ * Xinf) ^ 2))
            = Real.sqrt (n : ℝ) * Real.sqrt (((n : ℝ)⁻¹ * Xinf) ^ 2) := by
              rw [Real.sqrt_mul (le_of_lt hnR)]
        _ = Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * Xinf) := by
              simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hconst_nonneg]
        _ = Xinf / Real.sqrt (n : ℝ) := by
              have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt n_pos)
              have hsqrt0 : Real.sqrt (n : ℝ) ≠ 0 := by
                exact ne_of_gt (Real.sqrt_pos.2 hnR)
              have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
                simp ---[pow_two] using Real.sq_sqrt (le_of_lt hnR)
              field_simp [hn0, hsqrt0]
              rw [hsq]
    refine Finset.sup'_le
      (s := (Finset.univ : Finset (Fin d × Bool)))
      (H := hs)
      (f := fun jb =>
        Real.sqrt (∑ i : Fin n,
          ((n : ℝ)⁻¹ * |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)|) ^ 2))
      ?_
    intro jb hjb
    have hterm :
        ∀ i : Fin n,
          (((n : ℝ)⁻¹ * |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)|) ^ 2)
            ≤ (((n : ℝ)⁻¹ * Xinf) ^ 2) := by
      intro i
      have hxi : |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)| ≤ Xinf := by
        have hx := (Y' i).2 jb.1
        rw [show (Subtype.val ∘ Y') i = (Y' i).1 by rfl]
        simpa [coordSigned, abs_mul, abs_boolSign] using hx
      have hmuli :
          (n : ℝ)⁻¹ * |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)| ≤ (n : ℝ)⁻¹ * Xinf := by
        exact mul_le_mul_of_nonneg_left hxi (inv_nonneg.mpr (le_of_lt hnR))
      have hmuli_nonneg :
          0 ≤ (n : ℝ)⁻¹ * |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)| := by
        exact mul_nonneg (inv_nonneg.mpr (le_of_lt hnR)) (abs_nonneg _)
      nlinarith
    have hsum :
        (∑ i : Fin n, (((n : ℝ)⁻¹ * |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)|) ^ 2))
          ≤ ∑ i : Fin n, (((n : ℝ)⁻¹ * Xinf) ^ 2) := by
      exact Finset.sum_le_sum (fun i hi => hterm i)
    calc
      Real.sqrt (∑ i : Fin n, (((n : ℝ)⁻¹ * |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)|) ^ 2))
          ≤ Real.sqrt (∑ i : Fin n, (((n : ℝ)⁻¹ * Xinf) ^ 2)) := by
            exact Real.sqrt_le_sqrt hsum
      _ = Real.sqrt ((n : ℝ) * (((n : ℝ)⁻¹ * Xinf) ^ 2)) := by simp
      _ = Xinf / Real.sqrt (n : ℝ) := hsqrt_const

  -- log card = log(2d)
  have hcard : ((Finset.univ : Finset (Fin d × Bool)).card : ℝ) = 2 * d := by
    calc
      ((Finset.univ : Finset (Fin d × Bool)).card : ℝ) = (d : ℝ) * 2 := by simp
      _ = 2 * d := by ring

  have hcoord :
      empiricalRademacherComplexity_without_abs n
        (F_on (coordSigned (d := d)) (Finset.univ : Finset (Fin d × Bool)))
        (Subtype.val ∘ Y')
      ≤ (Xinf / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d)) := by
    have hmass' :
        empiricalRademacherComplexity_without_abs n
          (F_on (coordSigned (d := d)) (Finset.univ : Finset (Fin d × Bool)))
          (Subtype.val ∘ Y')
        ≤
        (Finset.sup' (Finset.univ : Finset (Fin d × Bool)) hs
          (fun jb =>
            Real.sqrt (∑ i : Fin n,
              ((n : ℝ)⁻¹ * |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)|) ^ 2)))
        * Real.sqrt (2 * Real.log (2 * d)) := by
      have htmp :
          empiricalRademacherComplexity_without_abs n
            (F_on (coordSigned (d := d)) (Finset.univ : Finset (Fin d × Bool)))
            (Subtype.val ∘ Y')
          ≤
          (Finset.sup' (Finset.univ : Finset (Fin d × Bool)) hs
            (fun jb =>
              Real.sqrt (∑ i : Fin n,
                ((n : ℝ)⁻¹ * |coordSigned (d := d) jb ((Subtype.val ∘ Y') i)|) ^ 2)))
          * Real.sqrt (2 * Real.log ((Finset.univ : Finset (Fin d × Bool)).card)) := by
        simpa [hbridge] using hmass
      simpa [hcard, mul_comm, mul_left_comm, mul_assoc] using htmp
    exact le_trans hmass' (mul_le_mul_of_nonneg_right hsup (Real.sqrt_nonneg _))

  -- (3) Duality: linear class ≤ W * coord class
  -- This part is standard: swap sums, apply abs_sum_mul_le_l1_mul, then l1≤W.
  -- In your repo, this is analogous to LinearPredictorL2.lean but with l1/l∞.
  have hdual :
      empiricalRademacherComplexity n
        (fun i a => (∑ j : Fin d, (w' i).1 j * a j))
        (Subtype.val ∘ Y')
      ≤
      W * empiricalRademacherComplexity_without_abs n
        (F_on (coordSigned (d := d)) (Finset.univ : Finset (Fin d × Bool)))
        (Subtype.val ∘ Y') := by
    let C : Signs n → ℝ :=
      fun σ =>
        ⨆ jb : { jb : Fin d × Bool // jb ∈ (Finset.univ : Finset (Fin d × Bool)) },
          (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * coordSigned (d := d) jb.1 ((Subtype.val ∘ Y') k)
    have hσBound :
        ∀ σ : Signs n,
          (⨆ i : ι,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              (∑ j : Fin d, (w' i).1 j * ((Subtype.val ∘ Y') k j))|)
          ≤ W * C σ := by
      intro σ
      let z : EuclideanSpace ℝ (Fin d) :=
        WithLp.toLp (2 : ENNReal)
          (fun j : Fin d => (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * ((Subtype.val ∘ Y') k j))
      have hbddC :
          BddAbove
            (Set.range
              (fun jb : { jb : Fin d × Bool // jb ∈ (Finset.univ : Finset (Fin d × Bool)) } =>
                (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
                  coordSigned (d := d) jb.1 ((Subtype.val ∘ Y') k))) := by
        exact (Set.toFinite _).bddAbove
      have hz_pos : ∀ j : Fin d, z j ≤ C σ := by
        intro j
        refine le_ciSup_of_le hbddC ⟨(j, true), by simp⟩ ?_
        simp [z, coordSigned, boolSign]
      have hz_neg : ∀ j : Fin d, -z j ≤ C σ := by
        intro j
        refine le_ciSup_of_le hbddC ⟨(j, false), by simp⟩ ?_
        simp [z, coordSigned, boolSign]
      have hz_abs : ∀ j : Fin d, |z j| ≤ C σ := by
        intro j
        exact abs_le.mpr ⟨by linarith [hz_neg j], hz_pos j⟩
      have hC_nonneg : 0 ≤ C σ := by
        let j0 : Fin d := ⟨0, d_pos⟩
        have hz0 := hz_abs j0
        exact le_trans (abs_nonneg (z j0)) hz0
      have hi :
          ∀ i : ι,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              (∑ j : Fin d, (w' i).1 j * ((Subtype.val ∘ Y') k j))|
            ≤ W * C σ := by
        intro i
        have hswap :
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              (∑ j : Fin d, (w' i).1 j * ((Subtype.val ∘ Y') k j))
            = ∑ j : Fin d, (w' i).1 j * z j := by
          calc
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
                (∑ j : Fin d, (w' i).1 j * ((Subtype.val ∘ Y') k j))
                = (n : ℝ)⁻¹ *
                    ∑ j : Fin d, (w' i).1 j *
                      (∑ k : Fin n, (σ k : ℝ) * ((Subtype.val ∘ Y') k j)) := by
                      apply congrArg (fun t => (n : ℝ)⁻¹ * t)
                      calc
                        ∑ k : Fin n, (σ k : ℝ) *
                            (∑ j : Fin d, (w' i).1 j * ((Subtype.val ∘ Y') k j))
                            = ∑ k : Fin n, ∑ j : Fin d,
                                (σ k : ℝ) * ((w' i).1 j * ((Subtype.val ∘ Y') k j)) := by
                                  simp [Finset.mul_sum]
                        _ = ∑ j : Fin d, ∑ k : Fin n,
                              (σ k : ℝ) * ((w' i).1 j * ((Subtype.val ∘ Y') k j)) := by
                                rw [Finset.sum_comm]
                        _ = ∑ j : Fin d, (w' i).1 j *
                              (∑ k : Fin n, (σ k : ℝ) * ((Subtype.val ∘ Y') k j)) := by
                                refine Finset.sum_congr rfl ?_
                                intro j hj
                                calc
                                  ∑ k : Fin n, (σ k : ℝ) * ((w' i).1 j * ((Subtype.val ∘ Y') k j))
                                      = ∑ k : Fin n, (w' i).1 j * ((σ k : ℝ) * ((Subtype.val ∘ Y') k j)) := by
                                          refine Finset.sum_congr rfl ?_
                                          intro k hk
                                          ring
                                  _ = (w' i).1 j * ∑ k : Fin n, (σ k : ℝ) * ((Subtype.val ∘ Y') k j) := by
                                        rw [Finset.mul_sum]
            _ = ∑ j : Fin d, (w' i).1 j * z j := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  simp [z]
                  ring
        calc
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              (∑ j : Fin d, (w' i).1 j * ((Subtype.val ∘ Y') k j))|
              = |∑ j : Fin d, (w' i).1 j * z j| := by rw [hswap]
          _ ≤ (l1Norm (d := d) ((w' i).1)) * C σ := by
                exact abs_sum_mul_le_l1_mul
                  (d := d) (w := (w' i).1) (z := z) (M := C σ) hz_abs
          _ ≤ W * C σ := by
                exact mul_le_mul_of_nonneg_right (w' i).2 hC_nonneg
      exact ciSup_le hi
    dsimp [empiricalRademacherComplexity, empiricalRademacherComplexity_without_abs]
    calc
      (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i : ι,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              (∑ j : Fin d, (w' i).1 j * ((Subtype.val ∘ Y') k j))|
        ≤ (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, W * C σ := by
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · exact Finset.sum_le_sum (fun σ hσ => hσBound σ)
            · positivity
      _ = (Fintype.card (Signs n) : ℝ)⁻¹ * (W * ∑ σ : Signs n, C σ) := by
            simp [Finset.mul_sum]
      _ = W * ((Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, C σ) := by ring
      _ = W * empiricalRademacherComplexity_without_abs n
            (F_on (coordSigned (d := d)) (Finset.univ : Finset (Fin d × Bool)))
            (Subtype.val ∘ Y') := by rfl
  calc
    empiricalRademacherComplexity n
      (fun i a => (∑ j : Fin d, (w' i).1 j * a j))
      (Subtype.val ∘ Y')
        ≤ W * empiricalRademacherComplexity_without_abs n
            (F_on (coordSigned (d := d)) (Finset.univ : Finset (Fin d × Bool)))
            (Subtype.val ∘ Y') := hdual
    _ ≤ W * ((Xinf / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d))) := by
      exact mul_le_mul_of_nonneg_left hcoord hW
    _ = (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d)) := by
      ring

/-- Empirical Rademacher bound for L1/Linfinity linear predictors. -/
theorem linear_predictor_l1_bound
    (d : ℕ)
    (Xinf W : ℝ)
    (hX : 0 ≤ Xinf) (hW : 0 ≤ W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Y' : Fin n → LinftyBall (d := d) Xinf)
    (w' : ι → L1Ball (d := d) W) :
    empiricalRademacherComplexity n
      (fun i a => ∑ j : Fin d, (w' i).1 j * a j)
      (Subtype.val ∘ Y') ≤
      (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d)) := by
  exact linear_predictor_l1_bound' (d := d) (n := n) (Xinf := Xinf) (W := W)
    hX hW d_pos n_pos Y' w'
