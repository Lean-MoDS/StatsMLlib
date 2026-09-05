/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import StatsMLlib.LearningTheory.FunctionClass.HilbertPredictor
import StatsMLlib.LearningTheory.Rademacher.Contraction

/-!
# A single normalized ReLU hidden unit

A hidden unit of a one-hidden-layer network is `x ↦ (⟪w, x⟫ + b)₊`.  The path norm of such
a network measures each unit through `‖(w, b / R)‖`, so the natural parameter is not the
pair `(w, b)` but the augmented vector `(w, b / R)`.  Pairing that vector with the
augmented input `(x, R)` recovers the affine map, and the normalization
`‖w‖² + b² / R² ≤ 1` becomes membership in the unit ball of `WithLp 2 (E × ℝ)`.

The reparametrization is what makes the Rademacher estimate a corollary of the
dimension-free Hilbert-predictor bound: no Cauchy-Schwarz, Jensen, or sign-orthogonality
computation is redone here.  The activation costs a factor `2`, the price of Lipschitz
contraction in the convention where `empiricalRademacherComplexity` takes an absolute value
inside the supremum.

## Main definitions

* `AugSpace`: the augmented space `E × ℝ` carrying the `L²` inner product.
* `augment`: an input of norm at most `R`, augmented by `R` in the new coordinate.
* `affineUnit`: an affine map on the input ball, indexed by the unit ball of `AugSpace`.
* `reluUnit`: the corresponding ReLU hidden unit.

## Main results

* `reluUnit_empiricalRademacherComplexity_le`: `Rhatₙ ≤ 2 √2 R / √n`, with no dependence on
  the dimension of the input space.
-/

noncomputable section

universe u

open Real

variable {n : ℕ}
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

namespace NeuralNetwork

/-- The augmented space `E × ℝ`, carrying the `L²` inner product.  A hidden unit
`x ↦ (⟪w, x⟫ + b)₊` is indexed by `(w, b / R)` here, which is the vector the path norm
measures. -/
abbrev AugSpace (E : Type u) : Type u := WithLp 2 (E × ℝ)

/-- An input of norm at most `R`, augmented by `R` in the new coordinate.  Pairing this
with `(w, b / R)` gives `⟪w, x⟫ + b`. -/
def augment (R : ℝ) (x : Metric.closedBall (0 : E) R) : AugSpace E :=
  WithLp.toLp 2 ((x : E), R)

omit [InnerProductSpace ℝ E] in
/-- The augmented input has norm at most `√2 R`. -/
lemma norm_augment_le (R : ℝ) (hR : 0 ≤ R) (x : Metric.closedBall (0 : E) R) :
    ‖augment R x‖ ≤ Real.sqrt 2 * R := by
  have hx : ‖(x : E)‖ ≤ R := mem_closedBall_zero_iff.mp x.2
  have hsq : ‖augment R x‖ ^ 2 = ‖(x : E)‖ ^ 2 + R ^ 2 := by
    have h := WithLp.prod_norm_sq_eq_of_L2 (augment R (E := E) x)
    simpa [augment, Real.norm_eq_abs, sq_abs] using h
  have hle : ‖augment R x‖ ^ 2 ≤ (Real.sqrt 2 * R) ^ 2 := by
    rw [hsq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [norm_nonneg (x : E)]
  calc ‖augment R x‖ = Real.sqrt (‖augment R x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt 2 * R) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt 2 * R := Real.sqrt_sq (by positivity)

/-- The affine part of a normalized hidden unit, as a function on the input ball. -/
def affineUnit (R : ℝ) (p : Metric.closedBall (0 : AugSpace E) 1)
    (x : Metric.closedBall (0 : E) R) : ℝ :=
  hilbertPredictor p (augment R x)

/-- A normalized ReLU hidden unit. -/
def reluUnit (R : ℝ) (p : Metric.closedBall (0 : AugSpace E) 1)
    (x : Metric.closedBall (0 : E) R) : ℝ :=
  max (affineUnit R p x) 0

/-- The affine unit is the affine map its name suggests: writing `p = (w, b / R)`, it is
`x ↦ ⟪w, x⟫ + b`. -/
lemma affineUnit_eq (R : ℝ) (p : Metric.closedBall (0 : AugSpace E) 1)
    (x : Metric.closedBall (0 : E) R) :
    affineUnit R p x = ⟪(p : AugSpace E).fst, (x : E)⟫ + R * (p : AugSpace E).snd := by
  simp [affineUnit, hilbertPredictor, augment, WithLp.prod_inner_apply]

/-- Cauchy-Schwarz on the augmented space. -/
lemma abs_affineUnit_le (R : ℝ) (hR : 0 ≤ R) (p : Metric.closedBall (0 : AugSpace E) 1)
    (x : Metric.closedBall (0 : E) R) :
    |affineUnit R p x| ≤ Real.sqrt 2 * R := by
  refine le_trans (abs_hilbertPredictor_le p (augment R x)) ?_
  simpa using norm_augment_le R hR x

/-- The activation does not increase the bound. -/
lemma abs_reluUnit_le (R : ℝ) (hR : 0 ≤ R) (p : Metric.closedBall (0 : AugSpace E) 1)
    (x : Metric.closedBall (0 : E) R) :
    |reluUnit R p x| ≤ Real.sqrt 2 * R := by
  refine le_trans ?_ (abs_affineUnit_le R hR p x)
  simpa [reluUnit] using abs_max_sub_max_le_abs (affineUnit R p x) 0 0

/--
The empirical Rademacher complexity of a single normalized ReLU hidden unit on inputs of
norm at most `R`:

`Rhatₙ ≤ 2 √2 R / √n`.

The factor `2` is the contraction constant for the activation and the factor `√2` comes
from the augmented input `(x, R)`, whose norm is `√(‖x‖² + R²)`.  The bound does not
involve the dimension of `E`.
-/
theorem reluUnit_empiricalRademacherComplexity_le
    (R : ℝ) (hR : 0 ≤ R) (S : Fin n → Metric.closedBall (0 : E) R) :
    empiricalRademacherComplexity n (reluUnit R) S ≤
      2 * Real.sqrt 2 * R / Real.sqrt (n : ℝ) := by
  have hne : Nonempty (Metric.closedBall (0 : AugSpace E) 1) :=
    (Metric.nonempty_closedBall.mpr zero_le_one).to_subtype
  have hb : (0 : ℝ) ≤ Real.sqrt 2 * R := by positivity
  have hcontract : empiricalRademacherComplexity n (reluUnit R) S ≤
      2 * 1 * empiricalRademacherComplexity n (affineUnit (E := E) R) S :=
    empiricalRademacherComplexity_contraction n (affineUnit (E := E) R)
      (fun _ u ↦ max u 0) S zero_le_one hb (abs_affineUnit_le R hR)
      (fun _ ↦ max_self 0) (fun _ u v ↦ by simpa using abs_max_sub_max_le_abs u v 0)
  have haffine : empiricalRademacherComplexity n (affineUnit (E := E) R) S =
      empiricalRademacherComplexity n
        (hilbertPredictor : Metric.closedBall (0 : AugSpace E) 1 → AugSpace E → ℝ)
        (augment R ∘ S) := by
    change empiricalRademacherComplexity n
        (fun p x ↦ hilbertPredictor p (augment R x)) S = _
    rw [empiricalRademacherComplexity_comp]
  have hhilbert : empiricalRademacherComplexity n
      (hilbertPredictor : Metric.closedBall (0 : AugSpace E) 1 → AugSpace E → ℝ)
      (augment R ∘ S) ≤ Real.sqrt 2 * R / Real.sqrt (n : ℝ) := by
    calc empiricalRademacherComplexity n
          (hilbertPredictor : Metric.closedBall (0 : AugSpace E) 1 → AugSpace E → ℝ)
          (augment R ∘ S)
        ≤ 1 * (n : ℝ)⁻¹ * Real.sqrt (∑ k : Fin n, ‖(augment R ∘ S) k‖ ^ 2) :=
          hilbertPredictor_empiricalRademacherComplexity_le 1 zero_le_one _
      _ ≤ 1 * (n : ℝ)⁻¹ * Real.sqrt (∑ _k : Fin n, (Real.sqrt 2 * R) ^ 2) := by
          gcongr with k
          exact norm_augment_le R hR (S k)
      _ = 1 * (n : ℝ)⁻¹ * Real.sqrt ((n : ℝ) * (Real.sqrt 2 * R) ^ 2) := by simp
      _ = 1 * (n : ℝ)⁻¹ * (Real.sqrt (n : ℝ) * (Real.sqrt 2 * R)) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hb]
      _ = Real.sqrt 2 * R / Real.sqrt (n : ℝ) := by
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn
            simp
          · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
            have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
            field_simp
            rw [Real.sq_sqrt hnR.le]
  calc empiricalRademacherComplexity n (reluUnit R) S
      ≤ 2 * 1 * empiricalRademacherComplexity n (affineUnit (E := E) R) S := hcontract
    _ = 2 * 1 * empiricalRademacherComplexity n
          (hilbertPredictor : Metric.closedBall (0 : AugSpace E) 1 → AugSpace E → ℝ)
          (augment R ∘ S) := by rw [haffine]
    _ ≤ 2 * 1 * (Real.sqrt 2 * R / Real.sqrt (n : ℝ)) := by gcongr
    _ = 2 * Real.sqrt 2 * R / Real.sqrt (n : ℝ) := by ring

/-! ## Examples

Worked uses of this module's public API. They are elaborated with the library, so they
double as acceptance tests that these statements stay usable as written.
-/

/-- A normalized ReLU hidden unit on the unit ball of any real inner-product space has
empirical Rademacher complexity at most `3 / √n` on every sample. -/
example (S : Fin n → Metric.closedBall (0 : E) 1) :
    empiricalRademacherComplexity n (reluUnit (E := E) 1) S ≤ 3 / Real.sqrt (n : ℝ) := by
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine (reluUnit_empiricalRademacherComplexity_le 1 zero_le_one S).trans ?_
  gcongr
  linarith

end NeuralNetwork

end
