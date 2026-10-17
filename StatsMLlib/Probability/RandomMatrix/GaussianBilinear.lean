/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Algebra.Order.Group.CompleteLattice
import StatsMLlib.Probability.Gaussian.GordonProcess
import StatsMLlib.Probability.Gaussian.NormMoment

/-!
# Gaussian comparison for the bilinear process of a Gaussian matrix

Let `W` be an `m × n` matrix with independent standard Gaussian entries, realized as
`Matrix.ofEuclidean w` for `w` distributed according to `stdGaussian (EuclideanSpace ℝ (m × n))`.
This file compares the bilinear Gaussian process `Z (u, v) = ⟪u, W v⟫` with the decoupled
process `⟪g, u⟫ + ⟪h, v⟫` built from independent standard Gaussian vectors `g` and `h`:

* the Sudakov–Fernique inequality (Chevet's inequality): if the `u` are unit vectors and
  `‖v‖ ≤ R`, then `𝔼 sup_{u, v} ⟪u, W v⟫ ≤ R 𝔼 sup_u ⟪u, g⟫ + 𝔼 sup_v ⟪v, h⟫`;
* Gordon's inequality: if the `u` and the `v` are unit vectors, then
  `𝔼 sup_u ⟪u, g⟫ + 𝔼 inf_v ⟪v, h⟫ ≤ 𝔼 inf_v sup_u ⟪u, W v⟫`.

All processes are realized as linear functionals `x ↦ ⟪c, x⟫` of a single standard Gaussian
vector: the decoupled process lives on `EuclideanSpace ℝ (m ⊕ n)`, whose two blocks are
independent standard Gaussian vectors, and the bilinear process is `⟪u ⊗ v, w⟫` with the
Kronecker product `u ⊗ v`. The covariances are then inner products of coefficient vectors.
For Gordon's inequality, an independent standard Gaussian variable is added to the bilinear
process to equalize variances; it is removed again since it does not depend on the indices.

## Main results

* `ProbabilityTheory.integral_iSup_inner_ofEuclidean_le`: Chevet's inequality for a Gaussian
  matrix.
* `ProbabilityTheory.integral_l2_opNorm_ofEuclidean_mul_le`:
  `𝔼 ‖W A‖ ≤ ‖A‖ √m + ‖A‖_F`.
* `ProbabilityTheory.integral_add_integral_iInf_le_integral_iInf_iSup_inner_ofEuclidean`:
  Gordon's inequality for a Gaussian matrix.
* `ProbabilityTheory.integral_norm_sub_integral_norm_le_integral_minSingularValue`:
  `𝔼 ‖g‖ - 𝔼 ‖h‖ ≤ 𝔼 σ_min(W)`.
-/

open MeasureTheory Metric Matrix
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

noncomputable section

/-! ### Block decomposition and Kronecker products of Euclidean vectors -/

namespace EuclideanSpace

section Blocks

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The two blocks of a vector of `EuclideanSpace ℝ (α ⊕ β)`. -/
def blocks (x : EuclideanSpace ℝ (α ⊕ β)) : EuclideanSpace ℝ α × EuclideanSpace ℝ β :=
  (WithLp.toLp 2 fun i ↦ x (Sum.inl i), WithLp.toLp 2 fun j ↦ x (Sum.inr j))

/-- The vector of `EuclideanSpace ℝ (α ⊕ β)` with blocks `a` and `b`. -/
def sumElim (a : EuclideanSpace ℝ α) (b : EuclideanSpace ℝ β) : EuclideanSpace ℝ (α ⊕ β) :=
  WithLp.toLp 2 (Sum.elim a b)

omit [Fintype α] [Fintype β] in
lemma continuous_blocks : Continuous (blocks : EuclideanSpace ℝ (α ⊕ β) → _) := by
  unfold blocks
  fun_prop

lemma inner_sumElim (a : EuclideanSpace ℝ α) (b : EuclideanSpace ℝ β)
    (x : EuclideanSpace ℝ (α ⊕ β)) :
    ⟪sumElim a b, x⟫ = ⟪a, (blocks x).1⟫ + ⟪b, (blocks x).2⟫ := by
  simp [sumElim, blocks, PiLp.inner_apply, Fintype.sum_sum_type]

omit [Fintype α] [Fintype β] in
@[simp]
lemma blocks_sumElim (a : EuclideanSpace ℝ α) (b : EuclideanSpace ℝ β) :
    blocks (sumElim a b) = (a, b) :=
  rfl

lemma inner_sumElim_sumElim (a a' : EuclideanSpace ℝ α) (b b' : EuclideanSpace ℝ β) :
    ⟪sumElim a b, sumElim a' b'⟫ = ⟪a, a'⟫ + ⟪b, b'⟫ := by
  rw [inner_sumElim, blocks_sumElim]

lemma norm_sumElim_le (a : EuclideanSpace ℝ α) (b : EuclideanSpace ℝ β) :
    ‖sumElim a b‖ ≤ ‖a‖ + ‖b‖ := by
  have h : ‖sumElim a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    simp only [← real_inner_self_eq_norm_sq, inner_sumElim_sumElim]
  exact abs_le_of_sq_le_sq' (by nlinarith [norm_nonneg a, norm_nonneg b])
    (by positivity) |>.2

end Blocks

section Kronecker

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The Kronecker product `u ⊗ v` of two Euclidean vectors, with entries `u i * v j`. -/
def kronecker (u : EuclideanSpace ℝ m) (v : EuclideanSpace ℝ n) : EuclideanSpace ℝ (m × n) :=
  WithLp.toLp 2 fun p ↦ u p.1 * v p.2

lemma inner_kronecker_kronecker (u u' : EuclideanSpace ℝ m) (v v' : EuclideanSpace ℝ n) :
    ⟪kronecker u v, kronecker u' v'⟫ = ⟪u, u'⟫ * ⟪v, v'⟫ := by
  simp only [kronecker, PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma norm_kronecker (u : EuclideanSpace ℝ m) (v : EuclideanSpace ℝ n) :
    ‖kronecker u v‖ = ‖u‖ * ‖v‖ := by
  have h : ‖kronecker u v‖ ^ 2 = (‖u‖ * ‖v‖) ^ 2 := by
    rw [mul_pow]
    simp only [← real_inner_self_eq_norm_sq, inner_kronecker_kronecker]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

variable [DecidableEq n]

lemma inner_kronecker (u : EuclideanSpace ℝ m) (v : EuclideanSpace ℝ n)
    (w : EuclideanSpace ℝ (m × n)) :
    ⟪kronecker u v, w⟫ = ⟪u, (ofEuclidean w).toEuclideanLin v⟫ := by
  simp only [kronecker, PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
    conj_trivial, toLpLin_apply, mulVec, dotProduct, ofEuclidean_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

end Kronecker

end EuclideanSpace

namespace ProbabilityTheory

open EuclideanSpace

/-! ### The law of the blocks of a standard Gaussian vector -/

section Law

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The two blocks of a standard Gaussian vector of `EuclideanSpace ℝ (α ⊕ β)` are independent
standard Gaussian vectors. -/
lemma map_blocks_stdGaussian :
    (stdGaussian (EuclideanSpace ℝ (α ⊕ β))).map blocks =
      (stdGaussian (EuclideanSpace ℝ α)).prod (stdGaussian (EuclideanSpace ℝ β)) := by
  have h := (measurePreserving_sumPiEquivProdPi (fun _ : α ⊕ β ↦ gaussianReal 0 1)).map_eq
  rw [← map_pi_eq_stdGaussian (ι := α ⊕ β), ← map_pi_eq_stdGaussian (ι := α),
    ← map_pi_eq_stdGaussian (ι := β), Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), ← h,
    Measure.map_map continuous_blocks.measurable (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The expectation of a sum of functions of the two blocks of a standard Gaussian vector. -/
lemma integral_blocks_add {F : EuclideanSpace ℝ α → ℝ} {G : EuclideanSpace ℝ β → ℝ}
    (hF : Integrable F (stdGaussian _)) (hG : Integrable G (stdGaussian _)) :
    ∫ x, F (blocks x).1 + G (blocks x).2 ∂stdGaussian (EuclideanSpace ℝ (α ⊕ β)) =
      ∫ y, F y ∂stdGaussian _ + ∫ z, G z ∂stdGaussian _ := by
  have hFG := (hF.comp_fst (stdGaussian (EuclideanSpace ℝ β))).add
    (hG.comp_snd (stdGaussian (EuclideanSpace ℝ α)))
  rw [← integral_map (f := fun p ↦ F p.1 + G p.2) continuous_blocks.aemeasurable
    (by rw [map_blocks_stdGaussian]; exact hFG.aestronglyMeasurable), map_blocks_stdGaussian,
    integral_add (hF.comp_fst _) (hG.comp_snd _), integral_fun_fst, integral_fun_snd]
  simp

end Law

/-! ### Suprema of families of linear functionals -/

section Suprema

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι κ : Type*} {K : ℝ}

lemma abs_inner_le_of_norm_le {c : E} (hc : ‖c‖ ≤ K) (x : E) : |⟪c, x⟫| ≤ K * ‖x‖ :=
  (abs_real_inner_le_norm c x).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg x))

lemma bddAbove_range_inner_of_norm_le {c : ι → E} (hc : ∀ i, ‖c i‖ ≤ K) (x : E) :
    BddAbove (Set.range fun i ↦ ⟪c i, x⟫) :=
  ⟨K * ‖x‖, by
    rintro _ ⟨i, rfl⟩
    exact (le_abs_self _).trans (abs_inner_le_of_norm_le (hc i) x)⟩

lemma abs_iSup_inner_le [Nonempty ι] {c : ι → E} (hc : ∀ i, ‖c i‖ ≤ K) (x : E) :
    |⨆ i, ⟪c i, x⟫| ≤ K * ‖x‖ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine abs_le.2 ⟨?_, ciSup_le fun j ↦ (abs_le.1 (abs_inner_le_of_norm_le (hc j) x)).2⟩
  exact (abs_le.1 (abs_inner_le_of_norm_le (hc i) x)).1.trans
    (le_ciSup (bddAbove_range_inner_of_norm_le hc x) i)

lemma lipschitzWith_iSup_inner [Nonempty ι] {c : ι → E} {L : NNReal} (hc : ∀ i, ‖c i‖ ≤ L) :
    LipschitzWith L fun x ↦ ⨆ i, ⟪c i, x⟫ := by
  refine LipschitzWith.of_le_add_mul L fun x y ↦ ciSup_le fun i ↦ ?_
  have h : ⟪c i, x⟫ ≤ ⟪c i, y⟫ + L * dist x y := by
    have := (le_abs_self _).trans (abs_inner_le_of_norm_le (hc i) (x - y))
    rw [inner_sub_right, ← dist_eq_norm] at this
    linarith
  exact h.trans (by gcongr; exact le_ciSup (bddAbove_range_inner_of_norm_le hc y) i)

lemma continuous_iSup_inner [Nonempty ι] {c : ι → E} (hc : ∀ i, ‖c i‖ ≤ K) :
    Continuous fun x ↦ ⨆ i, ⟪c i, x⟫ :=
  (lipschitzWith_iSup_inner (L := K.toNNReal)
    fun i ↦ (hc i).trans (Real.le_coe_toNNReal K)).continuous

lemma bddBelow_range_iSup_inner [Nonempty ι] {c : κ → ι → E} (hc : ∀ s t, ‖c s t‖ ≤ K)
    (x : E) : BddBelow (Set.range fun s ↦ ⨆ t, ⟪c s t, x⟫) :=
  ⟨-(K * ‖x‖), by
    rintro _ ⟨s, rfl⟩
    exact (abs_le.1 (abs_iSup_inner_le (hc s) x)).1⟩

lemma abs_iInf_iSup_inner_le [Nonempty κ] [Nonempty ι] {c : κ → ι → E}
    (hc : ∀ s t, ‖c s t‖ ≤ K) (x : E) : |⨅ s, ⨆ t, ⟪c s t, x⟫| ≤ K * ‖x‖ := by
  obtain ⟨s⟩ := ‹Nonempty κ›
  refine abs_le.2 ⟨le_ciInf fun s' ↦ (abs_le.1 (abs_iSup_inner_le (hc s') x)).1, ?_⟩
  exact (ciInf_le (bddBelow_range_iSup_inner hc x) s).trans
    (abs_le.1 (abs_iSup_inner_le (hc s) x)).2

lemma lipschitzWith_iInf_iSup_inner [Nonempty κ] [Nonempty ι] {c : κ → ι → E} {L : NNReal}
    (hc : ∀ s t, ‖c s t‖ ≤ L) : LipschitzWith L fun x ↦ ⨅ s, ⨆ t, ⟪c s t, x⟫ := by
  refine LipschitzWith.of_le_add_mul L fun x y ↦ ?_
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun s ↦ ?_
  rw [sub_le_iff_le_add]
  exact (ciInf_le (bddBelow_range_iSup_inner hc x) s).trans
    ((lipschitzWith_iSup_inner (hc s)).le_add_mul x y)

lemma continuous_iInf_iSup_inner [Nonempty κ] [Nonempty ι] {c : κ → ι → E}
    (hc : ∀ s t, ‖c s t‖ ≤ K) : Continuous fun x ↦ ⨅ s, ⨆ t, ⟪c s t, x⟫ :=
  (lipschitzWith_iInf_iSup_inner (L := K.toNNReal)
    fun s t ↦ (hc s t).trans (Real.le_coe_toNNReal K)).continuous

/-- The supremum of a sum of functions of separate indices. -/
lemma iSup_prod_add [Nonempty ι] [Nonempty κ] {f : ι → ℝ} {g : κ → ℝ}
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) :
    ⨆ p : ι × κ, (f p.1 + g p.2) = (⨆ i, f i) + ⨆ j, g j := by
  have hb : BddAbove (Set.range fun p : ι × κ ↦ f p.1 + g p.2) :=
    ⟨(⨆ i, f i) + ⨆ j, g j, by
      rintro _ ⟨p, rfl⟩
      exact add_le_add (le_ciSup hf p.1) (le_ciSup hg p.2)⟩
  rw [ciSup_prod hb, ciSup_add hf]
  exact iSup_congr fun i ↦ (add_ciSup hg (f i)).symm

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A continuous function bounded by a multiple of the norm is integrable under the standard
Gaussian measure. -/
lemma integrable_stdGaussian_of_abs_le {f : E → ℝ} (hf : Continuous f)
    (h : ∀ x, |f x| ≤ K * ‖x‖) : Integrable f (stdGaussian E) :=
  (integrable_norm_stdGaussian.const_mul K).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact h x)

lemma integral_inner_sub_sq_stdGaussian (a b : E) :
    ∫ x, (⟪a, x⟫ - ⟪b, x⟫) ^ 2 ∂stdGaussian E = ‖a - b‖ ^ 2 := by
  simp_rw [← inner_sub_left]
  exact integral_inner_sq_stdGaussian (a - b)

end Suprema

/-! ### Chevet's inequality -/

section Chevet

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Chevet's inequality** for a Gaussian matrix `W`: for unit vectors `u s` and vectors `v t`
of norm at most `R`, `𝔼 sup_{s, t} ⟪u s, W v t⟫ ≤ R 𝔼 sup_s ⟪u s, g⟫ + 𝔼 sup_t ⟪v t, h⟫`. This is
the Sudakov–Fernique inequality for the bilinear process and the decoupled process
`R ⟪u s, g⟫ + ⟪v t, h⟫`. -/
theorem integral_iSup_inner_ofEuclidean_le {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace.SeparableSpace S] [Nonempty S] [TopologicalSpace T]
    [TopologicalSpace.SeparableSpace T] [Nonempty T] {u : S → EuclideanSpace ℝ m}
    {v : T → EuclideanSpace ℝ n} (hu : Continuous u) (hv : Continuous v) (hu1 : ∀ s, ‖u s‖ = 1)
    {R : ℝ} (hR : ∀ t, ‖v t‖ ≤ R) :
    Integrable (fun w ↦ ⨆ p : S × T, ⟪u p.1, (ofEuclidean w).toEuclideanLin (v p.2)⟫)
        (stdGaussian (EuclideanSpace ℝ (m × n))) ∧
      ∫ w, ⨆ p : S × T, ⟪u p.1, (ofEuclidean w).toEuclideanLin (v p.2)⟫
          ∂stdGaussian (EuclideanSpace ℝ (m × n)) ≤
        R * ∫ g, ⨆ s, ⟪u s, g⟫ ∂stdGaussian (EuclideanSpace ℝ m) +
          ∫ h, ⨆ t, ⟪v t, h⟫ ∂stdGaussian (EuclideanSpace ℝ n) := by
  obtain ⟨t₀⟩ := ‹Nonempty T›
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR t₀)
  have hRu : ∀ s, ‖R • u s‖ ≤ R := fun s ↦ by
    rw [norm_smul, hu1, Real.norm_of_nonneg hR0, mul_one]
  have hcY : ∀ p : S × T, ‖sumElim (R • u p.1) (v p.2)‖ ≤ R + R := fun p ↦
    (norm_sumElim_le _ _).trans (add_le_add (hRu p.1) (hR p.2))
  have huu : ∀ s, ⟪u s, u s⟫ = 1 := fun s ↦ by rw [real_inner_self_eq_norm_sq, hu1, one_pow]
  -- the increments of the bilinear process are dominated by those of the decoupled process
  have hinc : ∀ p q : S × T,
      ∫ w, (⟪kronecker (u p.1) (v p.2), w⟫ - ⟪kronecker (u q.1) (v q.2), w⟫) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (m × n)) ≤
        ∫ x, (⟪sumElim (R • u p.1) (v p.2), x⟫ - ⟪sumElim (R • u q.1) (v q.2), x⟫) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (m ⊕ n)) := by
    intro p q
    have ha : ⟪u p.1, u q.1⟫ ≤ 1 :=
      (real_inner_le_norm _ _).trans (by rw [hu1, hu1, one_mul])
    have hb : ⟪v p.2, v q.2⟫ ≤ R * R :=
      (real_inner_le_norm _ _).trans (mul_le_mul (hR _) (hR _) (norm_nonneg _) hR0)
    simp only [integral_inner_sub_sq_stdGaussian, ← real_inner_self_eq_norm_sq, inner_sub_left,
      inner_sub_right, inner_kronecker_kronecker, inner_sumElim_sumElim, real_inner_smul_left,
      real_inner_smul_right, huu]
    rw [real_inner_comm (u p.1) (u q.1), real_inner_comm (v p.2) (v q.2)]
    nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]
  obtain ⟨hXi, hle⟩ := IsGaussianProcess.integral_iSup_le_of_separable
    (X := fun (p : S × T) (w : EuclideanSpace ℝ (m × n)) ↦
      ⟪kronecker (u p.1) (v p.2), w⟫)
    (Y := fun (p : S × T) (x : EuclideanSpace ℝ (m ⊕ n)) ↦
      ⟪sumElim (R • u p.1) (v p.2), x⟫)
    (isGaussianProcess_inner_stdGaussian _) (isGaussianProcess_inner_stdGaussian _)
    (fun p ↦ by simp only [integral_inner_stdGaussian]) hinc
    (ae_of_all _ fun w ↦ by
      simp only [inner_kronecker]
      exact (hu.comp continuous_fst).inner
        ((LinearMap.continuous_of_finiteDimensional _).comp (hv.comp continuous_snd)))
    (ae_of_all _ fun x ↦ by
      simp only [inner_sumElim]
      exact ((hu.comp continuous_fst).const_smul R).inner continuous_const |>.add
        ((hv.comp continuous_snd).inner continuous_const))
    (ae_of_all _ fun x ↦ bddAbove_range_inner_of_norm_le hcY x)
    (integrable_stdGaussian_of_abs_le (continuous_iSup_inner hcY) (abs_iSup_inner_le hcY))
  -- the supremum of the decoupled process splits into the two blocks
  have hYsup : ∀ x : EuclideanSpace ℝ (m ⊕ n), ⨆ p : S × T, ⟪sumElim (R • u p.1) (v p.2), x⟫ =
      R * (⨆ s, ⟪u s, (blocks x).1⟫) + ⨆ t, ⟪v t, (blocks x).2⟫ := by
    intro x
    simp only [inner_sumElim]
    rw [iSup_prod_add (bddAbove_range_inner_of_norm_le hRu _)
      (bddAbove_range_inner_of_norm_le hR _), Real.mul_iSup_of_nonneg hR0]
    simp only [real_inner_smul_left]
  have hU : Integrable (fun g ↦ R * ⨆ s, ⟪u s, g⟫) (stdGaussian (EuclideanSpace ℝ m)) :=
    (integrable_stdGaussian_of_abs_le (continuous_iSup_inner fun s ↦ (hu1 s).le)
      (abs_iSup_inner_le fun s ↦ (hu1 s).le)).const_mul R
  have hV : Integrable (fun h ↦ ⨆ t, ⟪v t, h⟫) (stdGaussian (EuclideanSpace ℝ n)) :=
    integrable_stdGaussian_of_abs_le (continuous_iSup_inner hR) (abs_iSup_inner_le hR)
  simp only [inner_kronecker, hYsup] at hXi hle
  rw [integral_blocks_add hU hV, integral_const_mul] at hle
  exact ⟨hXi, hle⟩

end Chevet

/-! ### Gordon's inequality -/

section Gordon

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Gordon's inequality** for a Gaussian matrix `W`: for unit vectors `u t` and `v s`,
`𝔼 sup_t ⟪u t, g⟫ + 𝔼 inf_s ⟪v s, h⟫ ≤ 𝔼 inf_s sup_t ⟪u t, W v s⟫`. -/
theorem integral_add_integral_iInf_le_integral_iInf_iSup_inner_ofEuclidean {S T : Type*}
    [TopologicalSpace S] [TopologicalSpace.SeparableSpace S] [Nonempty S] [TopologicalSpace T]
    [TopologicalSpace.SeparableSpace T] [Nonempty T] {u : T → EuclideanSpace ℝ m}
    {v : S → EuclideanSpace ℝ n} (hu : Continuous u) (hv : Continuous v) (hu1 : ∀ t, ‖u t‖ = 1)
    (hv1 : ∀ s, ‖v s‖ = 1) :
    ∫ g, ⨆ t, ⟪u t, g⟫ ∂stdGaussian (EuclideanSpace ℝ m) +
        ∫ h, ⨅ s, ⟪v s, h⟫ ∂stdGaussian (EuclideanSpace ℝ n) ≤
      ∫ w, ⨅ s, ⨆ t, ⟪u t, (ofEuclidean w).toEuclideanLin (v s)⟫
        ∂stdGaussian (EuclideanSpace ℝ (m × n)) := by
  set e : EuclideanSpace ℝ Unit := EuclideanSpace.single () 1
  have he : ⟪e, e⟫ = 1 := by simp [e]
  have he1 : ‖e‖ = 1 := by simp [e]
  have huu : ∀ t, ⟪u t, u t⟫ = 1 := fun t ↦ by rw [real_inner_self_eq_norm_sq, hu1, one_pow]
  have hvv : ∀ s, ⟪v s, v s⟫ = 1 := fun s ↦ by rw [real_inner_self_eq_norm_sq, hv1, one_pow]
  have hu1' : ∀ t, ‖u t‖ ≤ 1 := fun t ↦ (hu1 t).le
  have hck : ∀ s t, ‖kronecker (u t) (v s)‖ ≤ 1 := fun s t ↦ by
    rw [norm_kronecker, hu1, hv1, one_mul]
  have hcX : ∀ s t, ‖sumElim (u t) (v s)‖ ≤ 2 := fun s t ↦
    (norm_sumElim_le _ _).trans (by rw [hu1, hv1]; norm_num)
  have hcY : ∀ s t, ‖sumElim (kronecker (u t) (v s)) e‖ ≤ 2 := fun s t ↦
    (norm_sumElim_le _ _).trans (by rw [norm_kronecker, hu1, hv1, he1]; norm_num)
  -- the rows of both processes split into a supremum over `t` and a term depending on `s`
  have hXrow : ∀ (x : EuclideanSpace ℝ (m ⊕ n)) s, ⨆ t, ⟪sumElim (u t) (v s), x⟫ =
      (⨆ t, ⟪u t, (blocks x).1⟫) + ⟪v s, (blocks x).2⟫ := fun x s ↦ by
    simp only [inner_sumElim]
    exact (ciSup_add (bddAbove_range_inner_of_norm_le hu1' _) _).symm
  have hYrow : ∀ (y : EuclideanSpace ℝ ((m × n) ⊕ Unit)) s,
      ⨆ t, ⟪sumElim (kronecker (u t) (v s)) e, y⟫ =
        (⨆ t, ⟪kronecker (u t) (v s), (blocks y).1⟫) + ⟪e, (blocks y).2⟫ := fun y s ↦ by
    simp only [inner_sumElim]
    exact (ciSup_add (bddAbove_range_inner_of_norm_le (hck s) _) _).symm
  obtain ⟨-, hle⟩ := IsGaussianProcess.integral_iInf_iSup_le_gordon_of_separable
    (X := fun (i : S × T) (x : EuclideanSpace ℝ (m ⊕ n)) ↦ ⟪sumElim (u i.2) (v i.1), x⟫)
    (Y := fun (i : S × T) (y : EuclideanSpace ℝ ((m × n) ⊕ Unit)) ↦
      ⟪sumElim (kronecker (u i.2) (v i.1)) e, y⟫)
    (isGaussianProcess_inner_stdGaussian _) (isGaussianProcess_inner_stdGaussian _)
    (fun i ↦ integral_inner_stdGaussian _) (fun i ↦ integral_inner_stdGaussian _)
    (fun i ↦ by
      simp only [covariance_inner_stdGaussian, inner_sumElim_sumElim, inner_kronecker_kronecker,
        huu, hvv, he]
      norm_num)
    (fun s t t' _ ↦ by
      simp only [covariance_inner_stdGaussian, inner_sumElim_sumElim, inner_kronecker_kronecker,
        hvv, he, mul_one, le_refl])
    (fun s s' t t' _ ↦ by
      simp only [covariance_inner_stdGaussian, inner_sumElim_sumElim, inner_kronecker_kronecker,
        he]
      have ha : ⟪u t, u t'⟫ ≤ 1 := (real_inner_le_norm _ _).trans (by rw [hu1, hu1, one_mul])
      have hb : ⟪v s, v s'⟫ ≤ 1 := (real_inner_le_norm _ _).trans (by rw [hv1, hv1, one_mul])
      nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)])
    (ae_of_all _ fun x s ↦ by
      simp only [inner_sumElim]
      exact (hu.inner continuous_const).add continuous_const)
    (ae_of_all _ fun y s ↦ by
      simp only [inner_sumElim, inner_kronecker]
      exact (hu.inner continuous_const).add continuous_const)
    (ae_of_all _ fun x ↦ by
      simp only [hXrow]
      exact continuous_const.add (hv.inner continuous_const))
    (ae_of_all _ fun y ↦ by
      simp only [hYrow, inner_kronecker]
      exact ((continuous_iSup_inner hu1').comp
        ((LinearMap.continuous_of_finiteDimensional _).comp hv)).add continuous_const)
    (ae_of_all _ fun y s ↦ bddAbove_range_inner_of_norm_le (hcY s) y)
    (ae_of_all _ fun x ↦ bddBelow_range_iSup_inner hcX x)
    (fun s ↦ integrable_stdGaussian_of_abs_le (continuous_iSup_inner (hcY s))
      (abs_iSup_inner_le (hcY s)))
    (integrable_stdGaussian_of_abs_le (continuous_iInf_iSup_inner hcX)
      (abs_iInf_iSup_inner_le hcX))
  -- split the infima of the row suprema into the two blocks
  have hv1' : ∀ s (_ : Unit), ‖v s‖ ≤ 1 := fun s _ ↦ (hv1 s).le
  have hXinf : ∀ x : EuclideanSpace ℝ (m ⊕ n), ⨅ s, ⨆ t, ⟪sumElim (u t) (v s), x⟫ =
      (⨆ t, ⟪u t, (blocks x).1⟫) + ⨅ s, ⟪v s, (blocks x).2⟫ := fun x ↦ by
    have hb := bddBelow_range_iSup_inner hv1' (blocks x).2
    simp only [ciSup_const] at hb
    simp only [hXrow]
    exact (add_ciInf hb _).symm
  have hYinf : ∀ y : EuclideanSpace ℝ ((m × n) ⊕ Unit),
      ⨅ s, ⨆ t, ⟪sumElim (kronecker (u t) (v s)) e, y⟫ =
        (⨅ s, ⨆ t, ⟪u t, (ofEuclidean (blocks y).1).toEuclideanLin (v s)⟫) +
          ⟪e, (blocks y).2⟫ := fun y ↦ by
    simp only [hYrow]
    rw [← ciInf_add (bddBelow_range_iSup_inner hck _)]
    simp only [inner_kronecker]
  have hU : Integrable (fun g ↦ ⨆ t, ⟪u t, g⟫) (stdGaussian (EuclideanSpace ℝ m)) :=
    integrable_stdGaussian_of_abs_le (continuous_iSup_inner hu1') (abs_iSup_inner_le hu1')
  have hV : Integrable (fun h ↦ ⨅ s, ⟪v s, h⟫) (stdGaussian (EuclideanSpace ℝ n)) := by
    have := integrable_stdGaussian_of_abs_le (continuous_iInf_iSup_inner hv1')
      (abs_iInf_iSup_inner_le hv1')
    simpa only [ciSup_const] using this
  have hZ := integrable_stdGaussian_of_abs_le (continuous_iInf_iSup_inner hck)
    (abs_iInf_iSup_inner_le hck)
  simp only [inner_kronecker] at hZ
  simp only [hXinf, hYinf] at hle
  rwa [integral_blocks_add hU hV, integral_blocks_add hZ (integrable_inner_stdGaussian e),
    integral_inner_stdGaussian, add_zero] at hle

end Gordon

/-! ### Extreme singular values -/

section SingularValues

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]

omit [DecidableEq n] in
lemma norm_toEuclideanLin_le_l2_opNorm (B : Matrix m l ℝ) (x : EuclideanSpace ℝ l) :
    ‖B.toEuclideanLin x‖ ≤ ‖B‖ * ‖x‖ := by
  rw [l2_opNorm_def]
  exact ContinuousLinearMap.le_opNorm ((toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) B) x

/-- `𝔼 ‖W A‖ ≤ ‖A‖ √m + ‖A‖_F` for an `m × n` standard Gaussian matrix `W`. -/
theorem integral_l2_opNorm_ofEuclidean_mul_le [Nonempty m] [Nonempty l] (A : Matrix n l ℝ) :
    Integrable (fun w ↦ ‖ofEuclidean w * A‖) (stdGaussian (EuclideanSpace ℝ (m × n))) ∧
      ∫ w, ‖ofEuclidean w * A‖ ∂stdGaussian (EuclideanSpace ℝ (m × n)) ≤
        ‖A‖ * √(Fintype.card m : ℝ) + √(∑ i, ∑ j, A i j ^ 2) := by
  have : Nonempty (sphere (0 : EuclideanSpace ℝ m) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  have : Nonempty (sphere (0 : EuclideanSpace ℝ l) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  have hA1 : ∀ t : sphere (0 : EuclideanSpace ℝ l) 1, ‖A.toEuclideanLin t‖ ≤ ‖A‖ := fun t ↦ by
    simpa [norm_eq_of_mem_sphere t] using norm_toEuclideanLin_le_l2_opNorm A t
  obtain ⟨hi, hle⟩ := integral_iSup_inner_ofEuclidean_le (m := m)
    (S := sphere (0 : EuclideanSpace ℝ m) 1) (T := sphere (0 : EuclideanSpace ℝ l) 1)
    (u := Subtype.val) (v := fun t ↦ A.toEuclideanLin t) continuous_subtype_val
    ((LinearMap.continuous_of_finiteDimensional _).comp continuous_subtype_val)
    (fun s ↦ norm_eq_of_mem_sphere s) hA1
  -- `‖W A‖` as a supremum of the bilinear process over pairs of unit vectors
  have hnorm : (fun w ↦ ‖ofEuclidean w * A‖) = fun w ↦
      ⨆ p : sphere (0 : EuclideanSpace ℝ m) 1 × sphere (0 : EuclideanSpace ℝ l) 1,
        ⟪(p.1 : EuclideanSpace ℝ m), (ofEuclidean w).toEuclideanLin (A.toEuclideanLin p.2)⟫ := by
    funext w
    set B := ofEuclidean w * A
    have hBA : ∀ x, (ofEuclidean w).toEuclideanLin (A.toEuclideanLin x) = B.toEuclideanLin x :=
      fun x ↦ by simp [B]
    simp only [hBA]
    have hbd : ∀ p : sphere (0 : EuclideanSpace ℝ m) 1 × sphere (0 : EuclideanSpace ℝ l) 1,
        ⟪(p.1 : EuclideanSpace ℝ m), B.toEuclideanLin p.2⟫ ≤ ‖B‖ := fun p ↦
      (real_inner_le_norm _ _).trans (by
        simpa [norm_eq_of_mem_sphere p.1, norm_eq_of_mem_sphere p.2] using
          norm_toEuclideanLin_le_l2_opNorm B p.2)
    have hb : BddAbove (Set.range fun p : sphere (0 : EuclideanSpace ℝ m) 1 ×
        sphere (0 : EuclideanSpace ℝ l) 1 ↦
          ⟪(p.1 : EuclideanSpace ℝ m), B.toEuclideanLin p.2⟫) :=
      ⟨‖B‖, by rintro _ ⟨p, rfl⟩; exact hbd p⟩
    have key : ∀ x : EuclideanSpace ℝ l, ‖x‖ = 1 → ‖B.toEuclideanLin x‖ ≤
        ⨆ p : sphere (0 : EuclideanSpace ℝ m) 1 × sphere (0 : EuclideanSpace ℝ l) 1,
          ⟪(p.1 : EuclideanSpace ℝ m), B.toEuclideanLin p.2⟫ := fun x hx ↦ by
      rw [← iSup_inner_sphere_eq_norm]
      exact ciSup_le fun s ↦ le_ciSup_of_le hb (s, ⟨x, mem_sphere_zero_iff_norm.2 hx⟩) le_rfl
    obtain ⟨t₀⟩ := ‹Nonempty (sphere (0 : EuclideanSpace ℝ l) 1)›
    refine le_antisymm ?_ (ciSup_le hbd)
    rw [l2_opNorm_def]
    exact ContinuousLinearMap.opNorm_le_of_unit_norm
      ((norm_nonneg _).trans (key t₀ (norm_eq_of_mem_sphere t₀))) key
  have hh : ∀ h : EuclideanSpace ℝ n,
      ⨆ t : sphere (0 : EuclideanSpace ℝ l) 1, ⟪A.toEuclideanLin t, h⟫ = ‖Aᴴ.toEuclideanLin h‖ :=
    fun h ↦ by
      rw [← iSup_inner_sphere_eq_norm, toEuclideanLin_conjTranspose_eq_adjoint]
      simp only [LinearMap.adjoint_inner_right]
  simp only [iSup_inner_sphere_eq_norm, hh] at hle
  rw [hnorm]
  refine ⟨hi, hle.trans (add_le_add (mul_le_mul_of_nonneg_left
    integral_norm_stdGaussian_euclideanSpace_le (norm_nonneg A))
    ((integral_norm_toEuclideanLin_stdGaussian_le Aᴴ).trans_eq ?_))⟩
  rw [Finset.sum_comm]
  simp [conjTranspose_apply]

/-- `𝔼 ‖g‖ - 𝔼 ‖h‖ ≤ 𝔼 σ_min(W)` for an `m × n` standard Gaussian matrix `W` and standard
Gaussian vectors `g` of dimension `m` and `h` of dimension `n`. -/
theorem integral_norm_sub_integral_norm_le_integral_minSingularValue [Nonempty m] [Nonempty n] :
    ∫ g, ‖g‖ ∂stdGaussian (EuclideanSpace ℝ m) - ∫ h, ‖h‖ ∂stdGaussian (EuclideanSpace ℝ n) ≤
      ∫ w, (ofEuclidean w).minSingularValue ∂stdGaussian (EuclideanSpace ℝ (m × n)) := by
  have : Nonempty (sphere (0 : EuclideanSpace ℝ m) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  have : Nonempty (sphere (0 : EuclideanSpace ℝ n) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  have h := integral_add_integral_iInf_le_integral_iInf_iSup_inner_ofEuclidean
    (S := sphere (0 : EuclideanSpace ℝ n) 1) (T := sphere (0 : EuclideanSpace ℝ m) 1)
    (u := Subtype.val) (v := Subtype.val) continuous_subtype_val continuous_subtype_val
    (fun t ↦ norm_eq_of_mem_sphere t) (fun s ↦ norm_eq_of_mem_sphere s)
  simp only [iSup_inner_sphere_eq_norm, iInf_inner_sphere_eq_neg_norm, integral_neg] at h
  simpa only [minSingularValue, sub_eq_add_neg] using h

end SingularValues

end ProbabilityTheory
