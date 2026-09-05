/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.LearningTheory.FunctionClass.NeuralNetwork.HiddenUnit

/-!
# One-hidden-layer networks of bounded path norm

A one-hidden-layer network `x ↦ ∑ j, η j * (⟪w j, x⟫ + b j)₊` is not controlled by any
constraint on `η` alone: the ReLU is positively homogeneous, so rescaling
`(w j, b j) ↦ ρ⁻¹ • (w j, b j)` and `η j ↦ ρ * η j` leaves the function unchanged while
shrinking `‖η‖₁` arbitrarily.  The path norm `∑ j, |η j| * ‖(w j, b j / R)‖` is invariant
under that rescaling, so it constrains the function rather than its parametrization.

The hypothesis class `pathBall R D` is therefore a set of functions, with the width
existentially quantified: no bound below mentions the width.

The estimate is the one-hidden-unit bound of
`StatsMLlib.LearningTheory.FunctionClass.NeuralNetwork.HiddenUnit` scaled by `D`.  The
scaling step is where positive homogeneity is used, and it is an inequality *for each sign
vector separately*, which is what makes the union over widths harmless.

## Main definitions

* `pathNorm`: the path norm of a parameter, in the augmented parametrization.
* `netFun`: the network associated with a parameter.
* `pathBall`: the hypothesis class, as a set of functions on the input ball.
* `pathBallClass`: that class as an indexed family, for the Rademacher machinery.

## Main results

* `abs_signed_average_netFun_le`: the pointwise reduction to a single hidden unit.
* `empiricalRademacherComplexity_pathBall_le`: `Rhatₙ ≤ 2 √2 D R / √n`, with no dependence
  on the width or on the dimension of the input space.
-/

noncomputable section

universe u

open Real ProbabilityTheory

variable {n : ℕ}
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

namespace NeuralNetwork

/-- The unit vector in the direction of `p`, and `0` when `p = 0`. -/
def unitVector (p : AugSpace E) : Metric.closedBall (0 : AugSpace E) 1 :=
  ⟨‖p‖⁻¹ • p, by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)]⟩

/-- Positive homogeneity of the ReLU: a hidden unit with an unnormalized parameter is the
normalized unit scaled by the norm of the parameter.  This is the identity that makes the
path norm, rather than `‖η‖₁`, the right quantity to constrain. -/
lemma norm_mul_reluUnit_unitVector (R : ℝ) (p : AugSpace E)
    (x : Metric.closedBall (0 : E) R) :
    ‖p‖ * reluUnit R (unitVector p) x = max ⟪p, augment R x⟫ 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [reluUnit, affineUnit, hilbertPredictor, unitVector]
  · have hnorm : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    have h : affineUnit R (unitVector p) x = ‖p‖⁻¹ * ⟪p, augment R x⟫ := by
      simp [affineUnit, hilbertPredictor, unitVector, real_inner_smul_left]
      ring
    rw [reluUnit, h, mul_max_of_nonneg _ _ (norm_nonneg p), mul_zero,
      ← mul_assoc, mul_inv_cancel₀ hnorm, one_mul]

/-- The path norm of a parameter, written in the augmented parametrization: the `j`-th
hidden unit is `(η j, ŵ j)` with `ŵ j = (w j, b j / R)`. -/
def pathNorm {m : ℕ} (θ : Fin m → ℝ × AugSpace E) : ℝ :=
  ∑ j : Fin m, |(θ j).1| * ‖(θ j).2‖

/-- The one-hidden-layer network associated with a parameter. -/
def netFun (R : ℝ) {m : ℕ} (θ : Fin m → ℝ × AugSpace E) :
    Metric.closedBall (0 : E) R → ℝ :=
  fun x ↦ ∑ j : Fin m, (θ j).1 * max ⟪(θ j).2, augment R x⟫ 0

/-- The hypothesis class: networks of any width whose path norm is at most `D`.  The width
is existentially quantified, so this is the union over widths. -/
def pathBall (R D : ℝ) : Set (Metric.closedBall (0 : E) R → ℝ) :=
  {f | ∃ (m : ℕ) (θ : Fin m → ℝ × AugSpace E), pathNorm θ ≤ D ∧ netFun R θ = f}

/-- The hypothesis class as an indexed family. -/
def pathBallClass (R D : ℝ) :
    pathBall (E := E) R D → Metric.closedBall (0 : E) R → ℝ :=
  fun f x ↦ (f : Metric.closedBall (0 : E) R → ℝ) x

lemma zero_mem_pathBall (R : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    (0 : Metric.closedBall (0 : E) R → ℝ) ∈ pathBall R D :=
  ⟨0, Fin.elim0, by simpa [pathNorm] using hD, by funext x; simp [netFun]⟩

lemma neg_mem_pathBall {R D : ℝ} {f : Metric.closedBall (0 : E) R → ℝ}
    (hf : f ∈ pathBall R D) : -f ∈ pathBall R D := by
  obtain ⟨m, θ, hθ, rfl⟩ := hf
  refine ⟨m, fun j ↦ (-(θ j).1, (θ j).2), by simpa [pathNorm] using hθ, ?_⟩
  funext x
  simp [netFun, Finset.sum_neg_distrib]

lemma isNegClosed_pathBallClass (R D : ℝ) : IsNegClosed (pathBallClass (E := E) R D) :=
  fun i ↦ ⟨⟨-(i : Metric.closedBall (0 : E) R → ℝ), neg_mem_pathBall i.2⟩, rfl⟩

/-- A signed sample average of a bounded function is bounded by the same constant. -/
private lemma abs_signedAverage_le {𝒳 : Type*} {b : ℝ} (hb : 0 ≤ b)
    (g : 𝒳 → ℝ) (S : Fin n → 𝒳) (hg : ∀ k, |g (S k)| ≤ b) (σ : Signs n) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * g (S k)| ≤ b := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using hb
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_mul, abs_of_pos (inv_pos.mpr hnR)]
  calc (n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * g (S k)|
      ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, |(σ k : ℝ) * g (S k)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs (fun k : Fin n ↦ (σ k : ℝ) * g (S k)) Finset.univ
    _ = (n : ℝ)⁻¹ * ∑ k : Fin n, |g (S k)| := by
        congr 1
        exact Finset.sum_congr rfl fun k _ ↦ by rw [abs_mul, abs_sigma, one_mul]
    _ ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, b := by gcongr with k; exact hg k
    _ = b := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- A hidden unit evaluated at an input of norm at most `R` is bounded by `‖w‖ √2 R`. -/
private lemma abs_max_inner_augment_le (R : ℝ) (hR : 0 ≤ R) (w : AugSpace E)
    (x : Metric.closedBall (0 : E) R) :
    |max ⟪w, augment R x⟫ 0| ≤ ‖w‖ * (Real.sqrt 2 * R) := by
  have h1 : |max ⟪w, augment R x⟫ 0| ≤ |⟪w, augment R x⟫| := by
    simpa using abs_max_sub_max_le_abs ⟪w, augment R x⟫ 0 0
  refine h1.trans ((abs_real_inner_le_norm _ _).trans ?_)
  gcongr
  exact norm_augment_le R hR x

/-- Members of the class are uniformly bounded by `√2 R D` on the input ball. -/
lemma abs_pathBallClass_le (R D : ℝ) (hR : 0 ≤ R) (f : pathBall (E := E) R D)
    (x : Metric.closedBall (0 : E) R) :
    |pathBallClass R D f x| ≤ Real.sqrt 2 * R * D := by
  obtain ⟨f, m, θ, hθ, rfl⟩ := f
  have hb : (0 : ℝ) ≤ Real.sqrt 2 * R := by positivity
  show |netFun R θ x| ≤ _
  calc |netFun R θ x| ≤ ∑ j : Fin m, |(θ j).1 * max ⟪(θ j).2, augment R x⟫ 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin m, |(θ j).1| * ‖(θ j).2‖ * (Real.sqrt 2 * R) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [abs_mul, mul_assoc]
        gcongr
        exact abs_max_inner_augment_le R hR _ x
    _ = pathNorm θ * (Real.sqrt 2 * R) := by rw [pathNorm, Finset.sum_mul]
    _ ≤ D * (Real.sqrt 2 * R) := by gcongr
    _ = Real.sqrt 2 * R * D := by ring

/-- The substantive step: for a single sign vector, the path norm converts a whole network
into that multiple of the worst single hidden unit.  This is an inequality for each sign
vector, so averaging over the signs afterwards is the only remaining move — and the width
has already disappeared. -/
lemma abs_signed_average_netFun_le (R : ℝ) (hR : 0 ≤ R) {m : ℕ}
    (θ : Fin m → ℝ × AugSpace E) (S : Fin n → Metric.closedBall (0 : E) R) (σ : Signs n) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * netFun R θ (S k)| ≤
      pathNorm θ * ⨆ p : Metric.closedBall (0 : AugSpace E) 1,
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * reluUnit R p (S k)| := by
  have hbdd : BddAbove (Set.range fun p : Metric.closedBall (0 : AugSpace E) 1 ↦
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * reluUnit R p (S k)|) := by
    refine ⟨Real.sqrt 2 * R, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact abs_signedAverage_le (by positivity) (reluUnit R p) S
      (fun k ↦ abs_reluUnit_le R hR p (S k)) σ
  have hM : ∀ p : Metric.closedBall (0 : AugSpace E) 1,
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * reluUnit R p (S k)| ≤
        ⨆ q : Metric.closedBall (0 : AugSpace E) 1,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * reluUnit R q (S k)| :=
    fun p ↦ le_ciSup hbdd p
  have hterm : ∀ (k : Fin n) (j : Fin m),
      (σ k : ℝ) * ((θ j).1 * max ⟪(θ j).2, augment R (S k)⟫ 0)
        = ((θ j).1 * ‖(θ j).2‖) * ((σ k : ℝ) * reluUnit R (unitVector (θ j).2) (S k)) := by
    intro k j
    rw [← norm_mul_reluUnit_unitVector R (θ j).2 (S k)]
    ring
  have hrewrite : (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * netFun R θ (S k)
      = ∑ j : Fin m, ((θ j).1 * ‖(θ j).2‖) *
          ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * reluUnit R (unitVector (θ j).2) (S k)) := by
    calc (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * netFun R θ (S k)
        = (n : ℝ)⁻¹ * ∑ k : Fin n, ∑ j : Fin m,
            ((θ j).1 * ‖(θ j).2‖) * ((σ k : ℝ) * reluUnit R (unitVector (θ j).2) (S k)) := by
          congr 1
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [netFun, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ hterm k j
      _ = (n : ℝ)⁻¹ * ∑ j : Fin m, ∑ k : Fin n,
            ((θ j).1 * ‖(θ j).2‖) * ((σ k : ℝ) * reluUnit R (unitVector (θ j).2) (S k)) := by
          rw [Finset.sum_comm]
      _ = ∑ j : Fin m, ((θ j).1 * ‖(θ j).2‖) *
            ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * reluUnit R (unitVector (θ j).2) (S k)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [← Finset.mul_sum]
          ring
  rw [hrewrite]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [pathNorm, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [abs_mul, abs_mul, abs_norm]
  gcongr
  exact hM _

/-- The class-level form of the reduction. -/
theorem empiricalRademacherComplexity_pathBallClass_le (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (S : Fin n → Metric.closedBall (0 : E) R) :
    empiricalRademacherComplexity n (pathBallClass R D) S ≤
      D * empiricalRademacherComplexity n (reluUnit R) S := by
  have hne : Nonempty (pathBall (E := E) R D) := ⟨⟨0, zero_mem_pathBall R hD⟩⟩
  have key : ∀ σ : Signs n,
      (⨆ f : pathBall (E := E) R D,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * pathBallClass R D f (S k)|) ≤
        D * ⨆ p : Metric.closedBall (0 : AugSpace E) 1,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * reluUnit R p (S k)| := by
    intro σ
    have hM0 : (0 : ℝ) ≤ ⨆ p : Metric.closedBall (0 : AugSpace E) 1,
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * reluUnit R p (S k)| :=
      Real.iSup_nonneg fun _ ↦ abs_nonneg _
    refine ciSup_le ?_
    rintro ⟨f, m, θ, hθ, rfl⟩
    refine (abs_signed_average_netFun_le R hR θ S σ).trans ?_
    gcongr
  calc empiricalRademacherComplexity n (pathBallClass R D) S
      = (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n,
          ⨆ f : pathBall (E := E) R D,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * pathBallClass R D f (S k)| := rfl
    _ ≤ (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ _σ : Signs n,
          D * ⨆ p : Metric.closedBall (0 : AugSpace E) 1,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (_σ k : ℝ) * reluUnit R p (S k)| := by
        gcongr with σ _
        exact key σ
    _ = D * empiricalRademacherComplexity n (reluUnit R) S := by
        rw [empiricalRademacherComplexity, ← Finset.mul_sum]
        ring

/--
The empirical Rademacher complexity of the path-norm ball of one-hidden-layer ReLU
networks on inputs of norm at most `R`:

`Rhatₙ ≤ 2 √2 D R / √n`.

The bound involves neither the width of the network nor the dimension of the input space,
and it is linear in `D` and in `R`, as positive homogeneity of the class demands.
-/
theorem empiricalRademacherComplexity_pathBall_le (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (S : Fin n → Metric.closedBall (0 : E) R) :
    empiricalRademacherComplexity n (pathBallClass R D) S ≤
      2 * Real.sqrt 2 * D * R / Real.sqrt (n : ℝ) := by
  refine (empiricalRademacherComplexity_pathBallClass_le R D hR hD S).trans ?_
  calc D * empiricalRademacherComplexity n (reluUnit R) S
      ≤ D * (2 * Real.sqrt 2 * R / Real.sqrt (n : ℝ)) := by
        gcongr
        exact reluUnit_empiricalRademacherComplexity_le R hR S
    _ = 2 * Real.sqrt 2 * D * R / Real.sqrt (n : ℝ) := by ring

lemma norm_unitVector {p : AugSpace E} (hp : p ≠ 0) :
    ‖(unitVector p : AugSpace E)‖ = 1 := by
  show ‖‖p‖⁻¹ • p‖ = 1
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)]

/--
Normal form.  Every member of the class is a network whose hidden units are normalized and
whose output weights have `ℓ¹` norm at most `D`.  After normalization the `ℓ¹` norm of the
output weights *is* the path norm, which is the sense in which this is a canonical form
rather than an extra assumption: it picks one representative in each orbit of the rescaling
`(w, b) ↦ ρ⁻¹ • (w, b)`, `η ↦ ρ * η`.

Nothing below uses this.  The Rademacher bound applies positive homogeneity pointwise
instead (`abs_signed_average_netFun_le`), which avoids constructing the normalized
parameter and the reindexing that discarding the zero units forces.
-/
lemma exists_normalized_of_mem_pathBall {R D : ℝ}
    {f : Metric.closedBall (0 : E) R → ℝ} (hf : f ∈ pathBall R D) :
    ∃ (m : ℕ) (θ : Fin m → ℝ × AugSpace E),
      (∀ j, ‖(θ j).2‖ = 1) ∧ ∑ j, |(θ j).1| ≤ D ∧ netFun R θ = f := by
  classical
  obtain ⟨m, θ, hθ, rfl⟩ := hf
  set s : Finset (Fin m) := Finset.univ.filter fun j ↦ (θ j).2 ≠ 0
  set e : Fin s.card → Fin m := fun j' ↦ ((s.equivFin.symm j' : s) : Fin m)
  have hmem : ∀ j' : Fin s.card, (θ (e j')).2 ≠ 0 := by
    intro j'
    have h : (s.equivFin.symm j' : Fin m) ∈ Finset.univ.filter fun j ↦ (θ j).2 ≠ 0 :=
      (s.equivFin.symm j').2
    exact (Finset.mem_filter.mp h).2
  have hreindex : ∀ g : Fin m → ℝ, (∀ j, (θ j).2 = 0 → g j = 0) →
      ∑ j' : Fin s.card, g (e j') = ∑ j : Fin m, g j := by
    intro g hg
    calc ∑ j' : Fin s.card, g (e j') = ∑ x : s, g (x : Fin m) :=
          Equiv.sum_comp s.equivFin.symm fun x : s ↦ g (x : Fin m)
      _ = ∑ j ∈ s, g j := Finset.sum_coe_sort s g
      _ = ∑ j : Fin m, g j := by
          refine Finset.sum_subset (Finset.subset_univ s) fun j _ hj ↦ ?_
          have hj' : ¬(θ j).2 ≠ 0 := fun h ↦
            hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
          exact hg j (not_not.mp hj')
  refine ⟨s.card, fun j' ↦ (‖(θ (e j')).2‖ * (θ (e j')).1, unitVector (θ (e j')).2),
    fun j' ↦ norm_unitVector (hmem j'), ?_, ?_⟩
  · refine le_trans (le_of_eq ?_) hθ
    rw [pathNorm]
    refine hreindex (fun j ↦ |(θ j).1| * ‖(θ j).2‖) (fun j hj ↦ by simp [hj]) ▸ ?_
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [abs_mul, abs_norm]
    ring
  · funext x
    rw [netFun, netFun]
    refine Eq.trans ?_ (hreindex (fun j ↦ (θ j).1 * max ⟪(θ j).2, augment R x⟫ 0)
      (fun j hj ↦ by simp [hj]))
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [← norm_mul_reluUnit_unitVector R (θ (e j')).2 x]
    simp only [reluUnit, affineUnit, hilbertPredictor]
    ring

/-!
## The loss class

Lipschitz contraction is not free in the convention where `empiricalRademacherComplexity`
takes an absolute value inside the supremum.  A constant loss `ℓ ≡ M` is `0`-Lipschitz, and
its loss class is the single function `(x, y) ↦ M`, whose absolute empirical Rademacher
complexity is `M * E |n⁻¹ ∑ εᵢ| > 0`; a bound of the form `G * (…)` would force `0`.  So a
`G`-Lipschitz loss costs a bare `G` only in the one-sided convention, and in the absolute
convention it costs `2 * G` after the loss is centered at prediction zero.

Both forms are recorded below.  They differ by exactly the factor `2`.
-/

/--
The loss class of a path-norm ball, in the one-sided convention:

`Rhat⁻ₙ(𝒢) ≤ 2 √2 G D R / √n`.

No centering is needed here, because the one-sided contraction principle does not require
the loss to vanish at prediction zero, and because the class is closed under negation.
-/
theorem empiricalRademacherComplexity_without_abs_supervisedLossClass_pathBall_le
    {𝒴 : Type*} (R D G : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (loss : ℝ → 𝒴 → ℝ) (hloss : ∀ y u v, |loss u y - loss v y| ≤ G * |u - v|)
    (S : Fin n → Metric.closedBall (0 : E) R × 𝒴) :
    empiricalRademacherComplexity_without_abs n
        (supervisedLossClass (pathBallClass R D) loss) S ≤
      2 * Real.sqrt 2 * G * D * R / Real.sqrt (n : ℝ) := by
  have hne : Nonempty (pathBall (E := E) R D) := ⟨⟨0, zero_mem_pathBall R hD⟩⟩
  have hb : (0 : ℝ) ≤ Real.sqrt 2 * R * D := by positivity
  have hbnd : ∀ (h : pathBall (E := E) R D) (z : Metric.closedBall (0 : E) R × 𝒴),
      |pathBallClass R D h z.1| ≤ Real.sqrt 2 * R * D :=
    fun h z ↦ abs_pathBallClass_le R D hR h z.1
  have hneg : IsNegClosed (fun (h : pathBall (E := E) R D)
      (z : Metric.closedBall (0 : E) R × 𝒴) ↦ pathBallClass R D h z.1) :=
    fun i ↦ ⟨⟨-(i : Metric.closedBall (0 : E) R → ℝ), neg_mem_pathBall i.2⟩, rfl⟩
  have hcontract : empiricalRademacherComplexity_without_abs n
      (supervisedLossClass (pathBallClass R D) loss) S ≤
        G * empiricalRademacherComplexity_without_abs n
          (fun (h : pathBall (E := E) R D)
            (z : Metric.closedBall (0 : E) R × 𝒴) ↦ pathBallClass R D h z.1) S :=
    empiricalRademacherComplexity_without_abs_contraction n
      (fun (h : pathBall (E := E) R D)
        (z : Metric.closedBall (0 : E) R × 𝒴) ↦ pathBallClass R D h z.1)
      (fun z u ↦ loss u z.2) S hG hbnd (fun z u v ↦ hloss z.2 u v)
  have habs : empiricalRademacherComplexity_without_abs n
      (fun (h : pathBall (E := E) R D)
        (z : Metric.closedBall (0 : E) R × 𝒴) ↦ pathBallClass R D h z.1) S =
      empiricalRademacherComplexity n (pathBallClass R D) (Prod.fst ∘ S) :=
    (empiricalRademacherComplexity_eq_without_abs_of_neg_closed n
      (fun (h : pathBall (E := E) R D)
        (z : Metric.closedBall (0 : E) R × 𝒴) ↦ pathBallClass R D h z.1) S
      (Real.sqrt 2 * R * D) hb (fun i j ↦ hbnd i (S j)) hneg).symm.trans
      (empiricalRademacherComplexity_comp n (pathBallClass R D) Prod.fst S)
  rw [habs] at hcontract
  refine hcontract.trans ?_
  calc G * empiricalRademacherComplexity n (pathBallClass R D) (Prod.fst ∘ S)
      ≤ G * (2 * Real.sqrt 2 * D * R / Real.sqrt (n : ℝ)) := by
        gcongr
        exact empiricalRademacherComplexity_pathBall_le R D hR hD _
    _ = 2 * Real.sqrt 2 * G * D * R / Real.sqrt (n : ℝ) := by ring

/--
The loss class of a path-norm ball, in the absolute convention, with the loss centered at
prediction zero:

`Rhatₙ(𝒢) ≤ 4 √2 G D R / √n`.

The extra factor `2` relative to the one-sided form is the contraction constant that the
absolute convention forces, and the centering is what makes the contraction map vanish at
zero.  Neither can be dropped; see the discussion above.
-/
theorem empiricalRademacherComplexity_centered_supervisedLossClass_pathBall_le
    {𝒴 : Type*} (R D G : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (loss : ℝ → 𝒴 → ℝ) (hloss : ∀ y u v, |loss u y - loss v y| ≤ G * |u - v|)
    (S : Fin n → Metric.closedBall (0 : E) R × 𝒴) :
    empiricalRademacherComplexity n
        (supervisedLossClass (pathBallClass R D) (centeredLoss loss)) S ≤
      4 * Real.sqrt 2 * G * D * R / Real.sqrt (n : ℝ) := by
  have hne : Nonempty (pathBall (E := E) R D) := ⟨⟨0, zero_mem_pathBall R hD⟩⟩
  have hb : (0 : ℝ) ≤ Real.sqrt 2 * R * D := by positivity
  have hcontract := empiricalRademacherComplexity_centered_supervisedLossClass_le n
    (pathBallClass (E := E) R D) loss S hG hb
    (fun h x ↦ abs_pathBallClass_le R D hR h x) hloss
  refine hcontract.trans ?_
  rw [empiricalRademacherComplexity_comp n (pathBallClass R D) Prod.fst S]
  calc 2 * G * empiricalRademacherComplexity n (pathBallClass R D) (Prod.fst ∘ S)
      ≤ 2 * G * (2 * Real.sqrt 2 * D * R / Real.sqrt (n : ℝ)) := by
        gcongr
        exact empiricalRademacherComplexity_pathBall_le R D hR hD _
    _ = 4 * Real.sqrt 2 * G * D * R / Real.sqrt (n : ℝ) := by ring

/-! ## Examples

Worked uses of this module's public API. They are elaborated with the library, so they
double as acceptance tests that these statements stay usable as written.
-/

/-- The unit path-norm ball on the unit input ball has empirical Rademacher complexity at
most `3 / √n` on every sample, whatever the widths of the networks it contains. -/
example (S : Fin n → Metric.closedBall (0 : E) 1) :
    empiricalRademacherComplexity n (pathBallClass (E := E) 1 1) S ≤
      3 / Real.sqrt (n : ℝ) := by
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine (empiricalRademacherComplexity_pathBall_le 1 1 zero_le_one zero_le_one S).trans ?_
  gcongr
  linarith

/-- The absolute-deviation loss is `1`-Lipschitz in its prediction, so the one-sided
Rademacher complexity of its loss class over the unit path-norm ball is at most `3 / √n`. -/
example (S : Fin n → Metric.closedBall (0 : E) 1 × ℝ) :
    empiricalRademacherComplexity_without_abs n
        (supervisedLossClass (pathBallClass (E := E) 1 1) fun u y ↦ |u - y|) S ≤
      3 / Real.sqrt (n : ℝ) := by
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine (empiricalRademacherComplexity_without_abs_supervisedLossClass_pathBall_le
    1 1 1 zero_le_one zero_le_one zero_le_one _ (fun y u v ↦ ?_) S).trans ?_
  · have h := abs_abs_sub_abs_le_abs_sub (u - y) (v - y)
    rw [sub_sub_sub_cancel_right] at h
    linarith
  · gcongr
    linarith

/-- The same loss in the absolute convention, centered at prediction zero, costs the
further factor `2`: the bound becomes `6 / √n`. -/
example (S : Fin n → Metric.closedBall (0 : E) 1 × ℝ) :
    empiricalRademacherComplexity n
        (supervisedLossClass (pathBallClass (E := E) 1 1)
          (centeredLoss fun u y ↦ |u - y|)) S ≤
      6 / Real.sqrt (n : ℝ) := by
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine (empiricalRademacherComplexity_centered_supervisedLossClass_pathBall_le
    1 1 1 zero_le_one zero_le_one zero_le_one _ (fun y u v ↦ ?_) S).trans ?_
  · have h := abs_abs_sub_abs_le_abs_sub (u - y) (v - y)
    rw [sub_sub_sub_cancel_right] at h
    linarith
  · gcongr
    linarith

end NeuralNetwork

end
