/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.LinearAlgebra.Matrix.Perturbation
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator Norm and Extreme Singular Values of Real Matrices

This file collects deterministic facts about the `L²` operator norm and the extreme singular
values of real rectangular matrices, as needed for singular-value bounds of Gaussian matrices.
Throughout, `‖A‖` denotes the `L²` operator norm from `Matrix.Norms.L2Operator`.

## Main definitions

* `Matrix.ofEuclidean`: the linear map reshaping a vector of `EuclideanSpace ℝ (m × n)` into an
  `m × n` matrix.
* `Matrix.minSingularValue`: the infimum of `‖A v‖` over unit vectors `v`.

## Main results

* `iSup_inner_sphere_eq_norm` and `iInf_inner_sphere_eq_neg_norm`: variational formulas for the
  norm on the unit sphere of a real inner product space.
* `Matrix.l2_opNorm_le_sqrt_sum_sq`: the operator norm is bounded by the Frobenius norm.
* `Matrix.l2_opNorm_ofEuclidean_le`: reshaping a Euclidean vector into a matrix does not increase
  the norm.
* `Matrix.singularValues_card_sub_one`: the last singular value is `Matrix.minSingularValue`.
* `Matrix.singularValues_zero_eq_l2_opNorm`: the first singular value is the operator norm.
* `Matrix.minSingularValue_mul_le`: the smallest singular value is supermultiplicative.
* `Matrix.card_mul_minSingularValue_sq_le`: `n * σ_min(A)² ≤ ∑ᵢⱼ Aᵢⱼ²`.
* `Matrix.lipschitzWith_singularValues_ofEuclidean`,
  `Matrix.lipschitzWith_minSingularValue_ofEuclidean`, and
  `Matrix.lipschitzWith_l2_opNorm_ofEuclidean_mul`: `1`-Lipschitz (respectively `‖A‖`-Lipschitz)
  dependence on the matrix entries.
-/

open Metric Module
open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

/-! ## Variational formulas on the unit sphere -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inner products against unit vectors are bounded above by the norm. -/
theorem bddAbove_range_inner_sphere (x : E) :
    BddAbove (Set.range fun u : sphere (0 : E) 1 => ⟪(u : E), x⟫_ℝ) := by
  refine ⟨‖x‖, ?_⟩
  rintro _ ⟨u, rfl⟩
  calc ⟪(u : E), x⟫_ℝ ≤ ‖(u : E)‖ * ‖x‖ := real_inner_le_norm _ _
    _ = ‖x‖ := by rw [norm_eq_of_mem_sphere u, one_mul]

/-- Inner products against unit vectors are bounded below by minus the norm. -/
theorem bddBelow_range_inner_sphere (x : E) :
    BddBelow (Set.range fun u : sphere (0 : E) 1 => ⟪(u : E), x⟫_ℝ) := by
  refine ⟨-‖x‖, ?_⟩
  rintro _ ⟨u, rfl⟩
  have h := abs_real_inner_le_norm (u : E) x
  rw [norm_eq_of_mem_sphere u, one_mul] at h
  exact neg_le_of_abs_le h

variable [Nontrivial E]

/-- Some unit vector attains `⟪u, x⟫ = ‖x‖`. -/
theorem exists_inner_sphere_eq_norm (x : E) :
    ∃ u : sphere (0 : E) 1, ⟪(u : E), x⟫_ℝ = ‖x‖ := by
  have hunit : ∀ y : E, y ≠ 0 → ‖‖y‖⁻¹ • y‖ = 1 := fun y hy => by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  by_cases hx : x = 0
  · obtain ⟨y, hy⟩ := exists_ne (0 : E)
    exact ⟨⟨‖y‖⁻¹ • y, mem_sphere_zero_iff_norm.mpr (hunit y hy)⟩, by simp [hx]⟩
  · refine ⟨⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (hunit x hx)⟩, ?_⟩
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp

/-- The norm is the supremum of `⟪u, x⟫` over the unit sphere. -/
theorem iSup_inner_sphere_eq_norm (x : E) :
    ⨆ u : sphere (0 : E) 1, ⟪(u : E), x⟫_ℝ = ‖x‖ := by
  obtain ⟨u, hu⟩ := exists_inner_sphere_eq_norm x
  have : Nonempty (sphere (0 : E) 1) := ⟨u⟩
  refine le_antisymm (ciSup_le fun v => ?_) (hu ▸ le_ciSup (bddAbove_range_inner_sphere x) u)
  calc ⟪(v : E), x⟫_ℝ ≤ ‖(v : E)‖ * ‖x‖ := real_inner_le_norm _ _
    _ = ‖x‖ := by rw [norm_eq_of_mem_sphere v, one_mul]

/-- Minus the norm is the infimum of `⟪u, x⟫` over the unit sphere. -/
theorem iInf_inner_sphere_eq_neg_norm (x : E) :
    ⨅ u : sphere (0 : E) 1, ⟪(u : E), x⟫_ℝ = -‖x‖ := by
  obtain ⟨u, hu⟩ := exists_inner_sphere_eq_norm x
  have : Nonempty (sphere (0 : E) 1) := ⟨u⟩
  let v : sphere (0 : E) 1 := ⟨-(u : E), by simp⟩
  have hv : ⟪(v : E), x⟫_ℝ = -‖x‖ := by simp [v, inner_neg_left, hu]
  refine le_antisymm (hv ▸ ciInf_le (bddBelow_range_inner_sphere x) v) (le_ciInf fun w => ?_)
  have h := abs_real_inner_le_norm (w : E) x
  rw [norm_eq_of_mem_sphere w, one_mul] at h
  exact neg_le_of_abs_le h

end Sphere

namespace Matrix

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq n]

/-! ## Operator norm versus Frobenius norm -/

/-- The squared Euclidean norm of `A x`, written entrywise. -/
theorem norm_toEuclideanLin_sq (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    ‖A.toEuclideanLin x‖ ^ 2 = ∑ i, (∑ j, A i j * x j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [toLpLin_apply, mulVec, dotProduct]

/-- Row-wise Cauchy-Schwarz: `‖A x‖ ≤ ‖A‖_F ‖x‖`. -/
theorem norm_toEuclideanLin_le_sqrt_sum_sq_mul (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    ‖A.toEuclideanLin x‖ ≤ √(∑ i, ∑ j, A i j ^ 2) * ‖x‖ := by
  have hsq : ‖A.toEuclideanLin x‖ ^ 2 ≤ (∑ i, ∑ j, A i j ^ 2) * ‖x‖ ^ 2 := by
    rw [norm_toEuclideanLin_sq, EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hS : 0 ≤ ∑ i, ∑ j, A i j ^ 2 := by positivity
  calc ‖A.toEuclideanLin x‖ ≤ √((∑ i, ∑ j, A i j ^ 2) * ‖x‖ ^ 2) := Real.le_sqrt_of_sq_le hsq
    _ = √(∑ i, ∑ j, A i j ^ 2) * ‖x‖ := by rw [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg x)]

/-- The `L²` operator norm is bounded by the Frobenius norm. -/
theorem l2_opNorm_le_sqrt_sum_sq (A : Matrix m n ℝ) : ‖A‖ ≤ √(∑ i, ∑ j, A i j ^ 2) := by
  rw [l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    fun x => A.norm_toEuclideanLin_le_sqrt_sum_sq_mul x

/-! ## Reshaping Euclidean vectors into matrices -/

/-- Reshape a vector of `EuclideanSpace ℝ (m × n)` into an `m × n` matrix. -/
def ofEuclidean : EuclideanSpace ℝ (m × n) →ₗ[ℝ] Matrix m n ℝ where
  toFun w := of fun i j => w (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype m] [Fintype n] [DecidableEq n] in
@[simp]
theorem ofEuclidean_apply (w : EuclideanSpace ℝ (m × n)) (i : m) (j : n) :
    ofEuclidean w i j = w (i, j) :=
  rfl

omit [DecidableEq n] in
/-- The squared Frobenius norm of a reshaped vector is its squared Euclidean norm. -/
theorem sum_sq_ofEuclidean (w : EuclideanSpace ℝ (m × n)) :
    ∑ i, ∑ j, ofEuclidean w i j ^ 2 = ‖w‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  rfl

/-- Reshaping a Euclidean vector into a matrix does not increase the norm. -/
theorem l2_opNorm_ofEuclidean_le (w : EuclideanSpace ℝ (m × n)) : ‖ofEuclidean w‖ ≤ ‖w‖ := by
  refine (l2_opNorm_le_sqrt_sum_sq _).trans_eq ?_
  rw [sum_sq_ofEuclidean, Real.sqrt_sq (norm_nonneg w)]

/-- Reshaping into a matrix is `1`-Lipschitz for the `L²` operator norm. -/
theorem lipschitzWith_ofEuclidean :
    LipschitzWith 1 (ofEuclidean : EuclideanSpace ℝ (m × n) → Matrix m n ℝ) :=
  LipschitzWith.of_dist_le_mul fun w v => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    exact l2_opNorm_ofEuclidean_le _

/-! ## The smallest singular value -/

/-- The smallest singular value of `A`, as the infimum of `‖A v‖` over unit vectors `v`.
It equals `A.singularValues (Fintype.card n - 1)`, see `Matrix.singularValues_card_sub_one`. -/
def minSingularValue (A : Matrix m n ℝ) : ℝ :=
  ⨅ v : sphere (0 : EuclideanSpace ℝ n) 1, ‖A.toEuclideanLin (v : EuclideanSpace ℝ n)‖

/-- The smallest singular value is nonnegative. -/
theorem minSingularValue_nonneg (A : Matrix m n ℝ) : 0 ≤ A.minSingularValue :=
  Real.iInf_nonneg fun _ => norm_nonneg _

/-- The values `‖A v‖` over unit vectors are bounded below. -/
theorem bddBelow_range_norm_toEuclideanLin_sphere (A : Matrix m n ℝ) :
    BddBelow (Set.range fun v : sphere (0 : EuclideanSpace ℝ n) 1 =>
      ‖A.toEuclideanLin (v : EuclideanSpace ℝ n)‖) :=
  ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩

/-- With an empty column index, the smallest singular value is `0`. -/
theorem minSingularValue_of_isEmpty [IsEmpty n] (A : Matrix m n ℝ) : A.minSingularValue = 0 := by
  have : IsEmpty (sphere (0 : EuclideanSpace ℝ n) 1) := ⟨fun v => by
    have h := norm_eq_of_mem_sphere v
    rw [Subsingleton.elim (v : EuclideanSpace ℝ n) 0, norm_zero] at h
    exact zero_ne_one h⟩
  exact Real.iInf_of_isEmpty _

/-- Every unit vector bounds the smallest singular value from above. -/
theorem minSingularValue_le_norm (A : Matrix m n ℝ) {v : EuclideanSpace ℝ n} (hv : ‖v‖ = 1) :
    A.minSingularValue ≤ ‖A.toEuclideanLin v‖ :=
  ciInf_le A.bddBelow_range_norm_toEuclideanLin_sphere ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩

/-- A uniform lower bound on `‖A v‖` over unit vectors bounds the smallest singular value. -/
theorem le_minSingularValue [Nonempty n] (A : Matrix m n ℝ) {c : ℝ}
    (h : ∀ v : EuclideanSpace ℝ n, ‖v‖ = 1 → c ≤ ‖A.toEuclideanLin v‖) :
    c ≤ A.minSingularValue := by
  have : Nonempty (sphere (0 : EuclideanSpace ℝ n) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  exact le_ciInf fun v => h v (mem_sphere_zero_iff_norm.mp v.2)

/-- `‖A x‖ ≥ σ_min(A) ‖x‖`. -/
theorem minSingularValue_mul_norm_le (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    A.minSingularValue * ‖x‖ ≤ ‖A.toEuclideanLin x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hunit : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hxpos.ne']
  have h := A.minSingularValue_le_norm hunit
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, le_inv_mul_iff₀ hxpos] at h
  linarith [mul_comm A.minSingularValue ‖x‖]

/-- The singular-quotient infimum of `A` is `Matrix.minSingularValue`. -/
theorem iInf_singularQuotient_toEuclideanLin [Nonempty n] (A : Matrix m n ℝ) :
    ⨅ x : { x : EuclideanSpace ℝ n // x ≠ 0 }, LinearMap.singularQuotient A.toEuclideanLin x =
      A.minSingularValue := by
  have : Nonempty { x : EuclideanSpace ℝ n // x ≠ 0 } := by
    obtain ⟨x, hx⟩ := exists_ne (0 : EuclideanSpace ℝ n)
    exact ⟨⟨x, hx⟩⟩
  apply le_antisymm
  · refine A.le_minSingularValue fun v hv => ?_
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    calc _ ≤ LinearMap.singularQuotient A.toEuclideanLin v :=
          ciInf_le (LinearMap.bddBelow_range_singularQuotient _) ⟨v, hv0⟩
      _ = ‖A.toEuclideanLin v‖ := by simp [LinearMap.singularQuotient, hv]
  · refine le_ciInf fun x => ?_
    unfold LinearMap.singularQuotient
    rw [le_div_iff₀ (norm_pos_iff.mpr x.2)]
    exact A.minSingularValue_mul_norm_le x

/-- The last singular value is the smallest singular value `Matrix.minSingularValue`. -/
theorem singularValues_card_sub_one (A : Matrix m n ℝ) :
    A.singularValues (Fintype.card n - 1) = A.minSingularValue := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [A.singularValues_of_card_le (by simp), A.minSingularValue_of_isEmpty]
  · have hpos : 0 < Fintype.card n := Fintype.card_pos
    have key := LinearMap.singularValues_eq_singularCourantFischerMaxMin_succ A.toEuclideanLin
      finrank_euclideanSpace ⟨Fintype.card n - 1, by omega⟩
    have hk : Fintype.card n - 1 + 1 = finrank ℝ (EuclideanSpace ℝ n) := by
      rw [finrank_euclideanSpace]
      omega
    rw [singularValues_toEuclideanLin]
    rw [key, hk, LinearMap.singularCourantFischerMaxMin_finrank,
      iInf_singularQuotient_toEuclideanLin]

/-- The first singular value is the `L²` operator norm. -/
theorem singularValues_zero_eq_l2_opNorm (A : Matrix m n ℝ) : A.singularValues 0 = ‖A‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim A 0]
    simp
  · have : Nonempty { x : EuclideanSpace ℝ n // x ≠ 0 } := by
      obtain ⟨x, hx⟩ := exists_ne (0 : EuclideanSpace ℝ n)
      exact ⟨⟨x, hx⟩⟩
    have key : A.toEuclideanLin.singularValues 0 =
        LinearMap.singularCourantFischerMaxMin A.toEuclideanLin 1 :=
      LinearMap.singularValues_eq_singularCourantFischerMaxMin_succ A.toEuclideanLin
        finrank_euclideanSpace ⟨0, Fintype.card_pos⟩
    have hbdd := LinearMap.bddAbove_range_singularQuotient A.toEuclideanLin
    rw [singularValues_toEuclideanLin, key, LinearMap.singularCourantFischerMaxMin_one,
      l2_opNorm_def]
    apply le_antisymm
    · refine ciSup_le fun x => ?_
      unfold LinearMap.singularQuotient
      rw [div_le_iff₀ (norm_pos_iff.mpr x.2)]
      exact ContinuousLinearMap.le_opNorm
        ((toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A) (x : EuclideanSpace ℝ n)
    · refine ContinuousLinearMap.opNorm_le_bound _
        (Real.iSup_nonneg fun x => div_nonneg (norm_nonneg _) (norm_nonneg _)) fun x => ?_
      by_cases hx : x = 0
      · simp [hx]
      have h := le_ciSup hbdd ⟨x, hx⟩
      unfold LinearMap.singularQuotient at h
      rwa [div_le_iff₀ (norm_pos_iff.mpr hx)] at h

/-- The smallest singular value is supermultiplicative: `σ_min(A) σ_min(B) ≤ σ_min(A B)`. -/
theorem minSingularValue_mul_le (A : Matrix m n ℝ) (B : Matrix n l ℝ) :
    A.minSingularValue * B.minSingularValue ≤ (A * B).minSingularValue := by
  rcases isEmpty_or_nonempty l with hl | hl
  · rw [B.minSingularValue_of_isEmpty, mul_zero]
    exact (A * B).minSingularValue_nonneg
  · refine (A * B).le_minSingularValue fun v hv => ?_
    calc A.minSingularValue * B.minSingularValue
        ≤ A.minSingularValue * ‖B.toEuclideanLin v‖ :=
          mul_le_mul_of_nonneg_left (B.minSingularValue_le_norm hv) A.minSingularValue_nonneg
      _ ≤ ‖A.toEuclideanLin (B.toEuclideanLin v)‖ := A.minSingularValue_mul_norm_le _
      _ = ‖(A * B).toEuclideanLin v‖ := by simp

/-- Trace-free Frobenius bound: `n σ_min(A)² ≤ ∑ᵢⱼ Aᵢⱼ²`. -/
theorem card_mul_minSingularValue_sq_le (A : Matrix m n ℝ) :
    Fintype.card n * A.minSingularValue ^ 2 ≤ ∑ i, ∑ j, A i j ^ 2 := by
  have h : ∀ j, A.minSingularValue ^ 2 ≤ ∑ i, A i j ^ 2 := by
    intro j
    have hnorm : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
    have h2 : ‖A.toEuclideanLin (EuclideanSpace.single j 1)‖ ^ 2 = ∑ i, A i j ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [toLpLin_apply]
    rw [← h2]
    exact pow_le_pow_left₀ A.minSingularValue_nonneg (A.minSingularValue_le_norm hnorm) 2
  rw [Finset.sum_comm]
  calc (Fintype.card n : ℝ) * A.minSingularValue ^ 2 = ∑ _j : n, A.minSingularValue ^ 2 := by
        simp
    _ ≤ ∑ j, ∑ i, A i j ^ 2 := Finset.sum_le_sum fun j _ => h j

/-! ## Lipschitz dependence on the entries -/

/-- Weyl's inequality for singular values with the `L²` operator norm, for every index. -/
theorem abs_singularValues_sub_le_l2_opNorm (A B : Matrix m n ℝ) (k : ℕ) :
    |A.singularValues k - B.singularValues k| ≤ ‖A - B‖ := by
  by_cases hk : k < Fintype.card n
  · have h := LinearMap.abs_singularValues_sub_le_opNorm A.toEuclideanLin B.toEuclideanLin
      finrank_euclideanSpace ⟨k, hk⟩
    rw [l2_opNorm_def, LinearEquiv.trans_apply, map_sub]
    exact h
  · rw [A.singularValues_of_card_le (not_lt.mp hk), B.singularValues_of_card_le (not_lt.mp hk),
      sub_self, abs_zero]
    exact norm_nonneg _

/-- Each singular value is `1`-Lipschitz for the `L²` operator norm. -/
theorem lipschitzWith_singularValues (k : ℕ) :
    LipschitzWith 1 fun A : Matrix m n ℝ => A.singularValues k :=
  LipschitzWith.of_dist_le_mul fun A B => by
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    exact abs_singularValues_sub_le_l2_opNorm A B k

/-- The smallest singular value is `1`-Lipschitz for the `L²` operator norm. -/
theorem lipschitzWith_minSingularValue :
    LipschitzWith 1 fun A : Matrix m n ℝ => A.minSingularValue := by
  have h : (fun A : Matrix m n ℝ => A.minSingularValue) =
      fun A => A.singularValues (Fintype.card n - 1) :=
    funext fun A => (singularValues_card_sub_one A).symm
  rw [h]
  exact lipschitzWith_singularValues _

/-- Right multiplication by `A` composed with the operator norm is `‖A‖`-Lipschitz. -/
theorem lipschitzWith_l2_opNorm_mul (A : Matrix n l ℝ) :
    LipschitzWith ‖A‖₊ fun B : Matrix m n ℝ => ‖B * A‖ :=
  LipschitzWith.of_dist_le_mul fun B C => by
    rw [Real.dist_eq, dist_eq_norm, coe_nnnorm]
    calc |‖B * A‖ - ‖C * A‖| ≤ ‖B * A - C * A‖ := abs_norm_sub_norm_le _ _
      _ = ‖(B - C) * A‖ := by rw [Matrix.sub_mul]
      _ ≤ ‖B - C‖ * ‖A‖ := l2_opNorm_mul _ _
      _ = ‖A‖ * ‖B - C‖ := mul_comm _ _

/-- Each singular value of a reshaped Euclidean vector is a `1`-Lipschitz function of it. -/
theorem lipschitzWith_singularValues_ofEuclidean (k : ℕ) :
    LipschitzWith 1 fun w : EuclideanSpace ℝ (m × n) => (ofEuclidean w).singularValues k := by
  have h := (lipschitzWith_singularValues (m := m) (n := n) k).comp lipschitzWith_ofEuclidean
  rw [mul_one] at h
  exact h

/-- The smallest singular value of a reshaped Euclidean vector is a `1`-Lipschitz function of
it. -/
theorem lipschitzWith_minSingularValue_ofEuclidean :
    LipschitzWith 1 fun w : EuclideanSpace ℝ (m × n) => (ofEuclidean w).minSingularValue := by
  have h := (lipschitzWith_minSingularValue (m := m) (n := n)).comp lipschitzWith_ofEuclidean
  rw [mul_one] at h
  exact h

/-- For a fixed `A`, `w ↦ ‖ofEuclidean w * A‖` is `‖A‖`-Lipschitz. -/
theorem lipschitzWith_l2_opNorm_ofEuclidean_mul (A : Matrix n l ℝ) :
    LipschitzWith ‖A‖₊ fun w : EuclideanSpace ℝ (m × n) => ‖ofEuclidean w * A‖ := by
  have h := (lipschitzWith_l2_opNorm_mul (m := m) A).comp lipschitzWith_ofEuclidean
  rw [mul_one] at h
  exact h

end Matrix
