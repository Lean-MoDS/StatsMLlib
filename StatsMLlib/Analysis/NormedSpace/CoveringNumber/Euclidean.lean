/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import StatsMLlib.Topology.MetricSpace.CoveringNumber.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Covering Numbers of Euclidean Balls

We prove the standard covering number bound: for the Euclidean ball B_2^d(R) of radius R
in d dimensions, the covering number satisfies:

  N(ε, B_2^d(R)) ≤ (1 + 2R/ε)^d

## Main definitions

* `euclideanBall`: a closed Euclidean ball centered at zero.

## Main results

* `coveringNumber_euclideanBall_le`: volumetric covering-number bound.
-/

section EuclideanBall

open MeasureTheory Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The closed Euclidean ball of radius R centered at 0 in EuclideanSpace ℝ ι. -/
abbrev euclideanBall (R : ℝ) : Set (EuclideanSpace ℝ ι) := Metric.closedBall 0 R

omit [Nonempty ι] in
/-- The Euclidean ball is totally bounded (since it's compact in finite dimensions). -/
lemma euclideanBall_totallyBounded (R : ℝ) : TotallyBounded (euclideanBall R : Set (EuclideanSpace ℝ ι)) :=
  (ProperSpace.isCompact_closedBall 0 R).totallyBounded

omit [Nonempty ι] in
/-- The Euclidean ball is nonempty for non-negative radius. -/
lemma euclideanBall_nonempty {R : ℝ} (hR : 0 ≤ R) : (euclideanBall R : Set (EuclideanSpace ℝ ι)).Nonempty :=
  ⟨0, Metric.mem_closedBall_self hR⟩

/-- If points x and y are ε-separated (dist x y > ε), then the closed balls of radius ε/2
    around them are disjoint. -/
lemma closedBall_half_disjoint {E : Type*} [PseudoMetricSpace E] {x y : E} {eps : ℝ}
    (_heps : 0 ≤ eps) (hsep : eps < dist x y) :
    Disjoint (Metric.closedBall x (eps / 2)) (Metric.closedBall y (eps / 2)) := by
  apply Metric.closedBall_disjoint_closedBall
  calc eps / 2 + eps / 2 = eps := by ring
    _ < dist x y := hsep

/-- For a packing, the half-radius balls around distinct points are pairwise disjoint. -/
lemma packing_halfBalls_pairwiseDisjoint {E : Type*} [PseudoMetricSpace E]
    {t : Finset E} {eps : ℝ} {s : Set E}
    (heps : 0 ≤ eps) (hpacking : IsPacking t eps s) :
    (t : Set E).PairwiseDisjoint (fun x => Metric.closedBall x (eps / 2)) := by
  intro x hx y hy hxy
  have hsep := hpacking.2 hx hy hxy
  exact closedBall_half_disjoint heps hsep

/-- A half-radius ball around a point in closedBall(0, R) is contained in closedBall(0, R + eps/2). -/
lemma halfBall_subset_enlargedBall {E : Type*} [SeminormedAddCommGroup E]
    {x : E} {R eps : ℝ} (hx : x ∈ Metric.closedBall (0 : E) R) :
    Metric.closedBall x (eps / 2) ⊆ Metric.closedBall (0 : E) (R + eps / 2) := by
  intro z hz
  rw [Metric.mem_closedBall] at hx hz ⊢
  simp only [dist_zero_right] at hx ⊢
  have h1 : ‖z‖ = ‖z - x + x‖ := by simp
  calc ‖z‖ = ‖z - x + x‖ := h1
    _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
    _ = dist z x + ‖x‖ := by rw [dist_eq_norm]
    _ ≤ eps / 2 + R := by linarith [hz, hx]
    _ = R + eps / 2 := by ring

/-- Union of half-balls around a packing in B(0, R) is contained in B(0, R + eps/2). -/
lemma packing_halfBalls_subset {E : Type*} [SeminormedAddCommGroup E]
    {t : Finset E} {R eps : ℝ} {s : Set E}
    (hpacking : IsPacking t eps s) (hs : s ⊆ Metric.closedBall (0 : E) R) :
    (⋃ x ∈ t, Metric.closedBall x (eps / 2)) ⊆ Metric.closedBall (0 : E) (R + eps / 2) := by
  intro z hz
  rw [Set.mem_iUnion₂] at hz
  obtain ⟨x, hxt, hzx⟩ := hz
  have hxs : x ∈ s := hpacking.1 hxt
  have hxR : x ∈ Metric.closedBall (0 : E) R := hs hxs
  exact halfBall_subset_enlargedBall hxR hzx

omit [Nonempty ι] in
/-- Key volume lemma: The volume of disjoint half-balls equals the sum of individual volumes. -/
lemma volume_disjoint_union_closedBalls
    {t : Finset (EuclideanSpace ℝ ι)} {eps : ℝ} (_heps : 0 ≤ eps)
    (hpwd : (t : Set (EuclideanSpace ℝ ι)).PairwiseDisjoint
        (fun x => Metric.closedBall x (eps / 2))) :
    MeasureTheory.volume (⋃ x ∈ t, Metric.closedBall x (eps / 2)) =
    ∑ x ∈ t, MeasureTheory.volume (Metric.closedBall x (eps / 2)) := by
  have hmeas : ∀ b ∈ t, MeasurableSet (Metric.closedBall b (eps / 2)) :=
    fun _ _ => measurableSet_closedBall
  exact measure_biUnion_finset hpwd hmeas

/-- The volume of a closed ball in EuclideanSpace is proportional to r^d. -/
lemma volume_closedBall_euclidean (x : EuclideanSpace ℝ ι) (r : ℝ) :
    MeasureTheory.volume (Metric.closedBall x r) =
    ENNReal.ofReal r ^ (Fintype.card ι) *
      ENNReal.ofReal (Real.pi.sqrt ^ Fintype.card ι /
        Real.Gamma (Fintype.card ι / 2 + 1)) :=
  EuclideanSpace.volume_closedBall ι x r

/-- The constant factor in the volume of a unit ball. -/
noncomputable def euclideanBallVolumeConst (d : ℕ) : ℝ :=
  Real.pi.sqrt ^ d / Real.Gamma (d / 2 + 1)

lemma euclideanBallVolumeConst_pos (d : ℕ) : 0 < euclideanBallVolumeConst d := by
  unfold euclideanBallVolumeConst
  apply div_pos
  · exact pow_pos (Real.sqrt_pos.mpr Real.pi_pos) d
  · have h : (0 : ℝ) < (d : ℝ) / 2 + 1 := by positivity
    exact Real.Gamma_pos_of_pos h

/-- The volume of a closed ball with radius r equals r^d times the unit ball volume. -/
lemma volume_closedBall_eq_rpow (x : EuclideanSpace ℝ ι) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume (Metric.closedBall x r) =
    ENNReal.ofReal (r ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι)) := by
  rw [volume_closedBall_euclidean]
  have hr_pow : ENNReal.ofReal r ^ Fintype.card ι = ENNReal.ofReal (r ^ Fintype.card ι) := by
    induction Fintype.card ι with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      rw [mul_comm (ENNReal.ofReal _) (ENNReal.ofReal r)]
      rw [← ENNReal.ofReal_mul hr]
      rw [mul_comm r (r ^ n)]
  rw [hr_pow]
  unfold euclideanBallVolumeConst
  rw [← ENNReal.ofReal_mul (pow_nonneg hr _)]

/-- Key cardinality bound: For a packing in B(0, R), we have
    |t| ≤ ((R + ε/2) / (ε/2))^d = (1 + 2R/ε)^d -/
lemma packing_card_bound_aux
    {t : Finset (EuclideanSpace ℝ ι)} {R eps : ℝ}
    (hR : 0 ≤ R) (heps : 0 < eps)
    (hpacking : IsPacking t eps (euclideanBall R)) :
    (t.card : ℝ) ≤ ((R + eps / 2) / (eps / 2)) ^ Fintype.card ι := by
  -- The half-balls are pairwise disjoint
  have hpwd := packing_halfBalls_pairwiseDisjoint (le_of_lt heps) hpacking
  -- They are contained in the larger ball
  have hsub := packing_halfBalls_subset hpacking (le_refl _)
  -- Volume of union = sum of volumes
  have hvol_eq := volume_disjoint_union_closedBalls (le_of_lt heps) hpwd
  -- Volume of union ≤ volume of containing ball
  have hvol_le : MeasureTheory.volume (⋃ x ∈ t, Metric.closedBall x (eps / 2)) ≤
      MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ ι) (R + eps / 2)) :=
    MeasureTheory.measure_mono hsub
  -- Each ball has the same volume
  have heps_half_pos : 0 < eps / 2 := by linarith
  have heps_half_nonneg : 0 ≤ eps / 2 := le_of_lt heps_half_pos
  have hR_plus_pos : 0 ≤ R + eps / 2 := by linarith
  -- Volume of each small ball
  have hvol_small : ∀ x : EuclideanSpace ℝ ι, MeasureTheory.volume (Metric.closedBall x (eps / 2)) =
      ENNReal.ofReal ((eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι)) :=
    fun x => volume_closedBall_eq_rpow x (eps / 2) heps_half_nonneg
  -- Volume of large ball
  have hvol_large : MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ ι) (R + eps / 2)) =
      ENNReal.ofReal ((R + eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι)) :=
    volume_closedBall_eq_rpow 0 (R + eps / 2) hR_plus_pos
  -- Sum of small ball volumes
  have hvol_sum : ∑ x ∈ t, MeasureTheory.volume (Metric.closedBall x (eps / 2)) =
      t.card * ENNReal.ofReal ((eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι)) := by
    simp only [hvol_small]
    rw [sum_const]
    simp only [nsmul_eq_mul]
  -- Combine: t.card * vol_small ≤ vol_large
  rw [hvol_eq, hvol_sum] at hvol_le
  rw [hvol_large] at hvol_le
  -- Convert to real inequality
  have hconst_pos := euclideanBallVolumeConst_pos (Fintype.card ι)
  have hsmall_pos : 0 < (eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι) :=
    mul_pos (pow_pos heps_half_pos _) hconst_pos
  have hlarge_pos : 0 < (R + eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι) :=
    mul_pos (pow_pos (by linarith : 0 < R + eps / 2) _) hconst_pos
  have hlarge_nonneg : 0 ≤ (R + eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι) :=
    le_of_lt hlarge_pos
  -- Use ENNReal.ofReal for the bound
  have h : t.card * ENNReal.ofReal ((eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι)) ≤
      ENNReal.ofReal ((R + eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι)) := hvol_le
  rw [← ENNReal.ofReal_natCast] at h
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h
  have h' := ENNReal.ofReal_le_ofReal_iff hlarge_nonneg |>.mp h
  -- Simplify: t.card * vol_small ≤ vol_large gives t.card ≤ vol_large / vol_small
  have hdiv : t.card * ((eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι)) ≤
      (R + eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι) := h'
  have hcancel : (t.card : ℝ) ≤ (R + eps / 2) ^ Fintype.card ι / (eps / 2) ^ Fintype.card ι := by
    have hne : (eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι) ≠ 0 :=
      ne_of_gt hsmall_pos
    have hsmall_nonneg : 0 ≤ (eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι) :=
      le_of_lt hsmall_pos
    calc (t.card : ℝ)
      _ = t.card * ((eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι)) /
          ((eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι)) := by
        rw [mul_div_cancel_right₀ _ hne]
      _ ≤ (R + eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι) /
          ((eps / 2) ^ Fintype.card ι * euclideanBallVolumeConst (Fintype.card ι)) := by
        apply div_le_div_of_nonneg_right hdiv hsmall_nonneg
      _ = (R + eps / 2) ^ Fintype.card ι / (eps / 2) ^ Fintype.card ι := by
        rw [mul_div_mul_right _ _ (ne_of_gt hconst_pos)]
  have hdiv_eq : (R + eps / 2) ^ Fintype.card ι / (eps / 2) ^ Fintype.card ι =
      ((R + eps / 2) / (eps / 2)) ^ Fintype.card ι := by
    rw [← div_pow]
  rw [hdiv_eq] at hcancel
  exact hcancel

/-- Main bound: For a packing, |t| ≤ (1 + 2R/ε)^d. -/
lemma packing_card_bound
    {t : Finset (EuclideanSpace ℝ ι)} {R eps : ℝ}
    (hR : 0 ≤ R) (heps : 0 < eps)
    (hpacking : IsPacking t eps (euclideanBall R)) :
    (t.card : ℝ) ≤ (1 + 2 * R / eps) ^ Fintype.card ι := by
  have h := packing_card_bound_aux hR heps hpacking
  have heq : (R + eps / 2) / (eps / 2) = 1 + 2 * R / eps := by
    field_simp
    ring
  rw [heq] at h
  exact h

/-- A maximal packing is an ε-net: if no point of s can be added while maintaining
    ε-separation, then the packing is an ε-net. -/
lemma maximal_packing_isENet {E : Type*} [PseudoMetricSpace E]
    {t : Finset E} {eps : ℝ} {s : Set E}
    (heps : 0 ≤ eps)
    (_hpacking : IsPacking t eps s)
    (hmaximal : ∀ x ∈ s, x ∉ t → ∃ y ∈ t, dist x y ≤ eps) :
    IsENet t eps s :=
  isENet_of_maximal heps hmaximal

/-- Any ε-separated subset of a totally bounded set is finite. -/
lemma separated_finite_of_totallyBounded {E : Type*} [PseudoMetricSpace E]
    {s : Set E} {eps : ℝ} (heps : 0 < eps) (hs : TotallyBounded s)
    {t : Set E} (ht_sub : t ⊆ s) (ht_sep : t.Pairwise (fun x y => eps < dist x y)) :
    t.Finite := by
  -- If s is covered by finitely many ε/2-balls, any ε-separated set has bounded cardinality
  have heps2 : 0 < eps / 2 := by linarith
  obtain ⟨cover, _, hcover_finite, hcover⟩ := Metric.finite_approx_of_totallyBounded hs (eps / 2) heps2
  -- Each ε/2-ball can contain at most one point from t
  -- Define a function from t to cover: for each x ∈ t, pick a c ∈ cover with x ∈ ball(c, eps/2)
  classical
  have hmaps : ∀ x ∈ t, ∃ c ∈ cover, x ∈ Metric.ball c (eps / 2) := fun x hx => by
    have hxs := ht_sub hx
    have := hcover hxs
    simp only [Set.mem_iUnion] at this
    obtain ⟨c, hc, hxball⟩ := this
    exact ⟨c, hc, hxball⟩
  -- This function is injective
  let f : t → cover := fun ⟨x, hx⟩ => ⟨(hmaps x hx).choose, (hmaps x hx).choose_spec.1⟩
  have hf_inj : Function.Injective f := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ heq
    simp only [f, Subtype.mk.injEq] at heq
    -- If f x = f y = c, then x, y ∈ ball(c, eps/2), so dist x y < eps
    have hxc := (hmaps x hx).choose_spec.2
    have hyc : y ∈ Metric.ball (hmaps y hy).choose (eps / 2) := (hmaps y hy).choose_spec.2
    by_cases hxy : x = y
    · exact Subtype.ext hxy
    · exfalso
      have hsep_xy := ht_sep hx hy hxy
      have hdist : dist x y < eps := by
        have heq' : (hmaps x hx).choose = (hmaps y hy).choose := heq
        calc dist x y ≤ dist x (hmaps x hx).choose + dist (hmaps x hx).choose y := dist_triangle _ _ _
          _ < eps / 2 + eps / 2 := by
            apply add_lt_add
            · exact Metric.mem_ball.mp hxc
            · rw [heq', dist_comm]; exact Metric.mem_ball.mp hyc
          _ = eps := by ring
      linarith
  -- cover is finite, so t is finite via the injection
  have hfin_cover : Finite cover := hcover_finite
  have hfin_t : Finite t := Finite.of_injective f hf_inj
  exact Set.finite_coe_iff.mp hfin_t

/-- The existence of a maximal packing in a totally bounded set. -/
lemma exists_maximal_packing {E : Type*} [PseudoMetricSpace E]
    {s : Set E} (eps : ℝ) (heps : 0 < eps) (hs : TotallyBounded s) :
    ∃ t : Finset E, IsPacking t eps s ∧
      (∀ x ∈ s, x ∉ t → ∃ y ∈ t, dist x y ≤ eps) := by
  classical
  -- Get the cover that bounds packing sizes
  have heps2 : 0 < eps / 2 := by linarith
  obtain ⟨cover, _, hcover_finite, hcover⟩ := Metric.finite_approx_of_totallyBounded hs (eps / 2) heps2
  -- Any packing has size at most |cover|
  have hbound : ∀ t : Finset E, IsPacking t eps s → t.card ≤ cover.ncard := by
    intro t ht
    have ht_sep : (t : Set E).Pairwise (fun x y => eps < dist x y) := ht.2
    have hmaps : ∀ x ∈ t, ∃ c ∈ cover, x ∈ Metric.ball c (eps / 2) := fun x hx => by
      have hxs := ht.1 hx
      have := hcover hxs
      simp only [Set.mem_iUnion] at this
      obtain ⟨c, hc, hxball⟩ := this
      exact ⟨c, hc, hxball⟩
    let f : t → cover := fun ⟨x, hx⟩ => ⟨(hmaps x hx).choose, (hmaps x hx).choose_spec.1⟩
    have hf_inj : Function.Injective f := by
      intro ⟨x, hx⟩ ⟨y, hy⟩ heq
      simp only [f, Subtype.mk.injEq] at heq
      have hxc := (hmaps x hx).choose_spec.2
      have hyc : y ∈ Metric.ball (hmaps y hy).choose (eps / 2) := (hmaps y hy).choose_spec.2
      by_cases hxy : x = y
      · exact Subtype.ext hxy
      · exfalso
        have hsep_xy := ht_sep hx hy hxy
        have heq' : (hmaps x hx).choose = (hmaps y hy).choose := heq
        have hdist : dist x y < eps := by
          calc dist x y ≤ dist x (hmaps x hx).choose + dist (hmaps x hx).choose y := dist_triangle _ _ _
            _ < eps / 2 + eps / 2 := by
              apply add_lt_add
              · exact Metric.mem_ball.mp hxc
              · rw [heq', dist_comm]; exact Metric.mem_ball.mp hyc
            _ = eps := by ring
        linarith
    have : Finite cover := hcover_finite
    have : Fintype cover := Fintype.ofFinite cover
    calc t.card = Fintype.card t := by rw [Fintype.card_coe]
      _ ≤ Fintype.card cover := Fintype.card_le_of_injective f hf_inj
      _ = cover.ncard := by
          rw [Set.ncard_eq_toFinset_card cover]
          simp [Set.toFinset_card]
  -- Construct maximal packing by induction on (bound - current_size)
  let bound := cover.ncard
  -- Iterate: if current packing is not maximal, extend it
  have iterate : ∀ n : ℕ, ∀ t : Finset E, IsPacking t eps s → bound - t.card = n →
      ∃ t' : Finset E, t ⊆ t' ∧ IsPacking t' eps s ∧
        (∀ x ∈ s, x ∉ t' → ∃ y ∈ t', dist x y ≤ eps) := by
    intro n
    induction n with
    | zero =>
      intro t ht_pack heq
      -- bound - t.card = 0, so t.card ≥ bound, hence t must be maximal
      use t, Finset.Subset.refl t, ht_pack
      intro x hxs hxt
      by_contra h
      push Not at h
      -- x is ε-separated from t, so we could add x
      have hx_sep : ∀ y ∈ t, eps < dist x y := fun y hy => h y hy
      have ht'_pack : IsPacking (insert x t) eps s := by
        constructor
        · intro y hy
          rw [Finset.mem_coe, Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · exact hxs
          · exact ht_pack.1 hy
        · intro y hy z hz hyz
          rw [Finset.mem_coe, Finset.mem_insert] at hy hz
          rcases hy with rfl | hy <;> rcases hz with rfl | hz
          · exact absurd rfl hyz
          · exact hx_sep z hz
          · rw [dist_comm]; exact hx_sep y hy
          · exact ht_pack.2 hy hz hyz
      have h_bound := hbound (insert x t) ht'_pack
      have h_card : (insert x t).card = t.card + 1 := Finset.card_insert_of_notMem hxt
      omega
    | succ n ih =>
      intro t ht_pack heq
      by_cases hmaximal : ∀ x ∈ s, x ∉ t → ∃ y ∈ t, dist x y ≤ eps
      · use t, Finset.Subset.refl t, ht_pack, hmaximal
      · push Not at hmaximal
        obtain ⟨x, hxs, hxt, hx_sep⟩ := hmaximal
        -- Add x to get a larger packing
        have ht'_pack : IsPacking (insert x t) eps s := by
          constructor
          · intro y hy
            rw [Finset.mem_coe, Finset.mem_insert] at hy
            rcases hy with rfl | hy
            · exact hxs
            · exact ht_pack.1 hy
          · intro y hy z hz hyz
            rw [Finset.mem_coe, Finset.mem_insert] at hy hz
            rcases hy with rfl | hy <;> rcases hz with rfl | hz
            · exact absurd rfl hyz
            · have := hx_sep z hz; linarith
            · have := hx_sep y hy; rw [dist_comm]; linarith
            · exact ht_pack.2 hy hz hyz
        have h_card : (insert x t).card = t.card + 1 := Finset.card_insert_of_notMem hxt
        have h_gap : bound - (insert x t).card = n := by omega
        obtain ⟨t'', ht''_sub, ht''_pack, ht''_max⟩ := ih (insert x t) ht'_pack h_gap
        exact ⟨t'', Finset.Subset.trans (Finset.subset_insert x t) ht''_sub, ht''_pack, ht''_max⟩
  -- Apply with empty packing
  have hempty_pack : IsPacking (∅ : Finset E) eps s := by
    constructor
    · simp
    · simp
  have hgap : bound - (∅ : Finset E).card = bound := by simp
  obtain ⟨t, _, ht_pack, ht_max⟩ := iterate bound ∅ hempty_pack hgap
  exact ⟨t, ht_pack, ht_max⟩

/-- On a totally bounded set the covering number is at most the packing number at the same
radius: a maximal packing exists and is an `eps`-net.  Together with
`packingNumber_two_mul_le_coveringNumber` this is the two-sided comparison
`M(2 eps) ≤ N(eps) ≤ M(eps)`. -/
lemma coveringNumber_le_packingNumber {E : Type*} [PseudoMetricSpace E]
    {s : Set E} {eps : ℝ} (heps : 0 < eps) (hs : TotallyBounded s) :
    coveringNumber eps s ≤ packingNumber eps s := by
  obtain ⟨t, ht, hmax⟩ := exists_maximal_packing eps heps hs
  exact coveringNumber_le_packingNumber_of_maximal heps.le ht hmax

/-- The covering number of the Euclidean ball B(0, R) satisfies N(ε, B(0,R)) ≤ (1 + 2R/ε)^d.
    The metric (2-norm) is implicitly determined by the type EuclideanSpace ℝ ι.
    This version casts the covering number to ℝ for a clean bound without ceilings. -/
theorem coveringNumber_euclideanBall_le {R eps : ℝ} (hR : 0 ≤ R) (heps : 0 < eps) :
    ((coveringNumber eps (euclideanBall R : Set (EuclideanSpace ℝ ι))).untop
        (ne_top_of_lt (coveringNumber_lt_top_of_totallyBounded heps
          (euclideanBall_totallyBounded R))) : ℝ) ≤
    (1 + 2 * R / eps) ^ Fintype.card ι := by
  have htb := euclideanBall_totallyBounded (ι := ι) R
  -- Get a maximal packing, which is also an ε-net
  obtain ⟨t, ht_pack, ht_max⟩ := exists_maximal_packing eps heps htb
  -- The maximal packing is an ε-net
  have ht_net : IsENet t eps (euclideanBall R) := isENet_of_maximal (le_of_lt heps) ht_max
  -- The covering number is at most t.card
  have hcov_le : coveringNumber eps (euclideanBall R : Set (EuclideanSpace ℝ ι)) ≤ t.card :=
    coveringNumber_le_card ht_net
  -- By the packing bound, t.card ≤ (1 + 2R/ε)^d
  have hpack_bound : (t.card : ℝ) ≤ (1 + 2 * R / eps) ^ Fintype.card ι :=
    packing_card_bound hR heps ht_pack
  -- Extract the natural number from the covering number
  have htop : coveringNumber eps (euclideanBall R : Set (EuclideanSpace ℝ ι)) < ⊤ :=
    coveringNumber_lt_top_of_totallyBounded heps htb
  obtain ⟨n, hn⟩ := WithTop.untop_of_lt_top htop
  simp only [hn]
  -- n ≤ t.card from hcov_le, and t.card ≤ bound from hpack_bound
  have hn_le_card : n ≤ t.card := by
    rw [hn] at hcov_le
    exact WithTop.coe_le_coe.mp hcov_le
  calc (n : ℝ) ≤ t.card := by exact_mod_cast hn_le_card
    _ ≤ (1 + 2 * R / eps) ^ Fintype.card ι := hpack_bound

end EuclideanBall
