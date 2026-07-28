/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Nat.WithBot
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Covering and Packing Numbers

Basic definitions of epsilon-nets, covering numbers, and packing numbers for pseudo-metric spaces.

## Main definitions

* `IsENet`, `coveringNumber`: finite metric covers and their minimal cardinality.
* `IsPacking`, `packingNumber`: finite separated subsets and their maximal cardinality.
* `coveringNumberNat`, `coveringFinset`: finite views for totally bounded sets.

## Main results

* `coveringNumber_lt_top_of_totallyBounded`: finiteness at positive radius.
* `coveringNumber_image_le_of_lipschitz`: covering numbers under Lipschitz maps.
-/

noncomputable section

open Set Metric
open scoped BigOperators
open Classical

/-- `t` is an `eps`-net for `s` if every point of `s` lies in a closed ball of radius `eps`
centered at some element of `t`. We use closed balls to avoid side conditions when `eps = 0`. -/
def IsENet {A : Type*} [PseudoMetricSpace A] (t : Finset A) (eps : ℝ) (s : Set A) : Prop :=
  s ⊆ ⋃ x ∈ t, closedBall x eps

/-- Covering number: the minimal cardinality of a finite `eps`-net, as `WithTop Nat` (`⊤` if no
finite net exists). -/
def coveringNumber {A : Type*} [PseudoMetricSpace A] (eps : ℝ) (s : Set A) : WithTop Nat :=
  sInf {n : WithTop Nat | ∃ t : Finset A, IsENet t eps s ∧ (t.card : WithTop Nat) = n}

/-- `t` is an `eps`-packing for `s` if it is contained in `s` and any two distinct points are
`eps`-separated. -/
def IsPacking {A : Type*} [PseudoMetricSpace A] (t : Finset A) (eps : ℝ) (s : Set A) : Prop :=
  (↑t ⊆ s) ∧ (t : Set A).Pairwise (fun x y => eps < dist x y)

/-- Packing number: the maximal cardinality of a finite `eps`-packing, as `WithTop Nat` (`⊤` if
unbounded). -/
def packingNumber {A : Type*} [PseudoMetricSpace A] (eps : ℝ) (s : Set A) : WithTop Nat :=
  sSup {n : WithTop Nat | ∃ t : Finset A, IsPacking t eps s ∧ (t.card : WithTop Nat) = n}

lemma coveringNumber_le_card {A : Type*} [PseudoMetricSpace A] {t : Finset A} {eps : ℝ} {s : Set A}
    (h : IsENet t eps s) : coveringNumber eps s ≤ (t.card : WithTop Nat) := by
  unfold coveringNumber
  have : (t.card : WithTop Nat) ∈
      {n : WithTop Nat | ∃ t : Finset A, IsENet t eps s ∧ (t.card : WithTop Nat) = n} :=
    ⟨t, h, rfl⟩
  simpa using (sInf_le this)

lemma coveringNumber_empty {A : Type*} [PseudoMetricSpace A] (eps : ℝ) :
    coveringNumber eps (∅ : Set A) = 0 := by
  refine le_antisymm ?upper ?lower
  · have hnet : IsENet (∅ : Finset A) eps (∅ : Set A) := by
      intro x hx
      cases hx
    simpa using (coveringNumber_le_card hnet)
  · exact bot_le

/-!
## Basic properties of epsilon-nets and covering numbers
-/

variable {A : Type*} [PseudoMetricSpace A]

/-- If `t` is an `eps1`-net and `eps1 ≤ eps2`, then `t` is also an `eps2`-net. -/
lemma IsENet.mono_eps {t : Finset A} {eps1 eps2 : ℝ} {s : Set A}
    (h : IsENet t eps1 s) (heps : eps1 ≤ eps2) : IsENet t eps2 s := by
  intro x hx
  obtain ⟨y, hy_mem, hy_dist⟩ := mem_iUnion₂.mp (h hx)
  exact mem_iUnion₂.mpr ⟨y, hy_mem, closedBall_subset_closedBall heps hy_dist⟩

/-- Covering number is anti-monotone in epsilon: larger epsilon means smaller covering number. -/
lemma coveringNumber_anti_eps {eps1 eps2 : ℝ} {s : Set A}
    (heps : eps1 ≤ eps2) : coveringNumber eps2 s ≤ coveringNumber eps1 s := by
  unfold coveringNumber
  apply sInf_le_sInf
  intro n hn
  obtain ⟨t, ht_net, ht_card⟩ := hn
  exact ⟨t, ht_net.mono_eps heps, ht_card⟩

/-- Covering number is monotone in the set: larger set means larger covering number. -/
lemma coveringNumber_mono_set {eps : ℝ} {s t : Set A}
    (h : s ⊆ t) : coveringNumber eps s ≤ coveringNumber eps t := by
  unfold coveringNumber
  apply sInf_le_sInf
  intro n hn
  obtain ⟨net, hnet, hcard⟩ := hn
  exact ⟨net, fun x hx => hnet (h hx), hcard⟩

/-- A singleton has covering number at most 1. -/
lemma coveringNumber_singleton {a : A} {eps : ℝ} (heps : 0 ≤ eps) :
    coveringNumber eps {a} ≤ 1 := by
  have hnet : IsENet {a} eps {a} := by
    intro x hx
    rw [mem_singleton_iff] at hx
    rw [hx]
    exact mem_iUnion₂.mpr ⟨a, Finset.mem_singleton_self a, mem_closedBall_self heps⟩
  simpa [Finset.card_singleton] using coveringNumber_le_card hnet

/-!
## Properties relating covering and packing numbers
-/

/-- A maximal packing is a covering: if no point of `s` can be added to a packing `t`,
    then `t` is an `eps`-net for `s`. Requires `eps ≥ 0` for the closed ball condition. -/
lemma isENet_of_maximal {t : Finset A} {eps : ℝ} {s : Set A}
    (heps : 0 ≤ eps)
    (hmax : ∀ a ∈ s, a ∉ t → ∃ x ∈ t, dist a x ≤ eps) :
    IsENet t eps s := by
  intro a ha
  by_cases hat : a ∈ t
  · exact mem_iUnion₂.mpr ⟨a, hat, mem_closedBall_self heps⟩
  · obtain ⟨x, hx_mem, hx_dist⟩ := hmax a ha hat
    exact mem_iUnion₂.mpr ⟨x, hx_mem, mem_closedBall.mpr hx_dist⟩

/-!
## Covering numbers for totally bounded sets
-/

/-- For a totally bounded set, the covering number is finite for any positive epsilon. -/
lemma coveringNumber_lt_top_of_totallyBounded {eps : ℝ} {s : Set A}
    (heps : 0 < eps) (hs : TotallyBounded s) :
    coveringNumber eps s < ⊤ := by
  -- TotallyBounded gives us a finite cover by open balls
  obtain ⟨t, ht_sub, ht_finite, ht_cover⟩ := finite_approx_of_totallyBounded hs eps heps
  -- Convert to a Finset
  let t' : Finset A := ht_finite.toFinset
  -- The open ball cover implies a closed ball cover (with same radius)
  have hnet : IsENet t' eps s := by
    intro x hx
    have hx_cover := ht_cover hx
    rw [mem_iUnion₂] at hx_cover
    obtain ⟨y, hy_mem, hy_ball⟩ := hx_cover
    refine mem_iUnion₂.mpr ⟨y, ?_, mem_closedBall.mpr (le_of_lt (mem_ball.mp hy_ball))⟩
    exact ht_finite.mem_toFinset.mpr hy_mem
  calc coveringNumber eps s ≤ (t'.card : WithTop ℕ) := coveringNumber_le_card hnet
    _ < ⊤ := WithTop.coe_lt_top t'.card

/-- Helper: extract a natural number from a finite WithTop ℕ -/
lemma WithTop.untop_of_lt_top {n : WithTop ℕ} (h : n < ⊤) : ∃ m : ℕ, n = m := by
  cases n with
  | top => simp at h
  | coe m => exact ⟨m, rfl⟩

/-- For a totally bounded set, there exists a finite epsilon-net with points in s. -/
lemma exists_finset_isENet_subset_of_totallyBounded {eps : ℝ} {s : Set A}
    (heps : 0 < eps) (hs : TotallyBounded s) :
    ∃ t : Finset A, IsENet t eps s ∧ (t : Set A) ⊆ s := by
  obtain ⟨t, ht_sub, ht_finite, ht_cover⟩ := finite_approx_of_totallyBounded hs eps heps
  let t' : Finset A := ht_finite.toFinset
  refine ⟨t', ?_, ?_⟩
  · -- IsENet property
    intro x hx
    have hx_cover := ht_cover hx
    rw [mem_iUnion₂] at hx_cover
    obtain ⟨y, hy_mem, hy_ball⟩ := hx_cover
    refine mem_iUnion₂.mpr ⟨y, ?_, mem_closedBall.mpr (le_of_lt (mem_ball.mp hy_ball))⟩
    exact ht_finite.mem_toFinset.mpr hy_mem
  · -- Subset property
    intro x hx
    simp only [Finset.mem_coe] at hx
    exact ht_sub (ht_finite.mem_toFinset.mp hx)

/-- For a totally bounded set, there exists a finite epsilon-net. -/
lemma exists_finset_isENet_of_totallyBounded {eps : ℝ} {s : Set A}
    (heps : 0 < eps) (hs : TotallyBounded s) :
    ∃ t : Finset A, IsENet t eps s :=
  (exists_finset_isENet_subset_of_totallyBounded heps hs).imp fun _ h => h.1

/-- For a totally bounded set, there exists an optimal epsilon-net whose cardinality
    equals the covering number. -/
lemma exists_optimal_enet {eps : ℝ} {s : Set A}
    (heps : 0 < eps) (hs : TotallyBounded s) :
    ∃ t : Finset A, IsENet t eps s ∧ (t.card : WithTop ℕ) = coveringNumber eps s := by
  -- The set of cardinalities of eps-nets is nonempty
  have hne_set : {n : WithTop ℕ | ∃ t : Finset A, IsENet t eps s ∧ (t.card : WithTop ℕ) = n}.Nonempty := by
    obtain ⟨t, ht⟩ := exists_finset_isENet_of_totallyBounded heps hs
    exact ⟨t.card, t, ht, rfl⟩
  exact csInf_mem hne_set

/-- For an optimal epsilon-net, the cardinality equals the covering number as a natural number. -/
lemma exists_optimal_enet_nat {eps : ℝ} {s : Set A}
    (heps : 0 < eps) (hs : TotallyBounded s) :
    ∃ t : Finset A, IsENet t eps s ∧ (t.card : ℕ) = (coveringNumber eps s).untop
        (ne_top_of_lt (coveringNumber_lt_top_of_totallyBounded heps hs)) := by
  obtain ⟨t, ht_net, ht_card⟩ := exists_optimal_enet heps hs
  exact ⟨t, ht_net, WithTop.coe_injective (ht_card.trans (WithTop.coe_untop _ _).symm)⟩

/-- An eps-net inside s can be constructed from an (eps/2)-net by projecting points to s.
    For any (eps/2)-net t (possibly outside s), we project each point x ∈ t to some
    representative f(x) ∈ s ∩ closedBall(x, eps/2). The image f(t) is an eps-net for s
    contained in s (by triangle inequality: eps/2 + eps/2 = eps), with |f(t)| ≤ |t|. -/
lemma exists_enet_subset_from_half {eps : ℝ} {s : Set A}
    (heps : 0 < eps) (hs : TotallyBounded s) (hsne : s.Nonempty) :
    ∃ t : Finset A, IsENet t eps s ∧ (t : Set A) ⊆ s ∧
      (t.card : WithTop ℕ) ≤ coveringNumber (eps / 2) s := by
  have heps2 : 0 < eps / 2 := by linarith
  -- Get an optimal (eps/2)-net (which may have points outside s)
  obtain ⟨net, hnet_isNet, hnet_card⟩ := exists_optimal_enet heps2 hs
  -- hnet_card : net.card = coveringNumber(eps/2, s)
  obtain ⟨s₀, hs₀⟩ := hsne
  -- Define the projection: for x, if closedBall(x, eps/2) ∩ s is nonempty, pick an element
  -- Otherwise use s₀ (this case won't affect the covering property)
  let proj : A → A := fun x =>
    if h : (s ∩ closedBall x (eps / 2)).Nonempty then h.some else s₀
  -- Project the net to s
  let t' := net.image proj
  refine ⟨t', ?_, ?_, ?_⟩
  -- 1. t' is an eps-net for s
  · intro y hy
    -- y ∈ s, so by hnet_isNet, ∃ x ∈ net with y ∈ closedBall(x, eps/2)
    have hy_covered := hnet_isNet hy
    rw [mem_iUnion₂] at hy_covered
    obtain ⟨x, hx_mem, hy_ball⟩ := hy_covered
    have hdist_yx : dist y x ≤ eps / 2 := mem_closedBall.mp hy_ball
    -- proj x is in s ∩ closedBall(x, eps/2)
    have hproj_spec : (s ∩ closedBall x (eps / 2)).Nonempty := ⟨y, hy, hy_ball⟩
    have hproj_in : proj x ∈ s ∩ closedBall x (eps / 2) := by
      simp only [proj, dif_pos hproj_spec]
      exact hproj_spec.some_mem
    have hdist_proj_x : dist (proj x) x ≤ eps / 2 := mem_closedBall.mp hproj_in.2
    -- By triangle inequality: dist(y, proj x) ≤ dist(y, x) + dist(x, proj x) ≤ eps
    have hdist_y_proj : dist y (proj x) ≤ eps := by
      calc dist y (proj x) ≤ dist y x + dist x (proj x) := dist_triangle y x (proj x)
        _ ≤ eps / 2 + eps / 2 := add_le_add hdist_yx (by rw [dist_comm]; exact hdist_proj_x)
        _ = eps := by ring
    have hproj_in_t' : proj x ∈ t' := Finset.mem_image.mpr ⟨x, hx_mem, rfl⟩
    exact mem_iUnion₂.mpr ⟨proj x, hproj_in_t', mem_closedBall.mpr hdist_y_proj⟩
  -- 2. t' ⊆ s
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_image] at hz
    obtain ⟨x, _, rfl⟩ := hz
    by_cases h : (s ∩ closedBall x (eps / 2)).Nonempty
    · simp only [proj, dif_pos h]; exact h.some_mem.1
    · simp only [proj, dif_neg h]; exact hs₀
  -- 3. |t'| ≤ coveringNumber(eps/2, s)
  · have h_card_le : t'.card ≤ net.card := Finset.card_image_le
    calc (t'.card : WithTop ℕ) ≤ net.card := by exact_mod_cast h_card_le
      _ = coveringNumber (eps / 2) s := hnet_card

/-- Covering number is positive for nonempty totally bounded sets. -/
lemma coveringNumber_pos_of_nonempty_totallyBounded {eps : ℝ} {s : Set A}
    (heps : 0 < eps) (hs : TotallyBounded s) (hne : s.Nonempty) :
    0 < coveringNumber eps s := by
  have hfin : coveringNumber eps s < ⊤ := coveringNumber_lt_top_of_totallyBounded heps hs
  obtain ⟨n, hn⟩ := WithTop.untop_of_lt_top hfin
  rw [hn]
  by_contra h
  simp only [not_lt, nonpos_iff_eq_zero] at h
  rw [h] at hn
  have hzero : coveringNumber eps s = 0 := hn
  unfold coveringNumber at hzero
  have hmem : (0 : WithTop ℕ) ∈ {n : WithTop ℕ | ∃ t : Finset A, IsENet t eps s ∧ (t.card : WithTop ℕ) = n} := by
    have hne_set : {n : WithTop ℕ | ∃ t : Finset A, IsENet t eps s ∧ (t.card : WithTop ℕ) = n}.Nonempty := by
      obtain ⟨t, ht⟩ := exists_finset_isENet_of_totallyBounded heps hs
      exact ⟨t.card, t, ht, rfl⟩
    have hsInf := csInf_mem hne_set
    rwa [← hzero]
  obtain ⟨t, ht_net, ht_card⟩ := hmem
  have ht_card' : t.card = 0 := by simpa using ht_card
  rw [Finset.card_eq_zero] at ht_card'
  obtain ⟨x, hx⟩ := hne
  have := ht_net hx
  rw [ht_card'] at this
  simp at this

/-!
## Natural-valued covering numbers for totally bounded sets

The canonical `coveringNumber` deliberately takes values in `WithTop ℕ`.  Some finite chaining
arguments are more convenient with a natural number.  The following view is defined only from the
canonical covering number and records total boundedness in its arguments, so it cannot introduce a
second notion of covering number.
-/

/-- The natural-number value of `coveringNumber` for a totally bounded set.  It is defined to be
zero at nonpositive radii, matching the usual total extension of a positive-radius entropy
function. -/
noncomputable def coveringNumberNat {s : Set A} (hs : TotallyBounded s) (eps : ℝ) : ℕ :=
  if heps : 0 < eps then
    (coveringNumber eps s).untop
      (ne_top_of_lt (coveringNumber_lt_top_of_totallyBounded heps hs))
  else 0

/-- At a positive radius, coercing `coveringNumberNat` recovers the canonical covering number. -/
lemma coe_coveringNumberNat {s : Set A} (hs : TotallyBounded s) {eps : ℝ} (heps : 0 < eps) :
    (coveringNumberNat hs eps : WithTop ℕ) = coveringNumber eps s := by
  simp only [coveringNumberNat, dif_pos heps]
  exact WithTop.coe_untop _ _

/-- The natural-valued covering number is antitone on positive radii. -/
theorem coveringNumber_antitone {s : Set A} (hs : TotallyBounded s) :
    AntitoneOn (coveringNumberNat hs) (Set.Ioi 0) := by
  intro eps₁ heps₁ eps₂ heps₂ heps
  have h := coveringNumber_anti_eps (s := s) heps
  rw [← coe_coveringNumberNat hs heps₂, ← coe_coveringNumberNat hs heps₁] at h
  exact_mod_cast h

/-- The natural-valued covering number is positive for a nonempty totally bounded set and a
positive radius. -/
theorem coveringNumber_nonzero {s : Set A} (hne : s.Nonempty) (hs : TotallyBounded s)
    {eps : ℝ} (heps : 0 < eps) :
    0 < coveringNumberNat hs eps := by
  have h := coveringNumber_pos_of_nonempty_totallyBounded heps hs hne
  rw [← coe_coveringNumberNat hs heps] at h
  exact_mod_cast h

/-- The natural-valued covering number is almost-everywhere measurable as a function of its
radius. -/
theorem coveringNumber_aemeasurable {s : Set A} (hs : TotallyBounded s) :
    AEMeasurable (coveringNumberNat hs) MeasureTheory.volume := by
  have hpos : AEMeasurable (coveringNumberNat hs)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (coveringNumber_antitone hs)
  convert (aemeasurable_indicator_iff measurableSet_Ioi).mpr hpos
  ext eps
  by_cases heps : eps ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem heps]
  · rw [Set.indicator_of_notMem heps]
    simp only [coveringNumberNat, Set.mem_Ioi, not_lt] at heps ⊢
    simp [heps]

/-- An optimal finite epsilon-net witnessing the canonical covering number. -/
noncomputable def coveringFinset {s : Set A} (hs : TotallyBounded s) {eps : ℝ}
    (heps : 0 < eps) : Finset A :=
  Classical.choose (exists_optimal_enet_nat heps hs)

/-- `coveringFinset` is an epsilon-net. -/
lemma coveringFinset_isENet {s : Set A} (hs : TotallyBounded s) {eps : ℝ}
    (heps : 0 < eps) :
    IsENet (coveringFinset hs heps) eps s := by
  exact (Classical.choose_spec (exists_optimal_enet_nat heps hs)).1

/-- `coveringFinset` covers the set by closed epsilon-balls. -/
lemma coveringFinset_cover {s : Set A} (hs : TotallyBounded s) {eps : ℝ}
    (heps : 0 < eps) :
    s ⊆ ⋃ y ∈ coveringFinset hs heps, Metric.closedBall y eps :=
  coveringFinset_isENet hs heps

/-- The cardinality of `coveringFinset` is the natural-valued canonical covering number. -/
lemma coveringFinset_card {s : Set A} (hs : TotallyBounded s) {eps : ℝ}
    (heps : 0 < eps) :
    (coveringFinset hs heps).card = coveringNumberNat hs eps := by
  simpa only [coveringFinset, coveringNumberNat, dif_pos heps] using
    (Classical.choose_spec (exists_optimal_enet_nat heps hs)).2

end

/-!
## Covering Numbers Under Lipschitz Maps

If f : A → B is an L-Lipschitz surjection onto f(S), then any ε-net for S
induces an ε·L-net for f(S). This gives: N(ε·L, f(S)) ≤ N(ε, S).
-/

section LipschitzImage

variable {A B : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B]

/-- An ε-net for a set S induces an ε·L-net for the image f(S) under an L-Lipschitz map. -/
lemma IsENet.image_of_lipschitz [DecidableEq B] {L : ℝ} (hL : 0 ≤ L) {f : A → B}
    (hf : ∀ x y : A, dist (f x) (f y) ≤ L * dist x y)
    {t : Finset A} {eps : ℝ} {s : Set A}
    (hnet : IsENet t eps s) :
    IsENet (t.image f) (L * eps) (f '' s) := by
  intro y hy
  rw [Set.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx_cover := hnet hx
  rw [Set.mem_iUnion₂] at hx_cover
  obtain ⟨z, hz_mem, hx_ball⟩ := hx_cover
  rw [Set.mem_iUnion₂]
  refine ⟨f z, Finset.mem_image.mpr ⟨z, hz_mem, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall] at hx_ball ⊢
  calc dist (f x) (f z) ≤ L * dist x z := hf x z
    _ ≤ L * eps := mul_le_mul_of_nonneg_left hx_ball hL

/-- Covering number of a Lipschitz image: N(L·ε, f(S)) ≤ N(ε, S). -/
lemma coveringNumber_image_le_of_lipschitz [DecidableEq B] {L : ℝ} (hL : 0 < L) {f : A → B}
    (hf : ∀ x y : A, dist (f x) (f y) ≤ L * dist x y)
    {eps : ℝ} {s : Set A} :
    coveringNumber (L * eps) (f '' s) ≤ coveringNumber eps s := by
  -- If coveringNumber eps s = ⊤, the inequality is trivial
  by_cases h : coveringNumber eps s = ⊤
  · simp [h]
  -- Otherwise, there exists a finite ε-net for s
  · push Not at h
    -- Extract the covering number as a natural number
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
    -- The set of ε-net sizes is nonempty (since coveringNumber < ⊤)
    have hne : {m : WithTop ℕ | ∃ t : Finset A, IsENet t eps s ∧ ↑t.card = m}.Nonempty := by
      by_contra hemp
      have hemp' : {m : WithTop ℕ | ∃ t : Finset A, IsENet t eps s ∧ ↑t.card = m} = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hemp
      have : coveringNumber eps s = ⊤ := by
        unfold coveringNumber
        simp only [hemp', WithTop.sInf_empty]
      exact h this
    -- Get a finite ε-net achieving the infimum
    have hmem := csInf_mem hne
    obtain ⟨t, ht_net, ht_card⟩ := hmem
    have hnet_image := IsENet.image_of_lipschitz (le_of_lt hL) hf ht_net
    have hcard_le : (t.image f).card ≤ t.card := Finset.card_image_le
    calc coveringNumber (L * eps) (f '' s)
      _ ≤ (t.image f).card := coveringNumber_le_card hnet_image
      _ ≤ t.card := by exact_mod_cast hcard_le
      _ = coveringNumber eps s := ht_card

/-- For a 1-Lipschitz map, covering number of image ≤ covering number of preimage. -/
lemma coveringNumber_image_le_of_nonexpansive [DecidableEq B] {f : A → B}
    (hf : ∀ x y : A, dist (f x) (f y) ≤ dist x y)
    {eps : ℝ} {s : Set A} :
    coveringNumber eps (f '' s) ≤ coveringNumber eps s := by
  have h1 : ∀ x y : A, dist (f x) (f y) ≤ 1 * dist x y := fun x y => by simpa using hf x y
  have h := coveringNumber_image_le_of_lipschitz one_pos h1 (eps := eps) (s := s)
  simp only [one_mul] at h
  exact h

/-- Covering number is preserved under isometric bijections -/
theorem coveringNumber_image_of_isometry {f : A → B} (hf : Isometry f) (hbij : Function.Bijective f)
    {eps : ℝ} (s : Set A) :
    coveringNumber eps (f '' s) = coveringNumber eps s := by
  apply le_antisymm
  · -- Forward: coveringNumber (f '' s) ≤ coveringNumber s
    haveI : DecidableEq B := Classical.decEq B
    have h1Lip : ∀ x y : A, dist (f x) (f y) ≤ dist x y := fun x y => by
      rw [hf.dist_eq]
    exact coveringNumber_image_le_of_nonexpansive h1Lip
  · -- Backward: coveringNumber s ≤ coveringNumber (f '' s)
    by_cases hcover : coveringNumber eps (f '' s) = ⊤
    · simp [hcover]
    push Not at hcover
    have hne : {m : WithTop ℕ | ∃ t : Finset B, IsENet t eps (f '' s) ∧ (t.card : WithTop ℕ) = m}.Nonempty := by
      by_contra hemp
      have : coveringNumber eps (f '' s) = ⊤ := by
        unfold coveringNumber
        simp only [Set.not_nonempty_iff_eq_empty.mp hemp, WithTop.sInf_empty]
      exact hcover this
    have hmem := csInf_mem hne
    obtain ⟨t, ht_net, ht_card⟩ := hmem
    haveI : DecidableEq A := Classical.decEq A
    obtain ⟨g, hfg⟩ := hbij.2.hasRightInverse
    let t' : Finset A := t.image g
    have ht'_net : IsENet t' eps s := by
      intro x hx
      have hfx : f x ∈ f '' s := Set.mem_image_of_mem f hx
      have hcover_fx := ht_net hfx
      rw [Set.mem_iUnion₂] at hcover_fx ⊢
      obtain ⟨y, hy_mem, hfx_ball⟩ := hcover_fx
      refine ⟨g y, Finset.mem_image.mpr ⟨y, hy_mem, rfl⟩, ?_⟩
      rw [Metric.mem_closedBall] at hfx_ball ⊢
      calc dist x (g y) = dist (f x) (f (g y)) := (hf.dist_eq x (g y)).symm
        _ = dist (f x) y := by rw [hfg y]
        _ ≤ eps := hfx_ball
    calc coveringNumber eps s ≤ t'.card := coveringNumber_le_card ht'_net
      _ ≤ t.card := by exact_mod_cast Finset.card_image_le
      _ = coveringNumber eps (f '' s) := ht_card

end LipschitzImage
