/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import StatsMLlib.MeasureTheory.Integral.MonotoneConvergence
import StatsMLlib.Probability.Gaussian.SudakovFernique
import StatsMLlib.Topology.SeparableSpace.Supremum

/-!
# The Sudakov–Fernique inequality for Gaussian processes

Let `X : T → Ω → ℝ` and `Y : T → Ω' → ℝ` be Gaussian processes with the same mean function whose
increments satisfy `𝔼 (X s - X t)² ≤ 𝔼 (Y s - Y t)²`. This file extends the finite-dimensional
Sudakov–Fernique inequality of `StatsMLlib.Probability.Gaussian.SudakovFernique` to

* every finite subset `F` of `T`: `𝔼 max_{t ∈ F} X t ≤ 𝔼 max_{t ∈ F} Y t`;
* a countable index set: `𝔼 sup_t X t ≤ 𝔼 sup_t Y t`, by monotone convergence along an exhaustion
  of `T` by finite sets. Only `Y` is assumed to have bounded paths and an integrable supremum; the
  same properties of `X` follow from the comparison on finite sets;
* a separable index set with continuous sample paths, by reduction to a countable dense subset.

The finite-dimensional marginals and the enumeration of a countable index set are set up here so
that they can be reused for Gordon's inequality.

## Main results

* `ProbabilityTheory.IsGaussianProcess.isGaussian_map_pi`: a finite family of values of a
  Gaussian process has a Gaussian law on `ι → ℝ`.
* `ProbabilityTheory.IsGaussianProcess.integral_finset_sup'_le`: the Sudakov–Fernique inequality
  on a finite subset.
* `ProbabilityTheory.IsGaussianProcess.integral_iSup_le`: the Sudakov–Fernique inequality on a
  countable index set.
* `ProbabilityTheory.IsGaussianProcess.integral_iSup_le_of_separable`: the Sudakov–Fernique
  inequality on a separable index set with continuous sample paths.
-/

open MeasureTheory Filter Topology Finset

namespace ProbabilityTheory

section Exhaustion

variable {T : Type*}

/-- The `k`-th set `{e 0, …, e k}` of the exhaustion of `T` defined by `e : ℕ → T`. -/
noncomputable def exhaust (e : ℕ → T) (k : ℕ) : Finset T :=
  open Classical in (range (k + 1)).image e

lemma mem_exhaust (e : ℕ → T) (k : ℕ) : e k ∈ exhaust e k := by
  classical
  exact mem_image.2 ⟨k, mem_range.2 (Nat.lt_succ_self k), rfl⟩

lemma exhaust_nonempty (e : ℕ → T) (k : ℕ) : (exhaust e k).Nonempty :=
  ⟨e k, mem_exhaust e k⟩

lemma exhaust_mono (e : ℕ → T) : Monotone (exhaust e) := by
  classical
  intro a b hab
  exact image_subset_image (range_subset_range.2 (Nat.succ_le_succ hab))

/-- A maximum over `F` is a maximum over any finite type that parametrizes `F`. -/
lemma sup'_eq_univ_sup'_comp {ι : Type*} [Fintype ι] [Nonempty ι] {F : Finset T}
    (hF : F.Nonempty) {t : ι → T} (hmem : ∀ i, t i ∈ F) (hsurj : ∀ x ∈ F, ∃ i, t i = x)
    (f : T → ℝ) : F.sup' hF f = univ.sup' univ_nonempty (f ∘ t) := by
  refine le_antisymm (sup'_le _ _ fun x hx ↦ ?_) (sup'_le _ _ fun i _ ↦ le_sup' f (hmem i))
  obtain ⟨i, rfl⟩ := hsurj x hx
  exact le_sup' (f ∘ t) (mem_univ i)

/-- A minimum over `F` is a minimum over any finite type that parametrizes `F`. -/
lemma inf'_eq_univ_inf'_comp {ι : Type*} [Fintype ι] [Nonempty ι] {F : Finset T}
    (hF : F.Nonempty) {t : ι → T} (hmem : ∀ i, t i ∈ F) (hsurj : ∀ x ∈ F, ∃ i, t i = x)
    (f : T → ℝ) : F.inf' hF f = univ.inf' univ_nonempty (f ∘ t) := by
  refine le_antisymm (le_inf' _ _ fun i _ ↦ inf'_le f (hmem i)) (le_inf' _ _ fun x hx ↦ ?_)
  obtain ⟨i, rfl⟩ := hsurj x hx
  exact inf'_le (f ∘ t) (mem_univ i)

/-- The maxima of a bounded function over the exhaustion of `T` increase to its supremum. -/
lemma tendsto_exhaust_sup' [Nonempty T] {e : ℕ → T} (he : Function.Surjective e) {f : T → ℝ}
    (hf : BddAbove (Set.range f)) :
    Tendsto (fun k ↦ (exhaust e k).sup' (exhaust_nonempty e k) f) atTop (𝓝 (⨆ t, f t)) := by
  have hmono : Monotone fun k ↦ (exhaust e k).sup' (exhaust_nonempty e k) f :=
    fun a b hab ↦ sup'_mono f (exhaust_mono e hab) _
  have hle : ∀ k, (exhaust e k).sup' (exhaust_nonempty e k) f ≤ ⨆ t, f t :=
    fun k ↦ sup'_le _ _ fun t _ ↦ le_ciSup hf t
  have hbdd : BddAbove (Set.range fun k ↦ (exhaust e k).sup' (exhaust_nonempty e k) f) :=
    ⟨_, Set.forall_mem_range.2 hle⟩
  convert tendsto_atTop_ciSup hmono hbdd using 2
  refine le_antisymm (ciSup_le fun t ↦ ?_) (ciSup_le hle)
  obtain ⟨k, rfl⟩ := he t
  exact (le_sup' f (mem_exhaust e k)).trans (le_ciSup hbdd k)

/-- The minima of a function bounded below over the exhaustion of `T` decrease to its infimum. -/
lemma tendsto_exhaust_inf' [Nonempty T] {e : ℕ → T} (he : Function.Surjective e) {f : T → ℝ}
    (hf : BddBelow (Set.range f)) :
    Tendsto (fun k ↦ (exhaust e k).inf' (exhaust_nonempty e k) f) atTop (𝓝 (⨅ t, f t)) := by
  have hanti : Antitone fun k ↦ (exhaust e k).inf' (exhaust_nonempty e k) f :=
    fun a b hab ↦ inf'_mono f (exhaust_mono e hab) _
  have hge : ∀ k, ⨅ t, f t ≤ (exhaust e k).inf' (exhaust_nonempty e k) f :=
    fun k ↦ le_inf' _ _ fun t _ ↦ ciInf_le hf t
  have hbdd : BddBelow (Set.range fun k ↦ (exhaust e k).inf' (exhaust_nonempty e k) f) :=
    ⟨_, Set.forall_mem_range.2 hge⟩
  convert tendsto_atTop_ciInf hanti hbdd using 2
  refine le_antisymm (le_ciInf hge) (le_ciInf fun t ↦ ?_)
  obtain ⟨k, rfl⟩ := he t
  exact (ciInf_le hbdd k).trans (inf'_le f (mem_exhaust e k))

end Exhaustion

section Countable

variable {T Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {X : T → Ω → ℝ}

/-- If the maxima of a process over all finite sets of indices are integrable with expectations
bounded by `C`, and the index set is countable, then the sample paths are a.s. bounded above and
`sup_t X t` is integrable with expectation at most `C`. -/
lemma integral_iSup_le_of_forall_finset [Countable T] [Nonempty T]
    (hXi : ∀ (F : Finset T) (hF : F.Nonempty), Integrable (fun ω ↦ F.sup' hF (X · ω)) Q)
    {C : ℝ} (hC : ∀ (F : Finset T) (hF : F.Nonempty), ∫ ω, F.sup' hF (X · ω) ∂Q ≤ C) :
    (∀ᵐ ω ∂Q, BddAbove (Set.range (X · ω))) ∧ Integrable (fun ω ↦ ⨆ t, X t ω) Q ∧
      ∫ ω, ⨆ t, X t ω ∂Q ≤ C := by
  obtain ⟨e, he⟩ := exists_surjective_nat T
  have hMi : ∀ k, Integrable (fun ω ↦ (exhaust e k).sup' (exhaust_nonempty e k) (X · ω)) Q :=
    fun k ↦ hXi _ _
  have hmono : ∀ᵐ ω ∂Q, Monotone fun k ↦ (exhaust e k).sup' (exhaust_nonempty e k) (X · ω) :=
    ae_of_all _ fun ω a b hab ↦ sup'_mono _ (exhaust_mono e hab) _
  have hle : ∀ k, ∫ ω, (exhaust e k).sup' (exhaust_nonempty e k) (X · ω) ∂Q ≤ C :=
    fun k ↦ hC _ _
  have hXb : ∀ᵐ ω ∂Q, BddAbove (Set.range (X · ω)) := by
    filter_upwards [ae_bddAbove_of_monotone_of_integral_le hMi hmono hle] with ω ⟨b, hb⟩
    refine ⟨b, Set.forall_mem_range.2 fun t ↦ ?_⟩
    obtain ⟨k, rfl⟩ := he t
    exact (le_sup' (X · ω) (mem_exhaust e k)).trans (hb ⟨k, rfl⟩)
  have htend : ∀ᵐ ω ∂Q, Tendsto (fun k ↦ (exhaust e k).sup' (exhaust_nonempty e k) (X · ω))
      atTop (𝓝 (⨆ t, X t ω)) := by
    filter_upwards [hXb] with ω hω using tendsto_exhaust_sup' he hω
  have hi := integrable_of_tendsto_of_monotone_of_integral_le hMi hmono htend hle
  exact ⟨hXb, hi, le_of_tendsto' (integral_tendsto_of_tendsto_of_monotone hMi hi hmono htend) hle⟩

end Countable

namespace IsGaussianProcess

variable {T Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}

section Marginal

variable {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}

lemma hasGaussianLaw_pi (hX : IsGaussianProcess X P) :
    HasGaussianLaw (fun ω i ↦ X i ω) P :=
  (hX.hasGaussianLaw univ).map_fun (ContinuousLinearMap.pi fun i ↦
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : (univ : Finset ι) ↦ ℝ) ⟨i, mem_univ i⟩)

lemma isGaussian_map_pi (hX : IsGaussianProcess X P) :
    IsGaussian (P.map fun ω i ↦ X i ω) :=
  (hasGaussianLaw_pi hX).isGaussian_map

lemma integral_id_map_pi (hX : IsGaussianProcess X P) :
    ∫ x, x ∂(P.map fun ω i ↦ X i ω) = fun i ↦ ∫ ω, X i ω ∂P := by
  rw [integral_map (f := fun x ↦ x) (hasGaussianLaw_pi hX).aemeasurable
    aestronglyMeasurable_id]
  ext i
  exact eval_integral (fun i ↦ (hX.hasGaussianLaw_eval i).integrable) i

lemma integral_map_pi (hX : IsGaussianProcess X P) {g : (ι → ℝ) → ℝ} (hg : Continuous g) :
    ∫ x, g x ∂(P.map fun ω i ↦ X i ω) = ∫ ω, g (fun i ↦ X i ω) ∂P :=
  integral_map (hasGaussianLaw_pi hX).aemeasurable hg.aestronglyMeasurable

end Marginal

variable {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}

lemma integrable_finset_sup' (hX : IsGaussianProcess X P) (F : Finset T) (hF : F.Nonempty) :
    Integrable (fun ω ↦ F.sup' hF (X · ω)) P := by
  have : Nonempty F := hF.to_subtype
  have hg : Continuous fun x : F → ℝ ↦ univ.sup' univ_nonempty x :=
    Continuous.finset_sup'_apply univ_nonempty fun i _ ↦ continuous_apply i
  have heq : (fun ω ↦ F.sup' hF (X · ω)) =
      (fun x : F → ℝ ↦ univ.sup' univ_nonempty x) ∘ fun ω ↦ F.restrict (X · ω) := by
    ext ω
    exact sup'_eq_univ_sup'_comp hF (t := Subtype.val) (fun i ↦ i.2)
      (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩) _
  refine (integrable_finsetSum F fun t _ ↦ (hX.hasGaussianLaw_eval t).integrable.abs).mono' ?_
    (ae_of_all _ fun ω ↦ ?_)
  · rw [heq]
    exact hg.comp_aestronglyMeasurable (hX.hasGaussianLaw F).aemeasurable.aestronglyMeasurable
  · obtain ⟨k, hk, hk'⟩ := exists_mem_eq_sup' hF (X · ω)
    rw [Real.norm_eq_abs, hk']
    exact single_le_sum (f := fun t ↦ |X t ω|) (fun t _ ↦ abs_nonneg _) hk

/-- **Sudakov–Fernique inequality** along a finite family `t : Fin n → T` of indices. -/
lemma integral_sup'_comp_le {n : ℕ} [NeZero n] (hX : IsGaussianProcess X P)
    (hY : IsGaussianProcess Y P') (hm : ∀ t, ∫ ω, X t ω ∂P = ∫ ω, Y t ω ∂P')
    (h : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂P') (t : Fin n → T) :
    ∫ ω, univ.sup' univ_nonempty (fun i ↦ X (t i) ω) ∂P ≤
      ∫ ω, univ.sup' univ_nonempty (fun i ↦ Y (t i) ω) ∂P' := by
  have hXt : IsGaussianProcess (fun i ↦ X (t i)) P := hX.comp_right t
  have hYt : IsGaussianProcess (fun i ↦ Y (t i)) P' := hY.comp_right t
  have := isGaussian_map_pi hXt
  have := isGaussian_map_pi hYt
  have hmY : ∫ y, y ∂(P'.map fun ω i ↦ Y (t i) ω) = fun i ↦ ∫ ω, X (t i) ω ∂P :=
    (integral_id_map_pi hYt).trans (funext fun i ↦ (hm (t i)).symm)
  have hsq : ∀ i j, Continuous fun x : Fin n → ℝ ↦ (x i - x j) ^ 2 := fun i j ↦ by fun_prop
  have hincr : ∀ i j, GaussianMeasure.incrSq (P.map fun ω i ↦ X (t i) ω) i j ≤
      GaussianMeasure.incrSq (P'.map fun ω i ↦ Y (t i) ω) i j := by
    intro i j
    rw [GaussianMeasure.incrSq, GaussianMeasure.incrSq, integral_map_pi hXt (hsq i j),
      integral_map_pi hYt (hsq i j)]
    exact h (t i) (t j)
  have hsup : Continuous fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x :=
    Continuous.finset_sup'_apply univ_nonempty fun i _ ↦ continuous_apply i
  have := GaussianMeasure.integral_sup'_le_of_incrSq_le (integral_id_map_pi hXt) hmY hincr
  rwa [integral_map_pi hXt hsup, integral_map_pi hYt hsup] at this

/-- **Sudakov–Fernique inequality on a finite subset.** If two Gaussian processes have the same
mean function and the increments of the first are dominated in mean square by those of the second,
then the expected maximum of the first over any finite set of indices is at most that of the
second. -/
theorem integral_finset_sup'_le (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P')
    (hm : ∀ t, ∫ ω, X t ω ∂P = ∫ ω, Y t ω ∂P')
    (h : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂P')
    (F : Finset T) (hF : F.Nonempty) :
    ∫ ω, F.sup' hF (X · ω) ∂P ≤ ∫ ω, F.sup' hF (Y · ω) ∂P' := by
  have : NeZero F.card := ⟨(card_pos.2 hF).ne'⟩
  set t : Fin F.card → T := fun i ↦ (F.equivFin.symm i : T)
  have hmem : ∀ i, t i ∈ F := fun i ↦ (F.equivFin.symm i).2
  have hsurj : ∀ x ∈ F, ∃ i, t i = x := fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp [t]⟩
  simp_rw [sup'_eq_univ_sup'_comp hF hmem hsurj]
  exact integral_sup'_comp_le hX hY hm h t

/-- **Sudakov–Fernique inequality on a countable index set.** If moreover the sample paths of `Y`
are a.s. bounded above and `sup_t Y t` is integrable, then `sup_t X t` is integrable and
`𝔼 sup_t X t ≤ 𝔼 sup_t Y t`. -/
theorem integral_iSup_le [Countable T] [Nonempty T] (hX : IsGaussianProcess X P)
    (hY : IsGaussianProcess Y P') (hm : ∀ t, ∫ ω, X t ω ∂P = ∫ ω, Y t ω ∂P')
    (h : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂P')
    (hYb : ∀ᵐ ω ∂P', BddAbove (Set.range (Y · ω)))
    (hYi : Integrable (fun ω ↦ ⨆ t, Y t ω) P') :
    Integrable (fun ω ↦ ⨆ t, X t ω) P ∧ ∫ ω, ⨆ t, X t ω ∂P ≤ ∫ ω, ⨆ t, Y t ω ∂P' := by
  obtain ⟨-, hXi, hle⟩ := integral_iSup_le_of_forall_finset (integrable_finset_sup' hX)
    fun F hF ↦ (integral_finset_sup'_le hX hY hm h F hF).trans
      (integral_mono_ae (integrable_finset_sup' hY F hF) hYi
        (by filter_upwards [hYb] with ω hω using sup'_le _ _ fun t _ ↦ le_ciSup hω t))
  exact ⟨hXi, hle⟩

/-- **Sudakov–Fernique inequality on a separable index set.** For processes with a.s. continuous
sample paths on a separable space, the supremum reduces to a countable dense subset. -/
theorem integral_iSup_le_of_separable [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
    [Nonempty T] (hX : IsGaussianProcess X P)
    (hY : IsGaussianProcess Y P') (hm : ∀ t, ∫ ω, X t ω ∂P = ∫ ω, Y t ω ∂P')
    (h : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂P')
    (hXc : ∀ᵐ ω ∂P, Continuous (X · ω)) (hYc : ∀ᵐ ω ∂P', Continuous (Y · ω))
    (hYb : ∀ᵐ ω ∂P', BddAbove (Set.range (Y · ω)))
    (hYi : Integrable (fun ω ↦ ⨆ t, Y t ω) P') :
    Integrable (fun ω ↦ ⨆ t, X t ω) P ∧ ∫ ω, ⨆ t, X t ω ∂P ≤ ∫ ω, ⨆ t, Y t ω ∂P' := by
  set d := TopologicalSpace.denseSeq T
  have heqX : (fun ω ↦ ⨆ t, X t ω) =ᵐ[P] fun ω ↦ ⨆ i, X (d i) ω := by
    filter_upwards [hXc] with ω hω using separableSpaceSup_eq_real hω
  have heqY : (fun ω ↦ ⨆ t, Y t ω) =ᵐ[P'] fun ω ↦ ⨆ i, Y (d i) ω := by
    filter_upwards [hYc] with ω hω using separableSpaceSup_eq_real hω
  have hYb' : ∀ᵐ ω ∂P', BddAbove (Set.range fun i ↦ Y (d i) ω) := by
    filter_upwards [hYb] with ω hω using hω.mono (Set.range_comp_subset_range d (Y · ω))
  obtain ⟨hXi, hle⟩ := integral_iSup_le (hX.comp_right d) (hY.comp_right d)
    (fun i ↦ hm (d i)) (fun i j ↦ h (d i) (d j)) hYb' (hYi.congr heqY)
  refine ⟨hXi.congr heqX.symm, ?_⟩
  rwa [integral_congr_ae heqX, integral_congr_ae heqY]

end IsGaussianProcess

end ProbabilityTheory
