/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.Probability.Gaussian.Gordon
import StatsMLlib.Probability.Gaussian.SudakovFerniqueProcess

/-!
# Gordon's inequality for Gaussian processes

Let `X` and `Y` be centered Gaussian processes indexed by `S × T` with the same variances, such
that covariances within a row are larger for `X` and covariances across rows are smaller for `X`.
This file extends the finite-dimensional Gordon inequality of
`StatsMLlib.Probability.Gaussian.Gordon` to

* finite subsets `A ⊆ S`, `B ⊆ T`: `𝔼 min_{s ∈ A} max_{t ∈ B} X ≤ 𝔼 min_{s ∈ A} max_{t ∈ B} Y`;
* countable `S` and `T`: `𝔼 inf_s sup_t X ≤ 𝔼 inf_s sup_t Y`, by letting first the columns and then
  the rows exhaust `T` and `S`. The regularity of the rows of `X` is deduced from Gordon's
  inequality on a single row, and the lower bound on the rows of `Y` from the comparison itself;
* separable `S` and `T`, by reduction to countable dense subsets.

## Main results

* `ProbabilityTheory.IsGaussianProcess.integral_finset_inf'_sup'_le_gordon`: Gordon's inequality
  on finite subsets.
* `ProbabilityTheory.IsGaussianProcess.integral_iInf_iSup_le_gordon`: Gordon's inequality on
  countable index sets.
* `ProbabilityTheory.IsGaussianProcess.integral_iInf_iSup_le_gordon_of_separable`: Gordon's
  inequality on separable index sets.
-/

open MeasureTheory Filter Topology Finset

namespace ProbabilityTheory

namespace IsGaussianProcess

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}

lemma covariance_map_pi {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (hX : IsGaussianProcess X P)
    (i j : ι) :
    cov[fun x ↦ x i, fun x ↦ x j; P.map fun ω i ↦ X i ω] = cov[X i, X j; P] :=
  covariance_map_fun (continuous_apply i).aestronglyMeasurable
    (continuous_apply j).aestronglyMeasurable (hasGaussianLaw_pi hX).aemeasurable

lemma integrable_finset_inf' {ι : Type*} {g : ι → Ω → ℝ} (F : Finset ι) (hF : F.Nonempty)
    (hg : ∀ i ∈ F, Integrable (g i) P) : Integrable (fun ω ↦ F.inf' hF (g · ω)) P := by
  induction hF using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hg a (mem_singleton_self a)
  | cons a s ha hs ih =>
    simp only [inf'_cons hs]
    exact (hg a (mem_cons_self a s)).inf (ih fun i hi ↦ hg i (mem_cons_of_mem hi))

variable {S T : Type*} {X : S × T → Ω → ℝ} {Y : S × T → Ω' → ℝ}

/-- **Gordon's inequality on finite subsets.** Let `X` and `Y` be centered Gaussian processes on
`S × T` with the same variances, such that covariances within a row are larger for `X` and
covariances across rows are smaller for `X`. Then for all nonempty finite `A ⊆ S`, `B ⊆ T`,
`𝔼 min_{s ∈ A} max_{t ∈ B} X ≤ 𝔼 min_{s ∈ A} max_{t ∈ B} Y`. -/
theorem integral_finset_inf'_sup'_le_gordon (hX : IsGaussianProcess X P)
    (hY : IsGaussianProcess Y P') (hmX : ∀ i, ∫ ω, X i ω ∂P = 0) (hmY : ∀ i, ∫ ω, Y i ω ∂P' = 0)
    (hvar : ∀ i, cov[X i, X i; P] = cov[Y i, Y i; P'])
    (hrow : ∀ s t t', t ≠ t' → cov[Y (s, t), Y (s, t'); P'] ≤ cov[X (s, t), X (s, t'); P])
    (hcross : ∀ s s' t t', s ≠ s' → cov[X (s, t), X (s', t'); P] ≤ cov[Y (s, t), Y (s', t'); P'])
    (A : Finset S) (hA : A.Nonempty) (B : Finset T) (hB : B.Nonempty) :
    ∫ ω, A.inf' hA (fun s ↦ B.sup' hB fun t ↦ X (s, t) ω) ∂P ≤
      ∫ ω, A.inf' hA (fun s ↦ B.sup' hB fun t ↦ Y (s, t) ω) ∂P' := by
  classical
  have : Nonempty A := hA.to_subtype
  have : Nonempty B := hB.to_subtype
  set φ : A × B → S × T := fun p ↦ (p.1.1, p.2.1)
  have hXφ : IsGaussianProcess (fun p ↦ X (φ p)) P := hX.comp_right φ
  have hYφ : IsGaussianProcess (fun p ↦ Y (φ p)) P' := hY.comp_right φ
  have := isGaussian_map_pi hXφ
  have := isGaussian_map_pi hYφ
  have hμ : ∫ x, x ∂(P.map fun ω p ↦ X (φ p) ω) = 0 :=
    (integral_id_map_pi hXφ).trans (funext fun p ↦ hmX (φ p))
  have hν : ∫ x, x ∂(P'.map fun ω p ↦ Y (φ p) ω) = 0 :=
    (integral_id_map_pi hYφ).trans (funext fun p ↦ hmY (φ p))
  have hG := GaussianMeasure.integral_minMax_le_gordon hμ hν
    (fun p ↦ by rw [covariance_map_pi hXφ, covariance_map_pi hYφ]; exact hvar (φ p))
    (fun s t t' htt' ↦ by
      rw [covariance_map_pi hXφ, covariance_map_pi hYφ]
      exact hrow s.1 t.1 t'.1 fun h ↦ htt' (Subtype.ext h))
    (fun s s' t t' hss' ↦ by
      rw [covariance_map_pi hXφ, covariance_map_pi hYφ]
      exact hcross s.1 s'.1 t.1 t'.1 fun h ↦ hss' (Subtype.ext h)) 0
  simp only [add_zero] at hG
  rw [integral_map_pi hXφ GaussianMeasure.continuous_minMax,
    integral_map_pi hYφ GaussianMeasure.continuous_minMax] at hG
  have heq : ∀ Z : S × T → ℝ, A.inf' hA (fun s ↦ B.sup' hB fun t ↦ Z (s, t)) =
      minMax fun p : A × B ↦ Z (φ p) := by
    intro Z
    rw [inf'_eq_univ_inf'_comp hA (t := Subtype.val) (fun i ↦ i.2) fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩]
    refine inf'_congr _ rfl fun a _ ↦ ?_
    exact sup'_eq_univ_sup'_comp hB (t := Subtype.val) (fun i ↦ i.2)
      (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩) _
  calc _ = ∫ ω, minMax (fun p ↦ X (φ p) ω) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω ↦ heq (X · ω))
    _ ≤ ∫ ω, minMax (fun p ↦ Y (φ p) ω) ∂P' := hG
    _ = _ := integral_congr_ae (ae_of_all _ fun ω ↦ (heq (Y · ω)).symm)

/-- Along the exhaustion of the columns, `𝔼 min_{s ∈ A} max_{t ∈ B_l} Z` converges to
`𝔼 min_{s ∈ A} sup_t Z`. -/
lemma tendsto_integral_inf'_exhaust_sup' {Q : Measure Ω} {Z : S × T → Ω → ℝ}
    (hZ : IsGaussianProcess Z Q) [Nonempty T] {eT : ℕ → T} (heT : Function.Surjective eT)
    (hZb : ∀ᵐ ω ∂Q, ∀ s, BddAbove (Set.range fun t ↦ Z (s, t) ω))
    (hZr : ∀ s, Integrable (fun ω ↦ ⨆ t, Z (s, t) ω) Q) (A : Finset S) (hA : A.Nonempty) :
    Tendsto (fun l ↦ ∫ ω, A.inf' hA (fun s ↦
        (exhaust eT l).sup' (exhaust_nonempty eT l) fun t ↦ Z (s, t) ω) ∂Q) atTop
      (𝓝 (∫ ω, A.inf' hA (fun s ↦ ⨆ t, Z (s, t) ω) ∂Q)) := by
  refine integral_tendsto_of_tendsto_of_monotone (fun l ↦ ?_)
    (integrable_finset_inf' A hA fun s _ ↦ hZr s) (ae_of_all _ fun ω a b hab ↦ ?_) ?_
  · exact integrable_finset_inf' A hA fun s _ ↦
      integrable_finset_sup' (X := fun t ↦ Z (s, t)) (hZ.comp_right fun t ↦ (s, t)) _ _
  · exact le_inf' _ _ fun s hs ↦ (inf'_le _ hs).trans (sup'_mono _ (exhaust_mono eT hab) _)
  · filter_upwards [hZb] with ω hω
    exact Tendsto.finset_inf'_nhds_apply hA fun s _ ↦ tendsto_exhaust_sup' heT (hω s)

/-- **Gordon's inequality on countable index sets.** In addition to the hypotheses of the finite
version, assume that a.s. every row of `Y` is bounded above with integrable supremum, that a.s. the
row suprema of `X` are bounded below, and that `inf_s sup_t X` is integrable. Then
`inf_s sup_t Y` is integrable and `𝔼 inf_s sup_t X ≤ 𝔼 inf_s sup_t Y`. The corresponding
properties of the rows of `X` and the lower bound on the row suprema of `Y` follow from the
comparison on finite sets. -/
theorem integral_iInf_iSup_le_gordon [Countable S] [Nonempty S] [Countable T] [Nonempty T]
    (hX : IsGaussianProcess X P)
    (hY : IsGaussianProcess Y P') (hmX : ∀ i, ∫ ω, X i ω ∂P = 0) (hmY : ∀ i, ∫ ω, Y i ω ∂P' = 0)
    (hvar : ∀ i, cov[X i, X i; P] = cov[Y i, Y i; P'])
    (hrow : ∀ s t t', t ≠ t' → cov[Y (s, t), Y (s, t'); P'] ≤ cov[X (s, t), X (s, t'); P])
    (hcross : ∀ s s' t t', s ≠ s' → cov[X (s, t), X (s', t'); P] ≤ cov[Y (s, t), Y (s', t'); P'])
    (hYb : ∀ᵐ ω ∂P', ∀ s, BddAbove (Set.range fun t ↦ Y (s, t) ω))
    (hXb' : ∀ᵐ ω ∂P, BddBelow (Set.range fun s ↦ ⨆ t, X (s, t) ω))
    (hYr : ∀ s, Integrable (fun ω ↦ ⨆ t, Y (s, t) ω) P')
    (hXi : Integrable (fun ω ↦ ⨅ s, ⨆ t, X (s, t) ω) P) :
    Integrable (fun ω ↦ ⨅ s, ⨆ t, Y (s, t) ω) P' ∧
      ∫ ω, ⨅ s, ⨆ t, X (s, t) ω ∂P ≤ ∫ ω, ⨅ s, ⨆ t, Y (s, t) ω ∂P' := by
  obtain ⟨eS, heS⟩ := exists_surjective_nat S
  obtain ⟨eT, heT⟩ := exists_surjective_nat T
  -- the rows of `X` are a.s. bounded above with integrable suprema, by Gordon's inequality on a
  -- single row
  have hXrow : ∀ s, (∀ᵐ ω ∂P, BddAbove (Set.range fun t ↦ X (s, t) ω)) ∧
      Integrable (fun ω ↦ ⨆ t, X (s, t) ω) P ∧ _ := fun s ↦
    integral_iSup_le_of_forall_finset (X := fun t ↦ X (s, t))
      (integrable_finset_sup' (hX.comp_right fun t ↦ (s, t))) fun B hB ↦ by
        have h := integral_finset_inf'_sup'_le_gordon hX hY hmX hmY hvar hrow hcross {s}
          (singleton_nonempty s) B hB
        simp only [inf'_singleton] at h
        refine h.trans (integral_mono_ae (integrable_finset_sup'
          (X := fun t ↦ Y (s, t)) (hY.comp_right fun t ↦ (s, t)) B hB) (hYr s) ?_)
        filter_upwards [hYb] with ω hω using sup'_le _ _ fun t _ ↦ le_ciSup (hω s) t
  have hXb : ∀ᵐ ω ∂P, ∀ s, BddAbove (Set.range fun t ↦ X (s, t) ω) :=
    ae_all_iff.2 fun s ↦ (hXrow s).1
  have hXr : ∀ s, Integrable (fun ω ↦ ⨆ t, X (s, t) ω) P := fun s ↦ (hXrow s).2.1
  -- `𝔼 min_{s ∈ A_k} sup_t X ≤ 𝔼 min_{s ∈ A_k} sup_t Y`, letting the columns exhaust `T`
  have hH : ∀ k, ∫ ω, (exhaust eS k).inf' (exhaust_nonempty eS k) (fun s ↦ ⨆ t, X (s, t) ω) ∂P ≤
      ∫ ω, (exhaust eS k).inf' (exhaust_nonempty eS k) (fun s ↦ ⨆ t, Y (s, t) ω) ∂P' :=
    fun k ↦ le_of_tendsto_of_tendsto'
      (tendsto_integral_inf'_exhaust_sup' hX heT hXb hXr _ _)
      (tendsto_integral_inf'_exhaust_sup' hY heT hYb hYr _ _) fun l ↦
        integral_finset_inf'_sup'_le_gordon hX hY hmX hmY hvar hrow hcross _ _ _ _
  -- `𝔼 inf_s sup_t X ≤ 𝔼 min_{s ∈ A_k} sup_t X`
  have hXH : ∀ k, ∫ ω, ⨅ s, ⨆ t, X (s, t) ω ∂P ≤
      ∫ ω, (exhaust eS k).inf' (exhaust_nonempty eS k) (fun s ↦ ⨆ t, X (s, t) ω) ∂P := by
    intro k
    refine integral_mono_ae hXi (integrable_finset_inf' _ _ fun s _ ↦ hXr s) ?_
    filter_upwards [hXb'] with ω hω using le_inf' _ _ fun s _ ↦ ciInf_le hω s
  -- letting the rows exhaust `S` on the side of `Y`
  have hHYi : ∀ k, Integrable (fun ω ↦
      (exhaust eS k).inf' (exhaust_nonempty eS k) (fun s ↦ ⨆ t, Y (s, t) ω)) P' :=
    fun k ↦ integrable_finset_inf' _ _ fun s _ ↦ hYr s
  have hanti : ∀ᵐ ω ∂P', Antitone fun k ↦
      (exhaust eS k).inf' (exhaust_nonempty eS k) (fun s ↦ ⨆ t, Y (s, t) ω) :=
    ae_of_all _ fun ω a b hab ↦ inf'_mono _ (exhaust_mono eS hab) _
  have hle : ∀ k, ∫ ω, ⨅ s, ⨆ t, X (s, t) ω ∂P ≤
      ∫ ω, (exhaust eS k).inf' (exhaust_nonempty eS k) (fun s ↦ ⨆ t, Y (s, t) ω) ∂P' :=
    fun k ↦ (hXH k).trans (hH k)
  -- the row suprema of `Y` are a.s. bounded below, since their minima have bounded expectations
  have hYb' : ∀ᵐ ω ∂P', BddBelow (Set.range fun s ↦ ⨆ t, Y (s, t) ω) := by
    filter_upwards [ae_bddBelow_of_antitone_of_le_integral hHYi hanti hle] with ω ⟨b, hb⟩
    refine ⟨b, Set.forall_mem_range.2 fun s ↦ ?_⟩
    obtain ⟨k, rfl⟩ := heS s
    exact (hb ⟨k, rfl⟩).trans (inf'_le _ (mem_exhaust eS k))
  have htend : ∀ᵐ ω ∂P', Tendsto (fun k ↦
      (exhaust eS k).inf' (exhaust_nonempty eS k) (fun s ↦ ⨆ t, Y (s, t) ω)) atTop
      (𝓝 (⨅ s, ⨆ t, Y (s, t) ω)) := by
    filter_upwards [hYb'] with ω hω using tendsto_exhaust_inf' heS hω
  have hYi := integrable_of_tendsto_of_antitone_of_le_integral hHYi hanti htend hle
  exact ⟨hYi, ge_of_tendsto' (integral_tendsto_of_tendsto_of_antitone hHYi hYi hanti htend) hle⟩

/-- **Gordon's inequality on separable index sets.** If the rows of both processes are a.s.
continuous and so are the row suprema `s ↦ sup_t X (s, t)`, the infima and suprema reduce to
countable dense subsets. -/
theorem integral_iInf_iSup_le_gordon_of_separable [TopologicalSpace S]
    [TopologicalSpace.SeparableSpace S] [Nonempty S] [TopologicalSpace T]
    [TopologicalSpace.SeparableSpace T] [Nonempty T]
    (hX : IsGaussianProcess X P)
    (hY : IsGaussianProcess Y P') (hmX : ∀ i, ∫ ω, X i ω ∂P = 0) (hmY : ∀ i, ∫ ω, Y i ω ∂P' = 0)
    (hvar : ∀ i, cov[X i, X i; P] = cov[Y i, Y i; P'])
    (hrow : ∀ s t t', t ≠ t' → cov[Y (s, t), Y (s, t'); P'] ≤ cov[X (s, t), X (s, t'); P])
    (hcross : ∀ s s' t t', s ≠ s' → cov[X (s, t), X (s', t'); P] ≤ cov[Y (s, t), Y (s', t'); P'])
    (hXc : ∀ᵐ ω ∂P, ∀ s, Continuous fun t ↦ X (s, t) ω)
    (hYc : ∀ᵐ ω ∂P', ∀ s, Continuous fun t ↦ Y (s, t) ω)
    (hXc' : ∀ᵐ ω ∂P, Continuous fun s ↦ ⨆ t, X (s, t) ω)
    (hYc' : ∀ᵐ ω ∂P', Continuous fun s ↦ ⨆ t, Y (s, t) ω)
    (hYb : ∀ᵐ ω ∂P', ∀ s, BddAbove (Set.range fun t ↦ Y (s, t) ω))
    (hXb' : ∀ᵐ ω ∂P, BddBelow (Set.range fun s ↦ ⨆ t, X (s, t) ω))
    (hYr : ∀ s, Integrable (fun ω ↦ ⨆ t, Y (s, t) ω) P')
    (hXi : Integrable (fun ω ↦ ⨅ s, ⨆ t, X (s, t) ω) P) :
    Integrable (fun ω ↦ ⨅ s, ⨆ t, Y (s, t) ω) P' ∧
      ∫ ω, ⨅ s, ⨆ t, X (s, t) ω ∂P ≤ ∫ ω, ⨅ s, ⨆ t, Y (s, t) ω ∂P' := by
  -- index by the ranges of the dense sequences, so that distinct indices stay distinct
  set DS := Set.range (TopologicalSpace.denseSeq S)
  set DT := Set.range (TopologicalSpace.denseSeq T)
  have : Countable DS := (Set.countable_range _).to_subtype
  have : Countable DT := (Set.countable_range _).to_subtype
  have : Nonempty DS := (Set.range_nonempty _).to_subtype
  have : Nonempty DT := (Set.range_nonempty _).to_subtype
  have hXrow : ∀ᵐ ω ∂P, ∀ s, ⨆ t, X (s, t) ω = ⨆ b : DT, X (s, b) ω := by
    filter_upwards [hXc] with ω h s using separableSpaceSup_eq_range_real (h s)
  have hYrow : ∀ᵐ ω ∂P', ∀ s, ⨆ t, Y (s, t) ω = ⨆ b : DT, Y (s, b) ω := by
    filter_upwards [hYc] with ω h s using separableSpaceSup_eq_range_real (h s)
  have hX' : (fun ω ↦ ⨅ s, ⨆ t, X (s, t) ω) =ᵐ[P] fun ω ↦ ⨅ a : DS, ⨆ b : DT, X (a, b) ω := by
    filter_upwards [hXrow, hXc'] with ω h h'
    rw [separableSpaceInf_eq_range_real h']
    exact iInf_congr fun a ↦ h a
  have hY' : (fun ω ↦ ⨅ s, ⨆ t, Y (s, t) ω) =ᵐ[P'] fun ω ↦ ⨅ a : DS, ⨆ b : DT, Y (a, b) ω := by
    filter_upwards [hYrow, hYc'] with ω h h'
    rw [separableSpaceInf_eq_range_real h']
    exact iInf_congr fun a ↦ h a
  set φ : DS × DT → S × T := fun p ↦ (p.1.1, p.2.1)
  obtain ⟨hYi, hle⟩ := integral_iInf_iSup_le_gordon (X := fun p ↦ X (φ p))
    (Y := fun p ↦ Y (φ p)) (hX.comp_right φ) (hY.comp_right φ)
    (fun p ↦ hmX (φ p)) (fun p ↦ hmY (φ p)) (fun p ↦ hvar (φ p))
    (fun a b b' hbb' ↦ hrow a b b' fun h ↦ hbb' (Subtype.ext h))
    (fun a a' b b' haa' ↦ hcross a a' b b' fun h ↦ haa' (Subtype.ext h))
    (by filter_upwards [hYb] with ω h a using
      (h a).mono (Set.range_comp_subset_range Subtype.val fun t ↦ Y (a, t) ω))
    (by
      filter_upwards [hXb', hXrow] with ω h hr
      convert h.mono (Set.range_comp_subset_range Subtype.val fun s ↦ ⨆ t, X (s, t) ω)
        using 2
      ext a
      exact (hr a).symm)
    (fun a ↦ (hYr a).congr (by filter_upwards [hYrow] with ω h using h a))
    (hXi.congr hX')
  refine ⟨hYi.congr hY'.symm, ?_⟩
  rwa [integral_congr_ae hX', integral_congr_ae hY']

end IsGaussianProcess

end ProbabilityTheory
