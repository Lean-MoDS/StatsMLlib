/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import StatsMLlib.LearningTheory.Rademacher.Complexity
import StatsMLlib.LearningTheory.UniformDeviation.Defs
import StatsMLlib.LearningTheory.EmpiricalRiskMinimization.Defs
import StatsMLlib.Analysis.FiniteSample
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sequences

/-!
# Pointwise separable function classes

A function class `F : H → 𝒳 → ℝ` is *pointwise separable* if a countable subfamily
`g : ℕ → H` approximates every member of the class pointwise along a sequence, with one
sequence serving all inputs `x` at once.  This is the "pointwise measurable class" condition of
van der Vaart and Wellner, *Weak Convergence and Empirical Processes*, Example 2.3.4.

For a uniformly bounded class, the condition reduces the suprema over `H` that define empirical
Rademacher complexity, Rademacher complexity, and uniform deviation to suprema over `ℕ`.  The
reduction for uniform deviation uses dominated convergence along a sequence, so `H` carries no
topology.  Like `StatsMLlib.LearningTheory.Rademacher.Reindex`, these lemmas change the index of a
class while preserving the three central quantities.

Continuity in the parameter is one sufficient condition (`PointwiseSeparable.of_continuous`),
but it is not necessary: threshold classes `x ↦ 1[x ≤ t]` are pointwise separable although they
are discontinuous in `t`.

## Main definitions

* `PointwiseSeparable`: a countable subfamily approximates the class pointwise.

## Main results

* `empiricalRademacherComplexity_eq_comp_of_tendsto`,
  `rademacherComplexity_eq_comp_of_tendsto`, `uniformDeviation_eq_comp_of_tendsto`: the
  reductions to the countable subfamily.
* `PointwiseSeparable.of_continuous`: a class continuous in a separable Fréchet–Urysohn
  parameter space is pointwise separable.
* `PointwiseSeparable.comp`, `PointwiseSeparable.supervisedLossClass`: stability under
  composition with a continuous outer map, such as a loss.
-/

open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u v w x

variable {Ω : Type u} [MeasurableSpace Ω] {H : Type v} {𝒳 : Type w}

/--
A function class `F` is pointwise separable if some sequence `g` of hypotheses approximates every
hypothesis `h` pointwise along a subsequence `g ∘ u`, the same subsequence for every input.
-/
def PointwiseSeparable (F : H → 𝒳 → ℝ) : Prop :=
  ∃ g : ℕ → H, ∀ h, ∃ u : ℕ → ℕ, ∀ x,
    Tendsto (fun m ↦ F (g (u m)) x) atTop (𝓝 (F h x))

/--
A bounded indexed supremum equals the supremum along a sequence `g` when every value is a limit
of values along `g`.
-/
theorem ciSup_eq_ciSup_comp_of_tendsto [Nonempty H] {Φ : H → ℝ} (g : ℕ → H)
    (hΦ : BddAbove (range Φ))
    (hlim : ∀ h, ∃ u : ℕ → ℕ, Tendsto (fun m ↦ Φ (g (u m))) atTop (𝓝 (Φ h))) :
    ⨆ h, Φ h = ⨆ m, Φ (g m) := by
  have hg : BddAbove (range fun m ↦ Φ (g m)) :=
    hΦ.mono (by rintro _ ⟨m, rfl⟩; exact ⟨g m, rfl⟩)
  apply le_antisymm
  · apply ciSup_le
    intro h
    obtain ⟨u, hu⟩ := hlim h
    exact le_of_tendsto' hu fun m ↦ le_ciSup hg (u m)
  · exact ciSup_le fun m ↦ le_ciSup hΦ (g m)

section Reduction

variable {n : ℕ}

/-- A sample average of a family bounded by `b` is bounded by `|b|`, also for `n = 0`. -/
private lemma abs_sampleAverage_le (a : Fin n → 𝒳 → ℝ) (S : Fin n → 𝒳) {b : ℝ}
    (ha : ∀ k x, |a k x| ≤ b) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, a k (S k)| ≤ |b| := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · exact (abs_normalized_fin_sum_le hn a S ha).trans (le_abs_self b)

/--
For a uniformly bounded class, empirical Rademacher complexity is unchanged by restricting to a
sequence that approximates the class pointwise.
-/
theorem empiricalRademacherComplexity_eq_comp_of_tendsto [Nonempty H]
    (F : H → 𝒳 → ℝ) (g : ℕ → H)
    (hg : ∀ h, ∃ u : ℕ → ℕ, ∀ x, Tendsto (fun m ↦ F (g (u m)) x) atTop (𝓝 (F h x)))
    {b : ℝ} (hF : ∀ h x, |F h x| ≤ b) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n F S = empiricalRademacherComplexity n (F ∘ g) S := by
  dsimp only [empiricalRademacherComplexity]
  congr 1
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  refine ciSup_eq_ciSup_comp_of_tendsto
    (Φ := fun h ↦ |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F h (S k)|) g ?_ ?_
  · refine ⟨|b|, ?_⟩
    rintro _ ⟨h, rfl⟩
    exact abs_sampleAverage_le (fun k x ↦ (σ k : ℝ) * F h x) S
      (fun k x ↦ by simpa [abs_mul, abs_sigma] using hF h x)
  · intro h
    obtain ⟨u, hu⟩ := hg h
    refine ⟨u, (continuous_abs.tendsto _).comp ?_⟩
    exact ((tendsto_finsetSum _ fun k _ ↦ (hu (S k)).const_mul _).const_mul _)

/--
For a uniformly bounded class, Rademacher complexity is unchanged by restricting to a sequence
that approximates the class pointwise.
-/
theorem rademacherComplexity_eq_comp_of_tendsto [Nonempty H]
    (F : H → 𝒳 → ℝ) (g : ℕ → H)
    (hg : ∀ h, ∃ u : ℕ → ℕ, ∀ x, Tendsto (fun m ↦ F (g (u m)) x) atTop (𝓝 (F h x)))
    {b : ℝ} (hF : ∀ h x, |F h x| ≤ b) (μ : Measure Ω) (X : Ω → 𝒳) :
    rademacherComplexity n F μ X = rademacherComplexity n (F ∘ g) μ X := by
  dsimp only [rademacherComplexity]
  congr 1
  funext ω
  exact empiricalRademacherComplexity_eq_comp_of_tendsto F g hg hF (X ∘ ω)

/--
For a uniformly bounded measurable class, uniform deviation is unchanged by restricting to a
sequence that approximates the class pointwise.  The population term converges by dominated
convergence along the approximating sequence.
-/
theorem uniformDeviation_eq_comp_of_tendsto [Nonempty H]
    (F : H → 𝒳 → ℝ) (g : ℕ → H)
    (hg : ∀ h, ∃ u : ℕ → ℕ, ∀ x, Tendsto (fun m ↦ F (g (u m)) x) atTop (𝓝 (F h x)))
    {b : ℝ} (hF : ∀ h x, |F h x| ≤ b)
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → 𝒳)
    (hF_meas : ∀ h, Measurable (F h ∘ X)) (S : Fin n → 𝒳) :
    uniformDeviation n F μ X S = uniformDeviation n (F ∘ g) μ X S := by
  dsimp only [uniformDeviation]
  refine ciSup_eq_ciSup_comp_of_tendsto
    (Φ := fun h ↦ |(n : ℝ)⁻¹ * ∑ k : Fin n, F h (S k) - μ[fun ω ↦ F h (X ω)]|) g ?_ ?_
  · refine ⟨|b| + b * μ.real univ, ?_⟩
    rintro _ ⟨h, rfl⟩
    have hint : |μ[fun ω ↦ F h (X ω)]| ≤ b * μ.real univ := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω ↦ F h (X ω))
          (Filter.Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hF h (X ω))
    exact (abs_sub _ _).trans
      (add_le_add (abs_sampleAverage_le (fun _ x ↦ F h x) S (fun _ x ↦ hF h x)) hint)
  · intro h
    obtain ⟨u, hu⟩ := hg h
    refine ⟨u, (continuous_abs.tendsto _).comp ?_⟩
    refine Tendsto.sub
      ((tendsto_finsetSum _ fun k _ ↦ hu (S k)).const_mul _) ?_
    exact tendsto_integral_of_dominated_convergence (fun _ ↦ b)
      (fun m ↦ (hF_meas (g (u m))).aestronglyMeasurable) (integrable_const b)
      (fun m ↦ Filter.Eventually.of_forall fun ω ↦ by
        simpa [Real.norm_eq_abs] using hF (g (u m)) (X ω))
      (Filter.Eventually.of_forall fun ω ↦ hu (X ω))

end Reduction

namespace PointwiseSeparable

/--
A class indexed by a separable Fréchet–Urysohn space and continuous in the parameter at every
input is pointwise separable, along a dense sequence.  First-countable spaces, in particular
metric spaces, are Fréchet–Urysohn.
-/
theorem of_continuous [TopologicalSpace H] [TopologicalSpace.SeparableSpace H]
    [FrechetUrysohnSpace H] [Nonempty H]
    {F : H → 𝒳 → ℝ} (hF : ∀ x, Continuous fun h ↦ F h x) :
    PointwiseSeparable F := by
  refine ⟨TopologicalSpace.denseSeq H, fun h ↦ ?_⟩
  have hmem : h ∈ closure (range (TopologicalSpace.denseSeq H)) := by
    rw [(TopologicalSpace.denseRange_denseSeq H).closure_eq]
    exact mem_univ h
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose u hu using ha
  refine ⟨u, fun x ↦ ?_⟩
  simp only [hu]
  exact ((hF x).tendsto h).comp hlim

/--
Pointwise separability is preserved by reading the class at `π z` and post-composing with a map
`ψ z` that is continuous for every `z`.
-/
theorem comp {𝒵 : Type*} {F : H → 𝒳 → ℝ} (hF : PointwiseSeparable F)
    (π : 𝒵 → 𝒳) {ψ : 𝒵 → ℝ → ℝ} (hψ : ∀ z, Continuous (ψ z)) :
    PointwiseSeparable fun h z ↦ ψ z (F h (π z)) := by
  obtain ⟨g, hg⟩ := hF
  refine ⟨g, fun h ↦ ?_⟩
  obtain ⟨u, hu⟩ := hg h
  exact ⟨u, fun z ↦ ((hψ z).tendsto _).comp (hu (π z))⟩

/--
A supervised loss class built from a pointwise separable predictor class and a loss continuous
in the prediction is pointwise separable.
-/
theorem supervisedLossClass {𝒴 : Type*} {F : H → 𝒳 → ℝ} (hF : PointwiseSeparable F)
    {loss : ℝ → 𝒴 → ℝ} (hloss : ∀ y, Continuous fun u ↦ loss u y) :
    PointwiseSeparable (_root_.supervisedLossClass F loss) :=
  hF.comp Prod.fst (ψ := fun z u ↦ loss u z.2) fun z ↦ hloss z.2

end PointwiseSeparable
