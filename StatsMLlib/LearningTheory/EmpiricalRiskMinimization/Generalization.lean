/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Kei Tsukamoto
-/
import StatsMLlib.LearningTheory.EmpiricalRiskMinimization.Basic
import StatsMLlib.LearningTheory.Rademacher.Contraction
import StatsMLlib.LearningTheory.UniformDeviation.Confidence

/-!
# Excess-risk bounds for empirical risk minimization

This module composes two reusable bridges:

1. an `η`-approximate ERM has excess risk at most
   `2 * uniformDeviation + η`;
2. uniform deviation is controlled by expected or observed empirical
   Rademacher complexity.

No measurability assumption is imposed on the learning rule
`A : (Fin n → 𝒵) → H`: the probability is interpreted through
`Measure.real`, hence as an outer probability when the bad event is not known
to be measurable.
-/

noncomputable section

universe u v w

open MeasureTheory ProbabilityTheory Real TopologicalSpace
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {H : Type v} {𝒵 : Type w}
variable {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
Expected-complexity excess-risk tail bound for an approximate ERM:

`Pr{R(A(S)) - R(hstar) ≥ 4 C + 2 ε + η}
  ≤ exp (-n ε² / (2 b²))`.
-/
theorem approxERM_excessRisk_tail_bound_separable_of_rademacher_le
    [MeasurableSpace 𝒵] [Nonempty 𝒵] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (ℓ : H → 𝒵 → ℝ) (hℓ_meas : ∀ h, Measurable (ℓ h))
    (Z : Ω → 𝒵) (hZ : Measurable Z)
    {b C η : ℝ} (hb : 0 < b) (hℓ_bound : ∀ h z, |ℓ h z| ≤ b)
    (hℓ_cont : ∀ z : 𝒵, Continuous fun h ↦ ℓ h z)
    (A : (Fin n → 𝒵) → H)
    (hA : ∀ S, IsApproxERM η n ℓ S (A S))
    (hC : rademacherComplexity n ℓ μ Z ≤ C)
    (hstar : H) {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S : Fin n → Ω |
      4 * C + 2 * ε + η ≤
        excessRisk ℓ μ Z (A (Z ∘ S)) hstar}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  calc
    _ ≤ (μⁿ {S : Fin n → Ω |
        2 * C + ε ≤ uniformDeviation n ℓ μ Z (Z ∘ S)}).toReal := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro S hbad
      change 4 * C + 2 * ε + η ≤
        excessRisk ℓ μ Z (A (Z ∘ S)) hstar at hbad
      change 2 * C + ε ≤ uniformDeviation n ℓ μ Z (Z ∘ S)
      have horacle :=
        (hA (Z ∘ S)).excessRisk_le_two_mul_uniformDeviation
          (μ := μ) (Z := Z) (hstar := hstar)
          (bddAbove_range_riskDeviation
            hn (fun h ↦ (hℓ_meas h).comp hZ) hℓ_bound (Z ∘ S))
      linarith
    _ ≤ _ :=
      uniform_deviation_tail_bound_separable_of_rademacher_le
        (μ := μ) ℓ hℓ_meas Z hZ hb hℓ_bound hℓ_cont hC hε

/--
Observed empirical-complexity excess-risk tail bound for an approximate ERM:

`Pr{R(A(S)) - R(hstar) ≥ 4 Rhatₙ(ℓ;S) + 6 ε + η}
  ≤ 2 exp (-n ε² / (2 b²))`.
-/
theorem approxERM_excessRisk_tail_bound_separable_of_empirical_complexity
    [MeasurableSpace 𝒵] [Nonempty 𝒵] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (ℓ : H → 𝒵 → ℝ) (hℓ_meas : ∀ h, Measurable (ℓ h))
    (Z : Ω → 𝒵) (hZ : Measurable Z)
    {b η : ℝ} (hb : 0 < b) (hℓ_bound : ∀ h z, |ℓ h z| ≤ b)
    (hℓ_cont : ∀ z : 𝒵, Continuous fun h ↦ ℓ h z)
    (A : (Fin n → 𝒵) → H)
    (hA : ∀ S, IsApproxERM η n ℓ S (A S))
    (hstar : H) {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S : Fin n → Ω |
      4 * empiricalRademacherComplexity n ℓ (Z ∘ S) + 6 * ε + η ≤
        excessRisk ℓ μ Z (A (Z ∘ S)) hstar}).toReal ≤
      2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  calc
    _ ≤ (μⁿ {S : Fin n → Ω |
        2 * empiricalRademacherComplexity n ℓ (Z ∘ S) + 3 * ε ≤
          uniformDeviation n ℓ μ Z (Z ∘ S)}).toReal := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro S hbad
      change
        4 * empiricalRademacherComplexity n ℓ (Z ∘ S) +
              6 * ε + η ≤
          excessRisk ℓ μ Z (A (Z ∘ S)) hstar at hbad
      change
        2 * empiricalRademacherComplexity n ℓ (Z ∘ S) + 3 * ε ≤
          uniformDeviation n ℓ μ Z (Z ∘ S)
      have horacle :=
        (hA (Z ∘ S)).excessRisk_le_two_mul_uniformDeviation
          (μ := μ) (Z := Z) (hstar := hstar)
          (bddAbove_range_riskDeviation
            hn (fun h ↦ (hℓ_meas h).comp hZ) hℓ_bound (Z ∘ S))
      linarith
    _ ≤ _ :=
      uniform_deviation_tail_bound_separable_of_empirical_complexity
        (μ := μ) ℓ hℓ_meas Z hZ hb hℓ_bound hℓ_cont hε

/--
Confidence-parameter form of the expected-complexity excess-risk bound:

`Pr{R(A(S)) - R(hstar) ≥ 4 C + 2 r(b,δ,n) + η} ≤ δ`.
-/
theorem approxERM_excessRisk_tail_bound_separable_of_rademacher_le_delta
    [MeasurableSpace 𝒵] [Nonempty 𝒵] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (ℓ : H → 𝒵 → ℝ) (hℓ_meas : ∀ h, Measurable (ℓ h))
    (Z : Ω → 𝒵) (hZ : Measurable Z)
    {b C η δ : ℝ} (hb : 0 < b) (hℓ_bound : ∀ h z, |ℓ h z| ≤ b)
    (hℓ_cont : ∀ z : 𝒵, Continuous fun h ↦ ℓ h z)
    (A : (Fin n → 𝒵) → H)
    (hA : ∀ S, IsApproxERM η n ℓ S (A S))
    (hC : rademacherComplexity n ℓ μ Z ≤ C)
    (hstar : H) (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      4 * C + 2 * deterministicConfidenceRadius b δ n + η ≤
        excessRisk ℓ μ Z (A (Z ∘ S)) hstar}).toReal ≤ δ := by
  calc
    _ ≤ (μⁿ {S : Fin n → Ω |
        2 * C + deterministicConfidenceRadius b δ n ≤
          uniformDeviation n ℓ μ Z (Z ∘ S)}).toReal := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro S hbad
      change
        4 * C + 2 * deterministicConfidenceRadius b δ n + η ≤
          excessRisk ℓ μ Z (A (Z ∘ S)) hstar at hbad
      change
        2 * C + deterministicConfidenceRadius b δ n ≤
          uniformDeviation n ℓ μ Z (Z ∘ S)
      have horacle :=
        (hA (Z ∘ S)).excessRisk_le_two_mul_uniformDeviation
          (μ := μ) (Z := Z) (hstar := hstar)
          (bddAbove_range_riskDeviation
            hn (fun h ↦ (hℓ_meas h).comp hZ) hℓ_bound (Z ∘ S))
      linarith
    _ ≤ δ :=
      uniform_deviation_tail_bound_separable_of_rademacher_le_delta
        (μ := μ) hn ℓ hℓ_meas Z hZ hb hℓ_bound hℓ_cont hC hδ hδ_one

/--
Confidence-parameter form retaining any sample-dependent empirical-complexity
upper bound `C(S)`:

`Pr{R(A(S)) - R(hstar) ≥ 4 C(S) + 6 r₂(b,δ,n) + η} ≤ δ`.
-/
theorem approxERM_excessRisk_tail_bound_separable_of_sample_empirical_le_delta
    [MeasurableSpace 𝒵] [Nonempty 𝒵] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (ℓ : H → 𝒵 → ℝ) (hℓ_meas : ∀ h, Measurable (ℓ h))
    (Z : Ω → 𝒵) (hZ : Measurable Z)
    (C : (Fin n → 𝒵) → ℝ)
    {b η δ : ℝ} (hb : 0 < b) (hℓ_bound : ∀ h z, |ℓ h z| ≤ b)
    (hℓ_cont : ∀ z : 𝒵, Continuous fun h ↦ ℓ h z)
    (A : (Fin n → 𝒵) → H)
    (hA : ∀ S, IsApproxERM η n ℓ S (A S))
    (hC : ∀ S, empiricalRademacherComplexity n ℓ S ≤ C S)
    (hstar : H) (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      4 * C (Z ∘ S) + 6 * sampleConfidenceRadius b δ n + η ≤
        excessRisk ℓ μ Z (A (Z ∘ S)) hstar}).toReal ≤ δ := by
  calc
    _ ≤ (μⁿ {S : Fin n → Ω |
        2 * C (Z ∘ S) + 3 * sampleConfidenceRadius b δ n ≤
          uniformDeviation n ℓ μ Z (Z ∘ S)}).toReal := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro S hbad
      change
        4 * C (Z ∘ S) + 6 * sampleConfidenceRadius b δ n + η ≤
          excessRisk ℓ μ Z (A (Z ∘ S)) hstar at hbad
      change
        2 * C (Z ∘ S) + 3 * sampleConfidenceRadius b δ n ≤
          uniformDeviation n ℓ μ Z (Z ∘ S)
      have horacle :=
        (hA (Z ∘ S)).excessRisk_le_two_mul_uniformDeviation
          (μ := μ) (Z := Z) (hstar := hstar)
          (bddAbove_range_riskDeviation
            hn (fun h ↦ (hℓ_meas h).comp hZ) hℓ_bound (Z ∘ S))
      linarith
    _ ≤ δ := by
      simpa [sampleConfidenceRadius, confidenceRadius] using
        uniform_deviation_tail_bound_separable_of_sample_empirical_le_delta
          (μ := μ) hn ℓ hℓ_meas Z hZ C hb hℓ_bound hℓ_cont hC hδ hδ_one

/--
Exact-ERM specialization of the expected-complexity tail bound.
-/
theorem erm_excessRisk_tail_bound_separable_of_rademacher_le
    [MeasurableSpace 𝒵] [Nonempty 𝒵] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (ℓ : H → 𝒵 → ℝ) (hℓ_meas : ∀ h, Measurable (ℓ h))
    (Z : Ω → 𝒵) (hZ : Measurable Z)
    {b C : ℝ} (hb : 0 < b) (hℓ_bound : ∀ h z, |ℓ h z| ≤ b)
    (hℓ_cont : ∀ z : 𝒵, Continuous fun h ↦ ℓ h z)
    (A : (Fin n → 𝒵) → H)
    (hA : ∀ S, IsERM n ℓ S (A S))
    (hC : rademacherComplexity n ℓ μ Z ≤ C)
    (hstar : H) {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S : Fin n → Ω |
      4 * C + 2 * ε ≤ excessRisk ℓ μ Z (A (Z ∘ S)) hstar}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  simpa using
    approxERM_excessRisk_tail_bound_separable_of_rademacher_le
      (μ := μ) hn ℓ hℓ_meas Z hZ hb hℓ_bound hℓ_cont A
      (fun S ↦ (hA S).isApproxERM) hC hstar hε

/--
Apply the observed empirical-complexity theorem directly to the supervised
loss class `(x,y) ↦ loss (F h x) y`.
-/
theorem supervised_approxERM_excessRisk_tail_bound_of_empirical_complexity
    {𝒳 𝒴 : Type*}
    [MeasurableSpace (𝒳 × 𝒴)] [Nonempty (𝒳 × 𝒴)] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (F : H → 𝒳 → ℝ) (loss : ℝ → 𝒴 → ℝ)
    (hclass_meas : ∀ h, Measurable (supervisedLossClass F loss h))
    (Z : Ω → 𝒳 × 𝒴) (hZ : Measurable Z)
    {b η : ℝ}
    (hb : 0 < b)
    (hclass_bound : ∀ h z, |supervisedLossClass F loss h z| ≤ b)
    (hclass_cont :
      ∀ z : 𝒳 × 𝒴, Continuous fun h ↦ supervisedLossClass F loss h z)
    (A : (Fin n → 𝒳 × 𝒴) → H)
    (hA :
      ∀ S, IsApproxERM η n (supervisedLossClass F loss) S (A S))
    (hstar : H) {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S : Fin n → Ω |
      4 * empiricalRademacherComplexity n
            (supervisedLossClass F loss) (Z ∘ S) +
          6 * ε + η ≤
        excessRisk (supervisedLossClass F loss) μ Z
          (A (Z ∘ S)) hstar}).toReal ≤
      2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp :=
  approxERM_excessRisk_tail_bound_separable_of_empirical_complexity
    (μ := μ) hn (supervisedLossClass F loss) hclass_meas Z hZ
    hb hclass_bound hclass_cont A hA hstar hε


/-! ## Examples

Worked uses of this module's public API. They are elaborated with the library, so they
double as acceptance tests that these statements stay usable as written.
-/

/-!
## Approximate ERM and excess risk

Let `A(S)` be an $\eta$-approximate empirical risk minimizer for a bounded
loss class $\ell$.  The deterministic oracle inequality

$$
R(A(S))-R(h^\star)
\leq
2\operatorname{UD}_n(\ell;S)+\eta
$$

composes with the observed empirical Rademacher estimate to give

$$
\Pr\!\left\{
R(A(S))-R(h^\star)
\geq
4C(S)+6b\sqrt{\frac{2\log(2/\delta)}{n}}+\eta
\right\}
\leq\delta,
$$

whenever
$\widehat{\mathfrak R}_n(\ell;S)\leq C(S)$.
The learning rule itself need not be measurable: the conclusion uses outer
probability through `Measure.real`.
-/

/-- Main sample-dependent excess-risk example for an approximate ERM. -/
example
    [MeasurableSpace 𝒵] [Nonempty 𝒵] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (ℓ : H → 𝒵 → ℝ) (hℓ_meas : ∀ h, Measurable (ℓ h))
    (X : Ω → 𝒵) (hX : Measurable X)
    (C : (Fin n → 𝒵) → ℝ)
    {b η δ : ℝ} (hb : 0 < b) (hℓ_bound : ∀ h x, |ℓ h x| ≤ b)
    (hℓ_cont : ∀ x : 𝒵, Continuous fun h ↦ ℓ h x)
    (A : (Fin n → 𝒵) → H)
    (hA : ∀ S, IsApproxERM η n ℓ S (A S))
    (hC : ∀ S, empiricalRademacherComplexity n ℓ S ≤ C S)
    (hstar : H) (hn : 0 < n) (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      4 * C (X ∘ S) + 6 * sampleConfidenceRadius b δ n + η ≤
        excessRisk ℓ μ X (A (X ∘ S)) hstar}).toReal ≤ δ := by
  exact approxERM_excessRisk_tail_bound_separable_of_sample_empirical_le_delta
    (μ := μ) hn ℓ hℓ_meas X hX C hb hℓ_bound hℓ_cont
    A hA hC hstar hδ hδ_one

/-!
For a finite hypothesis type, a centered $L$-Lipschitz loss satisfies the
absolute-complexity contraction estimate

$$
\widehat{\mathfrak R}_n((\ell-\ell(0,\cdot))\circ F;S)
\leq
2L\,\widehat{\mathfrak R}_n(F;S).
$$

The factor `2` is specific to this repository's absolute-value definition.
The corresponding one-sided theorem has factor `L`.
-/

/-- Main contraction example for a centered supervised loss. -/
example
    {𝒴 : Type*} [Fintype H] [Nonempty H]
    (F : H → 𝒵 → ℝ) (loss : ℝ → 𝒴 → ℝ)
    (S : Fin n → 𝒵 × 𝒴) {L : ℝ} (hL : 0 ≤ L)
    (hloss : ∀ y u v, |loss u y - loss v y| ≤ L * |u - v|) :
    empiricalRademacherComplexity n
        (supervisedLossClass F (centeredLoss loss)) S ≤
      2 * L *
        empiricalRademacherComplexity n
          (fun (h : H) (z : 𝒵 × 𝒴) ↦ F h z.1) S := by
  exact empiricalRademacherComplexity_centered_supervisedLossClass_le
    n F loss S hL hloss

end
