/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Kei Tsukamoto
-/
import StatsMLlib.LearningTheory.FunctionClass.HilbertPredictor
import StatsMLlib.LearningTheory.UniformDeviation.Confidence

/-!
# Feature-map kernels and RKHS predictor bounds

Mathlib does not currently provide a construction of the RKHS associated with
an arbitrary positive-semidefinite kernel.  This module therefore starts with
a feature map `Φ : 𝒳 → H` into a real Hilbert space and uses the induced kernel

`K(x,y) = ⟪Φ x, Φ y⟫`.

This is exactly the representation used in the proof of Mohri, Rostamizadeh,
and Talwalkar, *Foundations of Machine Learning*, Theorem 6.12.
-/

noncomputable section

universe u v

open Real

variable {n : ℕ}
variable {𝒳 : Type u}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The kernel induced by a feature map into a real inner-product space. -/
noncomputable def kernelOfFeatureMap (Φ : 𝒳 → H) (x y : 𝒳) : ℝ :=
  ⟪Φ x, Φ y⟫

/-- The diagonal of a feature-map kernel is the squared feature norm. -/
@[simp]
lemma kernelOfFeatureMap_self
    (Φ : 𝒳 → H) (x : 𝒳) :
    kernelOfFeatureMap Φ x x = ‖Φ x‖ ^ 2 := by
  exact real_inner_self_eq_norm_sq _

/--
A feature-map kernel is positive semidefinite: every finite Gram quadratic
form is nonnegative.
-/
theorem kernelOfFeatureMap_positiveSemidefinite
    (Φ : 𝒳 → H) {m : ℕ} (x : Fin m → 𝒳) (a : Fin m → ℝ) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m,
      a i * a j * kernelOfFeatureMap Φ (x i) (x j) := by
  have hgram :
      ∑ i : Fin m, ∑ j : Fin m,
          a i * a j * kernelOfFeatureMap Φ (x i) (x j) =
        ‖∑ i : Fin m, a i • Φ (x i)‖ ^ 2 := by
    calc
      ∑ i : Fin m, ∑ j : Fin m,
          a i * a j * kernelOfFeatureMap Φ (x i) (x j) =
          ∑ i : Fin m, ∑ j : Fin m,
            ⟪a i • Φ (x i), a j • Φ (x j)⟫ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [kernelOfFeatureMap, real_inner_smul_left,
          real_inner_smul_right]
        ring
      _ = ⟪∑ i : Fin m, a i • Φ (x i),
          ∑ j : Fin m, a j • Φ (x j)⟫ := by
        rw [sum_inner]
        apply Finset.sum_congr rfl
        intro i _
        rw [inner_sum]
      _ = ‖∑ i : Fin m, a i • Φ (x i)‖ ^ 2 :=
        real_inner_self_eq_norm_sq _
  rw [hgram]
  positivity

/-- The diagonal kernel trace of a sample. -/
noncomputable def kernelTrace
    (Φ : 𝒳 → H) (S : Fin n → 𝒳) : ℝ :=
  ∑ k : Fin n, kernelOfFeatureMap Φ (S k) (S k)

@[simp]
lemma kernelTrace_eq_sum_norm_sq
    (Φ : 𝒳 → H) (S : Fin n → 𝒳) :
    kernelTrace Φ S = ∑ k : Fin n, ‖Φ (S k)‖ ^ 2 := by
  simp [kernelTrace]

/-- Prediction by a bounded Hilbert-space weight after applying a feature map. -/
noncomputable def rkhsPredictor
    (Φ : 𝒳 → H) {Λ : ℝ}
    (w : Metric.closedBall (0 : H) Λ) (x : 𝒳) : ℝ :=
  hilbertPredictor w (Φ x)

/-- Continuity of the feature-map predictor in its weight. -/
lemma continuous_rkhsPredictor_weight
    (Φ : 𝒳 → H) {Λ : ℝ} (x : 𝒳) :
    Continuous fun w : Metric.closedBall (0 : H) Λ ↦
      rkhsPredictor Φ w x :=
  continuous_hilbertPredictor_weight (Φ x)

/-- Measurability in the input follows from measurability of the feature map. -/
lemma measurable_rkhsPredictor_input
    [MeasurableSpace 𝒳] [MeasurableSpace H] [BorelSpace H]
    (Φ : 𝒳 → H) (hΦ : Measurable Φ) {Λ : ℝ}
    (w : Metric.closedBall (0 : H) Λ) :
    Measurable fun x ↦ rkhsPredictor Φ w x :=
  (continuous_hilbertPredictor_input w).measurable.comp hΦ

/-- A diagonal kernel bound implies the corresponding feature-norm bound. -/
lemma norm_featureMap_le_of_kernel_self_le
    (Φ : 𝒳 → H) {r : ℝ} (hr : 0 ≤ r) {x : 𝒳}
    (hx : kernelOfFeatureMap Φ x x ≤ r ^ 2) :
    ‖Φ x‖ ≤ r := by
  rw [kernelOfFeatureMap_self] at hx
  exact (sq_le_sq₀ (norm_nonneg _) hr).mp hx

/-- Pointwise boundedness obtained from the weight and kernel-diagonal bounds. -/
lemma abs_rkhsPredictor_le
    (Φ : 𝒳 → H) {Λ r : ℝ} (hΛ : 0 ≤ Λ) (hr : 0 ≤ r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (w : Metric.closedBall (0 : H) Λ) (x : 𝒳) :
    |rkhsPredictor Φ w x| ≤ r * Λ := by
  calc
    |rkhsPredictor Φ w x| ≤ Λ * ‖Φ x‖ :=
      abs_hilbertPredictor_le w (Φ x)
    _ ≤ Λ * r := by
      gcongr
      exact norm_featureMap_le_of_kernel_self_le Φ hr (hdiag x)
    _ = r * Λ := mul_comm _ _

/--
Mohri, Rostamizadeh, and Talwalkar, Theorem 6.12, in kernel-trace form:

`Rhatₙ ≤ Λ / n * sqrt (∑ₖ K(Sₖ,Sₖ))`.

The feature space is assumed complete here to match the Hilbert/RKHS
interpretation. The underlying dimension-free theorem,
`hilbertPredictor_empiricalRademacherComplexity_le`, does not require completeness.
-/
theorem rkhs_empiricalRademacherComplexity_le_kernelTrace
    [CompleteSpace H]
    (Φ : 𝒳 → H) (Λ : ℝ) (hΛ : 0 ≤ Λ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n
        (rkhsPredictor Φ :
          Metric.closedBall (0 : H) Λ → 𝒳 → ℝ) S ≤
      Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ S) := by
  change empiricalRademacherComplexity n
      (fun w x ↦ hilbertPredictor w (Φ x)) S ≤
    Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ S)
  rw [empiricalRademacherComplexity_comp]
  simpa using
    hilbertPredictor_empiricalRademacherComplexity_le
      Λ hΛ (Φ ∘ S)

/--
Uniform-diagonal form of Mohri et al., Theorem 6.12:

if `K(x,x) ≤ r²`, then `Rhatₙ ≤ r Λ / √n`.
-/
theorem rkhs_empiricalRademacherComplexity_le
    [CompleteSpace H]
    (Φ : 𝒳 → H) (Λ r : ℝ) (hΛ : 0 ≤ Λ) (hr : 0 ≤ r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n
        (rkhsPredictor Φ :
          Metric.closedBall (0 : H) Λ → 𝒳 → ℝ) S ≤
      r * Λ / Real.sqrt (n : ℝ) := by
  calc
    empiricalRademacherComplexity n
        (rkhsPredictor Φ :
          Metric.closedBall (0 : H) Λ → 𝒳 → ℝ) S ≤
        Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ S) :=
      rkhs_empiricalRademacherComplexity_le_kernelTrace Φ Λ hΛ S
    _ ≤ Λ * (n : ℝ)⁻¹ *
        Real.sqrt (∑ _k : Fin n, r ^ 2) := by
      rw [kernelTrace_eq_sum_norm_sq]
      gcongr with k
      exact norm_featureMap_le_of_kernel_self_le Φ hr (hdiag (S k))
    _ = Λ * (n : ℝ)⁻¹ * Real.sqrt ((n : ℝ) * r ^ 2) := by simp
    _ = Λ * (n : ℝ)⁻¹ * (Real.sqrt (n : ℝ) * r) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hr]
    _ = r * Λ / Real.sqrt (n : ℝ) := by
      by_cases hn : 0 < n
      · have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
        field_simp [hsqrt]
        rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        simp

end

-- The fixed-sample kernel estimates above and the generalization bounds below are
-- kept in one module. The section that follows carries the context the second group
-- needs, including its own universe assignment, which differs from the one above.
noncomputable section Generalization

universe u v w

open MeasureTheory ProbabilityTheory Real TopologicalSpace
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω]
variable {𝒳 : Type v} [MeasurableSpace 𝒳]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SeparableSpace H]
variable {μ : Measure Ω}

set_option hygiene false in
local notation "μⁿ" => Measure.pi (fun _ ↦ μ)
/--
Expected Rademacher estimate for the bounded feature-map class:

`Rₙ ≤ r Λ / √n`.
-/
theorem rkhs_rademacherComplexity_le
    [IsProbabilityMeasure μ]
    (Φ : 𝒳 → H) (hΦ : Measurable Φ)
    (Λ r : ℝ) (hΛ : 0 ≤ Λ) (hr : 0 ≤ r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (X : Ω → 𝒳) (hX : Measurable X) :
    rademacherComplexity n
        (rkhsPredictor Φ :
          Metric.closedBall (0 : H) Λ → 𝒳 → ℝ) μ X ≤
      r * Λ / Real.sqrt (n : ℝ) := by
  let : Nonempty (Metric.closedBall (0 : H) Λ) :=
    (Metric.nonempty_closedBall.mpr hΛ).to_subtype
  apply rademacherComplexity_le_of_empirical_le_separable
    (F := rkhsPredictor Φ) (X := X)
  · intro w
    exact (measurable_rkhsPredictor_input Φ hΦ w).comp hX
  · exact mul_nonneg hr hΛ
  · exact fun w x ↦ abs_rkhsPredictor_le Φ hΛ hr hdiag w x
  · exact continuous_rkhsPredictor_weight Φ
  · exact rkhs_empiricalRademacherComplexity_le Φ Λ r hΛ hr hdiag

/--
Expected uniform-deviation estimate:

`E[UDₙ] ≤ 2 r Λ / √n`.
-/
theorem rkhs_uniformDeviation_expectation_le
    [Nonempty 𝒳] [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (Φ : 𝒳 → H) (hΦ : Measurable Φ)
    (Λ r : ℝ) (hΛ : 0 ≤ Λ) (hr : 0 ≤ r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (X : Ω → 𝒳) (hX : Measurable X) :
    μⁿ[fun S : Fin n → Ω ↦
      uniformDeviation n
        (rkhsPredictor Φ :
          Metric.closedBall (0 : H) Λ → 𝒳 → ℝ)
        μ X (X ∘ S)] ≤
      2 * (r * Λ / Real.sqrt (n : ℝ)) := by
  let : Nonempty (Metric.closedBall (0 : H) Λ) :=
    (Metric.nonempty_closedBall.mpr hΛ).to_subtype
  apply uniform_deviation_expectation_le_of_empirical_le_separable
    (F := rkhsPredictor Φ) hn
  · exact fun w ↦ measurable_rkhsPredictor_input Φ hΦ w
  · exact hX
  · exact mul_nonneg hr hΛ
  · exact fun w x ↦ abs_rkhsPredictor_le Φ hΛ hr hdiag w x
  · exact continuous_rkhsPredictor_weight Φ
  · exact rkhs_empiricalRademacherComplexity_le Φ Λ r hΛ hr hdiag

/--
Deterministic confidence bound obtained from the diagonal estimate:

`Pr{UDₙ ≥ 2 rΛ/√n + rΛ sqrt(2 log(1/δ)/n)} ≤ δ`.

In the notation of Mohri et al., Theorem 6.12, Lean's `Λ` is the RKHS weight
radius and `r²` bounds `K(x,x)`.  `CompleteSpace H` records that the feature
space is Hilbert, `SeparableSpace H` is needed only for the uncountable-class
generalization bridge, `hΦ` supplies measurability of every predictor, and
`hdiag` supplies both the Rademacher and concentration radii.
-/
theorem rkhs_uniformDeviation_tail_bound_delta
    [Nonempty 𝒳] [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (Φ : 𝒳 → H) (hΦ : Measurable Φ)
    (Λ r : ℝ) (hΛ : 0 < Λ) (hr : 0 < r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (X : Ω → 𝒳) (hX : Measurable X)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * (r * Λ / Real.sqrt (n : ℝ)) +
          (r * Λ) * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n
          (rkhsPredictor Φ :
            Metric.closedBall (0 : H) Λ → 𝒳 → ℝ)
          μ X (X ∘ S)}).toReal ≤ δ := by
  let : Nonempty (Metric.closedBall (0 : H) Λ) :=
    (Metric.nonempty_closedBall.mpr hΛ.le).to_subtype
  apply uniform_deviation_tail_bound_separable_of_empirical_le_delta
    (μ := μ) hn (F := rkhsPredictor Φ)
  · exact fun w ↦ measurable_rkhsPredictor_input Φ hΦ w
  · exact hX
  · exact mul_pos hr hΛ
  · exact fun w x ↦ abs_rkhsPredictor_le Φ hΛ.le hr.le hdiag w x
  · exact continuous_rkhsPredictor_weight Φ
  · exact rkhs_empiricalRademacherComplexity_le
      Φ Λ r hΛ.le hr.le hdiag
  · exact hδ
  · exact hδ_one

/--
Sample-dependent confidence bound retaining the observed kernel trace:

`Pr{UDₙ ≥ 2Λ/n sqrt(trace K_S)
    + 3rΛ sqrt(2 log(2/δ)/n)} ≤ δ`.
-/
theorem rkhs_uniformDeviation_tail_bound_kernelTrace_delta
    [Nonempty 𝒳] [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (Φ : 𝒳 → H) (hΦ : Measurable Φ)
    (Λ r : ℝ) (hΛ : 0 < Λ) (hr : 0 < r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (X : Ω → 𝒳) (hX : Measurable X)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * (Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ (X ∘ S))) +
          3 * ((r * Λ) *
            Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
        uniformDeviation n
          (rkhsPredictor Φ :
            Metric.closedBall (0 : H) Λ → 𝒳 → ℝ)
          μ X (X ∘ S)}).toReal ≤ δ := by
  let : Nonempty (Metric.closedBall (0 : H) Λ) :=
    (Metric.nonempty_closedBall.mpr hΛ.le).to_subtype
  exact uniform_deviation_tail_bound_separable_of_sample_empirical_le_delta
    (μ := μ) hn
    (rkhsPredictor Φ :
      Metric.closedBall (0 : H) Λ → 𝒳 → ℝ)
    (fun w ↦ measurable_rkhsPredictor_input Φ hΦ w)
    X hX
    (fun S ↦ Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ S))
    (mul_pos hr hΛ)
    (fun w x ↦ abs_rkhsPredictor_le Φ hΛ.le hr.le hdiag w x)
    (continuous_rkhsPredictor_weight Φ)
    (rkhs_empiricalRademacherComplexity_le_kernelTrace Φ Λ hΛ.le)
    hδ hδ_one



/-! ## Examples

Worked uses of this module's public API. They are elaborated with the library, so they
double as acceptance tests that these statements stay usable as written.
-/

/-!
## Feature-map RKHS predictors

Let $\Phi:\mathcal X\to\mathcal H$ map into a real Hilbert space and define

$$
K(x,y)=\langle\Phi(x),\Phi(y)\rangle,
\qquad
f_w(x)=\langle w,\Phi(x)\rangle,
\qquad
\lVert w\rVert\le\Lambda.
$$

The sample-dependent form of Mohri, Rostamizadeh, and Talwalkar,
Theorem 6.12 retains the observed kernel trace:

$$
\Pr\!\left\{
  \operatorname{UD}_n
  \ge \frac{2\Lambda}{n}
      \sqrt{\sum_k K(X_k,X_k)}
    +3r\Lambda\sqrt{\frac{2\log(2/\delta)}{n}}
\right\}\le\delta.
$$
-/

/-- Main RKHS example retaining the observed kernel trace. -/
example
    [Nonempty 𝒳]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (Φ : 𝒳 → H) (hΦ : Measurable Φ)
    (Λ r : ℝ) (hΛ : 0 < Λ) (hr : 0 < r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (X : Ω → 𝒳) (hX : Measurable X)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * (Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ (X ∘ S))) +
          3 * ((r * Λ) *
            Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
        uniformDeviation n
          (rkhsPredictor Φ :
            Metric.closedBall (0 : H) Λ → 𝒳 → ℝ)
          μ X (X ∘ S)}).toReal ≤ δ := by
  exact rkhs_uniformDeviation_tail_bound_kernelTrace_delta
    hn Φ hΦ Λ r hΛ hr hdiag X hX hδ hδ_one

/-!
Replacing every diagonal value by $K(x,x)\le r^2$ gives the deterministic
endpoint

$$
\Pr\!\left\{
  \operatorname{UD}_n
  \ge \frac{2r\Lambda}{\sqrt n}
    +r\Lambda\sqrt{\frac{2\log(1/\delta)}{n}}
\right\}\le\delta.
$$

Completeness records the Hilbert-space interpretation; separability is used
only when the bounded weight ball is reduced to a countable dense subclass.
-/

/-- Main RKHS example using only a uniform kernel-diagonal bound. -/
example
    [Nonempty 𝒳]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (Φ : 𝒳 → H) (hΦ : Measurable Φ)
    (Λ r : ℝ) (hΛ : 0 < Λ) (hr : 0 < r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (X : Ω → 𝒳) (hX : Measurable X)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * (r * Λ / Real.sqrt (n : ℝ)) +
          (r * Λ) * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n
          (rkhsPredictor Φ :
            Metric.closedBall (0 : H) Λ → 𝒳 → ℝ)
          μ X (X ∘ S)}).toReal ≤ δ := by
  exact rkhs_uniformDeviation_tail_bound_delta
    hn Φ hΦ Λ r hΛ hr hdiag X hX hδ hδ_one

end Generalization
