# Connecting Rademacher complexity to generalization bounds — implementation plan (StatsMLlib edition)

## 0. About this document

### 0.0 Goals

This effort has two goals.

1. **Refactor StatsMLlib along the design of the upstream plan.** We do not transplant the code
   changes of `auto-res/lean-rademacher` verbatim; we rebuild the corresponding development in
   StatsMLlib following the design that plan lays out (the chain of bridges: empirical complexity →
   expected complexity → uniform deviation → excess risk). Module placement, statement shapes, and
   the choice of canonical definitions therefore follow StatsMLlib's `ARCHITECTURE.md` and may differ
   from upstream. They already do: `coveringNumber` (Appendix B-1), the placement of
   `LipschitzParameter` (§0.5), and the decision not to create `Main.lean` or a `ForMathlib` layer
   (§0.2).
2. **Remove the duplication between the FoML-derived API and StatsMLlib's own statistical-learning
   API.** How to handle it is in Appendix B. Removing the duplication is a deliverable, not a side
   constraint: B-3 (three entropy-integral developments), B-5 (two dense-countable bridges),
   B-6 (two ERM predicates), and B-8 (three maximal inequalities).

The work is done by one person, in small PRs. PRs that touch the library's design direction are
discussed individually; Appendix C marks which ones those are.

### 0.1 Provenance

This document is a rewrite of `note/plan.md` from `auto-res/lean-rademacher` (branch `ss`, HEAD
`d50ea5c`), adapted to StatsMLlib's module structure. The original is kept verbatim at
[`note/upstream/plan.md`](upstream/plan.md), together with
[`note/upstream/summary.md`](upstream/summary.md), which describes the upstream implementation as a
whole.

The upstream work covered here is the 15 commits after `3819e1e` (`ce9a506` … `bc33376`).
StatsMLlib's current code corresponds to the state just before them, so **every item in this plan is
unstarted in StatsMLlib.**

### 0.2 Reading conventions

1. **File paths** are translated per the table in §0.3. All paths in §1 onward are already
   translated; `FoML/...` remains only in the §0.3 tables.
2. **Declaration names are not translated.** When StatsMLlib absorbed the upstream code it renamed
   modules only; declarations were kept at their original names, mostly in the root namespace. So
   `empiricalRademacherComplexity`, `uniformDeviation`, `coveringNumber`, and
   `linear_predictor_l2_bound'` are referenced by the same names as upstream. The one exception is
   `EmpiricalProcess.empiricalNorm` (the canonical version taking `Fin n → ℝ`); the sample-indexed
   form `empiricalNorm S f` used upstream exists as an `abbrev` in
   `LearningTheory/EmpiricalProcess/FunctionClass.lean`, so upstream code compiles unchanged.
3. **Watch the tense of "existing", "currently", and "already".** §12 onward (upstream Phase 6 and
   later) was written when upstream had finished Phase 5, so it calls declarations "existing" that
   Phases 1–5 *of this plan* still have to add. What actually exists in StatsMLlib today is exactly
   the content of the 24 modules listed under "Modules extended" in §0.3. Confusing spots are
   annotated, e.g. "(added in §5.1)".
4. **Checkboxes track StatsMLlib progress.** Items marked `[x]` upstream are `[ ]` here, since
   nothing has been ported. The one item that was `[ ]` upstream (existence of a risk minimizer,
   §18.2) is annotated as unfinished upstream too.
5. **No counterpart to `Main.lean` or `FoML.lean` is created.** `ARCHITECTURE.md` ("Module naming")
   forbids adding `Main.lean`, and a whole-library umbrella must be declaration-free. Upstream
   `FoML/Main.lean` is 562 lines but contains zero theorems — 13 `example`s and documentation — so
   each `example` is distributed to the end of the corresponding module as an acceptance test.
   Where the original text referred to `Main.lean`, this document says "public example" and names
   the destination.
6. **No `ForMathlib` layer.** Per `ARCHITECTURE.md` ("Refactoring decisions"), `ForMathlib` is no
   longer a layer-one directory. Upstream `FoML/ForMathlib/X/Y.lean` goes directly into the
   subject-owning directory.

StatsMLlib's own constraints (import direction, naming) come from `ARCHITECTURE.md`: imports may
only go in the direction

```text
{Order, MeasureTheory, Topology, LinearAlgebra}  →  Analysis  →  Probability
    →  LearningTheory  →  Statistics
```

### 0.3 Module mapping

#### Modules extended

| Upstream module | StatsMLlib module |
|---|---|
| `FoML/Defs.lean` | `StatsMLlib/LearningTheory/Rademacher/Defs.lean`, `StatsMLlib/LearningTheory/UniformDeviation/Defs.lean` |
| `FoML/Probability/Expectation.lean` | `StatsMLlib/Probability/Moments/Expectation.lean` |
| `FoML/Probability/MeasurePi.lean` | `StatsMLlib/Probability/Independence/FinsetPi.lean` |
| `FoML/Probability/Hoeffding.lean` | `StatsMLlib/Probability/Concentration/Hoeffding.lean` |
| `FoML/Probability/McDiarmid.lean` | `StatsMLlib/Probability/Concentration/McDiarmid.lean` |
| `FoML/Rademacher/Signs.lean` | `StatsMLlib/LearningTheory/Rademacher/Signs.lean` |
| `FoML/Rademacher/Symmetrization.lean` | `StatsMLlib/LearningTheory/Rademacher/Symmetrization.lean` |
| `FoML/Rademacher/Expectation.lean` | `StatsMLlib/LearningTheory/Rademacher/Complexity.lean` |
| `FoML/Rademacher/BoundedDifference.lean` | `StatsMLlib/LearningTheory/UniformDeviation/BoundedDifference.lean` |
| `FoML/Entropy/CoveringNumber.lean` | `StatsMLlib/Topology/MetricSpace/CoveringNumber/Basic.lean` |
| `FoML/Entropy/PseudoMetric.lean` | `StatsMLlib/LearningTheory/EmpiricalProcess/Metric.lean`, `StatsMLlib/LearningTheory/EmpiricalProcess/FunctionClass.lean` |
| `FoML/Entropy/MaximalInequality.lean` | `StatsMLlib/Probability/Concentration/Maximal.lean` |
| `FoML/Entropy/Massart.lean` | `StatsMLlib/LearningTheory/Rademacher/Massart.lean` |
| `FoML/Entropy/Dudley.lean` | `StatsMLlib/LearningTheory/Rademacher/Dudley.lean` |
| `FoML/Generalization/Dudley.lean` | `StatsMLlib/LearningTheory/Rademacher/Dudley.lean` |
| `FoML/Generalization/Countable.lean` | `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` |
| `FoML/Generalization/Separable.lean` | `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` |
| `FoML/Model/LinearPredictorL2.lean` | `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L2.lean` |
| `FoML/Generalization/LinearPredictorL2.lean` | `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L2.lean` |
| `FoML/Model/LinearPredictorL1.lean` | `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L1.lean` |
| `FoML/Generalization/LinearPredictorL1.lean` | `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L1.lean` |
| `FoML/ForMathlib/Probability/Moments.lean` | `StatsMLlib/Probability/Moments/Cumulant.lean` |
| `FoML/ForMathlib/Topology/SeparableSpace.lean` | `StatsMLlib/Topology/SeparableSpace/Supremum.lean` |
| `FoML/ForMathlib/Analysis/SumIntegralComparisons.lean` | `StatsMLlib/LearningTheory/Rademacher/Dudley.lean` (already absorbed) |

Where upstream splits one subject across `Model/*` and `Generalization/*`, StatsMLlib already keeps
it in one file (`LinearPredictor/L1.lean`, `L2.lean`). For the same reason `Entropy/Dudley` and
`Generalization/Dudley` share `Rademacher/Dudley.lean`. New subjects follow the same policy: the
fixed-sample bound and the generalization bound live in one file.

#### New modules

| Upstream module | StatsMLlib module | Note |
|---|---|---|
| `FoML/Rademacher/Reindex.lean` | `StatsMLlib/LearningTheory/Rademacher/Reindex.lean` | |
| `FoML/Entropy/FiniteClass.lean` + `FoML/Generalization/FiniteClass.lean` | `StatsMLlib/LearningTheory/Rademacher/FiniteClass.lean` | |
| `FoML/Entropy/LipschitzParameter.lean` + `FoML/Generalization/LipschitzParameter.lean` | `StatsMLlib/LearningTheory/Rademacher/LipschitzParameter.lean` | |
| `FoML/Learning/Contraction.lean` | `StatsMLlib/LearningTheory/Rademacher/Contraction.lean` | |
| `FoML/Model/HilbertPredictor.lean` | `StatsMLlib/LearningTheory/FunctionClass/HilbertPredictor.lean` | |
| `FoML/Model/RKHS.lean` + `FoML/Generalization/RKHS.lean` | `StatsMLlib/LearningTheory/FunctionClass/KernelPredictor.lean` | |
| `FoML/Generalization/Confidence.lean` | `StatsMLlib/LearningTheory/UniformDeviation/Confidence.lean` | |
| `FoML/Learning/Defs.lean` | `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Defs.lean` | new directory |
| `FoML/Learning/ERM.lean` | `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Basic.lean` | |
| `FoML/Generalization/Learning.lean` | `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Generalization.lean` | |
| `FoML/Generalization/RKHSLearning.lean` | `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/KernelPredictor.lean` | |
| `FoML/ForMathlib/MeasureTheory/Measure/Real.lean` | `StatsMLlib/MeasureTheory/Measure/Real.lean` | new directory |
| `FoML/ForMathlib/Probability/Confidence.lean` | `StatsMLlib/Probability/Concentration/Confidence.lean` | |
| `FoML/ForMathlib/Analysis/FiniteSample.lean` | `StatsMLlib/Analysis/FiniteSample.lean` | depth 2 (§0.4) |
| `FoML/ForMathlib/Order/ISup.lean` | `StatsMLlib/Order/IndexedSupremum.lean` | new layer-one `Order` (§0.4) |

`LearningTheory/EmpiricalRiskMinimization/` is a second-level directory that does not yet exist, so
the structure diagram in `ARCHITECTURE.md` must be updated. `EmpiricalRiskMinimization/Defs.lean`
satisfies the rule that `Defs.lean` is acceptable when its directory names a precise subject.

#### Upstream files with no counterpart

| Upstream | Disposition |
|---|---|
| `FoML.lean` | Not created. An umbrella cannot carry declarations (`ARCHITECTURE.md`). |
| `FoML/Main.lean` | Not created. Its `example`s are distributed to module ends (§0.2-5). |

### 0.4 Settled naming

The three open naming questions are settled as follows, in each case matching `ARCHITECTURE.md`
("Module naming") and the existing directory conventions.

1. **`StatsMLlib/Order/IndexedSupremum.lean`** (new layer-one `Order`)

   The file holds `ciSup_comp_of_surjective` and `abs_ciSup_sub_ciSup_le`: order-theoretic facts
   about conditionally complete lattices and about `ℝ`. It sits at the same bottom tier as
   `{MeasureTheory, Topology, LinearAlgebra}`, mirroring Mathlib's `Mathlib/Order/`.
   The file is named `IndexedSupremum` rather than `ISup` to match how upstream
   `SeparableSpaceSup.lean` was absorbed as `Topology/SeparableSpace/Supremum.lean`.

   `ARCHITECTURE.md`'s layer table, structure diagram, and import-direction diagram gain `Order`
   (bottom tier: `{Order, MeasureTheory, Topology, LinearAlgebra}`).

2. **`StatsMLlib/Analysis/FiniteSample.lean`** (depth 2)

   Two elementary bounds on normalized sums over `Fin n`. `StatsMLlib/Probability/SmallBall.lean`
   is an existing depth-2 file, so there is no need to create a subject directory for one file.

3. **`StatsMLlib/LearningTheory/EmpiricalRiskMinimization/`**

   `ARCHITECTURE.md` asks for "full subject names in paths … rather than provenance or project
   abbreviations", and every existing layer-two name is spelled out (`EmpiricalProcess`,
   `FunctionClass`, `UniformDeviation`, `LeastSquares`). So the directory is spelled out rather than
   `ERM/`. Its contents — risks, empirical risk, ERM predicates, oracle inequalities — identify the
   subject.

   For the same reason, upstream `Model/RKHS.lean` + `Generalization/RKHS.lean` land in
   **`StatsMLlib/LearningTheory/FunctionClass/KernelPredictor.lean`**, not `FunctionClass/RKHS.lean`.
   That name sits alongside the existing `FunctionClass/LinearPredictor/` and the new
   `FunctionClass/HilbertPredictor.lean`, and matches the content (kernels induced by a feature map
   and bounds for the resulting predictor class). Upstream `Generalization/RKHSLearning.lean`
   becomes `EmpiricalRiskMinimization/KernelPredictor.lean`.

`ARCHITECTURE.md` and `FILE_TREE.md` are updated by the first PR that creates each directory.

### 0.5 Items excluded from the port

- **Upstream Phase 9 (module hierarchy).** StatsMLlib moved to its own subject-first hierarchy in
  the 2026-07 refactor; there is no corresponding work. The mapping table of §0.3 is what
  corresponds to its output.
- **Deleting `FoML/WIP/RademacherProperty.lean` and normalizing line endings via `.gitattributes`.**
  Upstream-specific; StatsMLlib has no such files.
- **`data/Mohri_FML.pdf`** (the reference PDF of §16.1) is not added to the repository;
  bibliographic data goes in docstrings.
- **Migration to Mathlib's `Metric.coveringNumber`** (§13.7): the codomains differ (`ℕ` vs `ℕ∞`) and
  open vs closed balls differ, so not now.

## 2. Issues arising from the current types

### 2.1 From empirical to expected quantities

By definition,

```lean
rademacherComplexity n f μ X =
  μⁿ[fun ω ↦ empiricalRademacherComplexity n f (X ∘ ω)]
```

so given

```lean
∀ S, empiricalRademacherComplexity n f S ≤ C
```

and integrability of the integrand, monotonicity of the integral over a probability measure yields

```lean
rademacherComplexity n f μ X ≤ C
```

Lean's Bochner integral assigns a value to non-integrable functions as well, so we must not
short-circuit the proof through the convention that the integral is `0` in that case: the shared
lemma states integrability explicitly.

### 2.2 Inclusion of the generalization events

The bad event evaluated by the existing high-probability theorems is

```text
2 * rademacherComplexity n f μ X + ε ≤ uniformDeviation ...
```

Given `rademacherComplexity n f μ X ≤ C`,

```text
{2 * C + ε ≤ uniformDeviation}
  ⊆
{2 * rademacherComplexity n f μ X + ε ≤ uniformDeviation}
```

so `measure_mono` lets us reuse the existing tail bound as is.

### 2.3 Domain of the linear predictors

The existing generalization theorems assume `∀ i x, |f i x| ≤ b` on the whole domain, so they do not
apply directly to a nontrivial linear function on the ambient Euclidean space.

The end-to-end theorems use bounded subtypes as the input and index spaces.

- $\ell_2$ version:
  - input: `Metric.closedBall 0 X`
  - weights: `Metric.closedBall 0 W`
- $\ell_1/\ell_\infty$ version:
  - input: `LinftyBall Xinf`
  - weights: `L1Ball W`

The existing empirical bounds are applied by mapping subtype values into the ambient space, then
returned to the subtype version via the identity for empirical Rademacher complexity under
composition.

### 2.4 The one-sided Dudley bound

What is currently proved is

```lean
empiricalRademacherComplexity_without_abs n F S
  ≤ empiricalRademacherComplexity n F S
```

and this direction cannot carry Dudley's upper bound over to the absolute-value version.

Sign-symmetrizing the function class as

```text
F± = {F i | i ∈ ι} ∪ {-F i | i ∈ ι}
```

gives, for each sign vector,

```text
sup_i |A i| = sup_(i,s) s * A i
```

We prove this identity explicitly in Lean, then apply the existing Dudley theorem to `F±`.

## 3. Shared lemmas to add

### 3.1 Basic lemmas on empirical Rademacher complexity

Add to `StatsMLlib/LearningTheory/Rademacher/Signs.lean`:

1. Nonnegativity

   ```lean
   empiricalRademacherComplexity_nonneg
   ```

   from nonnegativity of the averaging factor, of each summand, and of the absolute supremum.

2. Commutation with a map on the domain

   ```lean
   empiricalRademacherComplexity_comp
   ```

   in the shape

   ```lean
   empiricalRademacherComplexity n
       (fun i x ↦ g i (q x)) S
     =
   empiricalRademacherComplexity n g (q ∘ S)
   ```

   used to connect the subtype version of the linear predictors to the existing theorems. If the
   sign symmetrization needs the analogue for the one-sided version, add that too.

3. Measurability and integrability

   For a countable index, measurability of each `f i ∘ X`, and uniform boundedness, prove

   ```lean
   Measurable fun ω ↦
     empiricalRademacherComplexity n f (X ∘ ω)

   Integrable (fun ω ↦
     empiricalRademacherComplexity n f (X ∘ ω)) μⁿ
   ```

   collecting the arguments currently used in `measurable_signed_sup_sum_fst_core` and
   `abs_sum_sup_signed_le_pow_mul_bound` into the normalized definition.

### 3.2 The shared empirical-to-expected bridge

Add to `StatsMLlib/LearningTheory/Rademacher/Complexity.lean`, in two stages.

1. The general form integrating an a.e. bound

   ```lean
   rademacherComplexity_le_of_ae_empirical_le
   ```

   Main hypotheses:

   - `[IsProbabilityMeasure μ]`
   - `Integrable (fun ω ↦ empiricalRademacherComplexity n f (X ∘ ω)) μⁿ`
   - `∀ᵐ ω ∂μⁿ, empiricalRademacherComplexity n f (X ∘ ω) ≤ C`

   Conclusion:

   ```lean
   rademacherComplexity n f μ X ≤ C
   ```

2. The convenient form taking a bound for all fixed samples

   ```lean
   rademacherComplexity_le_of_empirical_le
   ```

   Main hypotheses:

   - the integrability above
   - `∀ S, empiricalRademacherComplexity n f S ≤ C`

   A thin wrapper passing `Filter.Eventually.of_forall` to the general form.

For countable classes, add a corollary that supplies integrability automatically from 3.1. For
separable classes, prefer reduction to a dense countable subclass via `RademacherComplexity_eq`, to
avoid duplicating the integrability proof.

## 4. Shared corollaries on the generalization side

Add to `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` the public theorems that substitute
a known constant `C` into the threshold.

Candidate names:

```lean
uniform_deviation_expectation_le_of_empirical_le_countable
uniform_deviation_expectation_le_of_empirical_le_separable
uniform_deviation_tail_bound_countable_of_empirical_le
uniform_deviation_tail_bound_separable_of_empirical_le
```

The expectation version composes the existing
`uniform_deviation_expectation_le_two_smul_rademacher_complexity` with
`rademacherComplexity n f μ X ≤ C` to give

```text
E[uniformDeviation] ≤ 2 * C
```

The separable version is derived through the existing dense-countable identity.

Implement first the versions matching the constant-optimized existing theorems

```lean
uniform_deviation_tail_bound_countable_of_pos
uniform_deviation_tail_bound_separable_of_pos
```

and add a free-`t` version as a thin wrapper only if a need is confirmed.

Statement shape:

```text
hypothesis:
  ∀ S, empiricalRademacherComplexity n F S ≤ C

conclusion:
  P(2 * C + ε ≤ uniformDeviation)
    ≤ exp(-n * ε^2 / (2 * b^2))
```

The proof is limited to two steps:

1. `rademacherComplexity n f μ X ≤ C` by 3.2.
2. the event inclusion of 2.2 plus the existing tail theorem.

Individual models reuse this shared corollary and never reprove the integration or the event
inclusion.

## 5. End-to-end corollaries for linear predictors

### 5.1 $\ell_2$ linear predictors

Add to `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L2.lean` a predictor taking both
input and weights as bounded-ball subtypes, plus an empirical-bound wrapper.

Candidate names:

```lean
linearPredictorL2
linear_predictor_l2_empirical_bound
```

Setting:

```text
ι  = Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W
𝒳  = Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X
f w x = ⟪(w : EuclideanSpace ...), (x : EuclideanSpace ...)⟫
```

Bound to prove:

```text
empiricalRademacherComplexity n f S
  ≤ X * W / sqrt n
```

derived from the existing `linear_predictor_l2_bound'` and `empiricalRademacherComplexity_comp`.

Then add to the same file, as public API:

```lean
linear_predictor_l2_rademacher_complexity_bound
linear_predictor_l2_uniform_deviation_expectation_bound
linear_predictor_l2_uniform_deviation_tail_bound
```

The first:

```text
rademacherComplexity n f μ Z
  ≤ X * W / sqrt n
```

The last:

```text
P(2 * (X * W / sqrt n) + ε ≤ uniformDeviation)
  ≤ exp(-n * ε^2 / (2 * (X * W)^2))
```

Main hypotheses:

- `0 < n`, `0 < X`, `0 < W`
- `Z : Ω → Metric.closedBall 0 X`
- `Measurable Z`
- `[IsProbabilityMeasure μ]`

The uniform boundedness needed by the generalization theorem follows from Cauchy–Schwarz as
`|f w x| ≤ W * X`. Check separability and first countability of the weight ball, continuity in the
parameter, and measurability in the input; since this is a naturally uncountable class, use the
separable-class generalization theorem.

### 5.2 $\ell_1/\ell_\infty$ linear predictors

Add to `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L1.lean`:

```lean
linearPredictorL1
linear_predictor_l1_empirical_bound
```

Setting:

```text
ι  = L1Ball W
𝒳  = LinftyBall Xinf
f w x = ∑ j, (w : EuclideanSpace ...) j * (x : EuclideanSpace ...) j
```

Empirical bound:

```text
empiricalRademacherComplexity n f S
  ≤ (Xinf * W / sqrt n) * sqrt (2 * log (2 * d))
```

derived from the existing `linear_predictor_l1_bound'` and the domain-map lemma.

Publish in the same file:

```lean
linear_predictor_l1_rademacher_complexity_bound
linear_predictor_l1_uniform_deviation_expectation_bound
linear_predictor_l1_uniform_deviation_tail_bound
```

The high-probability threshold uses the empirical complexity bound above; the uniform bound in the
exponent is

```text
b = Xinf * W
```

Prove `|f w x| ≤ Xinf * W` from `abs_sum_mul_le_l1_mul` and the subtype conditions.

Main hypotheses:

- `0 < d`, `0 < n`, `0 < Xinf`, `0 < W`
- `Z : Ω → LinftyBall Xinf`
- `Measurable Z`
- `[IsProbabilityMeasure μ]`

## 6. The absolute-value Dudley bound

### 6.1 Sign symmetrization: definition and identity

Add to `StatsMLlib/LearningTheory/Rademacher/Signs.lean` something like

```lean
def signSymmetrization (F : ι → 𝒳 → ℝ) :
    ι × Bool → 𝒳 → ℝ
```

with one `Bool` value giving `F i` and the other `-F i`.

Assuming the function values are uniformly bounded on the fixed sample, and making the finiteness of
the conditional supremum explicit, prove

```lean
empiricalRademacherComplexity_eq_without_abs_signSymmetrization
```

stating

```lean
empiricalRademacherComplexity n F S
  =
empiricalRademacherComplexity_without_abs n
  (signSymmetrization F) S
```

Do not omit the bounded-above hypothesis when rewriting `iSup`. Make "does not use
`empiricalRademacherComplexity_without_abs_le_empiricalRademacherComplexity` in the wrong direction"
an explicit review item.

Also provide, for classes already closed under negation,

```lean
empiricalRademacherComplexity_eq_without_abs_of_neg_closed
```

In that case the class is not enlarged and the original covering number can be used directly on
Dudley's right-hand side.

### 6.2 Transferring the empirical norm and total boundedness

Add the following three, splitting them by owner.

1. `empiricalNorm S (-f) = empiricalNorm S f`
   → `StatsMLlib/LearningTheory/EmpiricalProcess/Metric.lean` (prove for the canonical version) and
   `.../FunctionClass.lean` (transfer to the sample-indexed version).
2. The maps from the positive and negative copies of `EmpiricalFunctionSpace F S` into
   `EmpiricalFunctionSpace (signSymmetrization F) S` are isometries
   → `StatsMLlib/LearningTheory/EmpiricalProcess/FunctionClass.lean`, which owns
   `EmpiricalFunctionSpace`.
3. If the original function space is totally bounded, so is the sign-symmetrized one
   → `StatsMLlib/LearningTheory/Rademacher/Dudley.lean`, since it depends on `signSymmetrization`.

Candidate name:

```lean
signSymmetrization_totallyBounded
```

Prove it from total boundedness of the positive and negative images and the fact that their finite
union is the whole sign-symmetrized space. Naming this lemma keeps the total-boundedness proof term
passed to `coveringNumber` stable.

Note that `empiricalNorm S f` is an `abbrev` in
`StatsMLlib/LearningTheory/EmpiricalProcess/FunctionClass.lean` unfolding to
`EmpiricalProcess.empiricalNorm n (fun i ↦ f (S i))` from
`StatsMLlib/LearningTheory/EmpiricalProcess/Metric.lean`.

### 6.3 The absolute-value Dudley theorem

Add an internal theorem and a public wrapper in
`StatsMLlib/LearningTheory/Rademacher/Dudley.lean`.

Candidate names:

```lean
dudley_entropy_integral_abs
dudley_entropy_integral_bound_abs
```

Base conclusion:

```text
empiricalRademacherComplexity n F S
  ≤ 4 * ε
    + 12 / sqrt n
      * ∫ u in ε..c/2,
          sqrt (log (coveringNumber of signSymmetrization(F) at u))
```

Proof order:

1. Convert the absolute empirical quantity to the one-sided quantity for the sign-symmetrized class,
   via the identity of 6.1.
2. Transfer the `empiricalNorm` bound from `F` to `signSymmetrization F`.
3. Transfer total boundedness by 6.2.
4. Apply the existing `dudley_entropy_integral'`.

For classes closed under negation, add a dedicated corollary using the original covering number
rather than the sign-symmetrized one.

If time permits, also prove

```text
N(signSymmetrization F, u) ≤ 2 * N(F, u)
```

by merging the positive and negative covers. This is not required for the absolute-value Dudley
theorem; finish the core connection first.

## 7. From Dudley to expected quantities and generalization

Dudley's right-hand side depends on the sample `S`, so a sample-independent numerical bound cannot
be obtained from the fixed-sample version alone. The public corollary makes this an explicit
hypothesis.

Take a sample-independent `C` satisfying

```text
for every S,
  4 * ε
    + 12 / sqrt n * entropyIntegral(signSymmetrization F, S)
  ≤ C
```

together with Dudley's norm and total-boundedness conditions for every `S`. By 6.3 this produces

```lean
∀ S, empiricalRademacherComplexity n F S ≤ C
```

which is passed to the shared theorems of 3.2 and 4.

Candidate names:

```lean
rademacher_complexity_le_dudley_of_uniform_entropy
uniform_deviation_tail_bound_separable_of_uniform_dudley
```

After the deterministic-threshold versions through Phase 4, Phase 5 adds the bounded-difference
estimate and lower-tail concentration for the empirical Rademacher complexity, leaving Dudley's
right-hand side as a sample-dependent threshold.

## 8. Upstream phases and where they live here

Upstream's phases are chronological, not dependency-ordered. **Appendix C-3 is the single source of
truth for implementation order.** This table exists only for cross-reading upstream.

§3–§7 and §12 describe *what* to state and in what shape, and carry no checkboxes;
progress is tracked per PR in Appendix C-3.

| Upstream phase | Content | Body | PR in Appendix C |
|---|---|---|---|
| 1 | shared bridge | §3, §4 | 02, 05 |
| 2 | linear predictors | §5 | 10, 11, 12 |
| 3 | absolute-value Dudley | §6, §7 | 07 |
| 4 | public API and docs | §13.6 | 17 |
| 5 | sample-dependent tails | §12.2 | 05, 06 |
| 6 | end-to-end bounds | §12 | 06, 10, 12 |
| 7 | reorganizing the bridges | §13 | 03, 05, 06 |
| 8 | functionals, reindex, bounded differences | §14 | 02, 03 |
| 9 | module hierarchy | not done (§0.5) | — |
| 10 | RKHS | §16 | 09, 13 |
| 11 | explicit covering numbers | §17 | 08 |
| 12 | loss, ERM, excess risk | §18 | 14, 15, 16 |

## 10. Verification

In each phase:

1. Check each changed file individually with `lake env lean <file>`.
2. Check the whole of `StatsMLlib` with `lake build`.
3. Confirm with `rg -n 'sorry|admit' StatsMLlib` that no unfinished proofs were added.
4. Confirm with `#check` or a small example that the new public theorems apply after importing the
   module directly.
5. For the final linear-predictor theorems, verify by inspection that:
   - the complexity term in the threshold matches the constant in the existing empirical bound;
   - the McDiarmid exponent uses the uniform bound `X * W` or `Xinf * W` on the function values;
   - `0 < n` and the positive-radius conditions appear in the statement.
6. For Dudley, confirm that no inequality is used in reverse from the one-sided to the
   absolute-value version.
7. Confirm that new modules do not violate the import direction (tiers) of `ARCHITECTURE.md`.

## 11. Anticipated difficulties

0. **The Lean and Mathlib version gap**

   Upstream is written against `leanprover/lean4:v4.27.0-rc1` and mathlib `master`; StatsMLlib is on
   `v4.33.0` (mathlib tag `v4.33.0`). Ported code will not compile unchanged everywhere; deprecated
   names, the `Measure.real` area, `ConditionallyCompleteLattice` lemma names, and the behaviour of
   `gcongr` / `positivity` are the likely friction points. The spike branch (Appendix C-2) exists to
   find these first.

1. **Bounded-aboveness for `iSup`**

   The sign-symmetrization identity needs `BddAbove` for conditional suprema over `ℝ`. Keep the
   numerical uniform bound on the fixed sample as a hypothesis; do not prove it as an unconditional
   rewrite.

2. **Integrability for separable classes**

   Do not try to make an uncountable supremum measurable directly; reduce to the countable class on
   `denseSeq` via the existing `empiricalRademacherComplexity_eq` and `RademacherComplexity_eq`.

3. **Topology and measurable structure on `L1Ball`, `LinftyBall`**

   First use instance inference through the subtype of Euclidean space. Supply only the properties
   that cannot be inferred as local lemmas or instances; do not change the type definitions.

4. **`coveringNumber` taking a total-boundedness proof term**

   This is **partly resolved already** in StatsMLlib (Appendix B-1). The canonical
   `coveringNumber (eps) (s) : WithTop ℕ` takes no proof term; the upstream version taking one is
   renamed `coveringNumberNat (hs) (eps) : ℕ`. State new lemmas on the canonical side and derive the
   `coveringNumberNat` versions as corollaries of `coe_coveringNumberNat`.
   Keep `signSymmetrization_totallyBounded` a named lemma for the places that do go through
   `coveringNumberNat`, so that no two anonymous proofs are generated.
   `coveringNumber` is also used from `StatsMLlib/Analysis/MetricEntropy/` and
   `StatsMLlib/Statistics/Regression/LeastSquares/`, so do not change its definition or existing
   signatures.

5. **`n = 0`**

   The shared definitions keep working at `n = 0`, but the square-root bounds and the end-to-end
   application theorems assume `0 < n`. Do not expose an apparent triviality that depends on
   `0⁻¹ = 0` in the application API.

6. **Two roles for constants**

   Do not confuse the bound `C` on the empirical complexity with the uniform bound `b` on function
   values. For the $\ell_1$ version,

   ```text
   C = (Xinf * W / sqrt n) * sqrt (2 * log (2 * d))
   b = Xinf * W
   ```

   with `C` appearing in the tail threshold and `b` in the exponent.

## 12. Phase 6 in detail

### 12.1 What "E2E" means here

An E2E theorem assumes a probability space, a data random variable, model radii, a sample size and a
confidence level, and concludes a high-probability uniform-deviation bound that leaves neither the
expected Rademacher complexity nor an unevaluated empirical Rademacher complexity in the conclusion.

There are two kinds.

1. **Deterministic threshold.** Uses a sample-uniform bound on the empirical complexity. The
   existing linear-predictor tail theorems have this shape.

2. **Sample-dependent threshold.** Leaves the observed squared norms, per-coordinate sums of
   squares, or the Dudley entropy integral in the threshold.

In this phase the endpoint of E2E is `uniformDeviation`. Bounds involving a loss function, ERM, and
excess risk need the contraction inequality and a risk/empirical-risk API, and are a separate phase.

### 12.2 The shared bridge to add first

The theorem added in §13.3,

```lean
uniform_deviation_tail_bound_separable_of_empirical_complexity
```

puts the empirical Rademacher complexity itself in the threshold. Each model's E2E theorem instead
wants to substitute a sample-dependent bound

```lean
C : (Fin n → 𝒳) → ℝ
```

So, at least for separable classes, add to
`StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean`:

```lean
uniform_deviation_tail_bound_separable_of_sample_empirical_le
```

Hypothesis:

```lean
∀ S, empiricalRademacherComplexity n F S ≤ C S
```

Conclusion:

$$
\Pr\left\{
  \operatorname{UD}_n(F;S)
  \ge 2C(S)+3\varepsilon
\right\}
\le
2\exp\!\left(-\frac{n\varepsilon^2}{2b^2}\right).
$$

The proof uses only the existing theorem with the empirical complexity in the threshold plus event
inclusion. The event inclusion currently written inline in the Dudley-specific theorem is replaced
by this shared bridge. If needed, prove the countable version first and derive the separable one by
dense-countable reduction.

### 12.3 The confidence form

The public E2E theorems should not make the user solve for `ε`; provide a form taking
$0<\delta\le1$. The definition and the real-analytic computation live in
`StatsMLlib/Probability/Concentration/Confidence.lean`; the application to uniform deviation lives in
`StatsMLlib/LearningTheory/UniformDeviation/Confidence.lean`.

For the deterministic threshold,

$$
\varepsilon_\delta
=
b\sqrt{\frac{2\log(1/\delta)}{n}},
$$

and for the sample-dependent threshold, absorbing the union-bound prefactor $2$,

$$
\widetilde\varepsilon_\delta
=
b\sqrt{\frac{2\log(2/\delta)}{n}}.
$$

The final forms are then

$$
\Pr\left\{
  \operatorname{UD}_n\ge2C+\varepsilon_\delta
\right\}\le\delta
\qquad\text{and}\qquad
\Pr\left\{
  \operatorname{UD}_n\ge2C(S)+3\widetilde\varepsilon_\delta
\right\}\le\delta .
$$

Collect the manipulations of `exp`, `log`, squaring the square root, and $\log(1/\delta)\ge0$ into
shared lemmas rather than reproving them per model.

### 12.4 $\ell_2$ linear predictors

`linear_predictor_l2_empirical_bound` (added in §5.1) publishes only the bound after replacing each
sample point's norm by the uniform radius $X$. Extract the sharper sample-dependent bound that
appears mid-proof,

$$
\widehat{\mathfrak R}_n(\mathcal F_{2,W};S)
\le
\frac{W}{n}
\sqrt{\sum_{k=1}^n\|S_k\|_2^2},
$$

into `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L2.lean`.

Candidate name:

```lean
linear_predictor_l2_empirical_bound_of_sample
```

The existing $XW/\sqrt n$ bound becomes a corollary using $\|S_k\|_2\le X$. Put both E2E bounds in
the same file:

- deterministic:

  $$
  \Pr\left\{
    \operatorname{UD}_n
    \ge
    \frac{2XW}{\sqrt n}
    +XW\sqrt{\frac{2\log(1/\delta)}{n}}
  \right\}
  \le\delta .
  $$

- sample-dependent:

  $$
  \Pr\left\{
    \operatorname{UD}_n
    \ge
    \frac{2W}{n}
      \sqrt{\sum_k\|Z(\omega_k)\|_2^2}
    +3XW\sqrt{\frac{2\log(2/\delta)}{n}}
  \right\}
  \le\delta .
  $$

### 12.5 $\ell_1/\ell_\infty$ linear predictors

The existing proof replaces the per-coordinate sums of squares by the uniform bound
$X_\infty/\sqrt n$ right after Massart's lemma. Extract the step just before that as a
sample-dependent bound. With

$$
Q_\infty(S)
=
\frac1n
\sup_{j<d}
\sqrt{\sum_{k=1}^n |S_{k,j}|^2},
$$

publish

$$
\widehat{\mathfrak R}_n(\mathcal F_{1,W};S)
\le
WQ_\infty(S)\sqrt{2\log(2d)} .
$$

In Lean, do not expose `Finset.sup'` (which takes a proof term) in the final theorem; define the
quantity as `⨆ j : Fin d, ...`. Add a lemma identifying `iSup` over a finite type with the existing
`Finset.sup'` if one is missing.

Candidate name:

```lean
linear_predictor_l1_empirical_bound_of_sample
```

The final sample-dependent E2E bound is

$$
\Pr\left\{
  \operatorname{UD}_n
  \ge
  2WQ_\infty(S)\sqrt{2\log(2d)}
  +3X_\infty W
    \sqrt{\frac{2\log(2/\delta)}{n}}
\right\}
\le\delta .
$$

Add a `δ`-form E2E corollary for the existing deterministic bound as well.

### 12.6 Dudley

`uniform_deviation_tail_bound_separable_of_dudley` (added in §7) is an entropy-form E2E bound, but
upstream reproves the event inclusion inside the theorem. In StatsMLlib, build it from the start as
a thin corollary of the sample-dependent bridge of 12.2.

Also add the `δ` form

$$
\Pr\left\{
  \operatorname{UD}_n
  \ge
  2D_\alpha(S)
  +3b\sqrt{\frac{2\log(2/\delta)}{n}}
\right\}
\le\delta .
$$

A purely numerical Dudley E2E example would need covering-number bounds for Lipschitz functions,
RKHS, neural networks, and so on. This phase does not add covering-number bounds for new models; the
Dudley E2E endpoint is leaving the observed entropy integral in the threshold.

### 12.7 Structure of the public examples

The acceptance examples for the linear predictors go at the end of the corresponding module, in this
order:

1. E2E tail with a deterministic threshold.
2. E2E tail with a sample-dependent threshold.
3. Expectation / expected-complexity versions if useful.
4. Fixed-sample wrappers.

The existing

```lean
linear_predictor_l2_bound
linear_predictor_l1_bound
```

merely republish lower-level theorems, so they are excluded from the main E2E examples. They are not
deleted in this phase, and remain as low-level wrappers for API compatibility.

The docstring of each final theorem states the complexity term, the concentration term, and the
probability bound, and distinguishes "empirical bound", "expected bound", and "high-probability E2E
bound".

### 12.8 Order and completion criteria

1. The shared bridge taking a sample-dependent `C S`.
2. The shared conversion from `ε` form to `δ` form.
3. The sample-dependent empirical bound for $\ell_2$ and its uniform corollary.
4. The two E2E theorems for $\ell_2$.
5. The sample-dependent empirical bound for $\ell_1/\ell_\infty$ and its uniform corollary.
6. The two E2E theorems for $\ell_1/\ell_\infty$.
7. Rewriting the Dudley theorem through the shared bridge, plus the `δ` form.
8. Acceptance examples. `README.md` is PR 17; `FILE_TREE.md` goes in each module's PR.
9. `lake build`, search for unfinished proofs, `#check` from a direct import of each module.

Completion means each model's final theorem satisfies:

- the conclusion is a probability bound over the sample distribution;
- no unevaluated `rademacherComplexity` or `empiricalRademacherComplexity` remains in the threshold;
- the complexity term and the concentration term are distinguished;
- the difference between the deterministic and sample-dependent versions is clear from the theorem
  name and docstring;
- $n>0$, $0<\delta\le1$, and positive radii — the hypotheses needed for square roots, logarithms and
  division — appear in the statement.

## 13. Phase 7: reorganizing the bridges and the generalization API

### 13.1 Purpose

Collect the repeatedly performed conversions into reusable bridges.

1. Event inclusion from an upper bound on the threshold.
2. From a centred tail bound plus an expectation bound to a non-centred tail bound.
3. From the $\varepsilon$ form to the confidence form with $0<\delta\le1$.
4. Restriction of a separable hypothesis class to a dense countable subclass.

Lemmas that depend only on order, measure, and real arithmetic go into the subject-owning
directories (`StatsMLlib/Order/`, `StatsMLlib/Analysis/`, `StatsMLlib/MeasureTheory/`,
`StatsMLlib/Probability/Concentration/`), not a `ForMathlib` layer. Theorems depending on Rademacher
complexity, generalization bounds, or specific models go into the corresponding module of
`StatsMLlib/LearningTheory/`.

### 13.2 Generic lemmas

- [ ] Add monotonicity of superlevel events for real-valued functions with $A\le B$ to
  `StatsMLlib/MeasureTheory/Measure/Real.lean`.
- [ ] Add, in the same file, the lemma bounding $\Pr\{C+\varepsilon\le Y\}$ from a centred tail bound
  and $\mathbb E[Y]\le C$.
- [ ] Add the confidence radius for a general prefactor $\kappa$,

  $$
  \operatorname{confidenceRadius}(\kappa,b,\delta,n)
  =
  b\sqrt{\frac{2\log(\kappa/\delta)}{n}},
  $$

  and its exponential identity, to `StatsMLlib/Probability/Concentration/Confidence.lean`.

### 13.3 Generalization bounds for countable classes

- [ ] Put the expectation bound, the McDiarmid bound, and the deterministic and sample-dependent
  threshold bridges for countable classes in
  `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean`.
- [ ] Add `uniform_deviation_expectation_le_of_rademacher_le`.
- [ ] Add `uniform_deviation_tail_bound_countable_of_rademacher_le`.
- [ ] Rewrite the existing empirical-complexity-bound versions as corollaries of these bridges.
- [ ] Keep public declaration names as they are; remove only the repeated inline `measure_mono` and
  `linarith`.

> Upstream split this into `Generalization/Countable.lean` and `Generalization/Separable.lean` in
> Phase 7, but StatsMLlib keeps both in `UniformDeviation/Bounds.lean` (Appendix C-1).

### 13.4 Restriction to separable classes

- [ ] Define the term explicitly.

  ```lean
  abbrev denseRestriction
      [TopologicalSpace H] [SeparableSpace H] [Nonempty H]
      (F : H → α) : ℕ → α :=
    F ∘ denseSeq H
  ```

- [ ] Add, as individual bridges, invariance of the empirical Rademacher complexity, the expected
  Rademacher complexity, and the uniform deviation under `denseRestriction`. Placement and the
  relationship to the existing `denseSeqInTB` follow Appendix B-5.
- [ ] Add transfer lemmas for measurability and uniform boundedness.
- [ ] Put the separable-class theorems in `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean`.
- [ ] Align names such as `RademacherComplexity_eq` with Mathlib's lowerCamelCase convention,
  leaving compatibility aliases for the old names.

### 13.5 Confidence form and individual models

- [ ] Create `StatsMLlib/LearningTheory/UniformDeviation/Confidence.lean` and collect the $\delta$
  forms of the deterministic and sample-dependent thresholds there.
- [ ] Put the expectation and high-probability bounds for $\ell_2$ linear predictors in
  `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L2.lean`.
- [ ] Put those for $\ell_1/\ell_\infty$ in
  `StatsMLlib/LearningTheory/FunctionClass/LinearPredictor/L1.lean`.
- [ ] Put the connection between the Dudley entropy integral and the generalization bounds in
  `StatsMLlib/LearningTheory/Rademacher/Dudley.lean`.
- [ ] Write Dudley's repeated right-hand side once, as a definition taking the sample.
      **Follow the decision in Appendix B-3:** it is not a public `def`; keep it a
      `private noncomputable abbrev` in `StatsMLlib/LearningTheory/Rademacher/Dudley.lean`.
      The canonical entropy integral lives in `Analysis.MetricEntropy`, and converging on it is a
      separate PR.

### 13.6 Acceptance examples

- [ ] Distribute each `example` of upstream `FoML/Main.lean` to the end of the corresponding module.

  | Section of upstream `Main.lean` | # examples | Destination |
  |---|---|---|
  | The generic bridge | 1 | `LearningTheory/UniformDeviation/Bounds.lean` |
  | The observed empirical complexity | 1 | `LearningTheory/UniformDeviation/Bounds.lean` |
  | $\ell_2$ linear predictors | 2 | `LearningTheory/FunctionClass/LinearPredictor/L2.lean` |
  | $\ell_1/\ell_\infty$ linear predictors | 1 | `LearningTheory/FunctionClass/LinearPredictor/L1.lean` |
  | Feature-map RKHS predictors | 2 | `LearningTheory/FunctionClass/KernelPredictor.lean` |
  | Dudley entropy integral | 3 | `LearningTheory/Rademacher/Dudley.lean` |
  | Approximate ERM and excess risk | 3 | `LearningTheory/EmpiricalRiskMinimization/Generalization.lean` |

- [ ] Collect the `example`s at the end of each module under a `/-! ## Examples -/` heading.
- [ ] In the docstrings, distinguish the roles of the empirical-complexity term, the concentration
  term, and the probability bound, and state the final bound in LaTeX.

### 13.7 Out of scope here

Migration to Mathlib's `Metric.coveringNumber` is not done in this phase: the codomains differ
(`ℕ` vs `ℕ∞`) and open vs closed balls differ. Do it as an independent change after surveying the
correspondence between the theorems.

### 13.8 Accompanying cleanup

- [ ] Delete unreferenced definitions such as `MassartNotation.r'`, `CoordIndex`, `coordSignedOn`,
  after first confirming that no other StatsMLlib module refers to them.
- [ ] Remove Massart's duplicated nonemptiness hypothesis and the unused local hypotheses in the
  optimized tail theorem.
- [ ] Make declarations used only inside the Dudley proof `private`.
- [ ] Standardize doubling on reals from `2 • C` to `2 * C`.

## 14. Phase 8: shared functionals, reindexing, bounded differences

### 14.1 Scope

The shared confidence radius (13.2) and `dudleyEntropyEstimate` are implemented in Phase 7, so this
phase only rechecks the public API and documentation for them. The new work is these four items.

1. Add a wrapper to the i.i.d. product-measure McDiarmid using the same sensitivity in all coordinates.
2. Write once the functional and PMF bridge shared by the absolute and one-sided Rademacher
   complexities.
3. Add a reindexing API for maps on the hypothesis index.
4. Separate the supremum-difference estimate and the one-sample replacement computation into shared
   lemmas, reducing duplication in
   `StatsMLlib/LearningTheory/UniformDeviation/BoundedDifference.lean`.

### 14.2 Constant-sensitivity McDiarmid wrapper

Add to `StatsMLlib/Probability/Concentration/McDiarmid.lean`.

- [ ] Add `mcdiarmid_inequality_pos_iid_of_const`.
- [ ] Add `mcdiarmid_inequality_neg_iid_of_const`.
- [ ] Derive the upper tail for the uniform deviation and the lower tail for the empirical Rademacher
  complexity in `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean` from these wrappers.

The wrapper must not expose the constant function `fun _ ↦ c` in the conclusion; it takes

$$
t\,|\iota|\,c^2\le1
$$

as a hypothesis, so that the same reduction of `∑ i, (c i)^2` is not repeated in each application.

StatsMLlib's `McDiarmid.lean` currently has `mcdiarmid_inequality_pos`, `mcdiarmid_inequality_pos'`,
`mcdiarmid_inequality_pos_of_sum_sq_pos`, and `mcdiarmid_inequality_neg`, with no i.i.d.
product-measure version; port the upstream i.i.d. wrappers as well.

### 14.3 Rademacher functional and PMF bridge

Add to `StatsMLlib/LearningTheory/Rademacher/Signs.lean`.

- [ ] Add the normalized sign sum `normalizedRademacherSum`.
- [ ] Add `empiricalRademacherFunctional`, taking a post-processing function `φ : ℝ → ℝ`.
- [ ] Prove that the finite-average version and the `signVecPMF` integral version agree for general `φ`.
- [ ] Keep the existing API by deriving the absolute version as `φ = abs` and the one-sided version
  as `φ = id`.

Publish the definitions down to the terms:

```lean
normalizedRademacherSum n F S σ h
  = (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F h (S k)

empiricalRademacherFunctional n φ F S
  = (Fintype.card (Signs n) : ℝ)⁻¹ *
      ∑ σ : Signs n, ⨆ h, φ (normalizedRademacherSum n F S σ h)
```

### 14.4 Reindexing API for the hypothesis index

Create `StatsMLlib/LearningTheory/Rademacher/Reindex.lean`.

- [ ] Add monotonicity of the empirical Rademacher complexity under an arbitrary map `e : G → H`.
- [ ] Add invariance of the absolute and one-sided empirical Rademacher complexities when `e` is
  surjective.
- [ ] Add invariance of the expected Rademacher complexity and the uniform deviation under a
  surjective reindexing.
- [ ] Keep `denseRestriction` as a separate bridge that uses topological density; do not conflate it
  with a mere surjective reindexing.

This module imports `Rademacher/Complexity.lean`, `Analysis/FiniteSample.lean`, and
`Order/IndexedSupremum.lean`.

### 14.5 Shared bounded-difference lemmas

- [ ] Add the lemma deriving a distance estimate between two real-valued `iSup`s from a pointwise
  estimate, to `StatsMLlib/Order/IndexedSupremum.lean`.
- [ ] Add the one-sample replacement estimate for normalized sample means, to
  `StatsMLlib/Analysis/FiniteSample.lean`.
- [ ] Reorganize `uniformDeviation_bounded_difference` and
  `empiricalRademacherComplexity_bounded_difference` using these lemmas.

### 14.6 Acceptance examples and documentation

- [ ] Feature the basic theorem combining separability, high probability and the empirical Rademacher
  complexity,

  $$
  \Pr\left\{
    \operatorname{UD}_n(F;S)
    \ge 2\widehat{\mathfrak R}_n(F;S)+3\varepsilon
  \right\}
  \le
  2\exp\left(-\frac{n\varepsilon^2}{2b^2}\right),
  $$

  as the main example in `StatsMLlib/LearningTheory/UniformDeviation/Bounds.lean`.
- [ ] (batched into PR 17) Update the definitions, bridges and public API in `README.md`.
- [ ] Run `lake build`, the unfinished-proof search, and `#check` from a direct import of each module.

## 16. Phase 10: Rademacher complexity for RKHS

### 16.1 Goal and reference

Formalize Theorem 6.12 of Mohri, Rostamizadeh, Talwalkar, *Foundations of Machine Learning*
(printed page 118). For a real Hilbert space $\mathcal H$, a feature map
$\Phi:\mathcal X\to\mathcal H$, and a weight radius $\Lambda\ge0$, prove

$$
\widehat{\mathfrak R}_n
\left(
  \left\{x\mapsto\langle w,\Phi(x)\rangle:
    \lVert w\rVert_{\mathcal H}\le\Lambda
  \right\};S
\right)
\le
\frac{\Lambda}{n}
\sqrt{\sum_{k=1}^n K(S_k,S_k)}
$$

where

$$
K(x,y)=\langle\Phi(x),\Phi(y)\rangle.
$$

If $K(x,x)\le r^2$, the corollary is

$$
\widehat{\mathfrak R}_n\le\frac{r\Lambda}{\sqrt n}.
$$

This repository's empirical Rademacher complexity has the absolute value inside the supremum, but
since the weight ball is closed under $w\mapsto-w$ the bound coincides with Mohri's one-sided
definition.

The reference PDF is not added to the repository; the bibliographic data goes in the docstring.

### 16.2 Implementation

Mathlib has no directly usable general RKHS structure, so implement the Hilbert-space version via a
feature map first, then give the kernel notation.

1. `StatsMLlib/LearningTheory/FunctionClass/HilbertPredictor.lean`
   - Define `hilbertPredictor w x = ⟪w, x⟫` on a general real inner-product space.
   - Extract the dimension-independent mean-square bound for the Rademacher sign sum out of the
     current finite-dimensional `LinearPredictor/L2.lean` proof.
   - Prove, for the whole closed ball,

     $$
     \widehat{\mathfrak R}_n
     \le
     \frac{\Lambda}{n}
       \sqrt{\sum_k\lVert \Phi(S_k)\rVert^2}.
     $$

2. `StatsMLlib/LearningTheory/FunctionClass/KernelPredictor.lean`
   - Define `kernelOfFeatureMap Φ x y = ⟪Φ x, Φ y⟫` down to the term.
   - Prove the diagonal identity `kernelOfFeatureMap Φ x x = ‖Φ x‖ ^ 2`.
   - Define `kernelTrace Φ S = ∑ k, kernelOfFeatureMap Φ (S k) (S k)`.
   - Publish the trace version and the uniform-diagonal version $K(x,x)\le r^2$.

3. The second half of the same `KernelPredictor.lean`
   - Assuming measurability of the feature map, continuity in the weight variable, and separability
     of the Hilbert space, connect to the expected Rademacher complexity, the expected uniform
     deviation, and the high-probability bounds.
   - Provide a sample-dependent E2E bound leaving the observed kernel trace, and a deterministic E2E
     bound using $r\Lambda/\sqrt n$.
   - Put the trace version and the uniform-diagonal version at the end as acceptance `example`s.

Upstream splits 2 and 3 across `Model/RKHS.lean` and `Generalization/RKHS.lean`; StatsMLlib keeps
them in one file, as with `LinearPredictor/L1.lean` and `L2.lean`. Split into
`FunctionClass/KernelPredictor/Basic.lean` and `FunctionClass/KernelPredictor/Generalization.lean`
only if the line count becomes excessive.

### 16.3 Design notes

- [ ] The first theorem does not construct an RKHS from an arbitrary PDS kernel; it handles the
  kernel induced by a given feature map.
- [ ] State positive semidefiniteness separately, as nonnegativity of the quadratic form of a finite
  Gram matrix.
- [ ] For the fixed-sample bounds, where completeness is not needed, weaken the assumption to
  `InnerProductSpace ℝ H`; assume `CompleteSpace H` only in the public wrappers called RKHS.
- [ ] Require `SeparableSpace H` only in the theorems that go on to separable-class generalization
  bounds.
- [ ] Reorganize the existing $\ell_2$ linear predictor as the finite-dimensional corollary of the
  general Hilbert-space theorem.

### 16.4 Completion criteria

- [ ] Both the kernel-trace version and the $r\Lambda/\sqrt n$ version exist.
- [ ] Fixed sample, expected quantity, sample-dependent tail, and deterministic tail are connected.
- [ ] The correspondence between Mohri's hypotheses and the Lean hypotheses is in the docstring.
- [ ] There are at least two RKHS E2E `example`s.

## 17. Phase 11: Dudley bounds with explicit covering numbers

### 17.1 Stage one: finite hypothesis classes

Create `StatsMLlib/LearningTheory/Rademacher/FiniteClass.lean`.

For a class indexed by a finite type $H$, prove

$$
N(F,\varepsilon)\le |H| ,
$$

hence after sign symmetrization

$$
N(F^\pm,\varepsilon)\le 2|H| ,
$$

and substitute into Dudley's integral to obtain, for $\alpha>0$, a bound free of covering numbers:

$$
\widehat{\mathfrak R}_n(F;S)
\le
4\alpha+
\frac{12}{\sqrt n}
\left(\frac c2-\alpha\right)
\sqrt{\log(2|H|)} .
$$

- [ ] Add `coveringNumber_le_fintype_card`, taking the whole finite type as the centre set, to
  `StatsMLlib/Topology/MetricSpace/CoveringNumber/Basic.lean`.
- [ ] Add the `Fintype` instance and the cardinality bound for `EmpiricalFunctionSpace F S` to
  `StatsMLlib/LearningTheory/EmpiricalProcess/FunctionClass.lean`.
- [ ] Add the Dudley corollary using the sign-symmetrized cardinality $2|H|$ to `FiniteClass.lean`.
- [ ] Add the high-probability generalization bound with an explicit $\alpha$ in the same file, with
  an acceptance `example` at the end.

See Appendix B-2: most of this is already available from existing lemmas.

### 17.2 Stage two: one-dimensional Lipschitz parameter families

Create `StatsMLlib/LearningTheory/Rademacher/LipschitzParameter.lean`.

Beyond finite classes, handle classes indexed by $t\in[-W,W]$ satisfying

$$
|F_t(x)-F_s(x)|\le L|t-s| .
$$

An equally spaced grid gives

$$
N(F,\varepsilon)
\le
\left\lceil\frac{2WL}{\varepsilon}\right\rceil+1 .
$$

Instead of computing Dudley's integral exactly with special functions, use antitonicity of the
covering number:

$$
\int_\alpha^{c/2}\sqrt{\log N(F,x)}\,dx
\le
\left(\frac c2-\alpha\right)
\sqrt{\log N(F,\alpha)}
$$

and substitute the grid cardinality bound on the right.

- [ ] Add the finite equally spaced grid on a closed interval and the covering lemma.
      The pure interval-grid part, independent of the empirical distance, belongs in
      `StatsMLlib/Analysis/NormedSpace/CoveringNumber/` (which already holds
      `coveringNumber_euclideanBall_le` and `coveringNumber_l1Ball_le`); see Appendix B-4 for whether
      it needs to be written at all. The part using the empirical distance must live in
      `LearningTheory/Rademacher/LipschitzParameter.lean` because of the import direction.
- [ ] Add the bridge from Lipschitz continuity in the parameter to Lipschitz continuity in the
  empirical distance.
- [ ] Connect the explicit covering number, the Dudley bound, and the high-probability
  generalization bound.

### 17.3 Completion criteria

- [ ] No unevaluated `coveringNumber` remains in the final expression of the acceptance `example`s.
- [ ] At least two examples: a finite class and a continuous parameter family.
- [ ] The existing `coveringNumber` API taking a proof term stays internal.

## 18. Phase 12: loss functions, ERM, excess risk

### 18.1 Core definitions

Create `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Defs.lean` and define, for a data type
$\mathcal Z$ and a hypothesis type $H$, down to the terms:

```lean
def populationRisk
    (ℓ : H → 𝒵 → ℝ) (μ : Measure Ω) (Z : Ω → 𝒵) (h : H) : ℝ :=
  ∫ ω, ℓ h (Z ω) ∂μ

def empiricalRisk
    (n : ℕ) (ℓ : H → 𝒵 → ℝ) (S : Fin n → 𝒵) (h : H) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k : Fin n, ℓ h (S k)

def excessRisk
    (ℓ : H → 𝒵 → ℝ) (μ : Measure Ω) (Z : Ω → 𝒵)
    (h hstar : H) : ℝ :=
  populationRisk ℓ μ Z h - populationRisk ℓ μ Z hstar
```

Exact and $\eta$-approximate ERM are defined as predicates rather than by choosing an `argmin`.

```lean
def IsERM (n : ℕ) (ℓ : H → 𝒵 → ℝ) (S : Fin n → 𝒵) (hhat : H) : Prop :=
  ∀ h, empiricalRisk n ℓ S hhat ≤ empiricalRisk n ℓ S h

def IsApproxERM
    (η : ℝ) (n : ℕ) (ℓ : H → 𝒵 → ℝ)
    (S : Fin n → 𝒵) (hhat : H) : Prop :=
  ∀ h, empiricalRisk n ℓ S hhat ≤ empiricalRisk n ℓ S h + η
```

`StatsMLlib/Statistics/Regression/LeastSquares/Defs.lean:75` already has an ERM predicate
specialized to the squared loss, `isLeastSquaresEstimator`. Following Appendix B-6, add the general
form here, keep `isLeastSquaresEstimator` as it is, and provide one bridge lemma.

### 18.2 Deterministic oracle inequality

Put in `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Basic.lean`.

- [ ] Show that `uniformDeviation` is definitionally the supremum of the discrepancy between risk and
  empirical risk.
- [ ] Show that if `hhat` is an ERM then for any comparator `hstar`,

  $$
  R(h_{\rm ERM})-R(h^\star)
  \le 2\operatorname{UD}_n .
  $$

- [ ] Show for $\eta$-approximate ERM,

  $$
  R(\widehat h)-R(h^\star)
  \le 2\operatorname{UD}_n+\eta .
  $$

- [ ] Separate the existence of a true risk minimizer into another module assuming compactness and
  continuity of the risk. (Not done upstream either.)

### 18.3 Loss classes and contraction

For predictors $F_h:\mathcal X\to\mathbb R$ and labelled data $z=(x,y)$, define the loss class

$$
z\mapsto \ell(F_h(x),y).
$$

Contraction goes in `StatsMLlib/LearningTheory/Rademacher/Contraction.lean`.

- [ ] First implement the bridge passing a bounded loss directly as a function class to the existing
  generalization theorems.
- [ ] Add the Rademacher contraction inequality for the case where $u\mapsto\ell(u,y)$ is
  $L$-Lipschitz for each $y$.
- [ ] Provide the lemma rewriting to a centred loss when $\ell(0,y)\ne0$.
- [ ] Explicitly verify whether the contraction constant differs between the absolute and one-sided
  definitions.

Upstream proves contraction completely for finite hypothesis types. The constant is $L$ for the
one-sided definition and $2L$ for this repository's absolute definition. Extending to general
separable classes is split off as finite approximation or a separate contraction bridge.

### 18.4 High-probability excess-risk bounds

Put in `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/Generalization.lean`. Compose the
existing uniform-deviation bounds with the oracle inequality to obtain, for instance, the expected
Rademacher complexity version

$$
\Pr\left\{
  R(\widehat h)-R(h^\star)
  \ge
  4\mathfrak R_n(\ell\circ F)+2\varepsilon+\eta
\right\}
\le
\exp\left(-\frac{n\varepsilon^2}{2b^2}\right)
$$

and the observed empirical Rademacher complexity version

$$
\Pr\left\{
  R(\widehat h)-R(h^\star)
  \ge
  4\widehat{\mathfrak R}_n(\ell\circ F;S)+6\varepsilon+\eta
\right\}
\le
2\exp\left(-\frac{n\varepsilon^2}{2b^2}\right)
$$

where $b$ is an absolute bound on the loss values.

- [ ] Add the theorem taking a sample-dependent learning rule `A : (Fin n → 𝒵) → H` and pointwise
  `IsApproxERM η ℓ S (A S)`.
- [ ] Add the confidence-$\delta$ form.
- [ ] Add the E2E example connecting RKHS and a Lipschitz loss through contraction, in
  `StatsMLlib/LearningTheory/EmpiricalRiskMinimization/KernelPredictor.lean`.
- [ ] Feature the main ERM usage as `example`s at the end of
  `EmpiricalRiskMinimization/Generalization.lean`.

`EmpiricalRiskMinimization/KernelPredictor.lean` imports all four of Phase 10's
`FunctionClass/KernelPredictor.lean` and Phase 12's `EmpiricalRiskMinimization/Generalization.lean`,
`Rademacher/Contraction.lean`, and `Rademacher/Reindex.lean`.

### 18.5 Implementation order

1. Risk, empirical risk, excess risk, ERM predicates.
2. Deterministic oracle inequality.
3. High-probability theorem passing bounded loss classes to the existing bridges.
4. Contraction inequality.
5. $\eta$-approximate ERM and the confidence form.
6. E2E connection with RKHS or linear predictors.

### 18.6 Completion criteria

- [ ] The conclusion of the final theorems is the excess risk, not `uniformDeviation`.
- [ ] Measurability of the learning rule and existence of an argmin are not demanded by theorems that
  do not need them.
- [ ] Both exact and approximate ERM are handled.
- [ ] The deterministic oracle inequality, the Rademacher bound, contraction, and the tail bound are
  reusable as separate bridges.

---

## Appendix B. Handling the duplication (conclusions)

Conclusions from matching the 466 declarations of upstream `origin/main` against all StatsMLlib
declarations and inspecting the 203 unported ones by subject.

| | Duplication | What to do |
|---|---|---|
| B-1 | `coveringNumber` differs between upstream and StatsMLlib | The canonical one is `coveringNumber (eps) (s) : WithTop ℕ`; the upstream proof-term version is `coveringNumberNat`. State new lemmas on the canonical side and derive `coveringNumberNat` versions via `coe_coveringNumberNat`. Upstream proofs cannot be pasted (§11-4) |
| B-2 | `√log card` for finite classes | Available from `coveringNumber_le_card`, `sqrtEntropy_le_sqrt_log_card`, `exists_optimal_enet`. `coveringNumber_le_fintype_card` is `coveringNumber_le_card` at `Finset.univ`. Do not port upstream's `Nat.find` proof (§17.1) |
| B-3 | Three entropy-integral developments | **`Analysis.MetricEntropy` is canonical.** Add no new definition during the port; keep Dudley's right-hand side a `private noncomputable abbrev` (§13.5). Unification is PR 18 |
| B-4 | Explicit covering numbers | `coveringNumber_euclideanBall_le` and `coveringNumber_l1Ball_le` already exist. Do not add a one-dimensional grid under `LearningTheory/` (§17.2) |
| B-5 | Two dense-countable bridges | Make `denseRestriction` canonical; keep `denseSeqInTB` and make it a corollary through one bridge lemma. Steps below |
| B-6 | Two ERM predicates | Add `IsERM` as the general form, keep `isLeastSquaresEstimator`, and add one `isLeastSquaresEstimator → IsERM` bridge (§18.1) |
| B-8 | Three maximal inequalities | Untouched during the port; handled in PR 19 |

**Confirmed free of duplication** (no need to search again): the 14 confidence declarations
(`confidence` occurs 0 times), `measureReal_superlevel_*` (`superlevel` occurs 0 times), the three
i.i.d. McDiarmid wrappers, `abs_normalized_fin_sum_*`, `ciSup_comp_of_surjective`, and the RKHS
group. `abs_ciSup_sub_ciSup_le` is also absent, but
`UniformDeviation/BoundedDifference.lean` expands the same argument inline at `:125`–`:164` and
`:206`–`:245`, so §14.5 lands as a refactor of an existing proof rather than a new API.

### Steps for B-3

**Stage 1 (during the port)**

- [ ] Write the integral part in the same shape as the existing `dudley_entropy_integral_bound`:
      `∫ x in ε..c/2, √(Real.log (coveringNumberNat h' x))`.
- [ ] Keep the coefficient part a `private noncomputable abbrev` in
      `LearningTheory/Rademacher/Dudley.lean`; do not make it public API.

**Stage 2 (PR 18)**

`metricEntropyOfNat n = if n ≤ 1 then 0 else Real.log n`, but in Lean
`Real.log 0 = Real.log 1 = 0`, so it equals `Real.log n` for every `n`. Hence for totally bounded
`s` and `eps > 0`, `metricEntropy eps s = Real.log (coveringNumberNat hs eps)` follows almost
definitionally from `coe_coveringNumberNat`. What remains is converting between the lower integral
over `Ioc` and the interval integral; integrability comes from
`dudleyIntegrand_anti_eps_of_totallyBounded` and `entropyIntegralENNRealTrunc_lt_top`. Estimated at
30–60 lines.

- [ ] (a) `entropyIntegralTrunc (Set.univ : Set (EmpiricalFunctionSpace F S)) ε (c / 2)
      = ∫ x in ε..c/2, √(Real.log (coveringNumberNat h' x))` (equality)
- [ ] (b) `entropyIntegralTrunc T δ D ≤ dudleyEntropyIntegral T δ D` (an inequality, because
      internal and external nets differ)
- [ ] Add one line of ownership to "Import direction" in `ARCHITECTURE.md`.

**What not to do**

- Change the statement of `dudley_entropy_integral'` (`Rademacher/Dudley.lean:1528`). Nearly all
  1,600 lines of that file support it, so the proof would break. Stage 2 only adds corollaries.
- Delete `subsetENetCard` in favour of `coveringNumber`. Internal nets are essential to the chaining
  construction.
- Make upstream's `dudleyEntropyEstimate` a public `def`. That would be a fourth one.

### Steps for B-5

Mathlib's `denseSeq [SeparableSpace α] [Nonempty α]` depends on classes that are both `Prop`-valued
(`class SeparableSpace : Prop` at `Mathlib/Topology/Bases.lean:333`, and `Nonempty`), so proof
irrelevance makes the term independent of which instance is supplied. The instances `denseSeqInTB`
provides via `letI` therefore agree with those `denseRestriction` picks up from the context.

- [ ] Add `denseRestriction` and its companions to
      `StatsMLlib/Topology/SeparableSpace/Supremum.lean`, with the canonical form
      `separableSpaceSup_eq_denseRestriction : (⨆ h, F h) = ⨆ n, denseRestriction F n`.
- [ ] Add one bridge lemma `fun n ↦ f (denseSeqInTB hs hsne n) = denseRestriction f` in
      `Probability/Process/Dudley.lean`.
- [ ] Rewrite `sup_subtype_eq_iSup_denseSeq` as a corollary of
      `separableSpaceSup_eq_denseRestriction`; `sup_over_s_eq_iSup_denseSeq_pathwise` then follows.
- [ ] Leave the seven use sites (`Probability/Process/Dudley.lean` at `:1026`, `:1043`, `:1044`,
      `:2533`, `:2536`, `:2539`, `:2544`) as `denseSeqInTB`. **Do not delete it.**

## Appendix C. PR order

### C-1. Conventions

- **One PR, one branch** (`reflect/NN-<topic>`), based on `main`. While the previous PR is unmerged,
  base the next one on the previous branch (stacked PRs); GitHub retargets the base to `main` on
  merge. Avoid force-pushing after review comments appear; take `main` in with `git merge main`.
- **Every PR builds green on its own, with no `sorry` / `admit` / `axiom` / `native_decide`.** Never
  carry a `sorry` into the next PR. If a proof is long, split by statement group, never mid-proof.
- **Do not mix additions with refactors of existing, working proofs.** A PR containing a refactor
  states "no declarations added or removed".
- **Aim for 200–600 lines and 10–20 declarations per PR.** In Lean, a green build mechanically
  guarantees that the statements are proved, so the real review load is the number of declarations
  and design decisions, not the line count. Each PR description lists the new public declarations and
  separates "ported from upstream unchanged" from "rewritten for the Lean 4.27→4.33 delta", so that
  only the latter needs reading.
- **Documentation** is updated in the PR that adds the module (`FILE_TREE.md`); only the `README.md`
  tidy-up is batched into PR 17.
- **`note/` is never merged into `main`** (§C-2). The durable conclusions move into
  `ARCHITECTURE.md` / `FILE_TREE.md` / `README.md`.

**`UniformDeviation/Bounds.lean` is not split.** Upstream split countable classes, separable
classes and the confidence form into three files in Phase 7, but inserting a split PR first would
require rewriting existing imports and delay the start. Additions from §4, §12.2, §13.3, §13.4,
§14.2 and §14.6 all land in this file, so avoid conflicts operationally.

- [ ] Concentrate the additions to `Bounds.lean` in PR 05; the countable and separable parts of
      §13.3 go in the same PR.
- [ ] Always append at the end of the file; do not reorder existing declarations. §13.3's "rewrite
      the existing versions as corollaries of the bridge" is done last, after all additions are in.
- [ ] The confidence form goes straight into `UniformDeviation/Confidence.lean` (§13.5), not into
      `Bounds.lean`.

**`example`s go in the library itself.** `lakefile.lean` has exactly one target,
`lean_lib «StatsMLlib»`, with no test target; there is no `test/`; and there are zero line-initial
`example`s in the whole library. We still put them in the library rather than adding `test/`: no new
target or CI configuration, they appear in the doc-gen4 output, and they preserve the "index of how
to use the main theorems" value that upstream `Main.lean` had. Placement follows the table in §13.6.

### C-2. Before starting

**`note/` is not merged into `main`.**

As `FILE_TREE.md` states, this repository holds the public Lean source tree plus a small set of
permanent project-policy documents (`ARCHITECTURE.md`, `AUTHORS.md`, `CODE_OF_CONDUCT.md`,
`CONTRIBUTING.md`, `LICENSE`, `README.md`, `FILE_TREE.md`). A migration plan is not that kind of
document, and most of it goes stale once the work is done. `note/upstream/` is 133 KB of another
project's internal documentation, written in terms of `FoML/...` modules that do not exist here.

Each durable conclusion in this document has a destination.

| Conclusion | Destination | PR |
|---|---|---|
| adding layer-one `Order` | `ARCHITECTURE.md` | 01 |
| adding `LearningTheory/EmpiricalRiskMinimization/` | `ARCHITECTURE.md` | 14 |
| placement of the 15 new modules | `FILE_TREE.md` | each module's PR |
| entropy integral owned by `Analysis.MetricEntropy` (B-3) | "Import direction" in `ARCHITECTURE.md` | 18 |
| the canonical `coveringNumber` is the one without a proof term (B-1) | same | 18 |
| public API listing | `README.md` | 17 |

**Step 0 — issue and plan branch** ★design direction

- [ ] Open an issue, as `CONTRIBUTING.md` requires. Summarize in it the goals of §0.0, the mapping
      table of §0.3, the design decisions of Appendices A and B, and the PR list of this appendix.
      Do not paste the whole document: it is 101,896 bytes, over GitHub's 65,536-character issue body
      limit.
- [ ] Push `note/` on a `reflect/plan` branch and link it from the issue. **That branch is not
      merged.** If inline comments are wanted, open a draft PR from it and close it without merging,
      stating clearly in the description that it is not meant to be merged.
- [ ] Settle the file-header attribution policy (§C-5) in the issue.
- [ ] Subsequent PRs do not contain `note/`. Checkbox updates happen on the `reflect/plan` branch.

**Spike (never merged)**

Push once, with sloppy proofs, through
`Order/IndexedSupremum` → `empiricalRademacherComplexity_comp` in `Signs` →
`rademacherComplexity_le_of_empirical_le` in `Complexity` → the countable version in `Bounds` →
the deterministic tail in `LinearPredictor/L2`. This is where the Lean 4.27→4.33 mathlib delta shows
up (§11-0) and where the statement shapes of §3.2, §4, §12.2 and §12.3 get validated. Then throw it
away.

### C-3. The sequence

Line counts estimate the new Lean to be written, taken from upstream `origin/main`; declaration
counts are the breakdown of the 204 port targets. ★ marks PRs that touch the library's design
direction and are discussed individually.

#### Foundations (stacked in order)

| # | Target | Upstream | Lines | Decls | Depends on |
|---|---|---|---|---|---|
| 01 ★ | `Order/IndexedSupremum.lean`, `Analysis/FiniteSample.lean`, `MeasureTheory/Measure/Real.lean`, `Probability/Concentration/Confidence.lean` (all new) + add layer-one `Order` to `ARCHITECTURE.md` | `ForMathlib/{Order.ISup, Analysis.FiniteSample, MeasureTheory.Measure.Real, Probability.Confidence}` | 160 | 8 | — |
| 02 | `Rademacher/{Defs,Signs,Complexity}.lean`, `Probability/Concentration/McDiarmid.lean` | `Defs`, `Rademacher.Signs`, `Rademacher.Expectation`, `Probability.McDiarmid` | 384 | 23 | 01 |
| 03 ★ | `Rademacher/Reindex.lean` (new) + `UniformDeviation/BoundedDifference.lean` + **the §14.5 refactor** (factoring out `ciSup`; no declarations added or removed) | `Rademacher.Reindex`, `Rademacher.BoundedDifference` | 158 | 7 | 01, 02 |
| 04 | `EmpiricalProcess/{Metric,FunctionClass}.lean`, `Topology/MetricSpace/CoveringNumber/Basic.lean` | `Entropy.PseudoMetric`, `Entropy.CoveringNumber` | 137 | 11 | 01, 02 |
| 05 ★ | `UniformDeviation/Bounds.lean` (countable + separable), `denseRestriction` in `Topology/SeparableSpace/Supremum.lean` + **the B-5 refactor** (making `denseSeqInTB` a corollary) | `Generalization.{Countable,Separable}`, `ForMathlib.Topology.SeparableSpace` | 495 | 22 | 01, 03 |
| 06 | `UniformDeviation/Confidence.lean` (new, `δ` form) | `Generalization.Confidence` | 211 | 12 | 05 |

Once 06 lands, the route from any sample-uniform fixed-sample bound to a generalization bound is
complete. PRs 07–16 are mutually independent and may be reordered.

#### Branches

| # | Target | Upstream | Lines | Decls | Depends on |
|---|---|---|---|---|---|
| 07 | `Rademacher/Dudley.lean` (absolute-value version and the connection to generalization; §13.5's right-hand side stays a `private abbrev` — B-3 stage 1) | `Entropy.Dudley`, `Generalization.Dudley` | 357 | 17 | 04, 06 |
| 08 | `Rademacher/FiniteClass.lean`, `Rademacher/LipschitzParameter.lean` (both new) | `Entropy.{FiniteClass,LipschitzParameter}`, `Generalization.{FiniteClass,LipschitzParameter}` | 564 | 17 | 07 |
| 09 | `FunctionClass/HilbertPredictor.lean` (new) | `Model.HilbertPredictor` | 256 | 7 | 02 |
| 10 | `FunctionClass/LinearPredictor/L2.lean` | `Model.LinearPredictorL2`, `Generalization.LinearPredictorL2` | 279 | 11 | 03, 06, 09 |
| 11 | `FunctionClass/LinearPredictor/L1.lean` (through the fixed-sample bound) | `Model.LinearPredictorL1` | 444 | 11 | 02 |
| 12 | `FunctionClass/LinearPredictor/L1.lean` (generalization bounds) | `Generalization.LinearPredictorL1` | 166 | 5 | 06, 11 |
| 13 | `FunctionClass/KernelPredictor.lean` (new) | `Model.RKHS`, `Generalization.RKHS` | 292 | 16 | 06, 09 |
| 14 | `EmpiricalRiskMinimization/{Defs,Basic}.lean` (new) + **the B-6 bridge** (`isLeastSquaresEstimator` → `IsERM`) | `Learning.{Defs,ERM}` | 242 | 22 | 02 |
| 15 | `Rademacher/Contraction.lean` (new) | `Learning.Contraction` | 487 | 8 | 02, 14 |
| 16 | `EmpiricalRiskMinimization/{Generalization,KernelPredictor}.lean` (new) | `Generalization.{Learning,RKHSLearning}` | 339 | 7 | 03, 06, 13, 14, 15 |

**09 comes before 10.** Upstream `Model/LinearPredictorL2.lean` imports `Model.HilbertPredictor`,
and the $\ell_2$ bound is written as the finite-dimensional corollary of the Hilbert-space version.

#### Finishing

| # | Target |
|---|---|
| 17 | The 13 acceptance `example`s (into the module ends, per the table in §13.6) + the public API table in `README.md` |

That completes the port: 204 declarations, roughly 4,971 lines.

#### Removing duplication (goal 2 of §0.0)

| # | Target |
|---|---|
| 18 ★ | **B-3 stage 2.** Add the two bridge lemmas relating `entropyIntegralTrunc` to the FoML-side and `TruncatedDudley`-side integrals, and emit a corollary restating the public bound of `Rademacher/Dudley.lean` in canonical form. Do not change the statement of `dudley_entropy_integral'`. Add the ownership line to `ARCHITECTURE.md` |
| 19 ★ | **B-8.** Make the relationship among the three maximal inequalities in `Probability/Concentration/Maximal.lean`, `Probability/Process/FiniteMaximum.lean` and `Probability/Process/SubGaussian.lean` explicit, or make one a corollary of another. Propose and discuss the approach in the PR |

### C-4. Which rounds get a design discussion

Only the opening issue and the five ★ PRs of C-3 touch the library's design direction.

| # | What is discussed |
|---|---|
| Step 0 (issue) | The overall design decisions (the mapping of §0.3, the naming of §0.4, Appendix B and §C-1) and file-header attribution |
| 01 | Whether layer-one may gain `Order` (the layer table, structure diagram and import-direction diagram of `ARCHITECTURE.md` all change) |
| 03 | Rewriting existing proofs in `UniformDeviation/BoundedDifference.lean` |
| 05 | Rewriting the `denseSeqInTB` area of `Probability/Process/Dudley.lean` |
| 18 | Unifying ownership of the entropy integral on `Analysis.MetricEntropy` |
| 19 | Disposition of the three maximal inequalities |

The remaining 14 are new files or pure additions to existing files.

### C-5. Attribution

`AUTHORS.md` requires:

> Existing notices must be preserved when code is moved, renamed, or substantially reused.
> migrated source headers must not be inferred from commit authors alone.

The facts are:

- Every commit in the port range (upstream after `3819e1e`) is authored by Sho Sonoda according to
  the upstream git history.
- Upstream `lean-rademacher` has almost no file headers: only `FoML/Probability/Hoeffding.lean`
  carries an `Authors:` line. So there is no header to copy.
- Every existing FoML-derived file in StatsMLlib carries
  `Copyright (c) 2024 Kei Tsukamoto. All rights reserved.` /
  `Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda`.

- [ ] Decide in step 0 whether the headers of the 15 new files match the existing FoML-derived files
      or the actual upstream authors.
- [ ] Add to the `Authors` line of an existing file if an addition brings a new author.
- [ ] Include the appropriate `Co-authored-by:` trailers in commits.

This concerns attribution of someone else's work, so it is not decided unilaterally.
