# StatsMLlib architecture

StatsMLlib follows a subject-first filesystem modeled on Mathlib. Every Lean module lives below one of
eight layer-one directories; there are no Lean files directly in `StatsMLlib/`.

## Layer-one ownership

| Layer | Owns |
| --- | --- |
| `Order` | Order-theoretic results with no measure, topology, or algebraic structure, such as estimates for indexed suprema in conditionally complete lattices. |
| `MeasureTheory` | Reusable measure, integral, and convergence results that do not require probabilistic structure. |
| `Topology` | General topological and pseudo-metric constructions, including covering and packing numbers. |
| `LinearAlgebra` | Deterministic matrix, operator, singular-value, and spectral results. |
| `Analysis` | Deterministic analytic constructions built on the foundational layers, including metric entropy and normed-space covering estimates. |
| `Probability` | Random variables and processes, moments, concentration, entropy methods, Gaussian analysis, and random matrices. |
| `LearningTheory` | Empirical metrics, complexity measures, uniform convergence, and learning-theoretic function classes. |
| `Statistics` | Statistical models, estimators, regression, and finite-sample or minimax guarantees. |

The current second-level organization is:

```text
StatsMLlib/
├── Analysis/{MetricEntropy,NormedSpace}
├── LearningTheory/{EmpiricalProcess,EmpiricalRiskMinimization,FunctionClass,Rademacher,UniformDeviation}
├── LinearAlgebra/Matrix
├── MeasureTheory/{Function,Integral,Measure}
├── Order
├── Probability/{Concentration,Entropy,Gaussian,Independence,Moments,Process,RandomMatrix}
├── Statistics/Regression/LeastSquares
└── Topology/{MetricSpace,SeparableSpace}
```

## Import direction

The local import graph is tiered as follows:

```text
{Order, MeasureTheory, Topology, LinearAlgebra}
                    ↓
                 Analysis
                    ↓
                Probability
                    ↓
             LearningTheory
                    ↓
                Statistics
```

A module may import within its own layer and from any earlier tier. It must not import from a later
tier. Downstream modules may bypass an intermediate tier and import an earlier owner directly.

In particular:

- empirical norms and pseudo-metrics are owned by `LearningTheory.EmpiricalProcess`; statistical
  regression consumes them;
- deterministic covering numbers are owned by `Topology`, while Euclidean and L1 estimates are
  owned by `Analysis`;
- generic entropy functionals are under `Probability.Entropy`, while distribution-specific
  log-Sobolev inequalities are under `Probability.Concentration.LogSobolev`;
- the metric entropy integral is owned by `Analysis.MetricEntropy`, whose
  `entropyIntegralTrunc` is the canonical form; the Dudley bounds in
  `LearningTheory.Rademacher` and `Probability.Process` state their own spellings, which
  are related back to it by bridging lemmas rather than replaced;
- deterministic matrix spectral theory is under `LinearAlgebra.Matrix`, while random-matrix
  theorems are under `Probability.RandomMatrix`.

## Module naming

- Do not add `Main.lean`, `Infrastructure.lean`, or an unqualified `Defs.lean` under `StatsMLlib/`.
- `Basic.lean` and `Defs.lean` are acceptable only when their directory gives a precise subject.
- Prefer full subject names in paths: `RandomMatrix`, `LogSobolev`, and
  `EckartYoungMirsky`, rather than provenance or project abbreviations.
- A whole-library umbrella, if one is ever needed, must be a declaration-free `StatsMLlib.lean`
  outside `StatsMLlib/`; topic modules should remain selectively importable.

## Refactoring decisions

The 2026-07 refactor replaced the flat merged layout with the subject hierarchy above. The main
ownership changes were:

- the former `Main.lean` was split among uniform-deviation, linear-predictor, and Rademacher Dudley
  modules;
- the former `CoveringNumber.lean` was split between topology and analysis;
- the former `MeasureInfrastructure.lean` was split into layer-cake, Chernoff, exponential-moment,
  and finite-maximum modules;
- the canonical empirical metric was extracted from least-squares definitions;
- `GaussianLSI`, `GaussianPoincare`, `GaussianSobolevDense`, `MatrixInfra`, `RMT`, `ForMathlib`, and
  `LeastSquares` ceased to be layer-one directories.
