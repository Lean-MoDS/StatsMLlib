# StatsMLlib file tree

This document presents the public Lean source tree after the Mathlib-style subject refactor.
`StatsMLlib/` contains 109 Lean modules under eight layer-one directories and no root-level Lean
files. A filesystem path such as `StatsMLlib/Probability/Process/Dudley.lean` corresponds to the Lean
module `StatsMLlib.Probability.Process.Dudley`.

| Layer | Modules |
| --- | ---: |
| `Analysis` | 5 |
| `LearningTheory` | 24 |
| `LinearAlgebra` | 5 |
| `MeasureTheory` | 3 |
| `Order` | 1 |
| `Probability` | 44 |
| `Statistics` | 21 |
| `Topology` | 2 |
| **Total** | **105** |

```text
StatsMLlib/
├── Analysis/
│   ├── MetricEntropy/
│   │   ├── Basic.lean
│   │   └── Chaining.lean
│   ├── NormedSpace/
│   │   └── CoveringNumber/
│   │       ├── Euclidean.lean
│   │       ├── L1.lean
│   │       └── LipschitzBall.lean
│   └── FiniteSample.lean
├── LearningTheory/
│   ├── EmpiricalRiskMinimization/
│   │   ├── Basic.lean
│   │   ├── Defs.lean
│   │   ├── Generalization.lean
│   │   └── KernelPredictor.lean
│   ├── EmpiricalProcess/
│   │   ├── FunctionClass.lean
│   │   └── Metric.lean
│   ├── FunctionClass/
│   │   ├── LinearPredictor/
│   │   │   ├── L1.lean
│   │   │   └── L2.lean
│   │   ├── NeuralNetwork/
│   │   │   └── HiddenUnit.lean
│   │   ├── HilbertPredictor.lean
│   │   └── KernelPredictor.lean
│   ├── Rademacher/
│   │   ├── Complexity.lean
│   │   ├── Contraction.lean
│   │   ├── Defs.lean
│   │   ├── Dudley.lean
│   │   ├── FiniteClass.lean
│   │   ├── LipschitzBall.lean
│   │   ├── LipschitzParameter.lean
│   │   ├── Massart.lean
│   │   ├── OneStep.lean
│   │   ├── Reindex.lean
│   │   ├── Signs.lean
│   │   └── Symmetrization.lean
│   └── UniformDeviation/
│       ├── BoundedDifference.lean
│       ├── Bounds.lean
│       ├── Confidence.lean
│       └── Defs.lean
├── LinearAlgebra/
│   └── Matrix/
│       ├── CourantFischer.lean
│       ├── EckartYoungMirsky.lean
│       ├── Lieb.lean
│       ├── Perturbation.lean
│       └── SingularValue.lean
├── MeasureTheory/
│   ├── Function/
│   │   └── L1Subsequence.lean
│   ├── Integral/
│   │   └── LayerCake.lean
│   └── Measure/
│       └── Real.lean
├── Order/
│   └── IndexedSupremum.lean
├── Probability/
│   ├── Concentration/
│   │   ├── LogSobolev/
│   │   │   ├── Bernoulli.lean
│   │   │   ├── GaussianCompactSupport.lean
│   │   │   ├── GaussianOneDim.lean
│   │   │   ├── GaussianTensorization.lean
│   │   │   └── TwoPoint.lean
│   │   ├── Bernstein.lean
│   │   ├── Chernoff.lean
│   │   ├── Confidence.lean
│   │   ├── EfronStein.lean
│   │   ├── EuclideanNorm.lean
│   │   ├── HansonWright.lean
│   │   ├── Hoeffding.lean
│   │   ├── Maximal.lean
│   │   └── McDiarmid.lean
│   ├── Entropy/
│   │   ├── Conditional/
│   │   │   ├── Basic.lean
│   │   │   ├── Decomposition.lean
│   │   │   └── Subadditivity.lean
│   │   ├── Basic.lean
│   │   ├── Duality.lean
│   │   └── Variational.lean
│   ├── Gaussian/
│   │   ├── Poincare/
│   │   │   ├── EfronStein.lean
│   │   ├── EuclideanNorm.lean
│   │   │   ├── LevyContinuity.lean
│   │   │   ├── Limit.lean
│   │   │   ├── RademacherApproximation.lean
│   │   │   └── Taylor.lean
│   │   ├── Sobolev/
│   │   │   ├── Cutoff.lean
│   │   │   ├── Defs.lean
│   │   │   ├── Density.lean
│   │   │   ├── LipschitzMollification.lean
│   │   │   └── Mollification.lean
│   │   ├── Basic.lean
│   │   ├── Lipschitz.lean
│   │   └── LipschitzConcentration.lean
│   ├── Independence/
│   │   └── FinsetPi.lean
│   ├── Moments/
│   │   ├── Cumulant.lean
│   │   ├── Expectation.lean
│   │   ├── Exponential.lean
│   │   ├── Orlicz.lean
│   │   └── SubGaussianOrlicz.lean
│   ├── Process/
│   │   ├── Dudley.lean
│   │   ├── FiniteMaximum.lean
│   │   ├── SubGaussian.lean
│   │   └── TruncatedDudley.lean
│   ├── RandomMatrix/
│   │   ├── Basic.lean
│   │   ├── Bernstein.lean
│   │   └── Lieb.lean
│   └── SmallBall.lean
├── Statistics/
│   └── Regression/
│       └── LeastSquares/
│           ├── L1/
│           │   ├── CoveringBound.lean
│           │   ├── DesignMatrix.lean
│           │   ├── LocalizedBall.lean
│           │   ├── PredictorClass.lean
│           │   └── ShiftedClass.lean
│           ├── Linear/
│           │   ├── DesignMatrix.lean
│           │   ├── EmpiricalProcess.lean
│           │   ├── EntropyIntegral.lean
│           │   ├── EuclideanReduction.lean
│           │   ├── GaussianComplexity.lean
│           │   ├── IntegralBounds.lean
│           │   ├── LocalizedBall.lean
│           │   ├── MinimaxRate.lean
│           │   └── PredictorClass.lean
│           ├── BasicInequality.lean
│           ├── CriticalRadius.lean
│           ├── Defs.lean
│           ├── LocalGaussianComplexity.lean
│           ├── Localization.lean
│           ├── MasterErrorBound.lean
│           └── SubGaussianity.lean
└── Topology/
    ├── MetricSpace/
    │   └── CoveringNumber/
    │       └── Basic.lean
    └── SeparableSpace/
        └── Supremum.lean
```

Only the public `StatsMLlib/` source tree is shown. Historical provenance is recorded in file headers
and the README; build artifacts and dependency caches are omitted. See
[`ARCHITECTURE.md`](./ARCHITECTURE.md) for ownership and import-direction rules.
