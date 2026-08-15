<h1 align="center">StatsMLlib</h1>

<h4 align="center">Verified probability, statistics, and learning theory in Lean 4</h4>

<p align="center">
  <a href="https://github.com/leanprover/lean4/releases/tag/v4.32.0"><img src="https://img.shields.io/badge/Lean-v4.32.0-blue?style=for-the-badge" alt="Lean v4.32.0"></a>
  <a href="./LICENSE"><img src="https://img.shields.io/badge/License-Apache%202.0-lightgrey?style=for-the-badge" alt="Apache 2.0"></a>
  <a href="https://statsmllib.github.io/"><img src="https://img.shields.io/badge/Website-StatsMLlib-175b47?style=for-the-badge" alt="StatsMLlib website"></a>
</p>

StatsMLlib is a reusable Lean 4 library for probability, high-dimensional statistics, empirical
processes, and statistical learning theory. It is built on Mathlib and organized as a subject-first,
acyclic hierarchy rather than around individual projects or proof techniques.

The public source contains 90 modules and no `sorry`, `axiom`, `admit`, or `native_decide`.

## Scope

| Layer | Module root | Contents |
| --- | --- | --- |
| Measure theory | `StatsMLlib.MeasureTheory.*` | Integral, convergence, and L1 infrastructure |
| Topology | `StatsMLlib.Topology.*` | Covering and packing numbers, separable suprema |
| Analysis | `StatsMLlib.Analysis.*` | Metric entropy, chaining, normed-space covering estimates |
| Linear algebra | `StatsMLlib.LinearAlgebra.*` | Singular values, variational principles, matrix perturbation |
| Probability | `StatsMLlib.Probability.*` | Concentration, entropy methods, Gaussian analysis, random matrices |
| Learning theory | `StatsMLlib.LearningTheory.*` | Empirical metrics, Rademacher complexity, uniform deviation |
| Statistics | `StatsMLlib.Statistics.*` | Localized least squares, regression, and minimax guarantees |

The dependency order is foundational measure theory, topology, and linear algebra; then analysis;
probability; learning theory; and statistics. See [ARCHITECTURE.md](./ARCHITECTURE.md) for the
ownership policy and [FILE_TREE.md](./FILE_TREE.md) for the complete module index.

## Selected results

- Dudley's entropy integral and truncated Dudley bounds for sub-Gaussian processes
- Efron–Stein, Hoeffding, McDiarmid, scalar Bernstein, Gaussian Poincare, and Gaussian log-Sobolev inequalities
- Gaussian Lipschitz concentration, Hanson–Wright, and matrix Bernstein inequalities
- Singular-value decomposition, Courant–Fischer, Eckart–Young–Mirsky, Weyl, and Davis–Kahan
  perturbation results
- Symmetrization, Massart's lemma, Rademacher complexity, and uniform-deviation bounds
- Localized least-squares theory for linear and L1-constrained regression

Representative declarations include `dudley`, `truncated_dudley_entropy_bound`, `efronStein`,
`gaussian_lipschitz_concentration`, `bernstein_inequality`, `hanson_wright_inequality`,
`RMT.matrix_bernstein_inequality_hdp_all`, `expectation_le_rademacher`, and
`master_error_bound`.

## Getting started

StatsMLlib is pinned to Lean and Mathlib `v4.32.0`.

```bash
# Optional: download the Mathlib build cache.
lake exe cache get

# Build every StatsMLlib module.
LEAN_NUM_THREADS=$(nproc) lake build

# Build an individual module.
LEAN_NUM_THREADS=$(nproc) lake build StatsMLlib.Probability.Process.Dudley
```

To use the `v4.32.0` release from another Lake project:

```lean
require «StatsMLlib» from git
  "https://github.com/Lean-MoDS/StatsMLlib.git" @ "v4.32.0"
```

Then import only the modules needed by the project:

```lean
import StatsMLlib.Probability.Concentration.HansonWright
import StatsMLlib.LearningTheory.UniformDeviation.Bounds
```

## Contributing

Read [CONTRIBUTING.md](./CONTRIBUTING.md) and the
[Code of Conduct](./CODE_OF_CONDUCT.md) before opening a change. New code must preserve the subject
ownership rules, source attribution, complete-proof policy, and warning-free build.

## Authors, copyright, and provenance

StatsMLlib unifies material developed in the former SLT and FoML trees. Files retain their original
copyright and author headers. See [AUTHORS.md](./AUTHORS.md) for the organizer and contributor lists
and the repository's copyright, authorship, and co-authorship policy; the individual source headers
remain authoritative for file-level attribution.

## License

StatsMLlib is released under the [Apache License 2.0](./LICENSE). Copyright remains with the individual
holders identified in the source files.
