# Contributing to StatsMLlib

Thank you for contributing to StatsMLlib. Please open an issue before beginning a large formalization
or architectural change so that ownership and dependencies can be agreed in advance.

Participation in this project is governed by the [Code of Conduct](./CODE_OF_CONDUCT.md).

## Development requirements

- Use the Lean and Mathlib versions pinned by `lean-toolchain` and `lakefile.lean`.
- Place declarations in the subject-owned module described in `ARCHITECTURE.md`.
- Reuse existing StatsMLlib and Mathlib declarations before adding new infrastructure.
- Do not introduce `sorry`, `axiom`, `admit`, or `native_decide`.
- Keep builds free of warning and info messages; remove unused parameters instead of hiding them.
- Read [AUTHORS.md](./AUTHORS.md) and preserve all existing copyright and author attribution.
- Add significant authors to the relevant source-file `Authors` header. When work is co-written,
  add a `Co-authored-by` trailer for every additional author to the commit message.

## Before submitting a change

Run the whole-library verification from the repository root:

```bash
LEAN_NUM_THREADS=$(nproc) lake build
```

Describe the mathematical result, its source, the owning module, and any API decisions in the pull
request. New modules should include a Mathlib-style file header and module docstring.

Unless explicitly stated otherwise, intentionally submitted contributions are provided under the
Apache License 2.0 under the contribution terms in section 5 of [LICENSE](./LICENSE).
