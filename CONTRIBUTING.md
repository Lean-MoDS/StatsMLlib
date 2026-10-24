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

If the change adds, moves, or deletes a module, regenerate the module index; CI fails when
[`FILE_TREE.md`](./FILE_TREE.md) is out of date:

```bash
python3 scripts/file_tree.py
```

Describe the mathematical result, its source, the owning module, and any API decisions in the pull
request. New modules should include a Mathlib-style file header and module docstring.

## Citing references

Sources cited from docstrings are collected in [`docs/references.bib`](./docs/references.bib),
which doc-gen4 renders as the references page of the generated documentation. When a result is
taken from outside the main textbooks because it is more general or stronger than the textbook
version, add the source there and cite it from the module docstring as `[bibkey]` or
`[Author, *Title* (optional location)][bibkey]`.

Unless explicitly stated otherwise, intentionally submitted contributions are provided under the
Apache License 2.0 under the contribution terms in section 5 of [LICENSE](./LICENSE).
