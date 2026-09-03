# Claude / Lean workflow (StatsMLlib)

StatsMLlib is a Lean 4 + Mathlib library for probability, empirical processes, statistical learning
theory, and statistics.

This file is the authoritative runtime instruction set for agent work in this repository.
If external templates conflict with this file, follow this file.

## Sources of truth

Read these before making non-trivial changes:

- `ARCHITECTURE.md` — layer ownership, import direction, module naming. Binding for placement decisions.
- `CONTRIBUTING.md` — build and submission requirements.
- `note/plan.md` — the current work plan (Rademacher complexity → generalization bounds port).
  `note/plan.en.md` is the English rendering; `note/upstream/` holds the upstream originals.
- `FILE_TREE.md` — module-by-module map of the library.

## Skills index

Repository-local skills under `.claude/skills/`:

- `lean-rule` — execution workflow for Lean proof work (plan → skeleton → error-driven iteration).
- `mathlib-usage` — lemma discovery, imports, tactic preference order.

Planning helper: `.claude/workflow/proof-planning.md` (planning and replanning only).

Priority when several apply:

1. `CLAUDE.md` (this file)
2. `ARCHITECTURE.md` / `CONTRIBUTING.md` for placement and submission rules
3. `lean-rule` (execution workflow for Lean proof work)
4. `mathlib-usage`

## Common commands

- Type-check one file: `lake env lean StatsMLlib/Path/To/File.lean`
- Build the whole library: `LEAN_NUM_THREADS=$(sysctl -n hw.ncpu) lake build`
  (`CONTRIBUTING.md` writes `nproc`; on macOS use `sysctl -n hw.ncpu`.)
- Mathlib search: `rg -n "<pattern>" .lake/packages/mathlib/Mathlib`
- Repo search: `rg -n "<pattern>" StatsMLlib`

`lake env lean <file>` is the fast inner loop; `lake build` is the gate before proposing a change.

## Lean LSP tools

The `lean-lsp` MCP server (`.mcp.json`, `lean-lsp-mcp` 0.30.0 via `uvx`) exposes 23 tools built on
the Lean language server. The ones that matter day to day:

Goal and diagnostic inspection:

- `lean_goal` — goal and context at a position
- `lean_term_goal` — expected type at a position
- `lean_diagnostic_messages` — diagnostics for a file
- `lean_hover_info` — signature and docstring of a name
- `lean_file_outline` — declarations in a file
- `lean_declaration_file` / `lean_references` — jump to a definition, find its uses

Experimentation:

- `lean_multi_attempt` — try several tactics at a position without editing the file
- `lean_run_code` — `#check` and other minimal snippets
- `lean_verify` / `lean_build` — verify a file or the project
- `lean_minimal_hypotheses` / `lean_profile_proof` — trim unused hypotheses, find slow steps

Lemma search:

- `lean_local_search` — search this project and Mathlib by name
- `lean_leansearch` — natural-language search
- `lean_loogle` — search by shape or signature
- `lean_state_search` / `lean_hammer_premise` — suggestions from the current goal

Prefer these over re-running `lake env lean` for goal inspection: they answer "what is the goal here"
without a full re-elaboration. Still confirm the final state with `lake env lean <file>`.

## Standard proof workflow

1. Read the target statement and its surrounding module.
2. Plan a short tactic strategy and a theorem-reuse path.
3. Use skeleton-first for non-trivial proofs (`have ... := by sorry` blocks), then fill from the top.
4. Iterate with Lean diagnostics: fix one top error at a time, re-check after each fix.
5. Finish only after every `sorry` is gone and the file type-checks.

Details are in `.claude/skills/lean-rule/SKILL.md`.

## Repository invariants

These come from `CONTRIBUTING.md` and are not negotiable in committed code:

- No `sorry`, `axiom`, `admit`, or `native_decide`. A `sorry` skeleton is a transient drafting
  device inside a working session, never a stopping point and never a proposed change.
- No warnings or info messages in the build. `lakefile.lean` enables `linter.longLine`,
  `linter.cdot`, `linter.style.lambdaSyntax`, `linter.refine`, `linter.oldObtain`, and others;
  `autoImplicit` is off, so every variable must be bound explicitly.
- Remove unused parameters instead of hiding them with `_`.
- Reuse existing StatsMLlib and Mathlib declarations before adding new infrastructure.
- New modules need a Mathlib-style file header and a module docstring.
- Preserve existing copyright and `Authors` headers; add significant authors when you add substance.

## Reading Mathlib source

Mathlib at this pin (v4.33.0, 2026-08-10) uses the Lean module system: 8241 of its 8311 files open
with `module` and write `public import Mathlib.X`. StatsMLlib does not. When lifting code or imports
out of Mathlib, strip `module` / `public` — `public import` in a non-module file is a hard error.

## Placement rules

- Every Lean module lives under one of the seven layer-one directories. No Lean files directly in
  `StatsMLlib/`.
- Respect the import tier: `{MeasureTheory, Topology, LinearAlgebra}` → `Analysis` → `Probability`
  → `LearningTheory` → `Statistics`. Never import from a later tier.
- Do not add `Main.lean`, `Infrastructure.lean`, or an unqualified `Defs.lean`.
- When a declaration could go in two places, `ARCHITECTURE.md` "Layer-one ownership" decides.
- Changing where a declaration is owned is a design decision: state it explicitly rather than
  moving it silently.

## Proof style

- Keep steps small and local.
- Prefer `exact`, `simpa`, `rw`, `constructor`, `cases`, `intro`, `apply` before heavier automation.
- Prefer `simp only [...]` over broad `simp [*]` in fragile goals.
- Use explicit `*` and `^` notation.
- Prefer project notation and existing abbreviations over fully qualified names where they exist.

## Delegation

Claude Code has subagents; use them where Lean work is naturally parallel or search-heavy.

- `lean-dev` (`.claude/agents/lean-dev.md`) — a self-contained proof obligation: one lemma, one
  repair, one import cleanup. It inherits the main model, so it is fit for hard proofs, not just
  mechanical ones. Delegating keeps a long `lake env lean` / search loop out of the main context.
- `Explore` — "where does this concept already live, in StatsMLlib or Mathlib" questions that would
  otherwise dump many file excerpts into context.

Do not delegate a step whose result you need in order to choose the next one; the round trip costs
more than doing it inline.

## Safety and operations

- Keep edits minimal and task-local; avoid unrelated cleanup in the same change.
- Do not run destructive git commands unless explicitly requested.
- Do not commit unless explicitly requested. Stage only changed tracked files with `git add <file>`.
- PRs are kept small; `note/plan.md` appendix C marks the ones that touch library design and need
  discussion first.

## Language

- Repository artifacts (Lean code, docstrings, comments, commit messages, PR text) are in English.
- Conversation with the user follows the user's language.
