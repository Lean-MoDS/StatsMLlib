---
name: mathlib-usage
description: Mathlib usage for StatsMLlib — lemma discovery and existence checks, import policy, tactic preference order, simp discipline. Use when looking for a lemma, deciding imports, or choosing a tactic.
---

# Mathlib usage

## Basics

- Mathlib is a dependency of the library; its declarations are free to use.
- Add imports sparingly and only the ones actually needed. Prefer `open` / `open scoped` / `local`
  over adding an import.
- Respect the import tier in `ARCHITECTURE.md`: `{MeasureTheory, Topology, LinearAlgebra}` →
  `Analysis` → `Probability` → `LearningTheory` → `Statistics`. A module never imports from a later
  tier. Do not rely on transitive imports implicitly; after changing imports, re-check the edited
  file and its downstream importers.
- Try existing StatsMLlib and Mathlib declarations first. Only if none fits, add a minimal helper.
- Never invent lemma names. Confirm a name exists before using it.
- Do not ask the user which lemma to try when local search, diagnostics, or a small snippet answers it.

## Search flow

0. Mathlib sources live at `.lake/packages/mathlib/Mathlib`. If that path is missing, run `lake update`.
1. Build keywords: synonyms, case variants, typeclass and structure names; search notation as a string.
2. Narrow with `rg -n "<keyword>" .lake/packages/mathlib/Mathlib`.
3. Also search the library itself: `rg -n "<keyword>" StatsMLlib` — the result may already exist here.
4. Read the hits: check hypotheses, related lemmas, `[simp]` / `[grind]` / `[fun_prop]` attributes.
   - Mathlib at this pin has migrated to the Lean module system: 8241 of its 8311 files begin with
     `module` and write `public import Mathlib.X`. StatsMLlib does **not** use the module system.
     Never copy an import line verbatim out of Mathlib source — `public import` outside a `module`
     file fails with `cannot use 'public import' without 'module'`. Write plain `import Mathlib.X`.
   - Declaration lines are still bare `theorem` / `lemma`, so `rg` patterns are unaffected.
5. Confirm existence with `lean_run_code` (`#check`) or `lean_hover_info`.
6. The `lean-lsp` MCP server is usually faster than guessing keywords: `lean_local_search` (by name,
   across this project and Mathlib), `lean_leansearch` (natural language), `lean_loogle` (by shape),
   `lean_state_search` and `lean_hammer_premise` (from the current goal).
7. Confirm finally with `lake env lean StatsMLlib/Path/To/File.lean`.

## Tactic preference order

1. **Local cleanup** — `rw`, `simpa`, `simp only [...]`, `simp_rw [...]`. Handle subgoal rewrites here.
2. **Specialized** — `fun_prop`, `measurability`, `positivity`, `finiteness`, `ring_nf`, `field_simp`,
   `linarith`, `nlinarith`, `omega`, `gcongr`, `linear_combination`, `bound`, `order`.
   - `bound` closes routine `0 ≤ x` / `x ≤ y` bound goals by structural recursion; useful for the
     nonnegativity and monotonicity side conditions that appear all over complexity estimates.
   - `order` decides goals in linear and partial orders from the hypotheses in context.
   - `module` / `abel` / `noncomm_ring` cover the non-commutative and module-valued analogues of `ring`.
3. **General automation** — `grind`, `aesop`. `grind` is now heavily used inside Mathlib itself
   (~5900 call sites at the pinned version, up ~30% over 2026 H1, with `@[grind]` attributes on
   library lemmas). Treat it as a legitimate closer for arithmetic, order, and first-order goals,
   and try it on a stuck side goal before hand-rolling a chain of rewrites. It is still not the
   right main strategy for measure, integral, or spectral goals — there, structure the proof first
   and let `grind` close the leaves.

## simp discipline

- Do not routinely use `simp [*]` on subgoals.
- Do not flood `simp` with AC lemmas (`mul_assoc`, `mul_comm`, `add_assoc`, `add_comm`).
- Do not unfold large definitions without a purpose.
- Do not chain a fragile `rw` right after `simp`; insert a `have` and `simpa using` it.
- When `simp?` suggests a `simp only`, pin it — it is both faster and more stable.
- Under binders, use `simp_rw` when rewrite order matters.

## Goal-oriented patterns

**Structural properties** (`Continuous*`, `Measurable*`, `Integrable*`, `Differentiable*`): `fun_prop`
is the engine — `measurability` is now a backward-compatibility wrapper that delegates to it for
`Measurable` / `AEMeasurable` / `StronglyMeasurable` / `AEStronglyMeasurable`. Reach for `fun_prop`
first; when tagging a new lemma, use `@[fun_prop]`, not `@[measurability]`. Side goals that reduce to
order facts go to `positivity` or a short `linarith`.

**Algebraic normalization**: `ring_nf` for polynomial-style normalization; `noncomm_ring` / `abel` /
`module` outside commutative rings; `field_simp` only where denominators must be cleared;
`linear_combination` when a linear relation closes the goal.

**Rewriting-heavy goals**: `simp_rw` under binders, small explicit `simp only [...]` sets, targeted
local rewrites (`rw [mul_assoc]`) rather than large AC bundles.

**Inequalities**: `positivity` first for nonnegativity, then `linarith` / `nlinarith` / `omega` by
arithmetic domain, `gcongr` for congruence-style monotonicity steps.

## LSP helpers

- `lean_term_goal` — expected type at a position
- `lean_goal` — goal and context
- `lean_diagnostic_messages` — distinguishes import and typeclass issues from proof errors
- `lean_hover_info` — signature and docstring of a name
- `lean_multi_attempt` — compare candidate tactics without editing
- `lean_declaration_file` / `lean_references` — read a definition in place, see how it is used

Final confirmation is always `rg` / `#check` / `lake env lean`.
