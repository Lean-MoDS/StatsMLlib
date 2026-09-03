---
name: lean-rule
description: Execution workflow for Lean proof work in StatsMLlib (plan → sorry-skeleton → one-error-at-a-time iteration → Mathlib search → minimal diffs). Use when writing, repairing, or extending any proof in a .lean file.
---

# Lean execution workflow

`../../workflow/proof-planning.md` is only for **proof planning and replanning**. Do not auto-apply
its formatting rules or its olympiad-style syntax restrictions during implementation. During
implementation, `CLAUDE.md` and this skill come first.

The skeleton-first rule below is for proof construction — new proofs, proof repair, substantial
proof extension. Do not apply it to non-semantic refactoring or cleanup passes.

## Routing

- Writing or repairing a proof in a `.lean` file: this skill is the primary workflow, then
  `mathlib-usage` for lemma, import, and tactic decisions.
- "Does this lemma exist", import minimization, tactic choice: `mathlib-usage`.
- Where a declaration belongs: `ARCHITECTURE.md`.

## Workflow

1. Plan with `../../workflow/proof-planning.md` Part 1.
   - The plan is a transient artifact unless the user asked to see planning output.
   - Do not pause after planning when the next implementation step is already clear.
2. For non-trivial proofs, first write a visible skeleton in the file: many small
   `have ... := by sorry` steps exposing the main dependency chain.
   - This is the default first artifact of implementation, not a private note.
   - Skip it only when the proof closes immediately with a tiny local argument.
3. Two phases:
   - Phase 1: get a type-checkable `have ... := by sorry` skeleton.
   - Phase 2: fill the skeleton from the top until no `sorry` remains.
4. Keep each `have` mathematically meaningful and fillable in roughly 1–5 lines. Split any `have`
   that grows past that.
5. Implement in dependency order, top down.
6. For each `have`, iterate strictly:
   - Apply a minimal edit (1–5 lines) around the **topmost** error only.
   - Observe immediately: `lake env lean StatsMLlib/Path/To/File.lean`, or `lean_goal` /
     `lean_diagnostic_messages` from the `lean-lsp` MCP server.
   - Re-check before making any further speculative edit. Never batch guessed fixes.
   - In Phase 1 and early Phase 2, non-semantic lint warnings are not blockers: defer `longLine`,
     `unusedSimpArgs`, `unnecessarySimpa`. Prioritize type errors, goal-shape mismatches,
     elaboration failures, and heartbeat errors.
   - On a heartbeat error, isolate the heavy fragment, temporarily restore just that fragment to
     `by sorry`, keep the outer skeleton moving, and revisit with a smaller target.
   - If one `have` stays open 5 times or the errors worsen, re-plan.
7. Before stopping, run `lake env lean` on the target file. If compile errors, unsolved goals, or
   elaboration failures remain, keep working on the topmost one.
8. Before stopping, run `rg -n '\bsorry\b'` on the target file, extended to every changed Lean file
   when the work spans more than one. Any remaining proof `sorry` means the work is unfinished —
   continue from the easiest one.
9. Once the deferred lint warnings are the only thing left, clear them: the build must be
   warning-free (`CONTRIBUTING.md`).
10. Finish with `lake env lean` on the changed files, and `lake build` before proposing the change.
11. If stuck, re-plan with `../../workflow/proof-planning.md` Part 2.

## Implementation principles

- Keep changes minimal and local.
- Prefer an explicit `have ... := by sorry` skeleton over attempting one large direct proof script.
- Stabilize the proof first; clear deferred non-semantic lint after the dependency chain works.
- Temporary `have`s are fine while structuring, but collapse one-off scaffolding that no longer helps.
- A remaining `sorry` is never an acceptable stopping point, and never part of a proposed change.
- For subgoals, avoid `simp [*]` and huge `simp` sets; prefer `rw` / `simpa` / `simp only` / `simp_rw`.
- Do not chain a fragile `rw` right after `simp`; insert `have h : ... := by ...` then `simpa using h`.
- `ring` / `ring_nf` for commutative normalization; `noncomm_ring`, `abel`, or `module` outside
  commutative rings. `field_simp` in tiny helpers for denominators, `fun_prop` / `measurability`
  for regularity, `positivity` / `finiteness` for sign and finiteness side goals.
- `grind` is a legitimate closer for arithmetic, order, and first-order leaves, and Mathlib leans on
  it heavily at this pin; do not make it — or `aesop` — the main weapon for measure, integral, or
  spectral goals. Structure the proof, then let it close the leaves.
- `autoImplicit` is off: bind every variable explicitly.

## Standard observation loop

1. `lake env lean StatsMLlib/Path/To/File.lean`
2. For the top error, `lean_goal` / `lean_term_goal`
3. Minimal fix for that single error
4. Re-check immediately
5. Only then look at the new top error

`lean_multi_attempt` is the cheap way to compare several candidate tactics at one position without
editing the file. `lean_run_code` is for `#check` and throwaway snippets.

## Role and interaction

Proof work has a repo-specific stopping rule that overrides ordinary judgment about when a task is
done:

- While compile errors, unsolved goals, or relevant `sorry`s remain in the target file, keep working
  on the topmost one. A partially closed skeleton is not a deliverable, and a progress report is not
  a reason to stop.
- One failed approach is not a blocker: re-search, re-plan, split the goal, or isolate the heavy
  fragment before considering the line of attack exhausted.
- The question worth asking is the design one — where a declaration is owned, which of two API shapes
  the library should commit to (`ARCHITECTURE.md`, `note/plan.md` appendix C). Ask those early rather
  than proving the wrong statement well. Do not ask which tactic or lemma to try; that is answerable
  from the goal, the diagnostics, and search.

## Replanning triggers

Re-plan with `../../workflow/proof-planning.md` Part 2 if any holds:

1. The same approach fails 3 times in a row.
2. The same `have` is edited 5+ times without closing.
3. Errors grow more complex after fixes.
4. One `have` proof stretches beyond ~10 lines.

When replanning, split the current `have` into smaller ones and search for existing lemmas first.

## Heartbeat recovery

- Trigger only on an actual heartbeat error (`maximum heartbeats exceeded` and similar).
- Isolate the heavy fragment first: split the declaration, move the expensive subgoal into a smaller
  `have`, or factor a helper lemma.
- Temporarily replacing only the heavy fragment with `by sorry` is acceptable mid-loop.
- On return, reduce elaboration cost structurally: shrink `simp` / `rw` scope, add type annotations,
  break large terms into `let` / `have`, reduce instance search.
- Only after that, consider `set_option maxHeartbeats <n> in` locally, or
  `set_option synthInstance.maxHeartbeats <n> in` when typeclass search is the cause.
- Common causes: `simp` / `rw` explosions, oversized declarations, coercion-heavy terms, weak
  annotations, expensive typeclass search.

## Commit discipline

- Commit only when the user asks, at the granularity they ask for.
- Stage only changed tracked files with `git add <file>`; avoid unrelated untracked files.
- Add `Co-authored-by` trailers for co-written work (`CONTRIBUTING.md`).
