#!/bin/bash
# gate.sh — one command to run before opening a port PR.
#
# Implements note/plan.md §10 (verification policy) items 1-4 and 7, plus the
# appendix C-1 budget rule and the two failure modes the plan does not name:
# base drift and a note/ leak. §10-5 and §10-6 cannot be scripted, so this
# prints them as a checklist and requires a reviewer line in the ledger.
#
# Usage:  bash .claude/port/gate.sh [--pr NN] [--decls N] [--lines N]
#
# Exits 0 only if every mechanical check passes.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

PR=""; BUDGET_DECLS=20; BUDGET_LINES=600; EXTRA_PATHS=""
while [ $# -gt 0 ]; do
  case "$1" in
    --pr)    PR="$2"; shift 2 ;;
    --decls) BUDGET_DECLS="$2"; shift 2 ;;
    --lines) BUDGET_LINES="$2"; shift 2 ;;
    # Escape hatch for the infrastructure PR (00), which legitimately touches
    # .github/ and .gitignore. A port PR must never need this.
    --allow-path) EXTRA_PATHS="$EXTRA_PATHS $2"; shift 2 ;;
    *) echo "gate.sh: unknown argument $1" >&2; exit 2 ;;
  esac
done

fail=0
ok()   { printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad()  { printf '  \033[31mFAIL\033[0m  %s\n' "$1"; fail=1; }
note() { printf '        %s\n' "$1"; }
head_() { printf '\n\033[1m%s\033[0m\n' "$1"; }

BASE=$(git merge-base origin/main HEAD 2>/dev/null)
if [ -z "$BASE" ]; then
  echo "gate.sh: cannot find merge-base with origin/main (run git fetch origin)" >&2
  exit 2
fi
CHANGED=$(git diff --name-only "$BASE"...HEAD -- '*.lean')

head_ "Branch"
note "branch:     $(git rev-parse --abbrev-ref HEAD)"
note "merge-base: $(git rev-parse --short "$BASE")"
note "changed .lean files: $(echo "$CHANGED" | grep -c . )"

# ---------------------------------------------------------------- branch shape
head_ "Branch shape"

# A port PR carries the mathematics and nothing else: StatsMLlib Lean sources,
# plus the three documents C-1 requires be updated alongside them. Everything
# else — note/, .claude/, CLAUDE.md, .mcp.json, *.bak, lakefile.lean, .github/ —
# is a leak. This subsumes the note/ check: reflect/plan carries 7k lines of
# note/, so branching from the wrong HEAD is the easiest mistake available.
leak=0
while read -r p; do
  [ -z "$p" ] && continue
  case "$p" in
    StatsMLlib/*.lean|FILE_TREE.md|ARCHITECTURE.md|README.md|AUTHORS.md) continue ;;
  esac
  allowed=0
  for extra in $EXTRA_PATHS; do
    case "$p" in $extra) allowed=1; break ;; esac
  done
  [ "$allowed" -eq 1 ] && continue
  [ "$leak" -eq 0 ] && bad "the diff contains files that are not StatsMLlib mathematics"
  note "leak: $p"
  leak=1
done < <(git diff --name-only "$BASE"...HEAD)
[ "$leak" -eq 0 ] && ok "diff contains only StatsMLlib Lean sources and the C-1 documents"

if git merge-base --is-ancestor origin/main HEAD 2>/dev/null; then
  ok "branch contains origin/main (no base drift)"
else
  bad "origin/main is not an ancestor — run: git merge origin/main"
fi

TOTAL_ADDED=$(git diff --numstat "$BASE"...HEAD -- '*.lean' | awk '{s+=$1} END{print s+0}')
if [ "$TOTAL_ADDED" -le "$BUDGET_LINES" ]; then
  ok "added Lean lines: $TOTAL_ADDED (budget $BUDGET_LINES)"
else
  bad "added Lean lines: $TOTAL_ADDED exceeds the C-1 budget of $BUDGET_LINES — split at a boundary where both halves compile, or say so in the PR body"
fi

# ------------------------------------------------------------------- invariants
head_ "Repository invariants (CONTRIBUTING.md)"

if rg -n '\b(sorry|admit|native_decide)\b|^axiom ' StatsMLlib/ >/dev/null 2>&1; then
  bad "sorry / admit / axiom / native_decide present"
  rg -n '\b(sorry|admit|native_decide)\b|^axiom ' StatsMLlib/ | sed 's/^/        /'
else
  ok "no sorry / admit / axiom / native_decide in StatsMLlib/"
fi

# Import tier from ARCHITECTURE.md: {Order, MeasureTheory, Topology,
# LinearAlgebra} -> Analysis -> Probability -> LearningTheory -> Statistics.
# A module must not import from a later tier.
head_ "Import direction (§10-7, ARCHITECTURE.md)"
tier() {
  case "$1" in
    Order|MeasureTheory|Topology|LinearAlgebra) echo 0 ;;
    Analysis)      echo 1 ;;
    Probability)   echo 2 ;;
    LearningTheory) echo 3 ;;
    Statistics)    echo 4 ;;
    *) echo -1 ;;
  esac
}
tier_bad=0
for f in $CHANGED; do
  [ -f "$f" ] || continue
  own=$(echo "$f" | sed -n 's|^StatsMLlib/\([^/]*\)/.*|\1|p')
  [ -z "$own" ] && continue
  ot=$(tier "$own"); [ "$ot" -lt 0 ] && continue
  while read -r dep; do
    dt=$(tier "$dep"); [ "$dt" -lt 0 ] && continue
    if [ "$dt" -gt "$ot" ]; then
      bad "$f ($own, tier $ot) imports StatsMLlib.$dep (tier $dt)"
      tier_bad=1
    fi
  done < <(grep -h '^import StatsMLlib\.' "$f" | sed -n 's|^import StatsMLlib\.\([^.]*\)\..*|\1|p')
done
[ "$tier_bad" -eq 0 ] && ok "no module imports from a later tier"

# ------------------------------------------------------------------------ build
head_ "Build"
if lake build >/tmp/gate-build.$$ 2>&1; then
  ok "lake build is green"
else
  bad "lake build failed"
  tail -30 /tmp/gate-build.$$ | sed 's/^/        /'
fi

# lake build only re-emits warnings for files it rebuilt, so re-elaborate each
# changed file: its output must be completely empty.
head_ "Warnings (CONTRIBUTING.md requires a clean build)"
warn_bad=0
for f in $CHANGED; do
  [ -f "$f" ] || continue
  out=$(lake env lean "$f" 2>&1)
  if [ -n "$out" ]; then
    bad "$f is not clean"
    echo "$out" | head -10 | sed 's/^/        /'
    warn_bad=1
  fi
done
[ "$warn_bad" -eq 0 ] && ok "every changed file elaborates with no output"

# --------------------------------------------------- standalone import (§10-4)
head_ "Standalone import (§10-4)"
NEWFILES=$(git diff --name-only --diff-filter=A "$BASE"...HEAD -- 'StatsMLlib/*.lean')
if [ -z "$NEWFILES" ]; then
  note "no new modules in this PR"
else
  for f in $NEWFILES; do
    mod=$(echo "$f" | sed 's|/|.|g; s|\.lean$||')
    probe="${TMPDIR:-/tmp}/gate-import-$$.lean"
    echo "import $mod" > "$probe"
    if out=$(lake env lean "$probe" 2>&1) && [ -z "$out" ]; then
      ok "import $mod works standalone"
    else
      bad "import $mod fails standalone"
      echo "$out" | head -5 | sed 's/^/        /'
    fi
  done
fi

# --------------------------------------------------------------- human gates
head_ "Human checks — NOT scripted (§10-5, §10-6)"
cat <<'EOF'
        These cannot be automated. Record a reviewer line in
        .claude/port/ledger.md before opening the PR.

        §10-5  linear predictors: does the complexity constant in the threshold
               match the existing empirical bound? does the McDiarmid exponent
               use the uniform function-value bound (X * W or Xinf * W, not C)?
               are 0 < n and the positive-radius hypotheses stated?
        §10-6  Dudley: going from the one-sided version to the absolute-value
               version, is the inequality direction still correct?

        Declaration names (§0.2-2): run
          bash .claude/port/decls.sh compare <local files> <upstream files>
        and confirm the "upstream-only" bucket contains nothing you meant to port.
EOF

head_ "Result"
if [ "$fail" -eq 0 ]; then
  printf '  \033[32mall mechanical checks passed\033[0m'
  [ -n "$PR" ] && printf ' (PR %s)' "$PR"
  echo
  exit 0
else
  printf '  \033[31mgate failed\033[0m — fix the FAIL lines above\n'
  exit 1
fi
