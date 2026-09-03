#!/bin/bash
# decls.sh — declaration extractor for the lean-rademacher port.
#
# Two uses, one implementation (see the plan, "上流そのまま vs 4.33 で書き直し"):
#   1. generate the PR-body section C-1 requires (verbatim / rewritten / new)
#   2. detect declaration-name drift, which §0.2-2 forbids
#
# Upstream is read-only text at a fixed pin; never built, never checked out.
#
# Usage:
#   decls.sh names   <file.lean>              names in a local file
#   decls.sh unames  <FoML/Path.lean>         names in an upstream file at the pin
#   decls.sh blocks  <file.lean>              name<TAB>sha256 of each declaration block
#   decls.sh ublocks <FoML/Path.lean>         same, upstream
#   decls.sh compare <file.lean> <FoML/Path.lean> [<FoML/Path2.lean> ...]
#                                             bucket local declarations against upstream
set -uo pipefail

UPSTREAM_REPO="${UPSTREAM_REPO:-/Users/milano/lean-rademacher}"
UPSTREAM_PIN="${UPSTREAM_PIN:-bc33376}"

die() { echo "decls.sh: $*" >&2; exit 2; }

# Print an upstream file at the pin. Never reads the upstream working tree:
# its checked-out branch is NOT the port target.
ucat() {
  git -C "$UPSTREAM_REPO" show "$UPSTREAM_PIN:$1" 2>/dev/null \
    || die "no such upstream file at $UPSTREAM_PIN: $1"
}

# Split a Lean file into declaration blocks.
# A block starts at a column-0 declaration keyword and runs to just before the
# next one. Leading docstrings and attributes are attached to the block that
# follows them, so a docstring-only change shows up as a changed declaration.
# Emits: <name>\t<sha256 of the normalized block>
blocks_awk='
function flush() {
  if (name != "") print name "\t" body_hash(body)
}
function body_hash(b,   c, h) {
  c = "printf %s " quote(b) " | shasum -a 256 | cut -c1-16"
  c | getline h
  close(c)
  return h
}
function quote(s) {
  gsub(/'"'"'/, "'"'"'\\'"'"''"'"'", s)
  return "'"'"'" s "'"'"'"
}
BEGIN { name=""; body=""; pending="" }
{
  line = $0
  sub(/[ \t]+$/, "", line)
}
# attribute or docstring start at column 0: hold until we see the declaration
/^@\[/ || /^\/--/ { pending = pending line "\n"; next }
/^(private |protected |noncomputable |partial |unsafe |scoped )*(theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|example) / {
  flush()
  n = line
  sub(/^(private |protected |noncomputable |partial |unsafe |scoped )*/, "", n)
  sub(/^(theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|example)[ \t]+/, "", n)
  sub(/[ \t{(\[:].*$/, "", n)
  # Anonymous instances cannot be matched by name; number them so two of them
  # never collide and get reported as both verbatim and rewritten.
  if (n == "") { anon++; n = "<anonymous#" anon ">" }
  name = n
  body = pending line "\n"
  pending = ""
  next
}
{
  if (name != "") { body = body pending line "\n"; pending = "" }
  else { pending = "" }
}
END { flush() }
'

names_of() { awk "$blocks_awk" | cut -f1; }

case "${1:-}" in
  names)   [ $# -eq 2 ] || die "usage: decls.sh names <file.lean>"
           awk "$blocks_awk" "$2" | cut -f1 ;;
  unames)  [ $# -eq 2 ] || die "usage: decls.sh unames <FoML/Path.lean>"
           ucat "$2" | awk "$blocks_awk" | cut -f1 ;;
  blocks)  [ $# -eq 2 ] || die "usage: decls.sh blocks <file.lean>"
           awk "$blocks_awk" "$2" ;;
  ublocks) [ $# -eq 2 ] || die "usage: decls.sh ublocks <FoML/Path.lean>"
           ucat "$2" | awk "$blocks_awk" ;;
  compare)
    # §0.3 is not a bijection: one upstream file may map to two StatsMLlib
    # modules and vice versa, so both sides take a comma-separated list.
    [ $# -eq 3 ] || die "usage: decls.sh compare <local1.lean[,local2.lean]> <FoML/A.lean[,FoML/B.lean]>"
    tmp="${TMPDIR:-/tmp}/decls.$$"
    mkdir -p "$tmp"
    : > "$tmp/local"; : > "$tmp/up"
    IFS=',' read -ra LOCALS <<< "$2"
    IFS=',' read -ra UPS <<< "$3"
    for f in "${LOCALS[@]}"; do
      [ -f "$f" ] || die "no such local file: $f"
      awk "$blocks_awk" "$f" >> "$tmp/local"
    done
    for u in "${UPS[@]}"; do ucat "$u" | awk "$blocks_awk" >> "$tmp/up"; done

    echo "### Provenance against upstream $UPSTREAM_PIN"
    echo
    echo "Local:    $(for f in "${LOCALS[@]}"; do printf '`%s` ' "$f"; done)"
    echo "Upstream: $(for u in "${UPS[@]}"; do printf '`%s` ' "$u"; done)"
    echo
    same=0; changed=0; new=0
    echo "**Copied verbatim from upstream**"
    echo
    while IFS=$'\t' read -r n h; do
      uh=$(awk -F'\t' -v k="$n" '$1==k{print $2; exit}' "$tmp/up")
      if [ -n "$uh" ] && [ "$uh" = "$h" ]; then echo "- \`$n\`"; same=$((same+1)); fi
    done < "$tmp/local"
    [ "$same" -eq 0 ] && echo "- (none)"
    echo
    echo "**Rewritten for the Lean 4.27 → 4.33 diff**"
    echo
    while IFS=$'\t' read -r n h; do
      uh=$(awk -F'\t' -v k="$n" '$1==k{print $2; exit}' "$tmp/up")
      if [ -n "$uh" ] && [ "$uh" != "$h" ]; then echo "- \`$n\`"; changed=$((changed+1)); fi
    done < "$tmp/local"
    [ "$changed" -eq 0 ] && echo "- (none)"
    echo
    echo "**New in StatsMLlib (no upstream original)**"
    echo
    while IFS=$'\t' read -r n h; do
      uh=$(awk -F'\t' -v k="$n" '$1==k{print $2; exit}' "$tmp/up")
      if [ -z "$uh" ]; then echo "- \`$n\`"; new=$((new+1)); fi
    done < "$tmp/local"
    [ "$new" -eq 0 ] && echo "- (none)"
    echo
    echo "**Upstream declarations not present locally**"
    echo
    missing=0
    while IFS=$'\t' read -r n h; do
      lh=$(awk -F'\t' -v k="$n" '$1==k{print $2; exit}' "$tmp/local")
      if [ -z "$lh" ]; then echo "- \`$n\`"; missing=$((missing+1)); fi
    done < "$tmp/up"
    [ "$missing" -eq 0 ] && echo "- (none)"
    echo
    echo "verbatim=$same rewritten=$changed new=$new upstream-only=$missing"
    ;;
  *) die "usage: decls.sh {names|unames|blocks|ublocks|compare} ..." ;;
esac
