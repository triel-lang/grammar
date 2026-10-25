#!/usr/bin/env bash
# Make the copy of formal/core that is submitted to the Archive of Formal Proofs.
#
# Usage:
#   tools/make_afp_copy.sh [OUTPUT_DIR]
#
# The copy is written to OUTPUT_DIR/TRIEL_Core (default OUTPUT_DIR: afp in the
# system temporary directory). OUTPUT_DIR must be outside the repository: the
# theories are kept once, in formal/core, and the copy is made from them.
#
# The copy holds the files of formal/core in the commit HEAD (or $REF):
#
#   ROOT              chapter AFP, session TRIEL_Core with a timeout, the
#                     theories of formal/core/ROOT in the same order, and the
#                     document root.tex; no export_files, no document options
#                     (the AFP sets them for all entries)
#   *.thy             the theories of formal/core; in TRIEL_Exec.thy the
#                     subsection "Export" with export_code is left out
#   document/root.tex formal/core/document/root.tex, without the sentence on the
#                     export to Haskell and with the address of the repository
#
# CORE.md, build.log and output/ are not copied. The script fails if the copy
# contains sorry, oops, axiomatization, sledgehammer or smt_oracle, if it switches
# proof checking off (quick_and_dirty, skip_proofs), or if any command exports
# code or files.
#
# Build the copy as the AFP does:
#   isabelle build -v -o browser_info -o document=pdf \
#     -o "document_variants=document:outline=/proof,/ML" -D OUTPUT_DIR/TRIEL_Core

set -euo pipefail

[ $# -le 1 ] || { echo "usage: $0 [OUTPUT_DIR]" >&2; exit 2; }

REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
OUT=$(realpath -m "${1:-${TMPDIR:-/tmp}/afp}")
REF=${REF:-HEAD}
ENTRY="$OUT/TRIEL_Core"
URL=https://github.com/triel-lang/grammar

case "$OUT/" in
  "$REPO"/*) echo "error: the output directory must be outside the repository" >&2; exit 2 ;;
esac
if [ -e "$ENTRY" ]; then
  echo "error: $ENTRY exists; remove it or choose another output directory" >&2
  exit 2
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
git -C "$REPO" archive --format=tar "$REF" formal/core | tar -C "$TMP" -xf -
SRC="$TMP/formal/core"
# Line ends as in the repository, whatever the checkout does.
find "$SRC" -type f \( -name '*.thy' -o -name ROOT -o -name '*.tex' \) -exec perl -pi -e 's/\r$//' {} +

# The theories of the session, in the order of formal/core/ROOT.
mapfile -t THEORIES < <(awk '
  /^[[:space:]]*theories[[:space:]]*$/ { on = 1; next }
  /^[[:space:]]*(document_files|export_files|sessions|options)([[:space:](]|$)/ { on = 0 }
  on && NF { print $1 }' "$SRC/ROOT")
[ ${#THEORIES[@]} -gt 0 ] || { echo "error: no theories found in formal/core/ROOT" >&2; exit 1; }

mkdir -p "$ENTRY/document"

for t in "${THEORIES[@]}"; do
  [ -f "$SRC/$t.thy" ] || { echo "error: formal/core/$t.thy is in ROOT but not in $REF" >&2; exit 1; }
  cp "$SRC/$t.thy" "$ENTRY/$t.thy"
done
for f in "$SRC"/*.thy; do
  t=$(basename "$f" .thy)
  [ -f "$ENTRY/$t.thy" ] || { echo "error: formal/core/$t.thy is in no session" >&2; exit 1; }
done

# TRIEL_Exec: no export of the evaluator. The subsection "Export" runs from its
# heading to the "end" of the theory.
perl -0pi -e '
  s/\n\nsubsection \\<open>Export\\<close>\n.*?(?=\nend\s*\z)/\n/s or die "no subsection Export in TRIEL_Exec.thy\n";
  s/ and its export to Haskell\././ or die "no header sentence on the export in TRIEL_Exec.thy\n";
' "$ENTRY/TRIEL_Exec.thy"

# root.tex: the same document, without the export, with the repository address.
cp "$SRC/document/root.tex" "$ENTRY/document/root.tex"
U=$URL perl -0pi -e '
  s/ and is exported to\s+Haskell\././ or die "no sentence on the export in root.tex\n";
  s/(\\texttt\{FOUNDATIONS\.md\}\))/$1 at \\url{$ENV{U}}/ or die "no reference to FOUNDATIONS.md in root.tex\n";
' "$ENTRY/document/root.tex"

{
  echo "chapter AFP"
  echo
  echo "session TRIEL_Core = HOL +"
  echo "  options [timeout = 600]"
  echo "  sessions"
  echo "    \"HOL-Library\""
  echo "  theories"
  printf '    %s\n' "${THEORIES[@]}"
  echo "  document_files"
  echo "    \"root.tex\""
} > "$ENTRY/ROOT"

# Checks.
fail=0
check() {  # check MESSAGE GREP-OPTIONS PATTERN
  local hits
  if hits=$(cd "$ENTRY" && grep -nE $2 -e "$3" -- ROOT *.thy); then
    printf 'error: %s:\n%s\n' "$1" "$hits" >&2
    fail=1
  else
    echo "ok: no $1"
  fi
}
check "sorry, oops or axiomatization" -w 'sorry|oops|axiomatization'
check "sledgehammer or smt_oracle" -w 'sledgehammer|smt_oracle'
check "quick_and_dirty or skip_proofs" -s 'quick_and_dirty|skip_proofs'
check "export of code or files" -s \
  'export_code|export_files|export_generated_files|code_reflect'
[ $fail -eq 0 ] || { echo "the copy in $ENTRY does not meet the AFP rules" >&2; exit 1; }

echo "AFP copy of formal/core ($REF, $(git -C "$REPO" rev-parse --short "$REF")): $ENTRY"
echo "  ${#THEORIES[@]} theories, document/root.tex, ROOT (chapter AFP, session TRIEL_Core)"
