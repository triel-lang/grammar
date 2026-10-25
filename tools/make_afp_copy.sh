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
#                     theories of formal/core/ROOT in the same order, and its
#                     document files; no export_files, no document options
#                     (the AFP sets them for all entries)
#   *.thy             the theories of formal/core, unchanged; export_code in
#                     TRIEL_Exec.thy stays, so the AFP build checks the export of
#                     the evaluator, which writes no file
#   document/         the document files of formal/core/ROOT (root.bib and
#                     root.tex); root.tex gives the address of the repository
#
# CORE.md, build.log and output/ are not copied. The script fails if the copy
# contains sorry, oops, axiomatization, sledgehammer or smt_oracle, if it switches
# proof checking off (quick_and_dirty, skip_proofs), if it writes files
# (export_files, export_generated_files, code_reflect, or export_code with file
# or file_prefix), or if it has no export_code.
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
find "$SRC" -type f \( -name '*.thy' -o -name ROOT -o -name '*.tex' -o -name '*.bib' \) -exec perl -pi -e 's/\r$//' {} +

# The theories of the session, in the order of formal/core/ROOT.
mapfile -t THEORIES < <(awk '
  /^[[:space:]]*theories[[:space:]]*$/ { on = 1; next }
  /^[[:space:]]*(document_files|export_files|sessions|options)([[:space:](]|$)/ { on = 0 }
  on && NF { print $1 }' "$SRC/ROOT")
[ ${#THEORIES[@]} -gt 0 ] || { echo "error: no theories found in formal/core/ROOT" >&2; exit 1; }

# The document files, in the order of formal/core/ROOT.
mapfile -t DOCFILES < <(awk '
  /^[[:space:]]*document_files[[:space:]]*$/ { on = 1; next }
  /^[[:space:]]*(theories|export_files|sessions|options)([[:space:](]|$)/ { on = 0 }
  on && NF { gsub(/"/, "", $1); print $1 }' "$SRC/ROOT")
[ ${#DOCFILES[@]} -gt 0 ] || { echo "error: no document files found in formal/core/ROOT" >&2; exit 1; }

mkdir -p "$ENTRY/document"

for t in "${THEORIES[@]}"; do
  [ -f "$SRC/$t.thy" ] || { echo "error: formal/core/$t.thy is in ROOT but not in $REF" >&2; exit 1; }
  cp "$SRC/$t.thy" "$ENTRY/$t.thy"
done
for f in "$SRC"/*.thy; do
  t=$(basename "$f" .thy)
  [ -f "$ENTRY/$t.thy" ] || { echo "error: formal/core/$t.thy is in no session" >&2; exit 1; }
done

for f in "${DOCFILES[@]}"; do
  [ -f "$SRC/document/$f" ] || { echo "error: formal/core/document/$f is in ROOT but not in $REF" >&2; exit 1; }
  cp "$SRC/document/$f" "$ENTRY/document/$f"
done

# root.tex: the same document, with the address of the repository.
U=$URL perl -0pi -e '
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
  printf '    "%s"\n' "${DOCFILES[@]}"
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
check "export of files" -s 'export_files|export_generated_files|code_reflect'
# export_code may not write files: no file or file_prefix up to the end of the
# command (the next blank line).
n_export=$(cd "$ENTRY" && cat -- *.thy | grep -c '^export_code' || true)
hits=$(cd "$ENTRY" && awk '/^export_code/ { on = 1 } on && /^[[:space:]]*$/ { on = 0 }
  on && /(^|[[:space:]])file(_prefix)?([[:space:]]|$)/ { print FILENAME ":" FNR ": " $0 }' *.thy)
if [ "$n_export" -eq 0 ]; then
  echo "error: no export_code; the AFP build would not check the export" >&2
  fail=1
elif [ -n "$hits" ]; then
  printf 'error: export_code writes files:\n%s\n' "$hits" >&2
  fail=1
else
  echo "ok: $n_export export_code without file or file_prefix"
fi
[ $fail -eq 0 ] || { echo "the copy in $ENTRY does not meet the AFP rules" >&2; exit 1; }

echo "AFP copy of formal/core ($REF, $(git -C "$REPO" rev-parse --short "$REF")): $ENTRY"
echo "  ${#THEORIES[@]} theories, document: ${DOCFILES[*]}, ROOT (chapter AFP, session TRIEL_Core)"
