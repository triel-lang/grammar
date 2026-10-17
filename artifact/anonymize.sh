#!/usr/bin/env bash
# Make an anonymous source archive of the repository for double-blind review.
#
# Usage:
#   artifact/anonymize.sh WORDS_FILE [OUTPUT.tar.gz]
#
# WORDS_FILE lists the words that may not appear in the archive, one per line:
#
#   word                  replaced by ANONYMOUS
#   word => replacement   replaced by the given text
#
# Blank lines and lines starting with # are ignored. Matching is case-insensitive
# and longer words are replaced first. WORDS_FILE must be outside the repository,
# so that it is never committed.
#
# The archive holds the files of the commit HEAD (or of $REF), without .git,
# CLA.md, the signatures directory and .github/workflows/cla.yml. Tar owner names
# and timestamps are fixed, so they reveal nothing. The script fails, and writes
# no archive, if any listed word is still found in a file or a file name, in
# text or binary files.

set -euo pipefail

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
  echo "usage: $0 WORDS_FILE [OUTPUT.tar.gz]" >&2
  exit 2
fi

REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
WORDS=$(realpath "$1")
OUT=$(realpath -m "${2:-triel-artifact-anonymous.tar.gz}")
REF=${REF:-HEAD}

[ -f "$WORDS" ] || { echo "error: $WORDS is not a file" >&2; exit 2; }
case "$WORDS/" in
  "$REPO"/*) echo "error: the words file must be outside the repository" >&2; exit 2 ;;
esac

# The words and their replacements, longest word first.
mapfile -t ENTRIES < <(
  sed -e 's/\r$//' -e '/^[[:space:]]*\(#\|$\)/d' "$WORDS" | awk '
    { i = index($0, "=>")
      if (i) { w = substr($0, 1, i - 1); r = substr($0, i + 2) } else { w = $0; r = "ANONYMOUS" }
      gsub(/^[ \t]+|[ \t]+$/, "", w); gsub(/^[ \t]+|[ \t]+$/, "", r)
      if (w != "") print length(w) "\t" w "\t" r }' | sort -t "$(printf '\t')" -k1,1nr | cut -f2-)
[ ${#ENTRIES[@]} -gt 0 ] || { echo "error: $WORDS lists no words" >&2; exit 2; }

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
TREE="$TMP/triel"
mkdir "$TREE"

git -C "$REPO" archive --format=tar "$REF" | tar -C "$TREE" -xf -
rm -rf "$TREE/CLA.md" "$TREE/signatures" "$TREE/.github/workflows/cla.yml"

# Replace in every text file. The words and replacements are passed through the
# environment, so no character in them is interpreted by the shell or by Perl.
while IFS= read -r -d '' f; do
  for entry in "${ENTRIES[@]}"; do
    W=${entry%%$'\t'*} R=${entry#*$'\t'} perl -pi -e 's/\Q$ENV{W}\E/$ENV{R}/gi' "$f"
  done
done < <(grep -rlIZ -e '' "$TREE")

# Nothing may be left: contents of every file (binary files included) and paths.
left=0
for entry in "${ENTRIES[@]}"; do
  w=${entry%%$'\t'*}
  if hits=$(cd "$TREE" && grep -raliF -e "$w" .); then
    printf 'error: a forbidden word is still in:\n%s\n' "$hits" >&2
    left=1
  fi
  hits=$(cd "$TREE" && find . -iname "*$w*")
  if [ -n "$hits" ]; then
    printf 'error: a forbidden word is in the file names:\n%s\n' "$hits" >&2
    left=1
  fi
done
if [ $left -ne 0 ]; then
  echo "no archive written" >&2
  exit 1
fi

tar -C "$TMP" --sort=name --mtime='2000-01-01 00:00:00Z' --owner=0 --group=0 --numeric-owner \
    -cf - triel | gzip -n > "$OUT"
echo "anonymous archive: $OUT ($(tar -tzf "$OUT" | grep -vc '/$') files, ${#ENTRIES[@]} words checked)"
