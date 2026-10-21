#!/usr/bin/env bash
# Make an anonymous source archive of the repository for double-blind review.
#
# Usage:
#   artifact/anonymize.sh [-w WORDS_FILE] [OUTPUT.tar.gz]
#
# The name of the author is found in the archive itself, without a list of
# words: it is read from the places where the repository states it, which are
# the \author of formal/core/document/root.tex, the Copyright line of NOTICE,
# the Bound Entity and the copyright lines of LICENSE.md, the Author and (c)
# lines of the headers of both EBNF files, and the Contact section of README.md.
# The script fails if root.tex or NOTICE names no author, since then the
# structure is not what it expects. Each name found, and each of its words of
# three or more letters, is replaced by ANONYMOUS everywhere.
#
# The address of the repository and of the project's sites are always replaced
# by ANONYMIZED: github.com/triel-lang/grammar, triel-lang, triel.dev and
# triel.ai. The name of the language, TRIEL, is kept.
#
# WORDS_FILE (optional) lists further words that may not appear in the archive,
# one per line:
#
#   word                  replaced by ANONYMOUS
#   word => replacement   replaced by the given text
#
# Blank lines and lines starting with # are ignored. WORDS_FILE must be outside
# the repository, so that it is never committed.
#
# Matching is case-insensitive and longer words are replaced first.
#
# The archive holds the files of the commit HEAD (or of $REF), without .git,
# CLA.md, the signatures directory, .github/workflows/cla.yml and this script
# (which names the built-in words). Tar owner names
# and timestamps are fixed, so they reveal nothing. The script fails, and writes
# no archive, if any of these words is still found in a file or a file name, in
# text or binary files.

set -euo pipefail

usage() { echo "usage: $0 [-w WORDS_FILE] [OUTPUT.tar.gz]" >&2; exit 2; }
WORDS=
while getopts "w:" opt; do
  case $opt in
    w) WORDS=$(realpath "$OPTARG") ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
[ $# -le 1 ] || usage

REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
OUT=$(realpath -m "${1:-triel-artifact-anonymous.tar.gz}")
REF=${REF:-HEAD}

LISTED=()
if [ -n "$WORDS" ]; then
  [ -f "$WORDS" ] || { echo "error: $WORDS is not a file" >&2; exit 2; }
  case "$WORDS/" in
    "$REPO"/*) echo "error: the words file must be outside the repository" >&2; exit 2 ;;
  esac
  # The words of WORDS_FILE as "word => replacement" lines.
  mapfile -t LISTED < <(
    sed -e 's/\r$//' -e '/^[[:space:]]*\(#\|$\)/d' "$WORDS" | awk '
      { i = index($0, "=>")
        if (i) { w = substr($0, 1, i - 1); r = substr($0, i + 2) } else { w = $0; r = "ANONYMOUS" }
        gsub(/^[ \t]+|[ \t]+$/, "", w); gsub(/^[ \t]+|[ \t]+$/, "", r)
        if (w != "") print w " => " r }')
  [ ${#LISTED[@]} -gt 0 ] || { echo "error: $WORDS lists no words" >&2; exit 2; }
fi

# The repository and the sites of the project, replaced in every archive.
BUILTIN=(
  "github.com/triel-lang/grammar => ANONYMIZED"
  "triel-lang => ANONYMIZED"
  "triel.dev => ANONYMIZED"
  "triel.ai => ANONYMIZED"
)

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
TREE="$TMP/triel"
mkdir "$TREE"

git -C "$REPO" archive --format=tar "$REF" | tar -C "$TREE" -xf -
rm -rf "$TREE/CLA.md" "$TREE/signatures" "$TREE/.github/workflows/cla.yml" "$TREE/artifact/anonymize.sh"

# The name of the author, from the places where the repository states it.
author_lines() {
  local f
  sed -n 's/^\\author{\(.*\)}[[:space:]]*$/\1/p' "$TREE/formal/core/document/root.tex" 2>/dev/null
  sed -n 's/^Copyright [0-9][0-9]* \(.*\)$/\1/p' "$TREE/NOTICE" 2>/dev/null
  sed -n -e 's/^Bound Entity: \(.*\)$/\1/p' -e 's/^Copyright [0-9][0-9]* \(.*\)$/\1/p' \
         -e 's/.*© [0-9][0-9]* \(.*\)$/\1/p' "$TREE/LICENSE.md" 2>/dev/null
  for f in "$TREE"/TRIEL-grammar-*.ebnf; do
    head -n 20 "$f" | sed -n -e 's/^[[:space:]]*Author: \(.*\)$/\1/p' -e 's/^[[:space:]]*© [0-9][0-9]* \(.*\)$/\1/p'
  done
  awk '/^## Contact/ { on = 1; next } /^#/ { on = 0 } on && NF' "$TREE/README.md" 2>/dev/null
}
mapfile -t AUTHORS < <(author_lines | sed -e 's/\r$//' -e 's/[[:space:]]*$//' -e 's/\.$//' \
                                   -e 's/^[[:space:]]*//' | awk 'NF' | sort -u)
if ! grep -q '^\\author{..*}' "$TREE/formal/core/document/root.tex" 2>/dev/null \
   || ! grep -q '^Copyright [0-9][0-9]* ..*' "$TREE/NOTICE" 2>/dev/null; then
  echo "error: formal/core/document/root.tex or NOTICE names no author; the files are not as expected" >&2
  exit 1
fi
# Each name, and each of its words of three or more letters.
mapfile -t AUTHOR_WORDS < <(
  for a in "${AUTHORS[@]}"; do
    echo "$a"
    printf '%s\n' $a | sed 's/[^[:alpha:]-]//g' | awk 'length($0) >= 3'
  done | sort -u | sed 's/$/ => ANONYMOUS/')

# All words as "word<TAB>replacement", longest word first.
mapfile -t ENTRIES < <(
  printf '%s\n' "${LISTED[@]}" "${AUTHOR_WORDS[@]}" "${BUILTIN[@]}" | awk 'NF' | awk '
    { i = index($0, " => "); w = substr($0, 1, i - 1); r = substr($0, i + 4)
      print length(w) "\t" w "\t" r }' | sort -t "$(printf '\t')" -k1,1nr -k2,2 -u | cut -f2-)

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
echo "anonymous archive: $OUT ($(tar -tzf "$OUT" | grep -vc '/$') files, ${#ENTRIES[@]} words checked:" \
     "${#AUTHOR_WORDS[@]} from the name of the author, ${#LISTED[@]} from ${WORDS:+$(basename "$WORDS")}${WORDS:-a words file (none given)}," \
     "${#BUILTIN[@]} built in)"
