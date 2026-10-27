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
# triel.ai. The account of the maintainer (Dichis) and the surname of the author
# are always replaced by ANONYMOUS, also when no file states the name. The name
# of the language, TRIEL, is kept.
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
# The names of other people listed in KEEP below contain one of these words and
# are kept as they are: "Dmitriy Traytel", an author of the AFP entry
# MFOTL_Monitor cited in formal/core/document/root.bib, would otherwise become
# "ANONYMOUSy Traytel", which gives away the first name of the author. Each
# name of KEEP is matched exactly, with its case; it is put aside before the
# words are replaced and put back afterwards, and the checks at the end ignore
# these names, and only these.
#
# Two kinds of text that point to the history of the project are rewritten too:
# commit hashes and the stages of the development. The hashes are those of the
# tag v2.5.1 (1b775ff), of the tag v2.5 (57c5410, which LICENSE.md of v2.5.1
# still cites: "(commit `57c5410`)" is removed) and of the commit archived;
# each is replaced by ANONYMIZED. The stages: "the independent review of
# stage 13" becomes "an independent review", "in stage 9" and "until stage 15"
# become "in an earlier revision" and "until an earlier revision". The archive
# is checked for both, as for the words, and in addition no hexadecimal string
# in it may be the hash of a commit of the repository, and no e-mail address
# may be left.
#
# A word replaced inside a longer word leaves a replacement joined to letters,
# as "ANONYMOUSy" above: the archive may contain neither ANONYMOUS or ANONYMIZED
# followed by a letter nor a letter followed by ANONYM, matched with their case;
# a letter is one of any alphabet (the Unicode property L), so "ANONYMOUSа" with
# a Cyrillic а is found too. Nor may a name of KEEP be joined directly to
# ANONYMOUS or ANONYMIZED. The script fails on any of these, so a name of
# someone else damaged by a replacement is found, and can be added to KEEP.
#
# The archive holds the files of the commit HEAD (or of $REF), without .git,
# CLA.md, the signatures directory, .github/workflows/cla.yml, this script and
# check_anonymous.sh (both name the words searched for). It is reproducible:
# the same commit gives the same bytes, whoever writes it, with GNU tar and GNU
# gzip (the options below are those of GNU tar). The tar
# file lists the files sorted by name, with the time 2000-01-01 00:00:00 UTC,
# owner and group 0 without names, and the modes 644 and 755 (directories and
# executable files); gzip stores no file name and no time. The script fails, and
# writes no archive, if any of these words is still found in a file or a file
# name, in text or binary files.

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
  "Dichis => ANONYMOUS"
  "Chistyakov => ANONYMOUS"
)

# Names of other people kept as they are (see above).
KEEP=(
  "Dmitriy Traytel"
)

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
TREE="$TMP/triel"
mkdir "$TREE"

# Line ends as committed, whatever core.autocrlf or core.eol of the local configuration say.
git -C "$REPO" -c core.autocrlf=false -c core.eol=lf archive --format=tar "$REF" | tar -C "$TREE" -xf -
rm -rf "$TREE/CLA.md" "$TREE/signatures" "$TREE/.github/workflows/cla.yml" "$TREE/artifact/anonymize.sh" \
       "$TREE/artifact/check_anonymous.sh"

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
# The names of KEEP are first put aside as placeholders of control characters,
# which no word contains and no file of the repository may contain.
if hits=$(cd "$TREE" && grep -rlI -e $'\001' .); then
  printf 'error: a control character used as a placeholder is in:\n%s\n' "$hits" >&2
  exit 1
fi
while IFS= read -r -d '' f; do
  for i in "${!KEEP[@]}"; do
    K=${KEEP[$i]} P=$'\001'"$i"$'\001' perl -pi -e 's/\Q$ENV{K}\E/$ENV{P}/g' "$f"
  done
  for entry in "${ENTRIES[@]}"; do
    W=${entry%%$'\t'*} R=${entry#*$'\t'} perl -pi -e 's/\Q$ENV{W}\E/$ENV{R}/gi' "$f"
  done
done < <(grep -rlIZ -e '' "$TREE")

# The commit hashes of the tags v2.5.1 and v2.5 and of the commit archived, and
# the stages of the development.
HISTORY_HASHES=$(printf '%s\n' 1b775ff 57c5410 "$(git -C "$REPO" rev-parse "$REF^{commit}" | cut -c1-7)" | sort -u | paste -sd '|')
while IFS= read -r -d '' f; do
  H=$HISTORY_HASHES perl -pi -e '
    s/ \(commit `(?:$ENV{H})[0-9a-f]*`\)//g;
    s/\b(?:$ENV{H})[0-9a-f]*\b/ANONYMIZED/g;
    s/\bthe (?:independent )?review of stage \d+/an independent review/gi;
    s/\b(in|until|since|after|before) stage \d+/$1 an earlier revision/gi;
    s/\bstages? \d+/an earlier revision/gi;' "$f"
done < <(grep -rlIZ -e '' "$TREE")

# The names of KEEP are put back.
while IFS= read -r -d '' f; do
  for i in "${!KEEP[@]}"; do
    K=${KEEP[$i]} P=$'\001'"$i"$'\001' perl -pi -e 's/\Q$ENV{P}\E/$ENV{K}/g' "$f"
  done
done < <(grep -rlIZ -e '' "$TREE")

# The checks below read a copy in which each name of KEEP is replaced by a line
# break, so that it is neither found nor joins the text around it into a word.
CHECK="$TMP/check"
cp -a "$TREE" "$CHECK"
for k in "${KEEP[@]}"; do
  while IFS= read -r -d '' f; do
    K=$k perl -pi -e 's/\Q$ENV{K}\E/\n/g' "$f"
  done < <(grep -rlZF -e "$k" "$CHECK" || true)
done

# Nothing may be left: contents of every file (binary files included) and paths.
left=0
if hits=$(cd "$CHECK" && grep -raliE -e "$HISTORY_HASHES|stage ?[0-9]" .); then
  printf 'error: a commit hash or a stage of the development is still in:\n%s\n' "$hits" >&2
  left=1
fi
# No hexadecimal string of 7 to 40 digits may name a commit of the repository.
commits=$(cd "$CHECK" && grep -rhoIE '\b[0-9a-f]{7,40}\b' . | sort -u | while read -r h; do
  git -C "$REPO" cat-file -e "$h^{commit}" 2>/dev/null && echo "$h"
done || true)
if [ -n "$commits" ]; then
  printf 'error: the hash of a commit of the repository is still in the archive:\n%s\n' "$commits" >&2
  left=1
fi
if hits=$(cd "$CHECK" && grep -raoE '[A-Za-z0-9._%+-]+@[A-Za-z0-9-]+(\.[A-Za-z0-9-]+)*\.[A-Za-z]{2,}' .); then
  printf 'error: an e-mail address is still in:\n%s\n' "$hits" >&2
  left=1
fi
# A replacement joined to letters: a word was replaced inside a longer word.
# The files are read as UTF-8 (invalid sequences, as in a binary file, are
# skipped), so that a letter of any alphabet counts.
if hits=$(cd "$CHECK" && LC_ALL=C.UTF-8 grep -raoP '\p{L}*(ANONYM(OUS|IZED)\p{L}|\p{L}ANONYM)\p{L}*' .); then
  printf 'error: a replacement joined to letters (a word replaced inside a longer word) is in:\n%s\n' "$hits" >&2
  left=1
fi
# The copy read above has a line break in place of each name of KEEP, so a
# replacement joined directly to such a name is looked for in the archive itself.
for k in "${KEEP[@]}"; do
  if hits=$(cd "$TREE" && grep -raoF -e "${k}ANONYM" -e "ANONYMOUS${k}" -e "ANONYMIZED${k}" .); then
    printf 'error: a replacement joined to the name %s is in:\n%s\n' "$k" "$hits" >&2
    left=1
  fi
done
hits=$(cd "$CHECK" && find . | LC_ALL=C grep -E 'ANONYM(OUS|IZED)[A-Za-z]|[A-Za-z]ANONYM' || true)
if [ -n "$hits" ]; then
  printf 'error: a replacement joined to letters is in the file names:\n%s\n' "$hits" >&2
  left=1
fi
for entry in "${ENTRIES[@]}"; do
  w=${entry%%$'\t'*}
  if hits=$(cd "$CHECK" && grep -raliF -e "$w" .); then
    printf 'error: a forbidden word is still in:\n%s\n' "$hits" >&2
    left=1
  fi
  hits=$(cd "$CHECK" && find . -iname "*$w*")
  if [ -n "$hits" ]; then
    printf 'error: a forbidden word is in the file names:\n%s\n' "$hits" >&2
    left=1
  fi
done
if [ $left -ne 0 ]; then
  echo "no archive written" >&2
  exit 1
fi

# The modes of the extracted files depend on the umask and on whether tar runs
# as root, so they are set here.
LC_ALL=C tar -C "$TMP" --format=gnu --sort=name --mtime='2000-01-01 00:00:00Z' \
    --owner=0 --group=0 --numeric-owner --mode='u=rwX,go=rX' \
    -cf - triel | gzip -n > "$OUT"
echo "anonymous archive: $OUT ($(tar -tzf "$OUT" | grep -vc '/$') files, ${#ENTRIES[@]} words checked:" \
     "${#AUTHOR_WORDS[@]} from the name of the author, ${#LISTED[@]} from $([ -n "$WORDS" ] && basename "$WORDS" || echo "a words file (none given)")," \
     "${#BUILTIN[@]} built in; ${#KEEP[@]} names of other people kept)"
echo "sha256 $(sha256sum "$OUT" | cut -d' ' -f1)"
