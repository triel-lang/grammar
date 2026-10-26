#!/usr/bin/env bash
# Search an anonymous archive written by anonymize.sh for everything that could
# name the author or the repository, independently of the script that wrote it.
#
# Usage:
#   artifact/check_anonymous.sh ARCHIVE.tar.gz
#
# Each pattern below is searched, case-insensitively, in the uncompressed tar
# stream (so in file names, in the tar headers and in the contents of every
# file, binary files included). One line is printed per pattern with the number
# of matches. The exit code is 0 if no pattern is found, 1 otherwise.
#
# The names of other people in ALLOWED are matched by a pattern but name someone
# else: "Dmitriy Traytel", an author of the AFP entry MFOTL_Monitor cited in
# formal/core/document/root.bib. Each is matched exactly, with its case; its
# occurrences are counted and printed, and replaced by a line break before the
# patterns are searched. The list is kept here independently of the list KEEP of
# anonymize.sh.
#
# This script names the words it looks for, so anonymize.sh leaves it out of
# the archive, as it leaves out itself.

set -euo pipefail

[ $# -eq 1 ] && [ -f "$1" ] || { echo "usage: $0 ARCHIVE.tar.gz" >&2; exit 2; }

PATTERNS=(
  '1b775ff'                         # commit of the tag v2.5.1
  '57c5410'                         # commit of the tag v2.5
  'Dmitri'
  'Dmitr'                           # also Dmitry, Dmitrii
  'Chistyakov'
  'Dichis'
  'github\.com/triel-lang'
  'triel-lang'
  'triel\.dev'
  'triel\.ai'
  'Дмитр'
  'Чистяков'
  '[A-Za-z0-9._%+-]+@[A-Za-z0-9-]+(\.[A-Za-z0-9-]+)*\.[A-Za-z]{2,}'   # e-mail address
)

ALLOWED=(
  'Dmitriy Traytel'                 # an author of the AFP entry MFOTL_Monitor
)

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
gzip -dc "$1" > "$TMP/archive.tar"

echo "archive: $1 ($(tar -tf "$TMP/archive.tar" | grep -vc '/$') files, sha256 $(sha256sum "$1" | cut -d' ' -f1))"
echo "owners in the tar headers: $(tar -tvf "$TMP/archive.tar" | awk '{print $2}' | sort -u | paste -sd ' ')"
for a in "${ALLOWED[@]}"; do
  n=$({ grep -aoF -e "$a" "$TMP/archive.tar" || true; } | wc -l)
  printf 'allowed, not counted below: %s, %s occurrences\n' "$a" "$n"
  A=$a perl -pi -e 's/\Q$ENV{A}\E/\n/g' "$TMP/archive.tar"
done
found=0
for p in "${PATTERNS[@]}"; do
  n=$({ grep -aoiE -e "$p" "$TMP/archive.tar" || true; } | wc -l)
  printf '%-70s %s\n' "$p" "$n"
  [ "$n" -eq 0 ] || { grep -aoiE -e "$p" "$TMP/archive.tar" | sort | uniq -c | head -5; found=1; }
done
n=$({ grep -aoE "\bTRIEL\b" "$TMP/archive.tar" || true; } | wc -l)
echo "the name of the language, TRIEL, kept: $n occurrences"
if [ $found -eq 0 ]; then
  echo "RESULT: none of the ${#PATTERNS[@]} patterns found"
else
  echo "RESULT: FOUND"
fi
[ $found -eq 0 ]
