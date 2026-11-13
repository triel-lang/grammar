#!/usr/bin/env bash
# Reproduce every check of the CI workflows isabelle.yml, evaluator.yml and
# parse-examples.yml with one command, except the test of the documentation for
# AI agents (parser/test_skill.py) and the tests of the trace of a host
# (parser/test_host.py), then build the session of the theorems
# cited in the paper (and further ones) and print a summary. All numbers in the summary are
# computed by this run.
#
# Usage:
#   artifact/run.sh            (in the artifact image: docker run --rm triel-artifact)
#
# Needs on PATH: isabelle (Isabelle2025-2), ghc (9.6.7), python3 (3.12) with
# lark 1.3.1 and pytest. The repository is copied to a scratch directory and
# every step runs on the copy, so the checkout is never modified.
#
# Environment:
#   RESULTS_DIR  directory for the logs (default: a new directory under /tmp)
#   KEEP_WORK=1  keep the scratch copy
#
# Exit code: 0 if every step passed, 1 otherwise.

set -u

SRC=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
SCRATCH=$(mktemp -d "${TMPDIR:-/tmp}/triel-artifact.XXXXXX")
WORK="$SCRATCH/triel"
RESULTS_DIR=${RESULTS_DIR:-$SCRATCH/results}
mkdir -p "$WORK" "$RESULTS_DIR"
[ "${KEEP_WORK:-0}" = 1 ] || trap 'rm -rf "$WORK"' EXIT

failures=()
declare -A seconds

step() {
  # step NAME COMMAND...: run the command in $WORK, log its output, record the result
  local name=$1 log="$RESULTS_DIR/$1.log" start status
  shift
  echo
  echo "=== $name"
  start=$(date +%s)
  (cd "$WORK" && "$@") 2>&1 | tee "$log"
  status=${PIPESTATUS[0]}
  seconds[$name]=$(( $(date +%s) - start ))
  if [ $status -eq 0 ]; then
    echo "--- $name: PASS (${seconds[$name]} s)"
  else
    echo "--- $name: FAIL (exit $status, ${seconds[$name]} s)"
    failures+=("$name")
  fi
  return $status
}

# --- The steps -------------------------------------------------------------

# isabelle.yml: no unproved or assumed results, and no session option that
# switches proof checking off. The paper session is held to the same rule.
no_sorry() {
  local bad=0
  if grep -nwE 'sorry|oops|axiomatization' formal/core/*.thy artifact/isabelle/*.thy; then
    echo "error: sorry, oops or axiomatization found"
    bad=1
  fi
  if grep -nE 'quick_and_dirty|skip_proofs' formal/core/ROOT artifact/isabelle/ROOT; then
    echo "error: a ROOT switches proof checking off"
    bad=1
  fi
  [ $bad -eq 0 ] && echo "no sorry, oops or axiomatization in formal/core/*.thy and artifact/isabelle/*.thy"
  return $bad
}

# isabelle.yml and evaluator.yml: the PDF document needs LaTeX, which is not in
# the image, so it is switched off in the scratch copy of ROOT only (the same
# sed as CI); then a clean build of TRIEL_Core that also exports the evaluator
# and keeps the heap image (-b) for the session of the paper theorems.
isabelle_build() {
  sed -i -E 's/options \[document = pdf, document_output = "output"\]/options [document = false]/' formal/core/ROOT
  grep -q 'options \[document = false\]' formal/core/ROOT || { echo "error: ROOT not as expected"; return 1; }
  isabelle build -b -c -e -v -D formal/core
}

# evaluator.yml: the committed Haskell code is exactly what Isabelle exported.
# CI uses git diff; the scratch copy has no .git, so the export is compared
# with the files of the checkout.
exported_code() {
  diff -r -u "$SRC/evaluator/generated" evaluator/generated && echo "evaluator/generated is the exported code"
}

build_evaluator() {
  ghc -O1 -ievaluator/generated -outputdir evaluator/build -o evaluator/triel-eval evaluator/Main.hs
}

classification() {
  python3 parser/triel_to_core.py --classify examples > "$RESULTS_DIR/classification.txt" || return 1
  cat "$RESULTS_DIR/classification.txt"
  diff -u examples/core/classification.expected "$RESULTS_DIR/classification.txt"
}

scenarios() {
  local status=0 scn out="$RESULTS_DIR/scenarios"
  mkdir -p "$out"
  for scn in examples/core/scenarios/*.scn; do
    if python3 parser/triel_eval.py "$scn" > "$out/$(basename "${scn%.scn}").out" \
        && diff -u "${scn%.scn}.expected" "$out/$(basename "${scn%.scn}").out"; then
      echo "ok   $scn"
    else
      echo "FAIL $scn"
      status=1
    fi
  done
  return $status
}

# evaluator.yml: the tests of the translator and the driver, and of triel check.
tests() {
  python3 -m pytest -q -p no:cacheprovider parser/test_triel_to_core.py parser/test_triel_check.py
}

# parse-examples.yml: every example parses under parser/triel.lark with exactly
# one derivation, and the ambiguity regression tests pass.
parse_examples() {
  python3 parser/triel_parser.py --check-ambiguity \
    examples/*.triel examples/eudi/*.triel examples/semantics/*.triel examples/core/*.triel
}

ambiguity_tests() {
  python3 parser/test_ambiguity.py
}

# parse-examples.yml: the excerpts of the documents and the usage examples of
# the grammar file conform to the grammar.
document_excerpts() {
  python3 parser/test_documents.py
}

# The theorems listed by thm in Paper_Theorems.thy, up to its section on
# definitions, and the names of its oracle check must be the same list; then the session is built on top of the heap of
# TRIEL_Core, and the statements it exports are printed.
paper_theorems() {
  local thy=artifact/isabelle/Paper_Theorems.thy
  diff -u <(sed -n '/^section .*Definitions used in the paper/q;p' "$thy" | sed -nE 's/^thm ([A-Za-z0-9_.]+)$/\1/p' | sort) \
          <(grep -oE '"TRIEL_[A-Za-z0-9_.]+"' "$thy" | tr -d '"' | sort) \
    || { echo "error: the thm list and the oracle check of $thy differ"; return 1; }
  isabelle build -e -v -d formal/core -D artifact/isabelle || return 1
  cp artifact/isabelle/output/paper_theorems.txt "$RESULTS_DIR/paper_theorems.txt"
  echo
  cat "$RESULTS_DIR/paper_theorems.txt"
}

# evaluator.yml: the conformance suite (examples/core/conformance) with the
# reference implementation, on both levels.
conformance() {
  python3 examples/core/conformance/run.py --level verdicts || return 1
  python3 examples/core/conformance/run.py --level monitor
}

# evaluator.yml: manifest.json names the committed evaluator, every scenario,
# and the sha256 of every file it lists. The same code as in CI.
conformance_manifest() {
  python3 - <<'EOF'
import hashlib, json, re, sys
from pathlib import Path
m = json.loads(Path("examples/core/conformance/manifest.json").read_text(encoding="utf-8"))
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
errors = []
if m["evaluator_sha256"] != sha("evaluator/generated/TRIEL.hs"):
    errors.append("evaluator_sha256 is not the sha256 of evaluator/generated/TRIEL.hs")
traces = sorted(c["trace"] for c in m["cases"])
files = sorted(p.as_posix() for p in Path("examples/core/scenarios").glob("*.scn"))
if traces != files:
    errors.append("cases differ from the scenarios: only in manifest %s, only on disk %s"
                  % (sorted(set(traces) - set(files)), sorted(set(files) - set(traces))))
for c in m["cases"]:
    if Path(c["trace"]).stem != c["id"] or c["expected"] != c["trace"][:-len(".scn")] + ".expected":
        errors.append("%s: id, trace and expected do not agree" % c["id"])
    if not Path(c["trace"]).is_file():
        continue
    if re.findall(r'\(spec "([^"]*)"\)', Path(c["trace"]).read_text(encoding="utf-8")) != [c["spec"]]:
        errors.append("%s: spec is not the specification of the scenario" % c["id"])
    for k in ("trace", "spec", "expected"):
        if not Path(c[k]).is_file() or c["sha256"][k] != sha(c[k]):
            errors.append("%s: sha256 of %s differs from %s" % (c["id"], k, c[k]))
print("\n".join(errors) or "manifest.json: %d cases, every sha256 matches" % len(m["cases"]))
sys.exit(1 if errors else 0)
EOF
}

# evaluator.yml: run.py itself: a command that prints the expected outputs
# passes on both levels, a command that prints nothing fails.
conformance_self_check() {
  local level
  for level in verdicts monitor; do
    python3 examples/core/conformance/run.py --level $level --impl "sh -c 'cat \"\${0%.scn}.expected\"' {trace}" > "$SCRATCH/self.txt" || return 1
  done
  if python3 examples/core/conformance/run.py --impl true > "$SCRATCH/self.txt"; then
    echo "run.py passed a command without output"; return 1
  fi
  tail -n 1 "$SCRATCH/self.txt"
}

# isabelle.yml: the theories of formal/core/ROOT, read as tools/make_afp_copy.sh
# reads them.
root_theories() {
  awk '
    /^[[:space:]]*theories[[:space:]]*$/ { on = 1; next }
    /^[[:space:]]*(document_files|export_files|sessions|options)([[:space:](]|$)/ { on = 0 }
    on && NF { print $1 }' formal/core/ROOT | sort
}

# isabelle.yml: formal/checks/No_Oracles.thy imports exactly the theories of
# formal/core/ROOT (the imports read only between "imports" and "begin"); the
# session TRIEL_Core_Checks is built on top of the heap of TRIEL_Core and fails
# if a named theorem of these theories depends on an oracle, except the
# equations of the Quickcheck generators (full_exhaustive, narrowing), which
# Isabelle/HOL generates for a datatype and asserts with the oracle
# Pure.skip_proof instead of proving them; no other named theorem depends on
# them (No_Oracles.thy states the exact rule); the theories
# that its output no_oracles.txt reports are those of ROOT, and its numbers add
# up. The same checks as in CI.
no_oracles() {
  local root imports checked sum excluded sum_excluded listed line total total_excluded
  local out=formal/checks/output/no_oracles.txt
  root=$(root_theories)
  [ -n "$root" ] || { echo "error: no theories found in formal/core/ROOT"; return 1; }
  imports=$(awk '
    /^theory[[:space:]]+[A-Za-z0-9_]+[[:space:]]*$/ { header = 1 }
    header && /(^|[[:space:]])imports([[:space:]]|$)/ { on = 1 }
    on && /(^|[[:space:]])begin([[:space:]]|$)/ { exit }
    on { print }' formal/checks/No_Oracles.thy \
    | grep -oE '"?TRIEL_Core\.[A-Za-z0-9_]+' | sed -E 's/^"?TRIEL_Core\.//' | sort)
  diff -u <(echo "$root") <(echo "$imports") \
    || { echo "error: the theories of formal/core/ROOT (-) and the imports of formal/checks/No_Oracles.thy (+) differ"; return 1; }
  isabelle build -e -v -d formal/core -D formal/checks || return 1
  cp "$out" "$RESULTS_DIR/no_oracles.txt"
  checked=$(sed -nE 's/^TRIEL_Core\.([A-Za-z0-9_]+): [0-9]+ facts$/\1/p' "$out" | sort)
  sum=$(sed -nE 's/^TRIEL_Core\.[A-Za-z0-9_]+: ([0-9]+) facts$/\1/p' "$out" | awk '{ s += $1 } END { print s + 0 }')
  excluded=$(sed -nE 's/^  TRIEL_Core\.([A-Za-z0-9_]+): [0-9]+ excluded$/\1/p' "$out" | sort)
  sum_excluded=$(sed -nE 's/^  TRIEL_Core\.[A-Za-z0-9_]+: ([0-9]+) excluded$/\1/p' "$out" | awk '{ s += $1 } END { print s + 0 }')
  listed=$(grep -cE '^    [A-Za-z0-9_.]+$' "$out" || true)
  line=$(grep -E '^Named facts of TRIEL_Core without oracles: ' "$out" || true)
  total=$(echo "$line" | sed -nE 's/^Named facts of TRIEL_Core without oracles: ([0-9]+) \(excluded: [0-9]+ Quickcheck generator facts with Pure\.skip_proof\)$/\1/p')
  total_excluded=$(echo "$line" | sed -nE 's/^Named facts of TRIEL_Core without oracles: [0-9]+ \(excluded: ([0-9]+) Quickcheck generator facts with Pure\.skip_proof\)$/\1/p')
  diff -u <(echo "$root") <(echo "$checked") \
    || { echo "error: the theories of formal/core/ROOT (-) and those of $out (+) differ"; return 1; }
  diff -u <(echo "$root") <(echo "$excluded") \
    || { echo "error: the theories of formal/core/ROOT (-) and those of the excluded facts in $out (+) differ"; return 1; }
  [ -n "$total" ] && [ "$total" = "$sum" ] \
    || { echo "error: the total in $out (${total:-none}) is not the sum of the theories ($sum)"; return 1; }
  [ "$total_excluded" = "$sum_excluded" ] && [ "$total_excluded" = "$listed" ] \
    || { echo "error: the number of excluded facts in $out (${total_excluded:-none}) is not the sum of the theories ($sum_excluded) or the number listed ($listed)"; return 1; }
  echo
  cat "$RESULTS_DIR/no_oracles.txt"
}

# --- Run -------------------------------------------------------------------

echo "TRIEL artifact: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "source:  $SRC"
echo "copy:    $WORK"
echo "results: $RESULTS_DIR"
echo "isabelle $(isabelle version 2>/dev/null || echo '?'); ghc $(ghc --numeric-version 2>/dev/null || echo '?');" \
     "$(python3 --version 2>&1);" \
     "$(python3 -c 'import importlib.metadata as m; print("lark", m.version("lark") + "; pytest", m.version("pytest"))' 2>/dev/null || echo 'lark ?; pytest ?')"
echo "cpus $(nproc); memory $(awk '/MemTotal/ {printf "%.1f GiB", $2/1048576}' /proc/meminfo)"

tar -C "$SRC" --exclude=./.git --exclude=./formal/core/output --exclude=./evaluator/build \
    --exclude=./evaluator/triel-eval --exclude='__pycache__' -cf - . | tar -C "$WORK" -xf -

total_start=$(date +%s)
step 01-no-sorry           no_sorry
step 02-isabelle-build     isabelle_build
step 03-exported-code      exported_code
step 04-build-evaluator    build_evaluator
step 05-classification     classification
step 06-scenarios          scenarios
step 07-pytest             tests
step 08-parse-examples     parse_examples
step 09-ambiguity-tests    ambiguity_tests
step 10-document-excerpts  document_excerpts
step 11-paper-theorems     paper_theorems
step 12-conformance        conformance
step 13-conformance-manifest conformance_manifest
step 14-conformance-self-check conformance_self_check
step 15-no-oracles          no_oracles
total_seconds=$(( $(date +%s) - total_start ))

# --- Summary ---------------------------------------------------------------

# Theories: those that the clean build of TRIEL_Core checked, read from its log,
# against the .thy files of formal/core.
theories=$(grep -oE 'theory TRIEL_Core\.[A-Za-z0-9_]+' "$RESULTS_DIR/02-isabelle-build.log" 2>/dev/null | sort -u | wc -l)
thy_files=$(ls "$WORK"/formal/core/*.thy | wc -l)
statements=$(python3 "$WORK/artifact/count_statements.py" "$WORK"/formal/core/*.thy | sed -n 's/^total: //p')
# Theorems only: the thm lines before the section on definitions.
paper=$(sed -n '/^section .*Definitions used in the paper/q;p' "$WORK/artifact/isabelle/Paper_Theorems.thy" | grep -cE '^thm ')
paper_ok=$(sed -nE 's/^Paper theorems without oracles: ([0-9]+)$/\1/p' "$RESULTS_DIR/paper_theorems.txt" 2>/dev/null)
# The line of no_oracles.txt as it is: the number of named facts checked and
# of the excluded facts.
core_ok=$(sed -nE 's/^Named facts of TRIEL_Core without oracles: ([0-9]+ \(excluded: [0-9]+ Quickcheck generator facts with Pure\.skip_proof\))$/\1/p' "$RESULTS_DIR/no_oracles.txt" 2>/dev/null)
scn_total=$(ls "$WORK"/examples/core/scenarios/*.scn | wc -l)
scn_ok=$(grep -c '^ok ' "$RESULTS_DIR/06-scenarios.log" 2>/dev/null)
ex_total=$(grep -c ': ' "$RESULTS_DIR/classification.txt" 2>/dev/null)
ex_accepted=$(grep -c ': ACCEPTED$' "$RESULTS_DIR/classification.txt" 2>/dev/null)
tests_line=$(grep -E '[0-9]+ (passed|failed)' "$RESULTS_DIR/07-pytest.log" 2>/dev/null | tail -1)
parsed=$(sed -nE 's/^All ([0-9]+) file\(s\) parsed successfully\.$/\1/p' "$RESULTS_DIR/08-parse-examples.log" 2>/dev/null)
ambiguity=$(sed -nE 's/^All ([0-9]+) checks passed\.$/\1/p' "$RESULTS_DIR/09-ambiguity-tests.log" 2>/dev/null)
excerpts=$(sed -nE 's/^All ([0-9]+) excerpts conform to the grammar\.$/\1/p' "$RESULTS_DIR/10-document-excerpts.log" 2>/dev/null)

{
  echo
  echo "=== Summary"
  printf '%-44s %s\n' "theories checked by Isabelle (TRIEL_Core)" "$theories (.thy files in formal/core: $thy_files)"
  printf '%-44s %s\n' "proved statements (lemma/theorem/corollary)" "${statements:-?}"
  printf '%-44s %s\n' "paper theorems found, without oracles" "${paper_ok:-0} of $paper"
  printf '%-44s %s\n' "named facts of TRIEL_Core without oracles" "${core_ok:-?}"
  printf '%-44s %s\n' "scenarios matching .expected" "${scn_ok:-0} of $scn_total"
  printf '%-44s %s\n' "examples accepted by the core" "${ex_accepted:-0} of ${ex_total:-0}"
  printf '%-44s %s\n' "translator and driver tests (pytest)" "${tests_line:-?}"
  printf '%-44s %s\n' "examples parsed with one derivation" "${parsed:-0} of $(ls "$WORK"/examples/*.triel "$WORK"/examples/{eudi,semantics,core}/*.triel | wc -l)"
  printf '%-44s %s\n' "ambiguity regression checks passed" "${ambiguity:-0}"
  printf '%-44s %s\n' "document excerpts conforming to the grammar" "${excerpts:-0}"
  printf '%-44s %s\n' "wall-clock time" "$total_seconds s"
  for name in $(printf '%s\n' "${!seconds[@]}" | sort); do
    printf '  %-42s %s s\n' "$name" "${seconds[$name]}"
  done
  if [ ${#failures[@]} -eq 0 ]; then
    echo "RESULT: all ${#seconds[@]} steps passed"
  else
    echo "RESULT: FAILED: ${failures[*]}"
  fi
} | tee "$RESULTS_DIR/summary.txt"

[ ${#failures[@]} -eq 0 ]
