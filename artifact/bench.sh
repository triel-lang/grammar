#!/usr/bin/env bash
# Measure the time and the memory of the translation and of the evaluator on
# traces of 10^2 to 10^6 entries. It is not a step of run.sh.
#
# Usage:
#   artifact/bench.sh          (in the artifact image:
#                               docker run --rm --entrypoint artifact/bench.sh triel-artifact)
#
# Needs on PATH: ghc (9.6.7) and python3 (3.12) with lark 1.3.1; and GNU time
# as /usr/bin/time. The repository is copied to a scratch directory, and the
# evaluator is built there with the command of run.sh and evaluator.yml, so the
# checkout is never modified.
#
# Traces. For examples/core/core_invoice_agent.triel and for
# examples/core/core_sequence.triel, whose three terms are composite,
# artifact/bench_trace.py writes a scenario of N entries for each N of SIZES,
# drawn with the fixed seed SEED (the composition of the traces is described in
# that file). The scenarios are written to the scratch directory and removed
# when their point is done; their SHA-256 is listed in traces.sha256, so two
# runs can be checked to have measured the same traces.
#
# Two phases are measured apart, each on its own input:
#   translate  python3 parser/triel_eval.py SCENARIO --input > INPUT
#              everything before the evaluator: Python starts, the
#              specification is parsed (lark) and translated (triel_to_core.py),
#              both once whatever the length of the trace, and then the
#              scenario of N entries is read and the input of the evaluator is
#              written to a file;
#   evaluate   evaluator/triel-eval < INPUT
#              the evaluator exported from formal/core, on that file.
# Every point is run RUNS times. The time of a run is its wall-clock time,
# taken around /usr/bin/time -v and timeout, which add a few milliseconds; the
# point gives the median, the minimum and the maximum over its runs. Its memory
# is the largest "Maximum resident set size" that /usr/bin/time -v reports
# over its runs.
#
# Limits. Every run of a point is started under timeout LIMIT (120 s), and a
# run of 1000000 entries or more under timeout 60. A point with a run that does
# not finish within its limit is written to bench.csv with the status timeout
# and no time, and is not run again; all longer traces of the same example are
# then skipped, in both phases (status skipped), and so is the evaluation of a
# trace whose translation timed out. Nothing is extrapolated.
#
# Output in RESULTS_DIR: bench.csv (one line per point), bench.md (the same as a
# Markdown table), runs.csv (one line per run), machine.txt, traces.sha256 and
# the report of the evaluator on each trace (reports/EXAMPLE-N.out).
#
# Environment:
#   RESULTS_DIR  directory of the results (default: a new directory under /tmp)
#   RUNS         runs per point (default 5)
#   LIMIT        seconds of the timeout of a run (default 120)
#   SIZES        trace lengths (default "100 1000 10000 100000 1000000")
#   SEED         seed of the traces (default 20261027)
#   KEEP_WORK=1  keep the scratch copy
#
# Exit code: 0 if every run that was started finished or timed out, 1 if a run
# or the summary failed, 2 if RUNS, LIMIT, SIZES or SEED is not valid.

set -u
export LC_ALL=C

RUNS=${RUNS:-5}
LIMIT=${LIMIT:-120}
SIZES=${SIZES:-"100 1000 10000 100000 1000000"}
SEED=${SEED:-20261027}
EXAMPLES="invoice sequence"
for v in "$RUNS" "$LIMIT" $SIZES; do
  [[ $v =~ ^[1-9][0-9]*$ ]] || { echo "error: RUNS, LIMIT and SIZES must be positive integers" >&2; exit 2; }
done
[[ $SEED =~ ^[0-9]+$ ]] || { echo "error: SEED must be a non-negative integer" >&2; exit 2; }

SRC=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
SCRATCH=$(mktemp -d "${TMPDIR:-/tmp}/triel-bench.XXXXXX")
WORK="$SCRATCH/triel"
RESULTS_DIR=${RESULTS_DIR:-$SCRATCH/results}
mkdir -p "$WORK" "$RESULTS_DIR/reports"
RESULTS_DIR=$(cd "$RESULTS_DIR" && pwd)
# The scratch copy is removed; the scratch directory too when it is then empty.
[ "${KEEP_WORK:-0}" = 1 ] || trap 'rm -rf "$WORK"; rmdir "$SCRATCH" 2>/dev/null' EXIT

[ -x /usr/bin/time ] || { echo "error: GNU time (/usr/bin/time) is needed" >&2; exit 1; }

# --- The machine -----------------------------------------------------------

{
  echo "date:    $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "cpu:     $(LC_ALL=C lscpu 2>/dev/null | sed -n 's/^Model name:[[:space:]]*//p' | head -1)"
  echo "cores:   $(nproc) available to this process; $(LC_ALL=C lscpu 2>/dev/null | sed -n 's/^CPU(s):[[:space:]]*//p' | head -1) in all (lscpu)"
  echo "memory:  $(awk '/MemTotal/ {printf "%.1f GiB", $2/1048576}' /proc/meminfo)"
  echo "kernel:  $(uname -sr)"
  echo "ghc:     $(ghc --numeric-version 2>/dev/null || echo '?')"
  echo "python:  $(python3 --version 2>&1)"
  echo "lark:    $(python3 -c 'import importlib.metadata as m; print(m.version("lark"))' 2>/dev/null || echo '?')"
  echo "runs:    $RUNS per point; timeout $LIMIT s per run (60 s from 1000000 entries); seed $SEED"
} | tee "$RESULTS_DIR/machine.txt"

# --- The scratch copy and the evaluator ------------------------------------

tar -C "$SRC" --exclude=./.git --exclude=./formal/core/output --exclude=./evaluator/build \
    --exclude=./evaluator/triel-eval --exclude='__pycache__' -cf - . | tar -C "$WORK" -xf -
cd "$WORK" || exit 1
echo
echo "=== building the evaluator"
ghc -O1 -ievaluator/generated -outputdir evaluator/build -o evaluator/triel-eval evaluator/Main.hs \
  > "$RESULTS_DIR/ghc.log" 2>&1 || { cat "$RESULTS_DIR/ghc.log"; echo "error: ghc failed" >&2; exit 1; }
mkdir -p bench

# --- Measuring -------------------------------------------------------------

spec_of() {
  case $1 in
    invoice) echo examples/core/core_invoice_agent.triel ;;
    sequence) echo examples/core/core_sequence.triel ;;
  esac
}

# measure EXAMPLE N PHASE RUN LIMIT STDIN STDOUT COMMAND...: one run under
# timeout LIMIT; appends a line to runs.csv and prints its status: ok, timeout
# or failed.
measure() {
  local ex=$1 n=$2 phase=$3 run=$4 lim=$5 in=$6 out=$7 mem t0 t1 status secs rss
  shift 7
  mem=$(mktemp)
  t0=$EPOCHREALTIME
  /usr/bin/time -v -o "$mem" timeout -k 10 "$lim" "$@" < "$in" > "$out" 2> "$out.err"
  status=$?
  t1=$EPOCHREALTIME
  secs=$(awk -v a="$t0" -v b="$t1" 'BEGIN { printf "%.3f", b - a }')
  rss=$(sed -n 's/^[[:space:]]*Maximum resident set size (kbytes): //p' "$mem")
  rm -f "$mem"
  echo "$ex,$n,$phase,$run,$secs,${rss:-},$status" >> "$RESULTS_DIR/runs.csv"
  printf '%-9s %8s %-9s run %s: %10s s %10s KiB  exit %s\n' "$ex" "$n" "$phase" "$run" "$secs" "${rss:-?}" "$status" >&2
  if [ $status -eq 0 ]; then
    echo ok
  elif { [ $status -eq 124 ] || [ $status -eq 137 ]; } \
       && awk -v s="$secs" -v l="$lim" 'BEGIN { exit !(s >= l) }'; then
    echo timeout
  else
    sed 's/^/    /' "$out.err" | head -5 >&2
    echo failed
  fi
}

echo "example,entries,phase,run,seconds,max_rss_kib,exit" > "$RESULTS_DIR/runs.csv"
: > "$RESULTS_DIR/traces.sha256"
: > "$RESULTS_DIR/points.txt"
failed=0
for ex in $EXAMPLES; do
  skip=
  for n in $SIZES; do
    if [ -n "$skip" ]; then
      for phase in translate evaluate; do
        echo "$ex $n $phase skipped $skip" >> "$RESULTS_DIR/points.txt"
        printf '%-9s %8s %-9s skipped: %s\n' "$ex" "$n" "$phase" "$skip" >&2
      done
      continue
    fi
    lim=$LIMIT
    [ "$n" -ge 1000000 ] && [ "$lim" -gt 60 ] && lim=60
    scn="bench/$ex-$n.scn" inp="bench/$ex-$n.in"
    python3 artifact/bench_trace.py "$ex" "$n" "$SEED" > "$scn" || { echo "error: no trace" >&2; exit 1; }
    (cd bench && sha256sum "$ex-$n.scn") >> "$RESULTS_DIR/traces.sha256"
    for phase in translate evaluate; do
      if [ -n "$skip" ]; then
        echo "$ex $n $phase skipped $skip" >> "$RESULTS_DIR/points.txt"
        printf '%-9s %8s %-9s skipped: %s\n' "$ex" "$n" "$phase" "$skip" >&2
        continue
      fi
      result=ok
      for run in $(seq 1 "$RUNS"); do
        if [ $phase = translate ]; then
          result=$(measure "$ex" "$n" "$phase" "$run" "$lim" /dev/null "$inp" \
                     python3 parser/triel_eval.py "$scn" --input)
        else
          result=$(measure "$ex" "$n" "$phase" "$run" "$lim" "$inp" "bench/$ex-$n.out" \
                     evaluator/triel-eval)
          [ "$run" -eq 1 ] && [ "$result" = ok ] && cp "bench/$ex-$n.out" "$RESULTS_DIR/reports/$ex-$n.out"
        fi
        [ "$result" = ok ] || break
      done
      echo "$ex $n $phase $result $lim" >> "$RESULTS_DIR/points.txt"
      noun=translation
      [ $phase = evaluate ] && noun=evaluation
      case $result in
        timeout) skip="the $noun of the trace of $n entries timed out ($lim s)" ;;
        failed) failed=1; skip="the $noun of the trace of $n entries failed" ;;
      esac
    done
    rm -f "$scn" "$inp" "bench/$ex-$n.out" "bench/$ex-$n.out.err" "bench/$ex-$n.in.err"
  done
done

# --- Summary ---------------------------------------------------------------

echo
cat "$RESULTS_DIR/machine.txt" "$RESULTS_DIR/traces.sha256"
python3 - "$RESULTS_DIR" "$EXAMPLES" <<'EOF'
import csv, statistics, sys
from pathlib import Path

res = Path(sys.argv[1])
spec = {"invoice": "core_invoice_agent", "sequence": "core_sequence"}
runs = list(csv.DictReader(open(res / "runs.csv")))
points = [line.split(" ", 4) for line in (res / "points.txt").read_text().splitlines()]
rows = []
for ex, n, phase, status, rest in points:
    rs = [r for r in runs if (r["example"], r["entries"], r["phase"]) == (ex, n, phase)]
    row = {"example": spec[ex], "entries": n, "phase": phase, "status": status,
           "runs": "", "median_s": "", "min_s": "", "max_s": "", "peak_rss_mib": "",
           "timeout_s": rest if status != "skipped" else "", "note": rest if status == "skipped" else ""}
    if rs:
        row["runs"] = str(len(rs))
        rss = [int(r["max_rss_kib"]) for r in rs if r["max_rss_kib"]]
        if rss and status == "ok":
            row["peak_rss_mib"] = f"{max(rss) / 1024:.1f}"
    if status == "ok":
        t = [float(r["seconds"]) for r in rs]
        row.update(median_s=f"{statistics.median(t):.3f}", min_s=f"{min(t):.3f}", max_s=f"{max(t):.3f}")
    rows.append(row)
cols = ["example", "entries", "phase", "status", "runs", "median_s", "min_s", "max_s",
        "peak_rss_mib", "timeout_s", "note"]
with open(res / "bench.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=cols)
    w.writeheader()
    w.writerows(rows)
md = ["| Example | Entries | Phase | Median s | Min s | Max s | Peak memory MiB | Runs |",
      "|---|---:|---|---:|---:|---:|---:|---|"]
for r in rows:
    if r["status"] == "ok":
        md.append(f"| {r['example']} | {r['entries']} | {r['phase']} | {r['median_s']} | {r['min_s']} "
                  f"| {r['max_s']} | {r['peak_rss_mib']} | {r['runs']} |")
    elif r["status"] == "timeout":
        md.append(f"| {r['example']} | {r['entries']} | {r['phase']} | timeout ({r['timeout_s']} s) | | | "
                  f"| timed out in run {r['runs']} |")
    else:
        md.append(f"| {r['example']} | {r['entries']} | {r['phase']} | {r['status'].replace('_', ' ')} | | | "
                  f"| {r['note']} |")
(res / "bench.md").write_text("\n".join(md) + "\n")
print()
print("\n".join(md))
EOF
[ $? -eq 0 ] || { echo "error: the summary failed" >&2; failed=1; }

echo
echo "results: $RESULTS_DIR"
[ $failed -eq 0 ]
