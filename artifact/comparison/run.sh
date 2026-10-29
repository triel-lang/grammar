#!/usr/bin/env bash
# Runs the comparison of TRIEL with Cedar and Dogwood on the running example of
# the paper (examples/core/core_invoice_agent.triel), writes every output to
# results/ (or to the directory given as the first argument) and compares the
# outputs with the recorded ones in expected/.
#
# Needs, on PATH:
#   cedar    cedar-policy-cli 4.14.0   cargo install cedar-policy-cli --version 4.14.0 --locked
#   dogwood  dogwood-cli 1.1.0         cargo install dogwood-cli --version 1.1.0 --locked
#   python3 with lark (parser/requirements of the repository)
# and the TRIEL evaluator: the path in TRIEL_EVAL, or ghc to build it from
# evaluator/.
#
# The tools need network access to install, so this script is not a step of
# artifact/run.sh and is not run in the offline image.
#
# Exit code: 0 if every output equals its recorded counterpart, 1 otherwise.

set -u

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
OUT=${1:-$HERE/results}
WORK="$OUT/work"

for tool in cedar dogwood python3; do
  command -v "$tool" >/dev/null || { echo "error: $tool not found on PATH"; exit 1; }
done

rm -rf "$OUT"
mkdir -p "$WORK"
cp -r "$HERE/dw" "$HERE/cedar" "$HERE/cedar5" "$HERE/gen" "$WORK/"

# One output file per group of commands. Each command is printed, then its
# output (stdout and stderr), then its exit code.
group() { CURRENT="$OUT/$1.out"; : > "$CURRENT"; }
cmd() {
  { echo "\$ $*"; "$@" 2>&1; echo "[exit $?]"; echo; } >> "$CURRENT"
}

# --- Versions ----------------------------------------------------------------

group versions
cmd cedar --version
cmd dogwood --version

# --- Traces and requests -------------------------------------------------------

python3 -I "$WORK/gen/mktraces.py" "$WORK/dw/traces" >/dev/null
python3 -I "$WORK/gen/mkctx.py" "$WORK/cedar/req" >/dev/null

TRACES="within_limit over_limit approved approval_missing stale_quote owner_fallback owner_late no_amount owner_early owner_after_5d"
ATTR_TRACES="within_limit over_limit approved approval_missing stale_quote owner_fallback owner_late no_amount"
REQUESTS="within_limit over_limit approved approval_missing stale_quote owner_fallback owner_early owner_after_5d no_amount"

# --- Dogwood: quote, approval and activation as events in the history ---------

cd "$WORK/dw"
group dogwood-temporal
cmd dogwood validate temporal.dw --policy-schema schema.cedarschema --event-schema events.dwschema
cmd dogwood validate temporal.dw --policy-schema schema.cedarschema
for t in $TRACES; do
  cmd dogwood replay temporal.dw --policy-schema schema.cedarschema --event-schema events.dwschema --trace "traces/$t.log"
done

# --- Dogwood: amount and approval as request attributes ------------------------

group dogwood-attributes
for p in attr_unguarded attr_guarded; do
  cmd dogwood validate "$p.dw" --policy-schema schema.cedarschema --event-schema events.dwschema
  for t in $ATTR_TRACES; do
    cmd dogwood replay "$p.dw" --policy-schema schema.cedarschema --event-schema events.dwschema --trace "traces/$t.log"
  done
done
cmd dogwood replay attr_unguarded.dw --policy-schema schema.cedarschema --event-schema events.dwschema --trace traces/approval_missing.log --format json

# --- Dogwood: the default event schema (24h window, pin callerPrincipal) -------

group dogwood-default-schema
cmd dogwood validate temporal_24h.dw --policy-schema schema.cedarschema
for t in within_limit approved; do
  cmd dogwood replay temporal_24h.dw --policy-schema schema.cedarschema --trace "traces/$t.log"
  cmd dogwood replay temporal_24h.dw --policy-schema schema.cedarschema --event-schema events.dwschema --trace "traces/$t.log"
done

# --- Cedar: the example, unguarded, guarded and fail-closed --------------------

cd "$WORK/cedar"
for p in invoice invoice_guarded invoice_failclosed; do
  group "cedar-$p"
  cmd cedar validate --schema schema.cedarschema --policies "$p.cedar" -f plain
  for r in $REQUESTS; do
    cmd cedar authorize -p "$p.cedar" -s schema.cedarschema --entities entities.json --request-json "req/$r.json" -v -f plain
    cmd cedar authorize -p "$p.cedar" --entities entities.json --request-json "req/$r.json" -v -f plain
  done
done

# --- Cedar: one forbid over an absent attribute, three schemas, three guards ---

cd "$WORK/cedar5"
group cedar-absent
for k in opt req none; do
  cmd cedar validate -s "s_$k.cedarschema" -p absent.cedar -f plain
done
for c in empty false; do
  cmd cedar authorize -p absent.cedar --entities entities.json --request-json "req_$c.json" -v -f plain
  for k in opt req none; do
    cmd cedar authorize -p absent.cedar -s "s_$k.cedarschema" --entities entities.json --request-json "req_$c.json" -v -f plain
    cmd cedar authorize -p absent.cedar -s "s_$k.cedarschema" --request-validation false --entities entities.json --request-json "req_$c.json" -v -f plain
  done
done
group cedar-guards
for p in guard_and guard_or guard_if; do
  cmd cedar validate -s s_opt.cedarschema -p "$p.cedar" -f plain
  cmd cedar authorize -p "$p.cedar" -s s_opt.cedarschema --entities entities.json --request-json req_empty.json -v -f plain
done

# --- TRIEL: three further traces of the running example ------------------------

cd "$ROOT"
EVAL=${TRIEL_EVAL:-}
if [ -z "$EVAL" ]; then
  command -v ghc >/dev/null || { echo "error: set TRIEL_EVAL or install ghc"; exit 1; }
  mkdir -p "$WORK/triel-build"
  ghc -O1 -ievaluator/generated -outputdir "$WORK/triel-build" -o "$WORK/triel-eval" evaluator/Main.hs >/dev/null || exit 1
  EVAL="$WORK/triel-eval"
fi
group triel-further-traces
for s in x_no_amount x_no_entry_after_deadline x_tick_between; do
  cmd python3 parser/triel_eval.py "artifact/comparison/triel/$s.scn" --evaluator "$EVAL"
done

# --- Comparison with the recorded outputs --------------------------------------

# The evaluator path in the last group depends on the machine: compare its
# output without the command lines.
status=0
for f in "$HERE"/expected/*.out; do
  name=$(basename "$f")
  if [ "$name" = triel-further-traces.out ]; then
    diff <(grep -v '^\$ ' "$f") <(grep -v '^\$ ' "$OUT/$name") >/dev/null || { echo "DIFFERS: $name"; status=1; continue; }
  else
    diff -q "$f" "$OUT/$name" >/dev/null || { echo "DIFFERS: $name"; status=1; continue; }
  fi
  echo "same:    $name"
done
[ "$status" = 0 ] && echo "All outputs equal the recorded ones."
exit "$status"
