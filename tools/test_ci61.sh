#!/usr/bin/env bash
# Tests of three checks of CI, each run on a scratch copy that it must reject.
#
# Usage:
#   tools/test_ci61.sh g1|g2|g3
#
#   g1  the step "The manifest of the conformance suite matches the files" of
#       .github/workflows/evaluator.yml (job check-conformance), on a copy whose
#       manifest.json adds to the lines of the level monitor an entry without a
#       word: "", then " ". The step must exit with 1 and print
#       "levels.monitor.lines is empty or holds an entry without a word".
#   g2  the step "The committed code is the exported code" of evaluator.yml
#       (job build-evaluator), on a copy with its own git repository and a file
#       in evaluator/generated that evaluator/.gitignore ignores:
#       evaluator/generated/triel-eval, then evaluator/generated/build/Extra.hs.
#       The step must pass on the copy without the file and fail with it.
#   g3  the function check of tools/make_afp_copy.sh, on an entry with a .thy
#       file and a ROOT whose directory has mode 644, so that cd into it fails
#       while the list of its .thy files can still be read; the working
#       directory holds a ROOT and a .thy without sorry. The function must print
#       "error: grep failed (code 2)" and set fail=1. With mode 755 it must print
#       "ok: no sorry" and leave fail=0. A user that is not root is needed: root
#       may cd into the directory.
#
# The code of the step or the function is read from the file that CI runs, in
# the working tree, by the name of the step (and its job) or of the function;
# it is not copied here. The scratch copies are made from git archive HEAD. The
# test needs bash, git and python3 (no PyYAML), and reads no git configuration
# of the machine.
#
# Exit code: 0 if the check rejected every corrupted copy; otherwise 1 and the
# line "not caught: G1" (G2, G3); 2 on a usage error.

set -uo pipefail

usage() { echo "usage: $0 g1|g2|g3" >&2; exit 2; }
[ $# -eq 1 ] || usage
case $1 in g1|g2|g3) ;; *) usage ;; esac
G=$(printf '%s' "$1" | tr a-z A-Z)

REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
WORKFLOW="$REPO/.github/workflows/evaluator.yml"
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null GIT_TERMINAL_PROMPT=0
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE

TMP=$(mktemp -d)
trap 'chmod -R u+rwx "$TMP" 2>/dev/null; rm -rf "$TMP"' EXIT

missed=0
caught() { echo "caught: $G: $1"; }
miss() { echo "missed: $G: $1"; missed=1; }

# step_run JOB NAME: the run: block of the step NAME of the job JOB of
# evaluator.yml, without its indentation.
step_run() {
  python3 - "$WORKFLOW" "$1" "$2" <<'EOF'
import sys
path, job, name = sys.argv[1:4]
lines = open(path, encoding="utf-8").read().split("\n")
ind = lambda l: len(l) - len(l.lstrip(" "))
code = lambda l: l.strip() and not l.lstrip().startswith("#")
if "  %s:" % job not in lines:
    sys.exit("no job %s in %s" % (job, path))
j = lines.index("  %s:" % job)
end = next((k for k in range(j + 1, len(lines)) if code(lines[k]) and ind(lines[k]) <= 2), len(lines))
names = {"- name: " + q + name + q for q in ("", '"', "'")}
k = next((k for k in range(j + 1, end) if lines[k].strip() in names), None)
if k is None:
    sys.exit("no step %r in the job %s of %s" % (name, job, path))
dash = ind(lines[k])
stop = next((m for m in range(k + 1, end) if code(lines[m]) and ind(lines[m]) <= dash), end)
for m in range(k + 1, stop):
    if ind(lines[m]) == dash + 2 and lines[m].strip().startswith("run:"):
        value = lines[m].strip()[len("run:"):].strip()
        if value not in ("|", "|-", "|+"):
            print(value)
            sys.exit(0)
        body = []
        for l in lines[m + 1:stop]:
            if l.strip() and ind(l) <= dash + 2:
                break
            body.append(l)
        while body and not body[-1].strip():
            body.pop()
        n = min(ind(l) for l in body if l.strip())
        print("\n".join(l[n:] for l in body))
        sys.exit(0)
sys.exit("no run: in the step %r" % name)
EOF
}

# copy_of_head DIR: the files of HEAD in DIR.
copy_of_head() {
  mkdir -p "$1" && git -C "$REPO" archive --format=tar HEAD | tar -C "$1" -xf -
}

test_g1() {
  local step="The manifest of the conformance suite matches the files"
  local msg="levels.monitor.lines is empty or holds an entry without a word"
  local code out rc v
  code=$(step_run check-conformance "$step") || { miss "the step \"$step\" was not found"; return; }
  printf '%s\n' "$code" > "$TMP/manifest_step.py"
  for v in '""' '" "'; do
    rm -rf "$TMP/g1" && copy_of_head "$TMP/g1" || { miss "no copy of HEAD"; return; }
    python3 - "$TMP/g1/examples/core/conformance/manifest.json" "$v" <<'EOF' || { miss "manifest.json not changed"; return; }
import json, sys
path, entry = sys.argv[1], json.loads(sys.argv[2])
m = json.load(open(path, encoding="utf-8"))
m["levels"]["monitor"]["lines"].append(entry)
json.dump(m, open(path, "w", encoding="utf-8"), indent=2)
EOF
    out=$(cd "$TMP/g1" && python3 "$TMP/manifest_step.py" 2>&1); rc=$?
    if [ $rc -eq 1 ] && grep -qF -- "$msg" <<<"$out"; then
      caught "level monitor, lines entry $v: exit 1 and \"$msg\""
    else
      miss "level monitor, lines entry $v: exit $rc, output: $(tail -n 3 <<<"$out")"
    fi
  done
}

test_g2() {
  local step="The committed code is the exported code"
  local code out rc f n=0
  code=$(step_run build-evaluator "$step") || { miss "the step \"$step\" was not found"; return; }
  for f in evaluator/generated/triel-eval evaluator/generated/build/Extra.hs; do
    n=$((n + 1))
    local c="$TMP/g2-$n"
    copy_of_head "$c" || { miss "no copy of HEAD"; return; }
    git -C "$c" -c init.defaultBranch=main init -q \
      && git -C "$c" add -f -A . \
      && git -C "$c" -c user.name=test -c user.email=test -c commit.gpgsign=false commit -q -m copy \
      || { miss "no git repository in the copy"; return; }
    out=$(cd "$c" && bash -e -c "$code" 2>&1); rc=$?
    if [ $rc -ne 0 ]; then
      miss "the step fails on the copy without $f (exit $rc): $(tail -n 3 <<<"$out")"
      continue
    fi
    mkdir -p "$(dirname "$c/$f")" && echo x > "$c/$f"
    out=$(cd "$c" && bash -e -c "$code" 2>&1); rc=$?
    if [ $rc -ne 0 ]; then
      caught "$f: exit $rc"
    else
      miss "$f: exit 0, output: $(tail -n 3 <<<"$out")"
    fi
  done
}

test_g3() {
  local fn out d
  fn=$(sed -n '/^check() {/,/^}/p' "$REPO/tools/make_afp_copy.sh")
  [ -n "$fn" ] || { miss "no function check in tools/make_afp_copy.sh"; return; }
  if [ "$(id -u)" -eq 0 ]; then
    miss "run as root: cd into a directory without x does not fail for root"
    return
  fi
  for d in entry cwd; do
    mkdir -p "$TMP/g3/$d"
    printf 'theory A imports Main begin end\n' > "$TMP/g3/$d/A.thy"
    printf 'session A\n' > "$TMP/g3/$d/ROOT"
  done
  run_check() {
    (cd "$TMP/g3/cwd" && ENTRY="$TMP/g3/entry" bash -c "fail=0
$fn
check sorry -w sorry; echo \"fail=\$fail\"" 2>&1)
  }
  chmod 755 "$TMP/g3/entry"
  out=$(run_check)
  if ! grep -qF "ok: no sorry" <<<"$out" || ! grep -qx "fail=0" <<<"$out"; then
    miss "entry with mode 755: not ok, output: $(tail -n 3 <<<"$out")"
    return
  fi
  chmod 644 "$TMP/g3/entry"
  out=$(run_check)
  chmod 755 "$TMP/g3/entry"
  if grep -qF "error: grep failed (code 2)" <<<"$out" && grep -qx "fail=1" <<<"$out"; then
    caught "entry with mode 644: \"error: grep failed (code 2)\" and fail=1"
  else
    miss "entry with mode 644: output: $(tail -n 3 <<<"$out")"
  fi
}

"test_$1"
if [ $missed -ne 0 ]; then
  echo "not caught: $G"
  exit 1
fi
echo "$G: every corruption caught"
