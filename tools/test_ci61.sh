#!/usr/bin/env bash
# Tests of the checks of CI, each run on scratch copies that the check must
# reject (and, where named, on copies it must pass).
#
# Usage:
#   tools/test_ci61.sh g1|g2|g3|g4|g1run|g4run|steps|jobs
#
#   g1     the step "The manifest of the conformance suite matches the files"
#          of .github/workflows/evaluator.yml (job check-conformance). It must
#          pass on the manifest.json of HEAD; for every level of manifest.json
#          and each of the entries without a word "", " ", "\t" and "  " added
#          to the lines of the level, it must exit with 1 and print
#          "levels.<level>.lines is empty or holds an entry without a word".
#   g1run  the same for the function conformance_manifest of artifact/run.sh.
#   g2     the step "The committed code is the exported code" of evaluator.yml
#          (job build-evaluator), on a copy with its own git repository. Into
#          evaluator/generated go, one at a time, the files triel-eval,
#          build/Extra.hs, and <r>/triel-eval, build/<r>/<r>.o and <r>.pyc
#          with a name <r> read from /dev/urandom at every run; git
#          check-ignore must confirm that each is ignored. The step must pass
#          on the copy without the file and fail with it.
#   g3     the function check of tools/make_afp_copy.sh, on an entry with a .thy
#          file and a ROOT whose directory has mode 644, so that cd into it fails
#          while the list of its .thy files can still be read; the working
#          directory holds a ROOT and a .thy without sorry. The function must print
#          "error: grep failed (code 2)" and set fail=1. With mode 755 it must print
#          "ok: no sorry" and leave fail=0. A user that is not root is needed: root
#          may cd into the directory.
#   g4     the steps "Remove the exported code before the export" and "The
#          committed code is the exported code" of evaluator.yml (job
#          build-evaluator), run as on the runner (bash -e -c), on a copy with
#          its own git repository: the removal exits with 0 and leaves no .hs in
#          evaluator/generated; with no export the check fails; with TRIEL.hs
#          written as committed the check passes. On a copy whose commit holds
#          evaluator/generated/Sub/M.hs the removal must not exit with 0 and
#          must print "evaluator/generated still holds .hs files".
#   g4run  the functions isabelle_build and exported_code of artifact/run.sh,
#          run as run.sh runs them (bash -u, without -e) in one copy, with SRC
#          another copy, under an isabelle first on PATH that records its calls
#          and writes nothing or TRIEL.hs as in SRC. An export that writes
#          nothing fails; TRIEL.hs as in SRC passes; a Sub/M.hs in both copies
#          that the export does not write fails; a directory Old.hs with a file
#          in the copy fails isabelle_build with "evaluator/generated still
#          holds .hs files" before isabelle is called. SRC never changes.
#   steps  python3 tools/check_workflows.py steps of the working tree, run in a
#          copy of .github/workflows of HEAD in which one corruption is made as
#          text: continue-on-error at a step (also as a quoted key) and at a
#          job, an if: at a step that may not have one, an if: of the list with
#          another value at a step and at a job, an if: at a step of
#          check-conformance chosen at random among those with a name and no
#          if:, an evaluator.yml that is not YAML and an empty one. The check
#          must exit with 1 and print a line that names the job, the step (for
#          a step) and the key (continue-on-error or if:), or evaluator.yml.
#   jobs   python3 tools/check_workflows.py jobs, in the same way: a second job
#          build in a new extra.yml that runs on push with paths, a second job
#          evaluate in a new extra.yaml, name: afp at the job parse, paths at
#          the push of parse-examples.yml, an if: at the job bench, the job
#          afp-2026-lint renamed, and a new workflow file that is not YAML. The
#          check must exit with 1 and name each check concerned as a word of its
#          own (no letter, digit, _ or - next to it), or the file.
#
# The code of a step, a function or the check is read from the file that CI
# runs, in the working tree, by the name of the step (and its job), of the
# function or of the script; it is not copied here. The scratch copies are made
# from git archive HEAD. The test needs bash, git and python3 (no PyYAML), and
# reads no git configuration of the machine.
#
# Exit code: 0 if the check rejected every corrupted copy; otherwise 1 and the
# line "not caught: G1" (G2, G3, G4, G1RUN, G4RUN, STEPS, JOBS); 2 on a usage
# error.

set -uo pipefail

usage() { echo "usage: $0 g1|g2|g3|g4|g1run|g4run|steps|jobs" >&2; exit 2; }
[ $# -eq 1 ] || usage
case $1 in g1|g2|g3|g4|g1run|g4run|steps|jobs) ;; *) usage ;; esac
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

# manifest_cases CMD...: CMD, run in a copy of HEAD, must pass on the
# manifest.json of HEAD and, for every level of it and every entry without a
# word added to the lines of the level, exit with 1 and print the message of
# the level.
manifest_cases() {
  local c="$TMP/g1" m out rc lv v msg
  local -a levels
  rm -rf "$c" && copy_of_head "$c" || { miss "no copy of HEAD"; return; }
  m="$c/examples/core/conformance/manifest.json"
  cp "$m" "$TMP/manifest.json.head" || { miss "no manifest.json in the copy"; return; }
  out=$(cd "$c" && "$@" 2>&1); rc=$?
  if [ $rc -ne 0 ]; then
    miss "the manifest.json of HEAD: exit $rc, output: $(tail -n 3 <<<"$out")"
    return
  fi
  mapfile -t levels < <(python3 -c 'import json, sys; print("\n".join(json.load(open(sys.argv[1], encoding="utf-8"))["levels"]))' "$m")
  [ ${#levels[@]} -gt 0 ] && [ -n "${levels[0]}" ] || { miss "no level in manifest.json"; return; }
  for lv in "${levels[@]}"; do
    msg="levels.$lv.lines is empty or holds an entry without a word"
    for v in '""' '" "' '"\t"' '"  "'; do
      cp "$TMP/manifest.json.head" "$m"
      python3 - "$m" "$lv" "$v" <<'EOF' || { miss "manifest.json not changed"; return; }
import json, sys
path, level, entry = sys.argv[1], sys.argv[2], json.loads(sys.argv[3])
m = json.load(open(path, encoding="utf-8"))
m["levels"][level]["lines"].append(entry)
json.dump(m, open(path, "w", encoding="utf-8"), indent=2)
EOF
      out=$(cd "$c" && "$@" 2>&1); rc=$?
      if [ $rc -eq 1 ] && grep -qF -- "$msg" <<<"$out"; then
        caught "level $lv, lines entry $v: exit 1 and \"$msg\""
      else
        miss "level $lv, lines entry $v: exit $rc, output: $(tail -n 3 <<<"$out")"
      fi
    done
  done
}

test_g1() {
  local step="The manifest of the conformance suite matches the files"
  local code
  code=$(step_run check-conformance "$step") || { miss "the step \"$step\" was not found"; return; }
  printf '%s\n' "$code" > "$TMP/manifest_step.py"
  manifest_cases python3 "$TMP/manifest_step.py"
}

# git_copy_of_head DIR: the files of HEAD in DIR, committed in a git
# repository of its own (ignored files included).
git_copy_of_head() {
  copy_of_head "$1" \
    && git -C "$1" -c init.defaultBranch=main init -q \
    && git -C "$1" add -f -A . \
    && git -C "$1" -c user.name=test -c user.email=test -c commit.gpgsign=false commit -q -m copy
}

test_g2() {
  local step="The committed code is the exported code"
  local code out rc f p r c="$TMP/g2"
  code=$(step_run build-evaluator "$step") || { miss "the step \"$step\" was not found"; return; }
  r=x$(od -An -N6 -tx1 /dev/urandom | tr -d ' \n')
  [ ${#r} -eq 13 ] || { miss "no name read from /dev/urandom"; return; }
  git_copy_of_head "$c" || { miss "no git repository in the copy"; return; }
  for f in triel-eval build/Extra.hs "$r/triel-eval" "build/$r/$r.o" "$r.pyc"; do
    p="evaluator/generated/$f"
    out=$(cd "$c" && bash -e -c "$code" 2>&1); rc=$?
    if [ $rc -ne 0 ]; then
      miss "the step fails on the copy without $p (exit $rc): $(tail -n 3 <<<"$out")"
      continue
    fi
    mkdir -p "$(dirname "$c/$p")" && echo x > "$c/$p" || { miss "$p not written"; continue; }
    if ! git -C "$c" check-ignore -q -- "$p"; then
      miss "$p is not ignored by git: the case tests no ignored file"
    fi
    out=$(cd "$c" && bash -e -c "$code" 2>&1); rc=$?
    if [ $rc -ne 0 ]; then
      caught "$p: exit $rc"
    else
      miss "$p: exit 0, output: $(tail -n 3 <<<"$out")"
    fi
    rm -rf "$c/evaluator/generated/${f%%/*}"
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

# fn_of FILE NAME: the function NAME of FILE, from the line "NAME() {" to the
# first line "}".
fn_of() {
  sed -n "/^$2() {/,/^}/p" "$1"
}

test_g1run() {
  local fn
  fn=$(fn_of "$REPO/artifact/run.sh" conformance_manifest)
  [ -n "$fn" ] || { miss "no function conformance_manifest in artifact/run.sh"; return; }
  printf '%s\nconformance_manifest\n' "$fn" > "$TMP/manifest_fn.sh"
  manifest_cases bash "$TMP/manifest_fn.sh"
}

test_g4() {
  local rm_step="Remove the exported code before the export"
  local ck_step="The committed code is the exported code"
  local msg="evaluator/generated still holds .hs files"
  local rm_code ck_code out rc left c="$TMP/g4" s="$TMP/g4-sub"
  rm_code=$(step_run build-evaluator "$rm_step") || { miss "the step \"$rm_step\" was not found"; return; }
  ck_code=$(step_run build-evaluator "$ck_step") || { miss "the step \"$ck_step\" was not found"; return; }
  git_copy_of_head "$c" || { miss "no git repository in the copy"; return; }
  # 1. The removal exits with 0 and leaves no .hs file.
  out=$(cd "$c" && bash -e -c "$rm_code" 2>&1); rc=$?
  left=$(cd "$c" && find evaluator/generated -name '*.hs')
  if [ $rc -eq 0 ] && [ -z "$left" ]; then
    caught "the removal exits with 0 and leaves no .hs file"
  else
    miss "the removal: exit $rc, left: $(head -n 3 <<<"$left"), output: $(tail -n 3 <<<"$out")"
  fi
  # 2. An export that writes nothing: the check of the exported code fails.
  out=$(cd "$c" && bash -e -c "$ck_code" 2>&1); rc=$?
  if [ $rc -ne 0 ]; then
    caught "no export: the check exits with $rc"
  else
    miss "no export: the check exits with 0"
  fi
  # 3. An export that writes TRIEL.hs as committed: the check passes.
  git -C "$c" cat-file blob HEAD:evaluator/generated/TRIEL.hs > "$c/evaluator/generated/TRIEL.hs" \
    || { miss "TRIEL.hs not written"; return; }
  out=$(cd "$c" && bash -e -c "$ck_code" 2>&1); rc=$?
  if [ $rc -eq 0 ]; then
    caught "TRIEL.hs as committed: the check passes"
  else
    miss "TRIEL.hs as committed: the check exits with $rc: $(tail -n 3 <<<"$out")"
  fi
  # 4. A commit with evaluator/generated/Sub/M.hs: the removal fails.
  copy_of_head "$s" && mkdir -p "$s/evaluator/generated/Sub" \
    && printf 'module Sub.M where\n' > "$s/evaluator/generated/Sub/M.hs" \
    && git -C "$s" -c init.defaultBranch=main init -q \
    && git -C "$s" add -f -A . \
    && git -C "$s" -c user.name=test -c user.email=test -c commit.gpgsign=false commit -q -m copy \
    || { miss "no git repository in the copy with Sub/M.hs"; return; }
  out=$(cd "$s" && bash -e -c "$rm_code" 2>&1); rc=$?
  if [ $rc -ne 0 ] && grep -qF -- "$msg" <<<"$out"; then
    caught "Sub/M.hs in the commit: the removal exits with $rc and prints \"$msg\""
  else
    miss "Sub/M.hs in the commit: the removal exits with $rc, output: $(tail -n 3 <<<"$out")"
  fi
}

test_g4run() {
  local msg="evaluator/generated still holds .hs files"
  local fns build exported base="$TMP/g4run" out rc
  build=$(fn_of "$REPO/artifact/run.sh" isabelle_build)
  exported=$(fn_of "$REPO/artifact/run.sh" exported_code)
  [ -n "$build" ] && [ -n "$exported" ] \
    || { miss "no function isabelle_build or exported_code in artifact/run.sh"; return; }
  fns="$build
$exported"
  mkdir -p "$base/bin" && copy_of_head "$base/head" || { miss "no copy of HEAD"; return; }
  # The isabelle of the test: it records its call and, with EXPORT=TRIEL.hs,
  # writes TRIEL.hs as in SRC.
  cat > "$base/bin/isabelle" <<'EOF'
#!/bin/sh
echo "isabelle $*" >> "$CALLS"
if [ "$EXPORT" = TRIEL.hs ]; then
  cp "$SRC/evaluator/generated/TRIEL.hs" evaluator/generated/TRIEL.hs
fi
EOF
  chmod +x "$base/bin/isabelle"
  # g4run_case NAME EXPORT CALL: CALL run in $base/NAME/work with SRC
  # $base/NAME/src; sets out, rc, called (yes or no) and src_kept (yes or no).
  g4run_case() {
    local d="$base/$1"
    out=$(cd "$d/work" && PATH="$base/bin:$PATH" SRC="$d/src" CALLS="$d/calls" EXPORT="$2" \
      bash -u -c "$fns
$3" 2>&1); rc=$?
    called=no; [ -e "$d/calls" ] && called=yes
    src_kept=no; diff -r "$d/src-before" "$d/src/evaluator/generated" > /dev/null && src_kept=yes
  }
  # g4run_copies NAME: the copies src and work of HEAD for the case NAME.
  g4run_copies() {
    local d="$base/$1"
    mkdir -p "$d" && cp -a "$base/head" "$d/src" && cp -a "$base/head" "$d/work"
  }
  g4run_keep() { cp -a "$base/$1/src/evaluator/generated" "$base/$1/src-before"; }
  local called src_kept
  # 1. The export writes nothing.
  g4run_copies none && g4run_keep none || { miss "no copies"; return; }
  g4run_case none "" "isabelle_build && exported_code"
  if [ $rc -ne 0 ] && [ $src_kept = yes ]; then
    caught "no export: exit $rc, SRC unchanged"
  else
    miss "no export: exit $rc, SRC unchanged: $src_kept, output: $(tail -n 3 <<<"$out")"
  fi
  # 2. The export writes TRIEL.hs as in SRC.
  g4run_copies same && g4run_keep same || { miss "no copies"; return; }
  g4run_case same TRIEL.hs "isabelle_build && exported_code"
  if [ $rc -eq 0 ] && [ $src_kept = yes ]; then
    caught "TRIEL.hs as in SRC: exit 0, SRC unchanged"
  else
    miss "TRIEL.hs as in SRC: exit $rc, SRC unchanged: $src_kept, output: $(tail -n 3 <<<"$out")"
  fi
  # 3. Sub/M.hs in both copies; the export writes TRIEL.hs only.
  g4run_copies sub || { miss "no copies"; return; }
  mkdir -p "$base/sub/src/evaluator/generated/Sub" "$base/sub/work/evaluator/generated/Sub"
  printf 'module Sub.M where\n' > "$base/sub/src/evaluator/generated/Sub/M.hs"
  printf 'module Sub.M where\n' > "$base/sub/work/evaluator/generated/Sub/M.hs"
  g4run_keep sub || { miss "no copies"; return; }
  g4run_case sub TRIEL.hs "isabelle_build && exported_code"
  if [ $rc -ne 0 ] && [ $src_kept = yes ]; then
    caught "Sub/M.hs not exported: exit $rc, SRC unchanged"
  else
    miss "Sub/M.hs not exported: exit $rc, SRC unchanged: $src_kept, output: $(tail -n 3 <<<"$out")"
  fi
  # 4. A directory Old.hs with a file in the working copy.
  g4run_copies dir || { miss "no copies"; return; }
  mkdir -p "$base/dir/work/evaluator/generated/Old.hs" && echo x > "$base/dir/work/evaluator/generated/Old.hs/x"
  g4run_keep dir || { miss "no copies"; return; }
  g4run_case dir TRIEL.hs "isabelle_build"
  if [ $rc -ne 0 ] && grep -qF -- "$msg" <<<"$out" && [ $called = no ] && [ $src_kept = yes ]; then
    caught "a directory Old.hs: exit $rc, \"$msg\", isabelle not called"
  else
    miss "a directory Old.hs: exit $rc, isabelle called: $called, SRC unchanged: $src_kept, output: $(tail -n 3 <<<"$out")"
  fi
}

# wf_copy DIR: the files of .github/workflows of HEAD in DIR.
wf_copy() {
  rm -rf "$1" && mkdir -p "$1" && git -C "$REPO" archive --format=tar HEAD .github/workflows | tar -C "$1" -xf -
}

# edit_wf FILE ACTION ARGS...: a change of the text of a workflow file, made
# without a YAML library; fails if the place is not found exactly once.
#   step-key JOB STEP LINE  LINE as a key of the step STEP of the job JOB
#   step-if JOB STEP VALUE  the value of the if: of that step replaced
#   job-key JOB LINE        LINE as a key of the job JOB
#   job-if JOB VALUE        the value of the if: of the job JOB replaced
#   push-key LINE           LINE as a key of on.push
#   rename-job JOB NEW      the key of the job JOB is NEW
#   pick-step JOB           print the name of a step of JOB with a name and
#                           without if:, chosen at random
edit_wf() {
  python3 - "$@" <<'EOF'
import random, sys
path, action, args = sys.argv[1], sys.argv[2], sys.argv[3:]
lines = open(path, encoding="utf-8").read().split("\n")
ind = lambda l: len(l) - len(l.lstrip(" "))
code = lambda l: l.strip() and not l.lstrip().startswith("#")
def one(found, what):
    if len(found) != 1:
        sys.exit("%s: %s found %d times in %s" % (action, what, len(found), path))
    return found[0]
def job(name):
    j = one([k for k, l in enumerate(lines) if l == "  %s:" % name], "the job " + name)
    end = next((k for k in range(j + 1, len(lines)) if code(lines[k]) and ind(lines[k]) <= 2), len(lines))
    return j, end
def steps_of(name):
    j, end = job(name)
    out = []
    for k in range(j + 1, end):
        s = lines[k].strip()
        if s.startswith("- name:"):
            n = s[len("- name:"):].strip()
            if len(n) > 1 and n[0] == n[-1] and n[0] in "'\"":
                n = n[1:-1]
            dash = ind(lines[k])
            stop = next((m for m in range(k + 1, end) if code(lines[m]) and ind(lines[m]) <= dash), end)
            out.append((n, k, dash, stop))
    return out
def step(jname, sname):
    return one([x for x in steps_of(jname) if x[0] == sname], "the step %r of the job %s" % (sname, jname))
def key_line(start, stop, indent, key):
    return one([m for m in range(start, stop) if ind(lines[m]) == indent and lines[m].strip().startswith(key + ":")],
               "the key %s" % key)
if action == "step-key":
    n, k, dash, stop = step(args[0], args[1])
    lines.insert(k + 1, " " * (dash + 2) + args[2])
elif action == "step-if":
    n, k, dash, stop = step(args[0], args[1])
    m = key_line(k + 1, stop, dash + 2, "if")
    lines[m] = " " * (dash + 2) + "if: " + args[2]
elif action == "job-key":
    j, end = job(args[0])
    lines.insert(j + 1, "    " + args[1])
elif action == "job-if":
    j, end = job(args[0])
    m = key_line(j + 1, end, 4, "if")
    lines[m] = "    if: " + args[1]
elif action == "push-key":
    o = one([k for k, l in enumerate(lines) if l == "on:"], "on:")
    p = one([k for k in range(o + 1, len(lines)) if lines[k] == "  push:"
             and all(ind(lines[m]) > 0 or not code(lines[m]) for m in range(o + 1, k))], "on.push")
    lines.insert(p + 1, "    " + args[0])
elif action == "rename-job":
    j, end = job(args[0])
    lines[j] = "  %s:" % args[1]
elif action == "pick-step":
    free = [n for n, k, dash, stop in steps_of(args[0])
            if not any(ind(lines[m]) == dash + 2 and lines[m].strip().startswith("if:") for m in range(k + 1, stop))]
    if not free:
        sys.exit("pick-step: no step of %s with a name and without if:" % args[0])
    print(random.SystemRandom().choice(free))
    sys.exit(0)
else:
    sys.exit("edit_wf: unknown action " + action)
open(path, "w", encoding="utf-8").write("\n".join(lines))
EOF
}

# names_in OUT JOB STEP KEY: a line of OUT names the job JOB as a word of its
# own, the step STEP (none if empty) and the key KEY.
names_in() {
  python3 - "$@" <<'EOF'
import re, sys
out, job, step, key = sys.argv[1:5]
word = re.compile(r"(?<![\w-])%s(?![\w-])" % re.escape(job))
sys.exit(0 if any(word.search(l) and step in l and key in l for l in out.split("\n")) else 1)
EOF
}

# word_in OUT NAME: OUT holds NAME as a word of its own: no letter, digit, _
# or - before or after it.
word_in() {
  grep -qP "(?<![\\w-])\\Q$2\\E(?![\\w-])" <<<"$1"
}

# run_check SUB DIR: python3 tools/check_workflows.py SUB of the working tree,
# run in DIR; sets out and rc.
run_check() {
  out=$(cd "$2" && python3 "$REPO/tools/check_workflows.py" "$1" 2>&1); rc=$?
}

test_steps() {
  local c="$TMP/steps" ev=".github/workflows/evaluator.yml" out rc pick label
  # steps_case LABEL JOB STEP KEY ACTION ARGS...: the corruption ACTION of
  # evaluator.yml; the check must exit with 1 and name JOB, STEP and KEY.
  steps_case() {
    local label=$1 job=$2 step=$3 key=$4
    shift 4
    wf_copy "$c" || { miss "no copy of .github/workflows"; return; }
    edit_wf "$c/$ev" "$@" || { miss "$label: the corruption is not made"; return; }
    run_check steps "$c"
    if [ $rc -eq 1 ] && names_in "$out" "$job" "$step" "$key"; then
      caught "$label: exit 1, the job, the step and $key named"
    else
      miss "$label: exit $rc, output: $(tail -n 3 <<<"$out")"
    fi
  }
  steps_case "continue-on-error at the step of the manifest" check-conformance \
    "The manifest of the conformance suite matches the files" continue-on-error \
    step-key check-conformance "The manifest of the conformance suite matches the files" "continue-on-error: true"
  steps_case "\"continue-on-error\" as a quoted key at the check of the exported code" build-evaluator \
    "The committed code is the exported code" continue-on-error \
    step-key build-evaluator "The committed code is the exported code" '"continue-on-error": true'
  steps_case "if: false at the removal of the exported code" build-evaluator \
    "Remove the exported code before the export" "if:" \
    step-key build-evaluator "Remove the exported code before the export" "if: false"
  steps_case "the if: of test_ci61 G1 replaced by false" check-conformance "test_ci61 G1" "if:" \
    step-if check-conformance "test_ci61 G1" false
  steps_case "continue-on-error at the job check-scenarios" check-scenarios "" continue-on-error \
    job-key check-scenarios "continue-on-error: true"
  steps_case "the if: of the job evaluate replaced by success()" evaluate "" "if:" \
    job-if evaluate "success()"
  wf_copy "$c" && pick=$(edit_wf "$c/$ev" pick-step check-conformance) && [ -n "$pick" ] \
    || { miss "no step of check-conformance with a name and without if:"; pick=; }
  if [ -n "$pick" ]; then
    steps_case "if: \${{ !cancelled() }} at the step \"$pick\" of check-conformance" check-conformance "$pick" "if:" \
      step-key check-conformance "$pick" 'if: ${{ !cancelled() }}'
  fi
  for label in "not YAML" "empty"; do
    wf_copy "$c" || { miss "no copy of .github/workflows"; return; }
    if [ "$label" = "not YAML" ]; then printf 'jobs: [\n' > "$c/$ev"; else : > "$c/$ev"; fi
    run_check steps "$c"
    if [ $rc -eq 1 ] && grep -qF evaluator.yml <<<"$out"; then
      caught "evaluator.yml $label: exit 1, evaluator.yml named"
    else
      miss "evaluator.yml $label: exit $rc, output: $(tail -n 3 <<<"$out")"
    fi
  done
}

test_jobs() {
  local c="$TMP/jobs" w=".github/workflows" out rc
  # jobs_case LABEL NAMES SETUP...: SETUP run in the copy of
  # .github/workflows; the check must exit with 1 and name each of NAMES (a
  # list split at blanks) as a word of its own.
  jobs_case() {
    local label=$1 names=$2 n ok=1
    shift 2
    wf_copy "$c" || { miss "no copy of .github/workflows"; return; }
    "$@" || { miss "$label: the corruption is not made"; return; }
    run_check jobs "$c"
    for n in $names; do word_in "$out" "$n" || ok=0; done
    if [ $rc -eq 1 ] && [ $ok -eq 1 ]; then
      caught "$label: exit 1, $names named"
    else
      miss "$label: exit $rc, $names named: $ok, output: $(tail -n 3 <<<"$out")"
    fi
  }
  extra() {
    printf '%s\n' "name: Extra" "on:" "  push:" "    branches: [main, 'stage*']" "$3" "jobs:" "  $2:" \
      "    runs-on: ubuntu-24.04" "    steps:" "      - run: true" > "$c/$w/$1"
  }
  jobs_case "a second job build in extra.yml, on push with paths" build \
    extra extra.yml build "    paths: ['formal/**']"
  jobs_case "a second job evaluate in extra.yaml" evaluate \
    extra extra.yaml evaluate ""
  jobs_case "name: afp at the job parse" "afp parse" \
    edit_wf "$c/$w/parse-examples.yml" job-key parse "name: afp"
  jobs_case "paths at the push of parse-examples.yml" parse \
    edit_wf "$c/$w/parse-examples.yml" push-key "paths: ['parser/**']"
  jobs_case "if: at the job bench" bench \
    edit_wf "$c/$w/artifact.yml" job-key bench "if: github.ref_name == 'main'"
  jobs_case "the job afp-2026-lint renamed" afp-2026-lint \
    edit_wf "$c/$w/isabelle.yml" rename-job afp-2026-lint lint-of-the-copy
  wf_copy "$c" || { miss "no copy of .github/workflows"; return; }
  printf 'jobs: [\n' > "$c/$w/broken.yml"
  run_check jobs "$c"
  if [ $rc -eq 1 ] && grep -qF broken.yml <<<"$out"; then
    caught "a workflow file that is not YAML: exit 1, broken.yml named"
  else
    miss "a workflow file that is not YAML: exit $rc, output: $(tail -n 3 <<<"$out")"
  fi
}

"test_$1"
if [ $missed -ne 0 ]; then
  echo "not caught: $G"
  exit 1
fi
echo "$G: every corruption caught"
