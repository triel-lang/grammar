#!/usr/bin/env bash
# Tests of the checks of CI, each run on scratch copies that the check must
# reject (and, where named, on copies it must pass).
#
# Usage:
#   tools/test_ci61.sh g1|g2|g3|g4|g1run|g4run|steps|jobs|digit|order
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
#          holds .hs files" before isabelle is called. isabelle_build alone
#          must also fail before isabelle is called in a copy without
#          evaluator/generated; under a find of the test first on PATH that,
#          with -delete, runs the real find (the files are deleted) and exits
#          with 1; and under a find of the test that, without -delete, prints
#          nothing and exits with 1 (with -delete it runs the real find). SRC
#          never changes.
#   steps  python3 tools/check_workflows.py steps of the working tree, run in a
#          copy of .github/workflows of HEAD in which one corruption is made as
#          text: continue-on-error at a step (also as a quoted key) and at a
#          job, an if: at a step that may not have one, an if: of the list with
#          another value at a step and at a job, an if: at a step of
#          check-conformance chosen at random among those with a name and no
#          if:, a new step without a name with if: false and one with
#          continue-on-error: true in check-conformance, the step test_ci61 G3
#          removed, a second step test_ci61 G3 with its if:, the key
#          Continue-On-Error at the step test_ci61 G1, an evaluator.yml that is
#          not YAML and an empty one. The check must exit with 1 and print a line
#          that names the job, the step (for a step with a name) and the key as
#          written (continue-on-error, if:, Continue-On-Error; name for a
#          second step of the same name), or evaluator.yml.
#   jobs   python3 tools/check_workflows.py jobs, in the same way: a second job
#          build in a new extra.yml that runs on push with paths, a second job
#          evaluate in a new extra.yaml, name: afp at the job parse, paths at
#          the push of parse-examples.yml, an if: at the job bench, the job
#          afp-2026-lint renamed, a new workflow file that is not YAML;
#          paths-ignore at the push of parse-examples.yml, paths at the
#          pull_request of isabelle.yml, the branches of the push of
#          parse-examples.yml without stage* and with '!stagex*' added,
#          continue-on-error at the job bench, strategy at the job parse as a
#          mapping with matrix and as an expression, uses at the job artifact,
#          the needs of the job evaluate without check-scenarios, a new job
#          extra-check of evaluator.yml outside those needs, a second key "on"
#          at the end of parse-examples.yml, a new file extra.YML, and a new
#          extra.yml whose job has name: "", name: ${{ 'build' }} or
#          name: "build ". The check must exit with 1 and name each check
#          concerned as a word of its own (no letter, digit, _ or - next to it),
#          or the file.
#   digit  the search for sorry, oops and axiomatization in three places, each
#          run as CI or its script runs it, in a copy of HEAD: the step "Check
#          for sorry, oops and axiomatization" of the job build of
#          .github/workflows/isabelle.yml (bash -e -c), the function no_sorry of
#          artifact/run.sh (bash -u; the line goes into formal/core/*.thy and,
#          as cases of their own, into artifact/isabelle/*.thy), and the
#          function check of tools/make_afp_copy.sh with its line check "sorry,
#          oops or axiomatization", on an ENTRY with the theory and a ROOT. Each
#          must pass on the theories of HEAD and with the line
#          lemma sorry_free: "True" by simp added to a theory; with each of the
#          lines lemma "False" prefer 1sorry, lemma "False" prefer 1oops and
#          term 2axiomatization digit_c :: bool added, it must fail (exit code
#          not 0, or fail=1 for check) and print the line.
#   order  python3 tools/check_workflows.py order of the working tree, run in a
#          copy of .github/workflows and artifact/run.sh of HEAD with one
#          corruption: in the job build-evaluator of evaluator.yml the step
#          "The committed code is the exported code" moved before "Remove the
#          exported code before the export", the removal moved to the end of the
#          job, "Build TRIEL_Core and export the evaluator" moved before the
#          removal, a copy of the removal after the export; in run.sh the lines
#          step 02-... and step 03-... swapped, the line step 13-... removed, the
#          line step 03-... removed, the line "exported_code() {" renamed;
#          run.sh deleted; an empty evaluator.yml. The check must exit with 1
#          and print a line that names build-evaluator and the three steps
#          (build-evaluator and the step for the copy), run.sh and the function
#          the order needs at a place where it is broken (for a swap, at one of
#          the two places; for a removed line, at one of the places from it
#          on), or the file.
#
# The code of a step, a function or the check is read from the file that CI
# runs, in the working tree, by the name of the step (and its job), of the
# function or of the script; it is not copied here. The scratch copies are made
# from git archive HEAD. The test needs bash, git and python3 (no PyYAML), and
# reads no git configuration of the machine.
#
# Exit code: 0 if the check rejected every corrupted copy; otherwise 1 and the
# line "not caught: G1" (G2, G3, G4, G1RUN, G4RUN, STEPS, JOBS, DIGIT, ORDER); 2
# on a usage error.

set -uo pipefail

usage() { echo "usage: $0 g1|g2|g3|g4|g1run|g4run|steps|jobs|digit|order" >&2; exit 2; }
[ $# -eq 1 ] || usage
case $1 in g1|g2|g3|g4|g1run|g4run|steps|jobs|digit|order) ;; *) usage ;; esac
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
  step_run_in "$WORKFLOW" "$1" "$2"
}

# step_run_in FILE JOB NAME: the same for the workflow file FILE.
step_run_in() {
  python3 - "$1" "$2" "$3" <<'EOF'
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
  # The find of the test: with FIND_FAILS=delete, a call with -delete runs
  # the real find and exits with 1; with FIND_FAILS=list, a call without
  # -delete prints nothing and exits with 1; every other call is the real find.
  local real_find
  real_find=$(command -v find) && [ -n "$real_find" ] || { miss "no find on PATH"; return; }
  mkdir -p "$base/findbin" || { miss "no directory for the find of the test"; return; }
  cat > "$base/findbin/find" <<EOF
#!/bin/sh
case " \$* " in
  *" -delete "*)
    if [ "\$FIND_FAILS" = delete ]; then "$real_find" "\$@"; exit 1; fi ;;
  *)
    if [ "\$FIND_FAILS" = list ]; then exit 1; fi ;;
esac
exec "$real_find" "\$@"
EOF
  chmod +x "$base/findbin/find"
  # g4run_case NAME EXPORT CALL [FIND_FAILS]: CALL run in $base/NAME/work with
  # SRC $base/NAME/src, with the find of the test first on PATH if FIND_FAILS
  # is given; sets out, rc, called (yes or no) and src_kept (yes or no).
  g4run_case() {
    local d="$base/$1" path="$base/bin:$PATH"
    [ -n "${4:-}" ] && path="$base/findbin:$path"
    out=$(cd "$d/work" && PATH="$path" FIND_FAILS="${4:-}" SRC="$d/src" CALLS="$d/calls" EXPORT="$2" \
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
  # 5. No directory evaluator/generated in the working copy.
  g4run_copies nodir && g4run_keep nodir && rm -rf "$base/nodir/work/evaluator/generated" \
    || { miss "no copies"; return; }
  g4run_case nodir TRIEL.hs "isabelle_build"
  if [ $rc -ne 0 ] && [ $called = no ] && [ $src_kept = yes ]; then
    caught "no evaluator/generated: exit $rc, isabelle not called"
  else
    miss "no evaluator/generated: exit $rc, isabelle called: $called, SRC unchanged: $src_kept, output: $(tail -n 3 <<<"$out")"
  fi
  # 6. A find that deletes the files and exits with 1; 7. a find without
  # -delete that prints nothing and exits with 1.
  local mode
  for mode in delete list; do
    g4run_copies "find-$mode" && g4run_keep "find-$mode" || { miss "no copies"; return; }
    g4run_case "find-$mode" TRIEL.hs "isabelle_build" "$mode"
    if [ $rc -ne 0 ] && [ $called = no ] && [ $src_kept = yes ]; then
      caught "a find that fails ($mode): exit $rc, isabelle not called"
    else
      miss "a find that fails ($mode): exit $rc, isabelle called: $called, SRC unchanged: $src_kept, output: $(tail -n 3 <<<"$out")"
    fi
  done
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
#   pr-key LINE             LINE as a key of on.pull_request
#   rename-job JOB NEW      the key of the job JOB is NEW
#   pick-step JOB           print the name of a step of JOB with a name and
#                           without if:, chosen at random
#   add-step JOB AFTER LINE...  a new step of the lines LINE (the first starts
#                           with "- ", the others with two blanks) after the
#                           step AFTER of the job JOB, or at its end if AFTER
#                           is empty
#   del-step JOB STEP       the step STEP of the job JOB removed
#   move-step JOB STEP BEFORE  the step STEP moved before the step BEFORE, or
#                           to the end of the job if BEFORE is empty
#   copy-step JOB STEP AFTER  a copy of the step STEP after the step AFTER
#   branches-drop ITEM      ITEM removed from the list on.push.branches
#   branches-add ITEM       ITEM added at the end of that list
#   needs-drop JOB ITEM     ITEM removed from the list needs of the job JOB
#   add-job LINE...         the lines LINE right after the line jobs:
#   append LINE             LINE at the end of the file
#   swap-lines A B          the lines that start with A and with B swapped
#   del-line A              the line that starts with A removed
#   replace-line OLD NEW    the line OLD replaced by NEW
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
def trim(start, stop):
    # stop moved back over the blank lines and comments before the next code
    while stop > start + 1 and not code(lines[stop - 1]):
        stop -= 1
    return stop
def block(jname, sname):
    n, k, dash, stop = step(jname, sname)
    return k, trim(k, stop), dash
def job_end(name):
    j, end = job(name)
    return trim(j, end)
def event(name):
    o = one([k for k, l in enumerate(lines) if l == "on:"], "on:")
    p = one([k for k in range(o + 1, len(lines)) if lines[k] == "  %s:" % name
             and all(ind(lines[m]) > 0 or not code(lines[m]) for m in range(o + 1, k))], "on." + name)
    end = next((k for k in range(p + 1, len(lines)) if code(lines[k]) and ind(lines[k]) <= 2), len(lines))
    return p, end
def flow(m, key, add=None, drop=None):
    # the flow list [a, 'b', ...] of the line m, key: [...], changed
    head, value = lines[m].split(key + ":", 1)
    value = value.strip()
    if not (value.startswith("[") and value.endswith("]")):
        sys.exit("%s: the value of %s is not a list in brackets: %r" % (action, key, value))
    items = [i.strip() for i in value[1:-1].split(",") if i.strip()]
    if drop is not None:
        k = one([i for i, x in enumerate(items) if x.strip("'\"") == drop], "the item " + drop)
        del items[k]
    if add is not None:
        items.append(add)
    lines[m] = "%s%s: [%s]" % (head, key, ", ".join(items))
def remove(k, stop):
    del lines[k:stop]
    if 0 < k < len(lines) and not lines[k - 1].strip() and not lines[k].strip():
        del lines[k]
def at_start(prefix):
    return one([k for k, l in enumerate(lines) if l.startswith(prefix)], "a line starting with %r" % prefix)
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
    p, end = event("push")
    lines.insert(p + 1, "    " + args[0])
elif action == "pr-key":
    p, end = event("pull_request")
    lines.insert(p + 1, "    " + args[0])
elif action in ("branches-drop", "branches-add"):
    p, end = event("push")
    m = key_line(p + 1, end, 4, "branches")
    flow(m, "branches", **({"drop": args[0]} if action == "branches-drop" else {"add": args[0]}))
elif action == "needs-drop":
    j, end = job(args[0])
    flow(key_line(j + 1, end, 4, "needs"), "needs", drop=args[1])
elif action == "add-step":
    dash = steps_of(args[0])[0][2]
    at = block(args[0], args[1])[1] if args[1] else job_end(args[0])
    lines[at:at] = [""] + [" " * dash + l for l in args[2:]]
elif action == "del-step":
    k, stop, dash = block(args[0], args[1])
    remove(k, stop)
elif action == "move-step":
    k, stop, dash = block(args[0], args[1])
    moved = lines[k:stop]
    remove(k, stop)
    if args[2]:
        at = block(args[0], args[2])[0]
        lines[at:at] = moved + [""]
    else:
        at = job_end(args[0])
        lines[at:at] = [""] + moved
elif action == "copy-step":
    k, stop, dash = block(args[0], args[1])
    copied = lines[k:stop]
    at = block(args[0], args[2])[1]
    lines[at:at] = [""] + copied
elif action == "add-job":
    j = one([k for k, l in enumerate(lines) if l == "jobs:"], "jobs:")
    lines[j + 1:j + 1] = list(args) + [""]
elif action == "append":
    while lines and lines[-1] == "":
        lines.pop()
    lines += [args[0], ""]
elif action == "swap-lines":
    a, b = at_start(args[0]), at_start(args[1])
    lines[a], lines[b] = lines[b], lines[a]
elif action == "del-line":
    del lines[at_start(args[0])]
elif action == "replace-line":
    lines[one([k for k, l in enumerate(lines) if l == args[0]], "the line %r" % args[0])] = args[1]
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
  steps_case "a new step without a name with if: false in check-conformance" check-conformance "" "if:" \
    add-step check-conformance "" '- run: "true"' '  if: false'
  steps_case "a new step without a name with continue-on-error: true in check-conformance" check-conformance "" \
    continue-on-error add-step check-conformance "" '- run: "true"' '  continue-on-error: true'
  steps_case "the step test_ci61 G3 removed" check-conformance "test_ci61 G3" "if:" \
    del-step check-conformance "test_ci61 G3"
  steps_case "a second step test_ci61 G3 with its if:" check-conformance "test_ci61 G3" name \
    add-step check-conformance "test_ci61 G3" "- name: test_ci61 G3" '  if: ${{ !cancelled() }}' '  run: "true"'
  steps_case "the key Continue-On-Error at the step test_ci61 G1" check-conformance "test_ci61 G1" \
    Continue-On-Error step-key check-conformance "test_ci61 G1" "Continue-On-Error: true"
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
  # extra FILE JOB ON-LINE [JOB-LINE]: a new workflow file FILE with the job JOB.
  extra() {
    printf '%s\n' "name: Extra" "on:" "  push:" "    branches: [main, 'stage*']" "$3" "jobs:" "  $2:" "${4:-}" \
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
  jobs_case "paths-ignore at the push of parse-examples.yml" parse \
    edit_wf "$c/$w/parse-examples.yml" push-key "paths-ignore: ['docs/**']"
  jobs_case "paths at the pull_request of isabelle.yml" build \
    edit_wf "$c/$w/isabelle.yml" pr-key "paths: ['formal/**']"
  jobs_case "the branches of the push of parse-examples.yml without stage*" parse \
    edit_wf "$c/$w/parse-examples.yml" branches-drop "stage*"
  jobs_case "'!stagex*' in the branches of the push of parse-examples.yml" parse \
    edit_wf "$c/$w/parse-examples.yml" branches-add "'!stagex*'"
  jobs_case "continue-on-error at the job bench" bench \
    edit_wf "$c/$w/artifact.yml" job-key bench "continue-on-error: true"
  jobs_case "strategy with a matrix at the job parse" parse \
    edit_wf "$c/$w/parse-examples.yml" job-key parse "strategy: {matrix: {python: ['3.12']}}"
  jobs_case "strategy as an expression at the job parse" parse \
    edit_wf "$c/$w/parse-examples.yml" job-key parse 'strategy: ${{ fromJSON(vars.STRATEGY) }}'
  jobs_case "uses at the job artifact" artifact \
    edit_wf "$c/$w/artifact.yml" job-key artifact "uses: ./.github/workflows/extra.yml"
  jobs_case "the needs of the job evaluate without check-scenarios" evaluate \
    edit_wf "$c/$w/evaluator.yml" needs-drop evaluate check-scenarios
  jobs_case "a new job extra-check of evaluator.yml outside the needs of evaluate" evaluate \
    edit_wf "$c/$w/evaluator.yml" add-job "  extra-check:" "    runs-on: ubuntu-24.04" "    steps:" '      - run: "true"'
  jobs_case "a second key on at the end of parse-examples.yml" parse-examples.yml \
    edit_wf "$c/$w/parse-examples.yml" append "\"on\": {push: {branches: [main, 'stage*']}, pull_request: {branches: [main]}}"
  jobs_case "a new file extra.YML" extra.YML \
    extra extra.YML other ""
  jobs_case "name: \"\" at the job of a new extra.yml" extra.yml \
    extra extra.yml other "" '    name: ""'
  jobs_case "name: \${{ 'build' }} at the job of a new extra.yml" extra.yml \
    extra extra.yml other "" "    name: \${{ 'build' }}"
  jobs_case "name: \"build \" at the job of a new extra.yml" extra.yml \
    extra extra.yml other "" '    name: "build "'
  wf_copy "$c" || { miss "no copy of .github/workflows"; return; }
  printf 'jobs: [\n' > "$c/$w/broken.yml"
  run_check jobs "$c"
  if [ $rc -eq 1 ] && grep -qF broken.yml <<<"$out"; then
    caught "a workflow file that is not YAML: exit 1, broken.yml named"
  else
    miss "a workflow file that is not YAML: exit $rc, output: $(tail -n 3 <<<"$out")"
  fi
}

# line_with OUT SPEC...: a line of OUT holds every word of one SPEC, a list of
# words separated by |.
line_with() {
  python3 - "$@" <<'EOF'
import sys
out, specs = sys.argv[1], sys.argv[2:]
sys.exit(0 if any(all(w in l for w in s.split("|")) for s in specs for l in out.split("\n")) else 1)
EOF
}

test_order() {
  local c="$TMP/order" ev=".github/workflows/evaluator.yml" run="artifact/run.sh" out rc
  local rm_s="Remove the exported code before the export" ex_s="Build TRIEL_Core and export the evaluator"
  local ck_s="The committed code is the exported code"
  local all="build-evaluator|$rm_s|$ex_s|$ck_s"
  local -a want
  order_copy() {
    rm -rf "$c" && mkdir -p "$c" \
      && git -C "$REPO" archive --format=tar HEAD .github/workflows "$run" | tar -C "$c" -xf -
  }
  # order_case LABEL SETUP...: SETUP run in the copy; the check must exit with
  # 1 and print a line that holds every word of one of the lists in want.
  order_case() {
    local label=$1
    shift
    order_copy || { miss "no copy of .github/workflows and $run"; return; }
    "$@" || { miss "$label: the corruption is not made"; return; }
    run_check order "$c"
    if [ $rc -eq 1 ] && line_with "$out" "${want[@]}"; then
      caught "$label: exit 1, ${want[0]//|/, } named"
    else
      miss "$label: exit $rc, output: $(tail -n 3 <<<"$out")"
    fi
  }
  want=("$all")
  order_case "the check of the exported code before the removal" \
    edit_wf "$c/$ev" move-step build-evaluator "$ck_s" "$rm_s"
  order_case "the removal at the end of the job" \
    edit_wf "$c/$ev" move-step build-evaluator "$rm_s" ""
  order_case "the export before the removal" \
    edit_wf "$c/$ev" move-step build-evaluator "$ex_s" "$rm_s"
  want=("build-evaluator|$rm_s")
  order_case "a copy of the removal after the export" \
    edit_wf "$c/$ev" copy-step build-evaluator "$rm_s" "$ex_s"
  want=("run.sh|isabelle_build" "run.sh|exported_code")
  order_case "the lines step 02 and step 03 of run.sh swapped" \
    edit_wf "$c/$run" swap-lines "step 02-" "step 03-"
  # A line removed: the function that the order needs at one of the places
  # from the removed line on.
  local -a fns=(no_sorry isabelle_build exported_code build_evaluator classification scenarios tests
    parse_examples ambiguity_tests document_excerpts paper_theorems conformance conformance_manifest
    conformance_self_check no_oracles)
  local f
  want=()
  for f in "${fns[@]:12}"; do want+=("run.sh|$f"); done
  order_case "the line step 13 of run.sh removed" \
    edit_wf "$c/$run" del-line "step 13-"
  want=()
  for f in "${fns[@]:2}"; do want+=("run.sh|$f"); done
  order_case "the line step 03 of run.sh removed" \
    edit_wf "$c/$run" del-line "step 03-"
  want=("run.sh|exported_code")
  order_case "the function exported_code of run.sh not defined" \
    edit_wf "$c/$run" replace-line "exported_code() {" "exported_code_renamed() {"
  want=("run.sh")
  order_case "run.sh deleted" rm "$c/$run"
  want=("evaluator.yml")
  order_case "an empty evaluator.yml" truncate -s 0 "$c/$ev"
}

test_digit() {
  local step="Check for sorry, oops and axiomatization" c="$TMP/digit"
  local code fn_ns fn_ck line_ck n core art out rc line mech place
  local -a good=('lemma sorry_free: "True" by simp')
  local -a bad=('lemma "False" prefer 1sorry' 'lemma "False" prefer 1oops' 'term 2axiomatization digit_c :: bool')
  code=$(step_run_in "$REPO/.github/workflows/isabelle.yml" build "$step") \
    || { miss "the step \"$step\" was not found in isabelle.yml"; return; }
  fn_ns=$(fn_of "$REPO/artifact/run.sh" no_sorry)
  fn_ck=$(fn_of "$REPO/tools/make_afp_copy.sh" check)
  [ -n "$fn_ns" ] && [ -n "$fn_ck" ] \
    || { miss "no function no_sorry in artifact/run.sh or check in tools/make_afp_copy.sh"; return; }
  n=$(grep -c '^check "sorry, oops or axiomatization" ' "$REPO/tools/make_afp_copy.sh")
  [ "$n" = 1 ] || { miss "$n lines check \"sorry, oops or axiomatization\" in tools/make_afp_copy.sh"; return; }
  line_ck=$(grep '^check "sorry, oops or axiomatization" ' "$REPO/tools/make_afp_copy.sh")
  copy_of_head "$c/head" || { miss "no copy of HEAD"; return; }
  core=$(cd "$c/head" && ls formal/core/*.thy | head -n 1)
  art=$(cd "$c/head" && ls artifact/isabelle/*.thy | head -n 1)
  [ -n "$core" ] && [ -n "$art" ] || { miss "no theory in formal/core or artifact/isabelle"; return; }
  printf '%s\nno_sorry\n' "$fn_ns" > "$TMP/digit_no_sorry.sh"
  printf 'fail=0\n%s\n%s\necho "fail=$fail"\n' "$fn_ck" "$line_ck" > "$TMP/digit_check.sh"
  mkdir -p "$c/entry" "$c/cwd" && printf 'session A\n' > "$c/entry/ROOT" \
    && cp "$c/head/$core" "$c/entry/" || { miss "no entry for check"; return; }
  # digit_run MECH PLACE LINE: LINE (none if empty) added to the theory PLACE,
  # then the mechanism MECH run; sets out and rc (for check: 0 if fail=0, 1 if
  # fail=1, 2 otherwise). The theory is restored afterwards.
  digit_run() {
    local f
    if [ "$1" = check ]; then f="$c/entry/${core##*/}"; else f="$c/head/$2"; fi
    cp "$f" "$TMP/digit.thy" || return 1
    [ -z "$3" ] || printf '\n%s\n' "$3" >> "$f"
    case $1 in
      isabelle.yml) out=$(cd "$c/head" && bash -e -c "$code" 2>&1); rc=$? ;;
      no_sorry) out=$(cd "$c/head" && bash -u "$TMP/digit_no_sorry.sh" 2>&1); rc=$? ;;
      check)
        out=$(cd "$c/cwd" && ENTRY="$c/entry" bash "$TMP/digit_check.sh" 2>&1); rc=2
        grep -qx "fail=0" <<<"$out" && rc=0
        grep -qx "fail=1" <<<"$out" && rc=1 ;;
    esac
    cp "$TMP/digit.thy" "$f"
  }
  for mech in isabelle.yml no_sorry check; do
    for place in "$core" "$art"; do
      [ "$place" = "$art" ] && [ "$mech" != no_sorry ] && continue
      for line in "" "${good[@]}"; do
        digit_run "$mech" "$place" "$line"
        if [ $rc -eq 0 ]; then
          caught "$mech, $place ${line:-of HEAD}: passes"
        else
          miss "$mech, $place ${line:-of HEAD}: exit $rc, output: $(tail -n 3 <<<"$out")"
        fi
      done
      for line in "${bad[@]}"; do
        digit_run "$mech" "$place" "$line"
        if [ $rc -ne 0 ] && grep -qF -- "$line" <<<"$out"; then
          caught "$mech, $place with $line: exit $rc, the line printed"
        else
          miss "$mech, $place with $line: exit $rc, output: $(tail -n 3 <<<"$out")"
        fi
      done
    done
  done
}

"test_$1"
if [ $missed -ne 0 ]; then
  echo "not caught: $G"
  exit 1
fi
echo "$G: every corruption caught"
