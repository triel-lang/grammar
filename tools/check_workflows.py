#!/usr/bin/env python3
"""Checks of the workflow files of CI (.github/workflows of the current directory)
and of the order of the checks of the exported code and of artifact/run.sh.

Usage, from the root of the repository:
  python3 tools/check_workflows.py steps
  python3 tools/check_workflows.py jobs
  python3 tools/check_workflows.py order

steps  In evaluator.yml no job and no step has the key continue-on-error, with
       any value. The key if is at the jobs and steps of the list IF below
       only, with exactly the value listed there, and every entry of the list
       is in evaluator.yml with its if. A step is named by its job and its
       name:; a step without name: may not have if. No two steps of a job have
       the same name:, and no job or step has a key that differs from
       continue-on-error or if only in the case of its letters.
jobs   Each check in REQUIRED is the name of exactly one job of all the files
       of .github/workflows whose name ends in .yml or .yaml; the name of a job
       is its name:, without one its key. That job runs on every push to main
       and stage*: the branches of on.push hold main and stage* and no pattern
       that starts with !, and on.push has no paths, paths-ignore,
       branches-ignore, tags or tags-ignore; on.pull_request, if there is one,
       has no paths or paths-ignore. The job has no if other than always(), no
       continue-on-error, no strategy and no uses. The needs of the job
       evaluate of evaluator.yml are exactly the other jobs of that file, as
       the file lists them. Every job of every file has, if it has name:, a
       string that is not empty and holds no ${{; no job has a name that
       differs from a check of REQUIRED only in case or in blanks at its ends.
       A file whose name ends in .yml or .yaml with a capital letter is a
       problem, and is read as the others; so is a file with both the key on
       and the key "on" (YAML 1.1 reads the key on as true).
order  In the job build-evaluator of evaluator.yml each of the steps of ORDER
       is there exactly once, in the order of ORDER (other steps may stand
       between them). The lines of artifact/run.sh that start with "step " are
       exactly the lines of RUN_STEPS, in that order, and each function of
       RUN_STEPS is defined in run.sh by a line "<function>() {".

A file that cannot be read, is not YAML, is empty or has no jobs is a problem
too, not a file left out.

Exit code: 0 if the check passes (one line of summary); 1 with one line for
each problem found; 2 on a usage error or without PyYAML.
"""
import re
import sys
from pathlib import Path

WORKFLOWS = Path(".github/workflows")
EVALUATOR = WORKFLOWS / "evaluator.yml"
RUN_SH = Path("artifact/run.sh")
NOT_CANCELLED = "${{ !cancelled() }}"

# The if: that evaluator.yml may have, by (job, name of the step); a step of
# None is the job itself.
IF = {
    ("build-evaluator", "Download Isabelle"): "steps.cache-isabelle.outputs.cache-hit != 'true'",
    ("build-evaluator", "Post the exported code as commit comments when it differs"):
        "startsWith(github.ref_name, 'stage')",
    ("evaluate", None): "always()",
}
for name in ("test_ci61 G1", "test_ci61 G2", "test_ci61 G3", "test_ci61 G4", "test_ci61 G1 run.sh",
             "test_ci61 G4 run.sh", "test_ci61 steps", "test_ci61 jobs", "test_ci61 digit", "test_ci61 order",
             "test_ci61 download", "test_ci61 needs", "test_ci61 summary",
             "No step of evaluator.yml continues on error or is skipped unless named",
             "Every required check is one job that runs on every branch",
             "The checks of the export and of run.sh run in order"):
    IF[("check-conformance", name)] = NOT_CANCELLED

# The checks that the rule of the branch main requires.
REQUIRED = ["parse", "evaluate", "build", "build-log", "afp", "afp-2026", "afp-2026-lint",
            "artifact", "anonymous-archive", "bench"]
PUSH_KEYS_NOT_ALLOWED = ["paths", "paths-ignore", "branches-ignore", "tags", "tags-ignore"]
PR_KEYS_NOT_ALLOWED = ["paths", "paths-ignore"]
JOB_KEYS_NOT_ALLOWED = ["continue-on-error", "strategy", "uses"]
BRANCHES = ["main", "stage*"]

# The steps of the job build-evaluator of evaluator.yml, in their order: the
# exported code is removed, then exported, then compared with the commit.
ORDER_JOB = "build-evaluator"
ORDER = ["Remove the exported code before the export", "Build TRIEL_Core and export the evaluator",
         "The committed code is the exported code"]

# The lines "step <label> <function>" of artifact/run.sh, in their order.
RUN_STEPS = [("01-no-sorry", "no_sorry"), ("02-isabelle-build", "isabelle_build"),
             ("03-exported-code", "exported_code"), ("04-build-evaluator", "build_evaluator"),
             ("05-classification", "classification"), ("06-scenarios", "scenarios"), ("07-pytest", "tests"),
             ("08-parse-examples", "parse_examples"), ("09-ambiguity-tests", "ambiguity_tests"),
             ("10-document-excerpts", "document_excerpts"), ("11-paper-theorems", "paper_theorems"),
             ("12-conformance", "conformance"), ("13-conformance-manifest", "conformance_manifest"),
             ("14-conformance-self-check", "conformance_self_check"), ("15-no-oracles", "no_oracles")]


def read(path, problems):
    """The text of path, or None after a problem (it cannot be read or is empty)."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        problems.append("%s: cannot be read: %s" % (path, e))
        return None
    if not text.strip():
        problems.append("%s: empty" % path)
        return None
    return text


def load(path, problems):
    """The workflow in path as a mapping with jobs, or None after a problem."""
    text = read(path, problems)
    if text is None:
        return None
    try:
        w = yaml.safe_load(text)
    except yaml.YAMLError as e:
        problems.append("%s: not YAML: %s" % (path, " ".join(str(e).split())))
        return None
    if w is None:
        problems.append("%s: empty" % path)
        return None
    if not isinstance(w, dict) or not isinstance(w.get("jobs"), dict) or not w["jobs"]:
        problems.append("%s: no jobs" % path)
        return None
    return w


def where(job, step):
    return "job %s" % job if step is None else 'job %s, step "%s"' % (job, step)


def check_keys(problems, job, step, d, seen, at):
    """continue-on-error and if: of the job (step None) or of the step, as the mapping d; at names it."""
    for k in d:
        if str(k) != "continue-on-error" and str(k).lower() == "continue-on-error":
            problems.append("%s: %s: %r; a key that differs from continue-on-error only in case"
                            % (at, k, d[k]))
        if str(k) != "if" and str(k).lower() == "if":
            problems.append("%s: %s: %r; a key that differs from if only in case" % (at, k, d[k]))
    if "continue-on-error" in d:
        problems.append("%s: continue-on-error: %r; no job or step may have this key" % (at, d["continue-on-error"]))
    if "if" in d:
        if step is False:
            problems.append("%s: if: %r; a step without a name may not have if:" % (at, d["if"]))
        elif (job, step) not in IF:
            problems.append("%s: if: %r; only the jobs and steps of the list may have if:" % (at, d["if"]))
        elif d["if"] != IF[(job, step)]:
            problems.append("%s: if: %r; the list has if: %r" % (at, d["if"], IF[(job, step)]))
        else:
            seen.add((job, step))


def steps():
    problems = []
    w = load(EVALUATOR, problems)
    if w is None:
        return problems
    seen, present = set(), set()
    for job, j in w["jobs"].items():
        if not isinstance(j, dict):
            problems.append("%s: job %s is not a mapping" % (EVALUATOR, job))
            continue
        present.add((job, None))
        check_keys(problems, job, None, j, seen, where(job, None))
        st = j.get("steps") or []
        if not isinstance(st, list):
            problems.append("%s: job %s: steps is not a list" % (EVALUATOR, job))
            continue
        names = {}
        for i, s in enumerate(st):
            if not isinstance(s, dict):
                problems.append("%s: job %s: step %d is not a mapping" % (EVALUATOR, job, i + 1))
                continue
            name = s.get("name")
            if name is None:
                check_keys(problems, job, False, s, seen, "job %s, step %d without a name" % (job, i + 1))
                continue
            names.setdefault(str(name), []).append(i + 1)
            present.add((job, str(name)))
            check_keys(problems, job, str(name), s, seen, where(job, str(name)))
        for name, at in names.items():
            if len(at) > 1:
                problems.append("%s: name: the steps %s of the job have this name; a name is that of one step"
                                % (where(job, name), ", ".join(map(str, at))))
    for job, step in IF:
        if (job, step) not in present:
            problems.append("%s: if: is in the list of the check, but evaluator.yml has no such %s"
                            % (where(job, step), "job" if step is None else "step"))
        elif (job, step) not in seen:
            problems.append("%s: if: missing; the list has if: %r" % (where(job, step), IF[(job, step)]))
    return ["%s: %s" % (EVALUATOR, p) if not p.startswith(str(WORKFLOWS)) else p for p in problems]


def events(w):
    # YAML 1.1 reads the key on as True.
    on = w["on"] if "on" in w else w.get(True)
    if isinstance(on, str):
        return {on: None}
    if isinstance(on, list):
        return {e: None for e in on}
    return on if isinstance(on, dict) else {}


def as_list(v):
    if v is None:
        return []
    return [v] if isinstance(v, str) else list(v) if isinstance(v, list) else [v]


def workflow_files(problems):
    """The files of .github/workflows whose name ends in .yml or .yaml in any case."""
    files = sorted(p for p in WORKFLOWS.iterdir() if p.suffix.lower() in (".yml", ".yaml")) \
        if WORKFLOWS.is_dir() else []
    if not files:
        problems.append("%s: no workflow file" % WORKFLOWS)
    for f in files:
        if f.suffix not in (".yml", ".yaml"):
            problems.append("%s: the ending %s has a capital letter; a workflow file ends in .yml or .yaml"
                            % (f, f.suffix))
    return files


def jobs():
    problems = []
    found, loaded = {}, {}
    for f in workflow_files(problems):
        w = load(f, problems)
        if w is None:
            continue
        loaded[f.name] = w
        if "on" in w and True in w:
            problems.append('%s: both the key on and the key "on"; YAML 1.1 reads on: as true, and only one '
                            "of the two is read as the events" % f)
        for key, j in w["jobs"].items():
            j = j if isinstance(j, dict) else {}
            if "name" in j and not (isinstance(j["name"], str) and j["name"].strip() and "${{" not in j["name"]):
                problems.append("%s: job %s: name: %r; the name of a job is a string that is not empty and has "
                                "no ${{" % (f, key, j["name"]))
            name = str(j.get("name", key))
            for r in REQUIRED:
                if name != r and name.strip().lower() == r:
                    problems.append("%s: job %s: the name %r differs from a required check only in case or "
                                    "in blanks at its ends" % (f, key, name))
            found.setdefault(name, []).append((f, key, j, w))
    for r in REQUIRED:
        fs = found.get(r, [])
        if not fs:
            problems.append("%s: no job has this name" % r)
            continue
        if len(fs) > 1:
            problems.append("%s: %d jobs have this name: %s"
                            % (r, len(fs), ", ".join("%s job %s" % (f.name, k) for f, k, _, _ in fs)))
            continue
        f, key, j, w = fs[0]
        on = events(w)
        if "push" not in on:
            problems.append("%s: %s does not run on push" % (r, f.name))
        else:
            push = on["push"] if isinstance(on["push"], dict) else {}
            for k in PUSH_KEYS_NOT_ALLOWED:
                if k in push:
                    problems.append("%s: on.push of %s has %s" % (r, f.name, k))
            branches = [str(b) for b in as_list(push.get("branches"))]
            missing = [b for b in BRANCHES if b not in branches]
            if missing:
                problems.append("%s: on.push.branches of %s is %r, without %s"
                                % (r, f.name, push.get("branches"), " and ".join(missing)))
            for b in branches:
                if b.startswith("!"):
                    problems.append("%s: on.push.branches of %s has %r; a pattern with ! leaves branches out"
                                    % (r, f.name, b))
        pr = on.get("pull_request")
        if isinstance(pr, dict):
            for k in PR_KEYS_NOT_ALLOWED:
                if k in pr:
                    problems.append("%s: on.pull_request of %s has %s" % (r, f.name, k))
        if "if" in j and j["if"] != "always()":
            problems.append("%s: the job %s of %s has if: %r" % (r, key, f.name, j["if"]))
        for k in JOB_KEYS_NOT_ALLOWED:
            if k in j:
                problems.append("%s: the job %s of %s has %s" % (r, key, f.name, k))
    # The needs of evaluate: the other jobs of evaluator.yml, as the file lists them.
    w = loaded.get(EVALUATOR.name)
    e = w["jobs"].get("evaluate") if w else None
    if not isinstance(e, dict):
        problems.append("evaluate: %s has no job evaluate whose needs could be read" % EVALUATOR.name)
    else:
        needs = {str(n) for n in as_list(e.get("needs"))}
        others = {str(k) for k in w["jobs"] if k != "evaluate"}
        if needs != others:
            problems.append("evaluate: the needs of the job evaluate of %s are not the other jobs of the file: "
                            "missing %s, not a job %s" % (EVALUATOR.name, sorted(others - needs),
                                                          sorted(needs - others)))
    return problems


def order():
    problems = []
    w = load(EVALUATOR, problems)
    if w is not None:
        j = w["jobs"].get(ORDER_JOB)
        st = j.get("steps") if isinstance(j, dict) else None
        if not isinstance(st, list):
            problems.append("%s: job %s: no list of steps, so none of the steps %s"
                            % (EVALUATOR, ORDER_JOB, "; ".join('"%s"' % s for s in ORDER)))
        else:
            names = [str(s.get("name")) if isinstance(s, dict) and s.get("name") is not None else None for s in st]
            at = {}
            for s in ORDER:
                k = [i for i, n in enumerate(names) if n == s]
                if len(k) != 1:
                    problems.append('%s: job %s, step "%s": there %d times; the step is there once'
                                    % (EVALUATOR, ORDER_JOB, s, len(k)))
                else:
                    at[s] = k[0]
            if len(at) == len(ORDER) and [at[s] for s in ORDER] != sorted(at.values()):
                problems.append("%s: job %s: the steps are not in the order %s"
                                % (EVALUATOR, ORDER_JOB, ", then ".join('"%s"' % s for s in ORDER)))
    text = read(RUN_SH, problems)
    if text is not None:
        lines = text.split("\n")
        got = [l.split() for l in lines if re.match(r"step\s", l)]
        want = [["step", label, fn] for label, fn in RUN_STEPS]
        for i in range(max(len(got), len(want))):
            if i >= len(got):
                problems.append("%s: the line %d of the steps is missing; the order needs step %s %s there"
                                % (RUN_SH, i + 1, want[i][1], want[i][2]))
            elif i >= len(want):
                fn = got[i][2] if len(got[i]) > 2 else ""
                problems.append("%s: the line %d of the steps, %s, is one more than the %d of the order; function %s"
                                % (RUN_SH, i + 1, " ".join(got[i]), len(want), fn))
            elif got[i] != want[i]:
                problems.append("%s: the line %d of the steps is %s; the order needs step %s %s there"
                                % (RUN_SH, i + 1, " ".join(got[i]), want[i][1], want[i][2]))
        for label, fn in RUN_STEPS:
            if not any(re.match(r"%s\(\) \{(\s|$)" % re.escape(fn), l) for l in lines):
                problems.append("%s: the function %s of the step %s is not defined by a line %s() {"
                                % (RUN_SH, fn, label, fn))
    return problems


def main(argv):
    if len(argv) != 1 or argv[0] not in ("steps", "jobs", "order"):
        print("usage: python3 tools/check_workflows.py steps|jobs|order", file=sys.stderr)
        return 2
    problems = {"steps": steps, "jobs": jobs, "order": order}[argv[0]]()
    for p in problems:
        print("error: " + p)
    if problems:
        return 1
    if argv[0] == "steps":
        print("%s: no continue-on-error; if: at the %d jobs and steps of the list only, each with its value"
              % (EVALUATOR, len(IF)))
    elif argv[0] == "jobs":
        print("each of the %d required checks is one job that runs on every push to main and stage*" % len(REQUIRED))
    else:
        print("%s: the %d steps of the export in order; %s: the %d steps in order, each function defined"
              % (EVALUATOR, len(ORDER), RUN_SH, len(RUN_STEPS)))
    return 0


if __name__ == "__main__":
    try:
        import yaml
    except ImportError:
        print("error: PyYAML is needed (pip install pyyaml==6.0.3)", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1:]))
