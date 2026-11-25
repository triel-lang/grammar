#!/usr/bin/env python3
"""Checks of the workflow files of CI (.github/workflows of the current directory).

Usage, from the root of the repository:
  python3 tools/check_workflows.py steps
  python3 tools/check_workflows.py jobs

steps  In evaluator.yml no job and no step has the key continue-on-error, with
       any value. The key if is at the jobs and steps of the list IF below
       only, with exactly the value listed there, and every entry of the list
       is in evaluator.yml with its if. A step is named by its job and its
       name:; a step without name: may not have if.
jobs   Each check in REQUIRED is the name of exactly one job of all the files
       *.yml and *.yaml of .github/workflows; the name of a job is its name:,
       without one its key. That job runs on every push to main and stage*: the
       branches of on.push hold main and stage*, and on.push has no paths,
       paths-ignore, branches-ignore, tags or tags-ignore; on.pull_request, if
       there is one, has no paths or paths-ignore. The job has no if other than
       always(), no continue-on-error and no strategy.matrix.

A file that cannot be read, is not YAML, is empty or has no jobs is a problem
too, not a file left out.

Exit code: 0 if the check passes (one line of summary); 1 with one line for
each problem found; 2 on a usage error or without PyYAML.
"""
import sys
from pathlib import Path

WORKFLOWS = Path(".github/workflows")
EVALUATOR = WORKFLOWS / "evaluator.yml"
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
             "No step of evaluator.yml continues on error or is skipped unless named",
             "Every required check is one job that runs on every branch"):
    IF[("check-conformance", name)] = NOT_CANCELLED

# The checks that the rule of the branch main requires.
REQUIRED = ["parse", "evaluate", "build", "build-log", "afp", "afp-2026", "afp-2026-lint",
            "artifact", "anonymous-archive", "bench"]
PUSH_KEYS_NOT_ALLOWED = ["paths", "paths-ignore", "branches-ignore", "tags", "tags-ignore"]
PR_KEYS_NOT_ALLOWED = ["paths", "paths-ignore"]
BRANCHES = ["main", "stage*"]


def load(path, problems):
    """The workflow in path as a mapping with jobs, or None after a problem."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        problems.append("%s: cannot be read: %s" % (path, e))
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


def check_keys(problems, job, step, d, seen):
    """continue-on-error and if: of the job (step None) or of the step, as the mapping d."""
    if "continue-on-error" in d:
        problems.append("%s: continue-on-error: %r; no job or step may have this key"
                        % (where(job, step), d["continue-on-error"]))
    if "if" in d:
        if (job, step) not in IF:
            problems.append("%s: if: %r; only the jobs and steps of the list may have if:" % (where(job, step), d["if"]))
        elif d["if"] != IF[(job, step)]:
            problems.append("%s: if: %r; the list has if: %r" % (where(job, step), d["if"], IF[(job, step)]))
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
        check_keys(problems, job, None, j, seen)
        st = j.get("steps") or []
        if not isinstance(st, list):
            problems.append("%s: job %s: steps is not a list" % (EVALUATOR, job))
            continue
        for i, s in enumerate(st):
            if not isinstance(s, dict):
                problems.append("%s: job %s: step %d is not a mapping" % (EVALUATOR, job, i + 1))
                continue
            name = s.get("name")
            if name is None:
                if "continue-on-error" in s:
                    problems.append("job %s, step %d without a name: continue-on-error: %r; no job or step may have "
                                    "this key" % (job, i + 1, s["continue-on-error"]))
                if "if" in s:
                    problems.append("job %s, step %d without a name: if: %r; a step without a name may not have if:"
                                    % (job, i + 1, s["if"]))
                continue
            present.add((job, str(name)))
            check_keys(problems, job, str(name), s, seen)
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


def jobs():
    problems = []
    files = sorted(list(WORKFLOWS.glob("*.yml")) + list(WORKFLOWS.glob("*.yaml")))
    if not files:
        problems.append("%s: no workflow file" % WORKFLOWS)
    found = {}
    for f in files:
        w = load(f, problems)
        if w is None:
            continue
        for key, j in w["jobs"].items():
            j = j if isinstance(j, dict) else {}
            name = j.get("name", key)
            found.setdefault(str(name), []).append((f, key, j, w))
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
        pr = on.get("pull_request")
        if isinstance(pr, dict):
            for k in PR_KEYS_NOT_ALLOWED:
                if k in pr:
                    problems.append("%s: on.pull_request of %s has %s" % (r, f.name, k))
        if "if" in j and j["if"] != "always()":
            problems.append("%s: the job %s of %s has if: %r" % (r, key, f.name, j["if"]))
        if "continue-on-error" in j:
            problems.append("%s: the job %s of %s has continue-on-error" % (r, key, f.name))
        if isinstance(j.get("strategy"), dict) and "matrix" in j["strategy"]:
            problems.append("%s: the job %s of %s has strategy.matrix" % (r, key, f.name))
    return problems


def main(argv):
    if len(argv) != 1 or argv[0] not in ("steps", "jobs"):
        print("usage: python3 tools/check_workflows.py steps|jobs", file=sys.stderr)
        return 2
    problems = steps() if argv[0] == "steps" else jobs()
    for p in problems:
        print("error: " + p)
    if problems:
        return 1
    if argv[0] == "steps":
        print("%s: no continue-on-error; if: at the %d jobs and steps of the list only, each with its value"
              % (EVALUATOR, len(IF)))
    else:
        print("each of the %d required checks is one job that runs on every push to main and stage*" % len(REQUIRED))
    return 0


if __name__ == "__main__":
    try:
        import yaml
    except ImportError:
        print("error: PyYAML is needed (pip install pyyaml==6.0.3)", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1:]))
