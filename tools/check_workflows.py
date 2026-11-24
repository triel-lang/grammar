#!/usr/bin/env python3
# A check of the workflow files of CI, written for the acceptance of the tests of
# that check. Without flags it checks what tools/check_workflows.py checks; each
# flag in FLAGS leaves out one part of it.
#   steps: always-ok, text (continue-on-error found by its line only), parse-ok
#          (a file that is not YAML passes), no-job-level, no-if-value
#   jobs:  always-ok, exists-only, key-only, no-paths, no-job-if, yml-only,
#          broken-skip (a file that is not YAML is left out), dups-only
import re
import sys
from pathlib import Path

FLAGS = ['yml-only']
IF = {('build-evaluator', 'Download Isabelle'): "steps.cache-isabelle.outputs.cache-hit != 'true'", ('build-evaluator', 'Post the exported code as commit comments when it differs'): "startsWith(github.ref_name, 'stage')", ('evaluate', None): 'always()', ('check-conformance', 'test_ci61 G1'): '${{ !cancelled() }}', ('check-conformance', 'test_ci61 G2'): '${{ !cancelled() }}', ('check-conformance', 'test_ci61 G3'): '${{ !cancelled() }}', ('check-conformance', 'test_ci61 G4'): '${{ !cancelled() }}', ('check-conformance', 'test_ci61 G1 run.sh'): '${{ !cancelled() }}', ('check-conformance', 'test_ci61 G4 run.sh'): '${{ !cancelled() }}', ('check-conformance', 'test_ci61 steps'): '${{ !cancelled() }}', ('check-conformance', 'test_ci61 jobs'): '${{ !cancelled() }}', ('check-conformance', 'No step of evaluator.yml continues on error or is skipped unless named'): '${{ !cancelled() }}', ('check-conformance', 'Every required check is one job that runs on every branch'): '${{ !cancelled() }}'}
REQUIRED = ['parse', 'evaluate', 'build', 'build-log', 'afp', 'afp-2026', 'afp-2026-lint', 'artifact', 'anonymous-archive', 'bench']
WF = Path(".github/workflows")


def read(path, out, skip_broken):
    try:
        w = yaml.safe_load(path.read_text(encoding="utf-8"))
    except yaml.YAMLError as e:
        if not skip_broken:
            out.append("%s: not YAML: %s" % (path, " ".join(str(e).split())))
        return None
    except (OSError, UnicodeDecodeError) as e:
        out.append("%s: cannot be read: %s" % (path, e))
        return None
    if not isinstance(w, dict) or not isinstance(w.get("jobs"), dict) or not w["jobs"]:
        out.append("%s: no jobs" % path)
        return None
    return w


def check_if(out, key, value, at):
    if key not in IF:
        out.append("%s: if: %r is not in the list" % (at, value))
    elif "no-if-value" not in FLAGS and value != IF[key]:
        out.append("%s: if: %r, the list has %r" % (at, value, IF[key]))


def coe_by_lines(path):
    # continue-on-error found line by line: a key at the indentation of the keys
    # of a job is that of the job, any other that of the step named above it.
    out, job, step, in_jobs = [], None, None, False
    for line in path.read_text(encoding="utf-8").split("\n"):
        if re.match(r"^jobs:\s*$", line):
            in_jobs = True
            continue
        m = re.match(r"^  ([\w-]+):\s*$", line)
        if in_jobs and m:
            job, step = m.group(1), None
            continue
        m = re.match(r"^\s*- name:\s*(.*?)\s*$", line)
        if m:
            step = m.group(1).strip("'\"")
            continue
        m = re.match(r"^(\s*)continue-on-error\s*:", line)
        if m:
            if len(m.group(1)) == 4 or step is None:
                out.append("job %s: continue-on-error" % job)
            else:
                out.append('job %s, step "%s": continue-on-error' % (job, step))
    return out


def steps():
    out, seen = [], set()
    path = WF / "evaluator.yml"
    w = read(path, out, "parse-ok" in FLAGS)
    if w is None:
        return out
    for job, j in w["jobs"].items():
        j = j if isinstance(j, dict) else {}
        seen.add((job, None))
        if "no-job-level" not in FLAGS:
            if "continue-on-error" in j and "text" not in FLAGS:
                out.append("job %s: continue-on-error" % job)
            if "if" in j:
                check_if(out, (job, None), j["if"], "job %s" % job)
        for s in j.get("steps") or []:
            s = s if isinstance(s, dict) else {}
            n = s.get("name")
            seen.add((job, n))
            at = 'job %s, step "%s"' % (job, n) if n is not None else "job %s, a step without a name" % job
            if "continue-on-error" in s and "text" not in FLAGS:
                out.append("%s: continue-on-error" % at)
            if "if" in s:
                check_if(out, (job, n), s["if"], at)
    if "text" in FLAGS:
        out += coe_by_lines(path)
    for job, n in IF:
        if (job, n) not in seen:
            at = "job %s" % job if n is None else 'job %s, step "%s"' % (job, n)
            out.append("%s: if: is in the list, but not in the file" % at)
    return ["%s: %s" % (path, line) for line in out]


def events(w):
    on = w.get("on", w.get(True))
    if isinstance(on, str):
        return {on: None}
    if isinstance(on, list):
        return {e: None for e in on}
    return on if isinstance(on, dict) else {}


def jobs():
    out, found = [], {}
    files = sorted(WF.glob("*.yml"))
    if "yml-only" not in FLAGS:
        files += sorted(WF.glob("*.yaml"))
    if not files:
        out.append("%s: no workflow file" % WF)
    for f in files:
        w = read(f, out, "broken-skip" in FLAGS)
        if w is None:
            continue
        for k, j in w["jobs"].items():
            j = j if isinstance(j, dict) else {}
            n = k if "key-only" in FLAGS else str(j.get("name", k))
            found.setdefault(n, []).append((f, k, j, w))
    for r in REQUIRED:
        fs = found.get(r, [])
        if not fs:
            if "dups-only" not in FLAGS:
                out.append("%s: no job has this name" % r)
            continue
        if "exists-only" in FLAGS:
            continue
        if len(fs) > 1:
            out.append("%s: %d jobs have this name: %s" % (r, len(fs), ", ".join("%s:%s" % (f.name, k) for f, k, _, _ in fs)))
            continue
        f, k, j, w = fs[0]
        on = events(w)
        if "push" not in on:
            out.append("%s: %s does not run on push" % (r, f.name))
        else:
            push = on["push"] if isinstance(on["push"], dict) else {}
            pr = on.get("pull_request") if isinstance(on.get("pull_request"), dict) else {}
            keys = ["branches-ignore", "tags", "tags-ignore"] + ([] if "no-paths" in FLAGS else ["paths", "paths-ignore"])
            for key in keys:
                if key in push:
                    out.append("%s: on.push of %s has %s" % (r, f.name, key))
            if "no-paths" not in FLAGS:
                for key in ("paths", "paths-ignore"):
                    if key in pr:
                        out.append("%s: on.pull_request of %s has %s" % (r, f.name, key))
            if not {"main", "stage*"} <= set(push.get("branches") or []):
                out.append("%s: on.push.branches of %s is %r" % (r, f.name, push.get("branches")))
        if "if" in j and "no-job-if" not in FLAGS and j["if"] != "always()":
            out.append("%s: the job has if: %r" % (r, j["if"]))
        if "continue-on-error" in j:
            out.append("%s: the job has continue-on-error" % r)
        if isinstance(j.get("strategy"), dict) and "matrix" in j["strategy"]:
            out.append("%s: the job has a matrix" % r)
    return out


def main(argv):
    if len(argv) != 1 or argv[0] not in ("steps", "jobs"):
        print("usage: check_workflows.py steps|jobs", file=sys.stderr)
        return 2
    if "always-ok" in FLAGS:
        print("ok")
        return 0
    out = steps() if argv[0] == "steps" else jobs()
    for line in out:
        print("error: " + line)
    if not out:
        print("%s: ok" % argv[0])
    return 1 if out else 0


if __name__ == "__main__":
    try:
        import yaml
    except ImportError:
        print("error: PyYAML is needed", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1:]))
