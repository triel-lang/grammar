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
       Further, for each check of REQUIRED: its on.pull_request, if there is
       one with a value, is a mapping; a pattern of the branches of on.push
       that starts with ! is a problem unless it is exactly FINAL_ONLY (the
       image of the artifact is built on main and on the final branch of a
       stage, not on its working branches); its job, unless it is evaluate,
       has no needs (a job it waits for could be skipped, and the check with
       it). A key that differs from one of CASE_KEYS only in the case of its
       letters is a problem at the top level of every file, and in on,
       on.push, on.pull_request and the job of each check of REQUIRED: GitHub
       does not read it as that key.
order  In the job build-evaluator of evaluator.yml each of the steps of ORDER
       is there exactly once, in the order of ORDER (other steps may stand
       between them). The steps of EXPORT are there exactly once each, one
       right after the other in the order of EXPORT, and the sha256 of each,
       read as JSON (json.dumps with sort_keys, ensure_ascii=False and the
       separators "," and ":", as UTF-8), is the one of EXPORT_SHA256. The
       lines of artifact/run.sh that start with "step " are exactly the lines
       of RUN_STEPS, in that order, one right after the other. Each function
       of RUN_STEPS and the function step is defined in run.sh by a line
       "<function>() {" and nowhere else: the file holds exactly one
       definition of it, <function>(), <function> () or function <function>
       anywhere in a line after the start of the line, a blank, ;, &, |, (, {,
       a backquote or a quote, and that is its line "<function>() {". The
       sha256 of the lines of run.sh outside these sixteen functions (each
       from its line "<function>() {" to the next line "}"), joined by line
       breaks, as UTF-8, is RUN_OUTSIDE: no line between, before or after the
       steps changes what they do.

Every workflow file is read so that a key repeated in a mapping is a problem
of the file (YAML 1.1 reads on, On and true as one key, and PyYAML would keep
the last of them without a word). A file that cannot be read, is not YAML, is
empty or has no jobs is a problem too, not a file left out.

Exit code: 0 if the check passes (one line of summary); 1 with one line for
each problem found; 2 on a usage error or without PyYAML.
"""
import hashlib
import json
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
# The one pattern with ! that the branches of on.push of a required check may hold.
FINAL_ONLY = "!stage*-*"
# The keys that a key may not differ from only in case.
CASE_KEYS = ["on", "jobs", "push", "pull_request", "branches", "branches-ignore", "paths", "paths-ignore", "tags",
             "tags-ignore", "if", "continue-on-error", "strategy", "uses", "needs", "name"]
PUSH_KEYS_NOT_ALLOWED = ["paths", "paths-ignore", "branches-ignore", "tags", "tags-ignore"]
PR_KEYS_NOT_ALLOWED = ["paths", "paths-ignore"]
JOB_KEYS_NOT_ALLOWED = ["continue-on-error", "strategy", "uses"]
BRANCHES = ["main", "stage*"]

# The steps of the job build-evaluator of evaluator.yml, in their order: the
# exported code is removed, then exported, then compared with the commit.
ORDER_JOB = "build-evaluator"
ORDER = ["Remove the exported code before the export", "Build TRIEL_Core and export the evaluator",
         "The committed code is the exported code"]
# The four steps of the export, one right after the other, each pinned by the
# sha256 of its JSON.
EXPORT = ["Remove the exported code before the export", "Build TRIEL_Core and export the evaluator",
          "Post the exported code as commit comments when it differs", "The committed code is the exported code"]
EXPORT_SHA256 = {
    EXPORT[0]: "5e7fd16098620bc921c157eefae2e9816c7117dc369122f64c1ab326cc5bd1ad",
    EXPORT[1]: "190ea20bdc4622c18b6525fadb7019a98d4989489a44ec0c4e1fdfa365c27ed3",
    EXPORT[2]: "41652b5ce4fa46dbeb2ce1f5237da23c2df709d128aa3dca760b7dcba95e4317",
    EXPORT[3]: "49d2a2f5e43017a6395e73671cd9a60c62607a8090378e295fc79f10057e447d",
}

# The lines "step <label> <function>" of artifact/run.sh, in their order.
RUN_STEPS = [("01-no-sorry", "no_sorry"), ("02-isabelle-build", "isabelle_build"),
             ("03-exported-code", "exported_code"), ("04-build-evaluator", "build_evaluator"),
             ("05-classification", "classification"), ("06-scenarios", "scenarios"), ("07-pytest", "tests"),
             ("08-parse-examples", "parse_examples"), ("09-ambiguity-tests", "ambiguity_tests"),
             ("10-document-excerpts", "document_excerpts"), ("11-paper-theorems", "paper_theorems"),
             ("12-conformance", "conformance"), ("13-conformance-manifest", "conformance_manifest"),
             ("14-conformance-self-check", "conformance_self_check"), ("15-no-oracles", "no_oracles")]
# The functions of run.sh that the order pins: step and those of RUN_STEPS.
RUN_FUNCTIONS = ["step"] + [fn for _, fn in RUN_STEPS]
# The sha256 of the lines of run.sh outside the functions of RUN_FUNCTIONS.
RUN_OUTSIDE = "05807f0b364fa4384392e03cada6a9c4bfff2848ebdcff87f8fdb5485cb94bea"


class Repeated(Exception):
    """A key repeated in a mapping of a workflow file."""


def unique_loader():
    """A SafeLoader that raises Repeated on a key repeated in a mapping, as read by YAML 1.1."""
    class Loader(yaml.SafeLoader):
        pass

    def mapping(loader, node, deep=False):
        loader.flatten_mapping(node)
        lines = {}
        for key_node, _ in node.value:
            key = loader.construct_object(key_node, deep=deep)
            try:
                first = lines.get(key)
            except TypeError:
                continue
            line = key_node.start_mark.line + 1
            if first is not None:
                raise Repeated("the key %r of line %d repeats the key %r of line %d in one mapping"
                               % (key_node.value, line, first[1], first[0]))
            lines[key] = (line, key_node.value)
        return yaml.SafeLoader.construct_mapping(loader, node, deep=deep)

    Loader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, mapping)
    return Loader


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
        w = yaml.load(text, Loader=unique_loader())
    except Repeated as e:
        problems.append("%s: %s; YAML 1.1 reads on, On and true as one key, and only the last is read" % (path, e))
        return None
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


def case_keys(d, at, problems):
    """A key of the mapping d that differs from one of CASE_KEYS only in case; at names d."""
    if not isinstance(d, dict):
        return
    for k in d:
        if isinstance(k, str) and k not in CASE_KEYS and k.lower() in CASE_KEYS:
            problems.append("%s: the key %r differs from %s only in case, and is not read as it"
                            % (at, k, k.lower()))


def jobs():
    problems = []
    found, loaded = {}, {}
    for f in workflow_files(problems):
        w = load(f, problems)
        if w is None:
            continue
        loaded[f.name] = w
        case_keys(w, str(f), problems)
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
        at = "%s: %s" % (r, f.name)
        case_keys(on, at + " on", problems)
        if "push" not in on:
            problems.append("%s: %s does not run on push" % (r, f.name))
        else:
            push = on["push"] if isinstance(on["push"], dict) else {}
            case_keys(on["push"], at + " on.push", problems)
            for k in PUSH_KEYS_NOT_ALLOWED:
                if k in push:
                    problems.append("%s: on.push of %s has %s" % (r, f.name, k))
            branches = [str(b) for b in as_list(push.get("branches"))]
            missing = [b for b in BRANCHES if b not in branches]
            if missing:
                problems.append("%s: on.push.branches of %s is %r, without %s"
                                % (r, f.name, push.get("branches"), " and ".join(missing)))
            for b in branches:
                if b.startswith("!") and b != FINAL_ONLY:
                    problems.append("%s: on.push.branches of %s has %r; a pattern with ! leaves branches out, "
                                    "and only %r may" % (r, f.name, b, FINAL_ONLY))
        pr = on.get("pull_request")
        if pr is not None and not isinstance(pr, dict):
            problems.append("%s: on.pull_request of %s is %r, not a mapping" % (r, f.name, pr))
        if isinstance(pr, dict):
            case_keys(pr, at + " on.pull_request", problems)
            for k in PR_KEYS_NOT_ALLOWED:
                if k in pr:
                    problems.append("%s: on.pull_request of %s has %s" % (r, f.name, k))
        case_keys(j, "%s: the job %s of %s" % (r, key, f.name), problems)
        if "if" in j and j["if"] != "always()":
            problems.append("%s: the job %s of %s has if: %r" % (r, key, f.name, j["if"]))
        for k in JOB_KEYS_NOT_ALLOWED:
            if k in j:
                problems.append("%s: the job %s of %s has %s" % (r, key, f.name, k))
        if r != "evaluate" and "needs" in j:
            problems.append("%s: the job %s of %s has needs: %r; a required job other than evaluate waits for no "
                            "job" % (r, key, f.name, j["needs"]))
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
            export_steps(st, names, problems)
    text = read(RUN_SH, problems)
    if text is not None:
        run_sh(text.split("\n"), problems)
    return problems


def export_steps(st, names, problems):
    """The steps of EXPORT in st (names: their names), one after the other and each with its sha256."""
    at = {}
    for s in EXPORT:
        k = [i for i, n in enumerate(names) if n == s]
        if len(k) != 1:
            problems.append('%s: job %s, step "%s": there %d times; each step of the export is there once'
                            % (EVALUATOR, ORDER_JOB, s, len(k)))
        else:
            at[s] = k[0]
    if len(at) != len(EXPORT):
        return
    start = at[EXPORT[0]]
    for i, s in enumerate(EXPORT[1:], 1):
        if start + i >= len(names) or names[start + i] != s:
            there = names[start + i] if start + i < len(names) else None
            problems.append('%s: job %s, step "%s": it stands where "%s" belongs; the steps %s follow each other'
                            % (EVALUATOR, ORDER_JOB, there if there is not None else s, s,
                               ", ".join('"%s"' % e for e in EXPORT)))
            break
    for s in EXPORT:
        h = hashlib.sha256(json.dumps(st[at[s]], sort_keys=True, ensure_ascii=False,
                                      separators=(",", ":")).encode("utf-8")).hexdigest()
        if h != EXPORT_SHA256[s]:
            problems.append('%s: job %s, step "%s": the sha256 of the step is %s; the check pins %s'
                            % (EVALUATOR, ORDER_JOB, s, h, EXPORT_SHA256[s]))


def definitions(lines, fn):
    """The numbers of the lines of lines with a definition of the function fn of bash, a line once for each
    definition in it."""
    p = re.compile(r"""(?<![^ \t;&|({`"'])(function[ \t]+%s(?=[ \t({]|$)|%s[ \t]*\([ \t]*\))"""
                   % (re.escape(fn), re.escape(fn)))
    return [i + 1 for i, l in enumerate(lines) for _ in p.finditer(l)]


def outside(lines):
    """The sha256 of the lines outside the functions of RUN_FUNCTIONS, each from its line "<function>() {"
    to the next line "}"."""
    start = re.compile(r"(%s)\(\) \{(\s|$)" % "|".join(re.escape(fn) for fn in RUN_FUNCTIONS))
    kept, i = [], 0
    while i < len(lines):
        if start.match(lines[i]):
            i = next((k for k in range(i + 1, len(lines)) if lines[k].strip() == "}"), len(lines)) + 1
        else:
            kept.append(lines[i])
            i += 1
    return hashlib.sha256("\n".join(kept).encode("utf-8")).hexdigest()


def run_sh(lines, problems):
    """The lines step of run.sh, the definitions of its functions and its lines outside them."""
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
    at = [i for i, l in enumerate(lines) if re.match(r"step\s", l)]
    for i in range(1, len(at)):
        if at[i] != at[i - 1] + 1:
            fn = got[i][2] if len(got[i]) > 2 else ""
            problems.append("%s: the line %d, %s, does not follow the line step before it (line %d); the lines "
                            "step follow each other; function %s" % (RUN_SH, at[i] + 1, " ".join(got[i]),
                                                                     at[i - 1] + 1, fn))
            break
    label = dict((fn, label) for label, fn in RUN_STEPS)
    for fn in RUN_FUNCTIONS:
        of = "the function %s of the step %s" % (fn, label[fn]) if fn in label else "the function %s" % fn
        if not any(re.match(r"%s\(\) \{(\s|$)" % re.escape(fn), l) for l in lines):
            problems.append("%s: %s is not defined by a line %s() {" % (RUN_SH, of, fn))
        d = definitions(lines, fn)
        if len(d) > 1:
            problems.append("%s: %s() is defined %d times (lines %s); %s is defined once, by its line %s() {"
                            % (RUN_SH, fn, len(d), ", ".join(map(str, d)), of, fn))
    h = outside(lines)
    if h != RUN_OUTSIDE:
        problems.append("%s: the sha256 of the lines outside the %d functions is %s; the check pins %s"
                        % (RUN_SH, len(RUN_FUNCTIONS), h, RUN_OUTSIDE))


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
        print("each of the %d required checks is one job that runs on every push to main and stage* (a branch of "
              "%s left out only by %r)" % (len(REQUIRED), "stage*", FINAL_ONLY))
    else:
        print("%s: the %d steps of the export in order, one after the other, each as pinned; %s: the %d steps in "
              "order, one after the other, each function defined once, the lines outside them as pinned"
              % (EVALUATOR, len(EXPORT), RUN_SH, len(RUN_STEPS)))
    return 0


if __name__ == "__main__":
    try:
        import yaml
    except ImportError:
        print("error: PyYAML is needed (pip install pyyaml==6.0.3)", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1:]))
