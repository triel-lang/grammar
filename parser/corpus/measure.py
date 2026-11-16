#!/usr/bin/env python3
"""What the corpus of the translator catches and what it does not, in one command:

    python3 parser/corpus/measure.py

The output is markdown, in five sections:

  1. the corpus: the cases by origin and by outcome, the rules of the grammar in
     their parse trees, the reasons of rejection with and without a pair of cases;
  2. the deletion of every call of reject, one mutant per call;
  3. the coverage of the translator by statements and by branches, by the corpus
     and by the corpus together with parser/test_triel_to_core.py;
  4. 100 random first-order mutants of the translator;
  5. the time of each section.

--section N (1 to 4) computes one section alone; section 2 then also computes
the coverage it needs. Without arguments every section is computed.

TRIEL_TRANSLATOR names the translator to measure (default parser/triel_to_core.py
of this repository). Its grammar is the triel.lark next to it, and its tests are
the test_triel_to_core.py next to it, run in a temporary copy of the repository
that holds it (the parent of its directory). TRIEL_EVALUATOR names the evaluator
for those tests (default evaluator/triel-eval of this repository, if it is
built); without it, the tests that need it skip themselves.

Every temporary file, coverage data included, is written to a temporary
directory, which is removed at the end; nothing is written to the repository.
"""
import argparse
import ast
import gc
import io
import json
import os
import pickle
import random
import re
import select
import shutil
import signal
import struct
import subprocess
import sys
import tempfile
import time
from contextlib import redirect_stdout
from pathlib import Path

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
sys.path.insert(0, str(HERE))
import rejects  # noqa: E402

from lark import UnexpectedInput  # noqa: E402

TRANSLATOR = Path(os.environ.get("TRIEL_TRANSLATOR", REPO / "parser" / "triel_to_core.py")).resolve()
T_REPO = TRANSLATOR.parent.parent
EVALUATOR = os.environ.get("TRIEL_EVALUATOR", str(REPO / "evaluator" / "triel-eval"))
CASES = [json.loads(x) for x in (HERE / "cases.jsonl").read_text(encoding="utf-8").splitlines()]
CLASSES = json.loads((HERE / "classes.json").read_text(encoding="utf-8"))["reasons"]
UNREACHABLE = json.loads((HERE / "unreachable.json").read_text(encoding="utf-8"))
SOURCE = TRANSLATOR.read_text(encoding="utf-8")

# The functions of the module that translation calls, whose bodies are the
# places of the random mutants (section 4), besides the methods of Translation.
MUTATED_FUNCTIONS = ("sexp", "header", "referable", "unquote", "iso_seconds", "same_type", "kids",
                     "subtrees", "tokens", "leaves", "literal_text", "constraint_text", "ident")
# Functions whose lines the corpus does not need: printing, --actions,
# --classify and the command line.
NOT_NEEDED = ("pretty", "show_string", "show_number", "show_action", "monitored_actions", "classify",
              "actions_command", "main", "only")
SAMPLE = 100
SEED = 7

# Lines of the places of mutation that no input reaches, other than the calls
# of reject (those are in unreachable.json): the text of the line, stripped, in
# its function -> the argument.
UNREACHABLE_LINES = {
    ("Translation.conditional", "i += 1"):
        "Every alternative of matched_condition and unmatched_condition is a sequence of IF, ELIF or WHEN, each "
        "followed by expr, THEN and a branch, and ELSE followed by a branch, so the loop sees only those keywords.",
    ("referable.walk", "return w"):
        "A deadline, FROM, a handler or WITHIN ... ELSE inside a composite term is rejected before referable is "
        "called, so walk finds a reason only at the top of an element.",
}

# Random mutants that no input tells apart from the translator:
# (line, column, operator, variant) of the place -> the argument.
EQUIVALENT = {
    (282, 4, "statement", 0): "ident is called only on nodes that the grammar makes identifier nodes, so the "
                              "assertion never fails.",
    (343, 48, "constant", 0): "VERSION is followed only by version_literal, which no branch of declaration reads, "
                              "and every later subtree comes after a keyword of the list, which sets key again.",
    (387, 24, "constant", 1): "Every alternative of type_base but Optional (handled above) has exactly one "
                              "subtree, so [-1] is [0].",
    (498, 38, "constant", 1): "A stale_action has exactly one token, its keyword (the subject of ESCALATE_TO is a "
                              "subtree), so [-1] is [0].",
    (611, 8, "statement", 0): "A translation function returns None only after a reason was added, so the "
                              "specification is rejected and the term built with None is never printed.",
    (675, 27, "constant", 1): "u is a unary_expr, which has exactly one subtree, so [-1] is [0].",
    (739, 31, "constant", 2): "The line is unreachable (unreachable.json: value, call 3).",
    (777, 8, "statement", 0): "fb is None only after a reason was added; then operand_type is None or the type "
                              "of an inner fallback already rejected as \"DEFAULT fallback of another type\", so "
                              "the check below adds no other reason and no term is printed.",
    (846, 24, "constant", 1): "c is a matched_term or an unmatched_term, each with exactly one subtree, so [-1] "
                              "is [0].",
    (887, 15, "and/or", 0): "a and c are None only after a reason was added, so with one of them None the "
                            "specification is rejected anyway and no term is printed.",
    (1089, 28, "constant", 1): "The loop goes on only while x has exactly one subtree, so [-1] is [0].",
}

OUT = []


def say(s=""):
    OUT.append(s)
    print(s, flush=True)


# --- the translator, the parse trees ----------------------------------------------

def load_module():
    import importlib.util
    spec = importlib.util.spec_from_file_location("triel_to_core", TRANSLATOR)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class CachedParser:
    """The parser of the translator with every tree of the corpus parsed once.
    The garbage collector is off during a parse; then the garbage of the parse
    is collected and the trees kept are frozen (as in test_corpus.py)."""

    def __init__(self, parser):
        self.parser = parser
        self.trees = {}

    def parse(self, text):
        if text not in self.trees:
            gc.disable()
            try:
                self.trees[text] = self.parser.parse(text)
            except UnexpectedInput as e:
                self.trees[text] = e
            finally:
                gc.enable()
                gc.collect()
                gc.freeze()
        r = self.trees[text]
        if isinstance(r, UnexpectedInput):
            raise r
        return r


MOD = None
CACHED = None


def setup():
    global MOD, CACHED
    if MOD is None:
        MOD = load_module()
        CACHED = CachedParser(MOD.parser())
        for c in CASES:
            try:
                CACHED.parse(c["source"])
            except UnexpectedInput:
                pass
        MOD.parser = lambda: CACHED


def run_case(ns, src):
    """What the module ns gives for src: its outcome, term, header and reasons,
    printed by its own sexp and header."""
    try:
        tr = ns["translate"](src)
    except UnexpectedInput:
        return ("parse_error",)
    except Exception as e:  # noqa: BLE001
        return ("exception", type(e).__name__)
    try:
        if tr.rejected:
            return ("rejected", tuple(ns["header"](tr)), tuple(sorted(tr.rejected)))
        return ("accepted", ns["sexp"](tr.core), tuple(ns["header"](tr)))
    except Exception as e:  # noqa: BLE001
        return ("exception", type(e).__name__)


def namespace(code):
    ns = {"__name__": "triel_to_core", "__file__": str(TRANSLATOR)}
    exec(code, ns)
    ns["parser"] = lambda: CACHED
    return ns


BASE = None
BASE_TIME = None


def base_outputs():
    global BASE, BASE_TIME
    if BASE is None:
        setup()
        ns = vars(MOD)
        t = time.process_time()
        BASE = [run_case(ns, c["source"]) for c in CASES]
        BASE_TIME = time.process_time() - t
        bad = [c["id"] for c, o in zip(CASES, BASE) if o[0] == "exception"]
        if bad:
            raise SystemExit(f"the translator raises an exception on {bad}")
    return BASE


# --- running a mutant in a child process -------------------------------------------

def _send(fd, obj):
    b = pickle.dumps(obj)
    os.write(fd, struct.pack(">I", len(b)) + b)


def _child(code, w):
    try:
        ns = namespace(code)
    except BaseException as e:  # noqa: BLE001
        _send(w, ("load_error", repr(e)))
        os._exit(0)
    for i, c in enumerate(CASES):
        _send(w, (i, run_case(ns, c["source"])))
    _send(w, ("done",))
    os._exit(0)


def run_mutant(code, limit):
    """The outputs of the mutant on the cases it finished, and whether it ran
    out of time (limit, in seconds of wall time)."""
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        try:
            _child(code, w)
        finally:
            os._exit(1)
    os.close(w)
    out = {}
    buf = b""
    deadline = time.monotonic() + limit
    timed_out = False
    finished = False
    with os.fdopen(r, "rb", buffering=0) as f:
        while True:
            left = deadline - time.monotonic()
            if left <= 0:
                timed_out = True
                break
            ready, _, _ = select.select([f], [], [], left)
            if not ready:
                continue
            chunk = f.read(1 << 16)
            if not chunk:
                break
            buf += chunk
            while len(buf) >= 4:
                n = struct.unpack(">I", buf[:4])[0]
                if len(buf) < 4 + n:
                    break
                msg = pickle.loads(buf[4:4 + n])
                buf = buf[4 + n:]
                if msg[0] == "load_error":
                    raise SystemExit(f"a mutant does not load: {msg[1]}")
                if msg[0] == "done":
                    finished = True
                else:
                    out[msg[0]] = msg[1]
            if finished:
                break
    if timed_out:
        os.kill(pid, signal.SIGKILL)
    os.waitpid(pid, 0)
    if not timed_out and not finished:
        raise SystemExit("a mutant died without an answer")
    return out, timed_out


def limit():
    return max(10 * BASE_TIME, 10.0)


def verdict(code):
    """caught (divergence), caught (exceptions only), caught (time) or not caught,
    and the ids of the cases on which the output differs."""
    base = base_outputs()
    lim = limit()
    for attempt in (1, 2):
        out, timed_out = run_mutant(code, lim)
        diff = [i for i in sorted(out) if out[i] != base[i]]
        ids = [CASES[i]["id"] for i in diff]
        if any(out[i][0] != "exception" for i in diff):
            return "caught (divergence)", ids
        if diff:
            return "caught (exceptions only)", ids
        if not timed_out:
            return "not caught", []
        lim *= 10  # out of time with no difference so far: once more, with ten times the limit
    return "caught (time)", []


# --- section 1: the corpus ---------------------------------------------------------

def rules_of_tree(t):
    return set() if t is None or isinstance(t, UnexpectedInput) else {s.data for s in t.iter_subtrees()}


def pairs_of_reasons():
    by_id = {c["id"]: c for c in CASES}
    with_pair, without = [], []
    for reason in sorted(rejects.reasons(SOURCE)):
        ok = any(c["outcome"] == "rejected" and c.get("single_defect") and c["reasons"] == [reason]
                 and "pair" in c and by_id[c["pair"]]["outcome"] == "accepted" for c in CASES)
        (with_pair if ok else without).append(reason)
    return with_pair, without


def section_corpus():
    setup()
    say("## 1. Corpus")
    say()
    origin = {"moved": 0, "new": 0}
    outcome = {"accepted": 0, "rejected": 0, "parse_error": 0}
    for c in CASES:
        origin["new" if c["origin"] == "new" else "moved"] += 1
        outcome[c["outcome"]] += 1
    say(f"- cases: {len(CASES)}; by origin: moved from test_triel_to_core.py {origin['moved']}, "
        f"new {origin['new']}; by outcome: accepted {outcome['accepted']}, rejected {outcome['rejected']}, "
        f"parse_error {outcome['parse_error']}")
    grammar = re.findall(r"^([a-z_][a-z0-9_]*)\s*:", (TRANSLATOR.parent / "triel.lark").read_text(encoding="utf-8"),
                         flags=re.M)
    seen = set()
    for c in CASES:
        seen |= rules_of_tree(CACHED.trees.get(c["source"]))
    missing = [r for r in grammar if r not in seen]
    say(f"- rules of triel.lark in the parse trees: {len(grammar) - len(missing)} of {len(grammar)}"
        + (f"; missing: {', '.join(missing)}" if missing else ""))
    with_pair, without = pairs_of_reasons()
    say(f"- reasons by the static enumeration: {len(with_pair) + len(without)}; with a pair: "
        f"{len(with_pair)}; without a pair: {len(without)}" + (f" ({'; '.join(without)})" if without else ""))
    say()


# --- section 2: deletion of the calls of reject -------------------------------------

def _parents(tree):
    p = {}
    for n in ast.walk(tree):
        for ch in ast.iter_child_nodes(n):
            p[ch] = n
    return p


def _find_call(tree, call):
    for n in ast.walk(tree):
        if (isinstance(n, ast.Call) and n.lineno == call["line"] and n.col_offset == call["col"]
                and isinstance(n.func, ast.Attribute) and n.func.attr == "reject"):
            return n
    raise LookupError(call)


def _remove_statement(tree, parents, stmt):
    holder = parents[stmt]
    for field in ("body", "orelse", "finalbody", "handlers"):
        seq = getattr(holder, field, None)
        if isinstance(seq, list) and stmt in seq:
            seq.remove(stmt)
            if not seq and field != "orelse" and field != "finalbody":
                seq.append(ast.Pass())
            return
    raise LookupError("statement not found in its parent")


def deletion_code(call):
    tree = ast.parse(SOURCE)
    parents = _parents(tree)
    node = _find_call(tree, call)
    if call["statement"]:
        _remove_statement(tree, parents, parents[node])
    else:
        holder = parents[node]
        for field, value in ast.iter_fields(holder):
            if value is node:
                setattr(holder, field, ast.Constant(None))
                break
            if isinstance(value, list) and node in value:
                value[value.index(node)] = ast.Constant(None)
                break
        else:
            raise LookupError("call not found in its parent")
    ast.fix_missing_locations(tree)
    return compile(tree, str(TRANSLATOR), "exec")


class _Hits(ast.NodeTransformer):
    """self.reject(ARG) -> self.reject(__hit__(K, ARG)), K the position of the call."""

    def visit_Call(self, node):
        self.generic_visit(node)
        if (isinstance(node.func, ast.Attribute) and node.func.attr == "reject"
                and isinstance(node.func.value, ast.Name) and node.func.value.id == "self"):
            key = ast.Constant((node.lineno, node.col_offset))
            node.args = [ast.Call(ast.Name("__hit__", ast.Load()), [key, node.args[0]], [])]
        return node


def hits_by_source(sources):
    """For every source, the positions (line, col) of the calls of reject it executes."""
    setup()
    tree = _Hits().visit(ast.parse(SOURCE))
    ast.fix_missing_locations(tree)
    code = compile(tree, str(TRANSLATOR), "exec")
    hit = set()
    ns = {"__name__": "triel_to_core", "__file__": str(TRANSLATOR),
          "__hit__": lambda k, a: (hit.add(k), a)[1]}
    exec(code, ns)
    ns["parser"] = lambda: CACHED
    out = {}
    for s in sources:
        hit.clear()
        reasons = run_case(ns, s)
        out[s] = (set(hit), reasons)
    return out


def section_rejects(coverage_lines):
    base_outputs()
    say("## 2. Deletion of the calls of reject")
    say()
    calls = rejects.calls(SOURCE)
    null = compile(ast.parse(SOURCE), str(TRANSLATOR), "exec")
    out, timed_out = run_mutant(null, max(100 * BASE_TIME, 100.0))
    if timed_out or [i for i in range(len(CASES)) if out.get(i) != BASE[i]]:
        raise SystemExit("the null mutant (the translator parsed and compiled again) differs from the translator")
    say(f"- null mutant: the same output as the translator on all {len(CASES)} cases")
    say(f"- time of the translator on the corpus (parse trees cached): {BASE_TIME:.2f} s; "
        f"limit of a mutant: {limit():.1f} s, then x10")
    entries = {(u["function"], u["index"]): u for u in UNREACHABLE}
    pos = {(c["function"], c["index"]): c for c in calls}
    errors = []
    for k, u in entries.items():
        if k not in pos:
            errors.append(f"unreachable.json: no call {k[1]} in {k[0]}")
        elif rejects_reason(pos[k]) != u["reason"]:
            errors.append(f"unreachable.json: call {k[1]} of {k[0]} gives {rejects_reason(pos[k])!r}, not {u['reason']!r}")
    case_hits = hits_by_source([c["source"] for c in CASES])
    inputs = hits_by_source([u["input"] for u in UNREACHABLE])
    results = []
    for c in calls:
        key = (c["function"], c["index"])
        v, ids = verdict(deletion_code(c))
        u = entries.get(key)
        p = (c["line"], c["col"])
        if u is not None:
            if v != "not caught":
                errors.append(f"{key}: listed as {u['kind']} in unreachable.json, but the mutant is {v} on {ids[:5]}")
            if u["kind"] == "unreachable":
                if c["line"] in coverage_lines:
                    errors.append(f"{key}: listed as unreachable, but its line {c['line']} is executed")
                if p in inputs[u["input"]][0]:
                    errors.append(f"{key}: listed as unreachable, but its input reaches it")
                v = "unreachable"
            else:
                o = pos.get((u["other"]["function"], u["other"]["index"]))
                q = (o["line"], o["col"]) if o else None
                if q is None or not {p, q} <= inputs[u["input"]][0]:
                    errors.append(f"{key}: on its input the two calls are not both executed")
                if u["input"] not in {cc["source"] for cc in CASES}:
                    errors.append(f"{key}: its input is not a case of the corpus")
                for cc in CASES:
                    h = case_hits[cc["source"]][0]
                    if p in h and q not in h:
                        errors.append(f"{key}: on {cc['id']} it is executed and the other call is not")
                v = "redundant"
        results.append((c, v, ids))
    names = ["caught (divergence)", "caught (exceptions only)", "caught (time)", "not caught", "redundant",
             "unreachable"]
    say(f"- calls of reject: {len(calls)} ({sum(c['statement'] for c in calls)} statements, "
        f"{sum(not c['statement'] for c in calls)} inside expressions)")
    for n in names:
        say(f"- {n}: {sum(v == n for _, v, _ in results)}")
    for u in UNREACHABLE:
        if u["kind"] == "unreachable":
            hit, out = inputs[u["input"]]
            say(f"- input of the unreachable call {u['index']} of {u['function']}: "
                f"{out[0]}{' ' + str(list(out[2])) if out[0] == 'rejected' else ''}")
    say()
    say("| line | function | call | reason | statement | result | first cases that differ |")
    say("|---|---|---|---|---|---|---|")
    for c, v, ids in results:
        say(f"| {c['line']} | {c['function']} | {c['index']} | {rejects_reason(c)} | "
            f"{'yes' if c['statement'] else 'no'} | {v} | {', '.join(ids[:3])}{' …' if len(ids) > 3 else ''} |")
    say()
    if errors:
        say("Errors in unreachable.json:")
        for e in errors:
            say(f"- {e}")
        say()
    return results, errors


def rejects_reason(call):
    return call["value"] if call["kind"] == "str" else call["arg"]


# --- section 3: coverage ------------------------------------------------------------------

def _copy_repo(dest):
    """A copy of the repository that holds the translator, without .git and
    built files, with the translator in place."""
    ignore = shutil.ignore_patterns(".git", "__pycache__", ".pytest_cache", "build", "triel-eval", "output",
                                    "*.pyc", ".coverage*")
    shutil.copytree(T_REPO, dest, ignore=ignore, symlinks=True)
    shutil.copy2(TRANSLATOR, dest / "parser" / "triel_to_core.py")
    return dest


def _env(extra=None):
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env.pop("COVERAGE_PROCESS_START", None)
    if extra:
        env.update(extra)
    return env


def corpus_runner():
    """--translate-corpus PATH: translate every case with the translator at PATH
    and print its term and header as test_corpus.py does (run under coverage)."""
    import importlib.util
    path = Path(sys.argv[2])
    spec = importlib.util.spec_from_file_location("triel_to_core", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    mod.parser()
    for c in CASES:
        gc.disable()
        try:
            tr = mod.translate(c["source"])
            mod.header(tr)
            if not tr.rejected:
                mod.sexp(tr.core)
        except UnexpectedInput:
            pass
        finally:
            gc.enable()
            gc.collect()
    return 0


COVERAGE = None


def coverage_data(tmp):
    """Coverage of the translator by the corpus, and by the corpus with
    test_triel_to_core.py: the two JSON reports of coverage."""
    global COVERAGE
    if COVERAGE is not None:
        return COVERAGE
    copy = _copy_repo(tmp / "repo")
    target = copy / "parser" / "triel_to_core.py"
    rc = tmp / "coveragerc"
    rc.write_text(f"[run]\nbranch = True\npatch = subprocess\nparallel = True\n"
                  f"data_file = {tmp / 'cov' / '.coverage'}\ninclude = {target}\n", encoding="utf-8")
    (tmp / "cov").mkdir()
    ev = {"TRIEL_EVALUATOR": EVALUATOR}
    subprocess.run([sys.executable, "-m", "coverage", "run", f"--rcfile={rc}", str(Path(__file__).resolve()),
                    "--translate-corpus", str(target)], cwd=copy, env=_env(), check=True)
    corpus_files = sorted((tmp / "cov").glob(".coverage*"))
    t = time.monotonic()
    r = subprocess.run([sys.executable, "-m", "coverage", "run", f"--rcfile={rc}", "-m", "pytest", "-q",
                        "-p", "no:cacheprovider", "parser/test_triel_to_core.py"],
                       cwd=copy, env=_env(ev), capture_output=True, text=True)
    tests_time = time.monotonic() - t
    tests_summary = without_time(r.stdout.strip().splitlines()[-1]) if r.stdout.strip() else r.stderr[-300:]
    all_files = sorted((tmp / "cov").glob(".coverage*"))
    test_files = [f for f in all_files if f not in corpus_files]
    reports = {}
    import coverage
    for name, files in (("corpus", corpus_files), ("corpus and tests", corpus_files + test_files)):
        cov = coverage.Coverage(config_file=False, branch=True,
                                data_file=str(tmp / f"{name.replace(' ', '_')}.data"))
        cov.combine([str(f) for f in files], keep=True)
        out = tmp / f"{name.replace(' ', '_')}.json"
        with redirect_stdout(io.StringIO()):
            cov.json_report(outfile=str(out), include=[str(target)])
        rep = json.loads(out.read_text(encoding="utf-8"))
        reports[name] = list(rep["files"].values())[0]
    COVERAGE = {"reports": reports, "tests": tests_summary, "tests_time": tests_time,
                "tests_ok": r.returncode == 0}
    return COVERAGE


def _function_of_line():
    """line -> the dotted name of the innermost function or class that holds it."""
    owner = {}

    def walk(node, prefix):
        for ch in ast.iter_child_nodes(node):
            if isinstance(ch, (ast.FunctionDef, ast.ClassDef)):
                name = f"{prefix}.{ch.name}" if prefix else ch.name
                for ln in range(ch.lineno, ch.end_lineno + 1):
                    owner[ln] = name
                walk(ch, name)
            else:
                walk(ch, prefix)
    walk(ast.parse(SOURCE), "")
    return owner


def mutation_site(fn):
    """Whether the function (dotted name from _function_of_line) is a place of
    the random mutants: a method of Translation, or a function of
    MUTATED_FUNCTIONS (with the functions nested in it)."""
    if fn is None:
        return False
    parts = fn.split(".")
    if parts[0] == "Translation":
        return len(parts) > 1
    return parts[0] in MUTATED_FUNCTIONS


def section_coverage(tmp):
    say("## 3. Coverage of the translator")
    say()
    data = coverage_data(tmp)
    lines = SOURCE.splitlines()
    owner = _function_of_line()
    unreach_calls = {(u["function"], u["index"]) for u in UNREACHABLE if u["kind"] == "unreachable"}
    calls = rejects.calls(SOURCE)
    call_lines = {c["line"]: (c["function"], c["index"]) for c in calls}
    say(f"- test_triel_to_core.py under coverage: {data['tests']} "
        f"(evaluator: {'built, ' + EVALUATOR if os.path.exists(EVALUATOR) else 'not built'})")
    for name, rep in data["reports"].items():
        s = rep["summary"]
        say(f"- {name}: statements {s['covered_lines']} of {s['num_statements']} "
            f"({100 * s['covered_lines'] / s['num_statements']:.1f}%), branches {s['covered_branches']} of "
            f"{s['num_branches']} ({100 * s['covered_branches'] / max(1, s['num_branches']):.1f}%)")
    say()
    for name, rep in data["reports"].items():
        missing = rep["missing_lines"]
        say(f"Lines not executed by the {name} ({len(missing)}):")
        say()
        counts = {"not needed by the corpus": 0, "unreachable": 0, "gap": 0}
        rows = []
        for ln in missing:
            fn = owner.get(ln)
            text = lines[ln - 1].strip()
            if not mutation_site(fn):
                why = "not needed by the corpus"
                arg = ""
            elif ln in call_lines and call_lines[ln] in unreach_calls:
                why = "unreachable"
                arg = "unreachable.json"
            elif ln not in call_lines and (fn, text) in UNREACHABLE_LINES:
                why = "unreachable"
                arg = UNREACHABLE_LINES[(fn, text)]
            else:
                why = "gap"
                arg = ""
            counts[why] += 1
            rows.append((ln, fn, why, arg, text))
        say("- " + ", ".join(f"{k}: {v}" for k, v in counts.items()))
        say()
        say("| line | function | why | argument | code |")
        say("|---|---|---|---|---|")
        for ln, fn, why, arg, text in rows:
            code = text[:70].replace("|", "\\|")
            say(f"| {ln} | {fn} | {why} | {arg} | `{code}` |")
        say()
        mb = rep.get("missing_branches", [])
        say(f"Branches not taken by the {name} ({len(mb)}): "
            + ", ".join(f"{a}->{b}" for a, b in mb))
        say()
    return data


# --- section 4: random mutants ---------------------------------------------------------------

CMP_SWAP = {ast.Eq: ast.NotEq, ast.NotEq: ast.Eq, ast.Lt: ast.LtE, ast.LtE: ast.Lt, ast.Gt: ast.GtE,
            ast.GtE: ast.Gt, ast.In: ast.NotIn, ast.NotIn: ast.In, ast.Is: ast.IsNot, ast.IsNot: ast.Is}


def _site_roots(tree):
    roots = []
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.name == "Translation":
            roots += [m for m in node.body if isinstance(m, ast.FunctionDef)]
        elif isinstance(node, ast.FunctionDef) and node.name in MUTATED_FUNCTIONS:
            roots.append(node)
    return roots


def _docstrings(roots):
    out = set()
    for f in roots:
        for n in ast.walk(f):
            if isinstance(n, ast.FunctionDef) and n.body and isinstance(n.body[0], ast.Expr) and isinstance(n.body[0].value, ast.Constant) \
                    and isinstance(n.body[0].value.value, str):
                out.add(id(n.body[0]))
                out.add(id(n.body[0].value))
    return out


def _is_reject_stmt(stmt):
    """A statement whose value is a call of reject: deleting it is a mutant of section 2."""
    v = getattr(stmt, "value", None)
    return (isinstance(stmt, (ast.Expr, ast.Return, ast.Assign)) and isinstance(v, ast.Call)
            and isinstance(v.func, ast.Attribute) and v.func.attr == "reject")


def places():
    """Every place of a random mutant: (line, col, operator, variant, description)."""
    tree = ast.parse(SOURCE)
    roots = _site_roots(tree)
    docs = _docstrings(roots)
    in_fstring = set()
    for f in roots:
        for n in ast.walk(f):
            if isinstance(n, ast.JoinedStr):
                for m in ast.walk(n):
                    in_fstring.add(id(m))
    out = []
    for f in roots:
        for n in ast.walk(f):
            if id(n) in docs:
                continue
            if isinstance(n, ast.Compare):
                for k, op in enumerate(n.ops):
                    new = CMP_SWAP[type(op)].__name__
                    out.append((n.lineno, n.col_offset, "comparison", k, f"{type(op).__name__} -> {new}"))
            elif isinstance(n, ast.BoolOp):
                out.append((n.lineno, n.col_offset, "and/or", 0,
                            "and -> or" if isinstance(n.op, ast.And) else "or -> and"))
            elif isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.Not):
                out.append((n.lineno, n.col_offset, "not", 0, "not removed"))
            elif isinstance(n, ast.Constant) and id(n) not in in_fstring:
                v = n.value
                if isinstance(v, bool):
                    out.append((n.lineno, n.col_offset, "constant", 0, f"{v} -> {not v}"))
                elif isinstance(v, int):
                    out.append((n.lineno, n.col_offset, "constant", 0, f"{v} -> {v + 1}"))
                    out.append((n.lineno, n.col_offset, "constant", 1, f"{v} -> {v - 1}"))
                elif isinstance(v, str):
                    out.append((n.lineno, n.col_offset, "constant", 0, f"{v!r} -> {v + 'X'!r}"))
                if v is not None:
                    out.append((n.lineno, n.col_offset, "constant", 2, f"{v!r} -> None"))
            if isinstance(n, ast.stmt) and n is not f and id(n) not in docs and not _is_reject_stmt(n):
                out.append((n.lineno, n.col_offset, "statement", 0, f"delete {type(n).__name__}"))
    out.sort(key=lambda p: (p[0], p[1], p[2], p[3]))
    return out


def mutant_code(place):
    line, col, op, variant, _ = place
    tree = ast.parse(SOURCE)
    roots = _site_roots(tree)
    parents = _parents(tree)
    target = None
    for f in roots:
        for n in ast.walk(f):
            if getattr(n, "lineno", None) == line and getattr(n, "col_offset", None) == col:
                if (op == "comparison" and isinstance(n, ast.Compare)) \
                        or (op == "and/or" and isinstance(n, ast.BoolOp)) \
                        or (op == "not" and isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.Not)) \
                        or (op == "constant" and isinstance(n, ast.Constant)) \
                        or (op == "statement" and isinstance(n, ast.stmt) and n is not f):
                    target = n
                    break
        if target is not None:
            break
    if target is None:
        raise LookupError(place)
    n = target
    if op == "comparison":
        n.ops[variant] = CMP_SWAP[type(n.ops[variant])]()
    elif op == "and/or":
        n.op = ast.Or() if isinstance(n.op, ast.And) else ast.And()
    elif op in ("not", "constant"):
        if op == "not":
            new = n.operand
        else:
            v = n.value
            if variant == 2:
                new = ast.Constant(None)
            elif isinstance(v, bool):
                new = ast.Constant(not v)
            elif isinstance(v, int):
                new = ast.Constant(v + 1 if variant == 0 else v - 1)
            else:
                new = ast.Constant(v + "X")
        holder = parents[n]
        for field, value in ast.iter_fields(holder):
            if value is n:
                setattr(holder, field, new)
                break
            if isinstance(value, list) and n in value:
                value[value.index(n)] = new
                break
    else:
        _remove_statement(tree, parents, n)
    ast.fix_missing_locations(tree)
    return compile(tree, str(TRANSLATOR), "exec"), ast.unparse(tree)


def run_tests(tmp, text, name, evaluator, stop_at_first=True):
    """test_triel_to_core.py in a copy of the repository with the translator
    replaced by text: (exit code, last line)."""
    copy = tmp / name
    _copy_repo(copy)
    (copy / "parser" / "triel_to_core.py").write_text(text, encoding="utf-8")
    env = _env({"TRIEL_EVALUATOR": evaluator})
    r = subprocess.run([sys.executable, "-m", "pytest"] + (["-x"] if stop_at_first else [])
                       + ["-q", "-p", "no:cacheprovider", "parser/test_triel_to_core.py"],
                       cwd=copy, env=env, capture_output=True, text=True)
    shutil.rmtree(copy)
    last = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""
    return r.returncode, without_time(last)


def without_time(line):
    """The summary line of pytest without its time, so that two runs print the same."""
    return re.sub(r" in [0-9.]+s( \([0-9:]+\))?", "", line).strip("= ")


def section_random(tmp):
    base_outputs()
    say("## 4. Random first-order mutants")
    say()
    ps = places()
    by_op = {}
    for p in ps:
        by_op[p[2]] = by_op.get(p[2], 0) + 1
    say(f"- places: {len(ps)} (" + ", ".join(f"{k} {v}" for k, v in sorted(by_op.items())) + ")")
    chosen = random.Random(SEED).sample(ps, SAMPLE)
    rows = []
    survivors = []
    for p in chosen:
        code, text = mutant_code(p)
        v, ids = verdict(code)
        rows.append([p, v, ids, ""])
        if v == "not caught":
            survivors.append((rows[-1], text))
    have_eval = os.path.exists(EVALUATOR)
    if survivors:
        rc, last = run_tests(tmp, SOURCE, "control", EVALUATOR if have_eval else str(tmp / "no-evaluator"),
                             stop_at_first=False)
        control_ok = rc == 0 and (not have_eval or " skipped" not in last)
        say(f"- control run of test_triel_to_core.py on the translator itself: {last} "
            f"(evaluator: {'built, ' + EVALUATOR if have_eval else 'not built'})")
        use = EVALUATOR if have_eval and control_ok else str(tmp / "no-evaluator")
        if have_eval and not control_ok:
            say("- the control run did not pass: the survivors are run without the evaluator")
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=os.cpu_count() or 1) as pool:
            done = list(pool.map(lambda k: run_tests(tmp, survivors[k][1], f"mutant{k}", use),
                                 range(len(survivors))))
        for (row, text), (rc, last) in zip(survivors, done):
            if rc != 0:
                row[1] = "caught by test_triel_to_core.py"
            else:
                key = tuple(row[0][:4])
                row[1] = "equivalent" if key in EQUIVALENT else "gap"
                row[3] = EQUIVALENT.get(key, "")
            row[2] = [last]
    names = ["caught (divergence)", "caught (exceptions only)", "caught (time)", "caught by test_triel_to_core.py",
             "equivalent", "gap"]
    for n in names:
        say(f"- {n}: {sum(r[1] == n for r in rows)}")
    say()
    say("| line | operator | change | result | note |")
    say("|---|---|---|---|---|")
    for p, v, ids, arg in sorted(rows, key=lambda r: r[0][:4]):
        note = arg or (", ".join(ids[:2]) + (" …" if len(ids) > 2 else ""))
        change = p[4].replace("|", "\\|")
        say(f"| {p[0]} | {p[2]} | {change} | {v} | {note} |")
    say()
    return rows


# --- main -------------------------------------------------------------------------------

def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--translate-corpus":
        return corpus_runner()
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--section", type=int, choices=[1, 2, 3, 4])
    args = ap.parse_args()
    sections = [args.section] if args.section else [1, 2, 3, 4]
    times = []
    say(f"# Measurements of the corpus: {TRANSLATOR.relative_to(T_REPO) if TRANSLATOR.is_relative_to(T_REPO) else TRANSLATOR}")
    say()
    with tempfile.TemporaryDirectory(prefix="corpus-measure-") as d:
        tmp = Path(d)
        t0 = time.monotonic()
        setup()
        times.append(("parse trees of the corpus", time.monotonic() - t0))
        cov = None
        for s in sections:
            t = time.monotonic()
            if s == 1:
                section_corpus()
            elif s == 2:
                if cov is None:
                    cov = coverage_data(tmp)
                executed = set(cov["reports"]["corpus and tests"]["executed_lines"])
                section_rejects(executed)
            elif s == 3:
                cov = section_coverage(tmp)
            elif s == 4:
                section_random(tmp)
            times.append((f"section {s}", time.monotonic() - t))
        say("## 5. Time")
        say()
        for name, t in times:
            say(f"- {name}: {t:.0f} s (time)")
        if COVERAGE is not None:
            say(f"- of which test_triel_to_core.py under coverage: {COVERAGE['tests_time']:.0f} s (time)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
