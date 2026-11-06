#!/usr/bin/env python3
"""
triel check: the report of the evaluator exported from formal/core on a trace,
with the verdicts of the norms and the decisions of the fail-closed monitor of
each prohibition.

Usage:
    python3 parser/triel.py check SPEC.triel TRACE [--json] [--last] [--evaluator PATH]

TRACE is a scenario (examples/core/README.md, Scenarios) or the same scenario
in JSON (evaluator/README.md); a file whose first character other than white
space is { is read as JSON. The trace names its specification, and it must be
the file SPEC.triel.

The specification is translated by triel_to_core.py and the trace converted by
the functions of triel_eval.py; the evaluator computes the report, which is
printed as triel_eval.py prints it. --json prints the same report as a JSON
array, one object per line of the report (evaluator/README.md). --last adds the
line LAST ENTRY J : ..., the decisions of the monitors on the last entry of the
trace, printed by the evaluator from the MONITOR lines it computed. This
program decides nothing: every verdict and every decision is in the lines
printed by the evaluator.

The evaluator binary is taken from --evaluator, else from the environment
variable TRIEL_EVALUATOR, else evaluator/triel-eval (triel-eval.exe on Windows).

Exit codes, read from the words of the report lines, checked in this order:
  2  the translator rejects the specification (the line REJECTED: ...);
  1  any other error, including a report that is missing or not recognised,
     or with --last no LAST line;
  4  the evaluator rejects the trace (TIME ORDER REJECTED, ACTIVATION
     REJECTED, BLOCK REJECTED or TYPES ILL-TYPED);
  3  a monitor blocks an action: BLOCK in a MONITOR line; with --last, BLOCK
     in the LAST line;
  6  without --last: a violation in the report (a TERM line whose verdict is
     BREACHED or ELSE BREACHED, STATUS VIOLATED, or an invariant F);
  5  with --last: LAST ENTRY J : NO DECISION, no monitor decided on the last
     action;
  0  without --last: none of these; with --last: the LAST line has ALLOW.
With --last the code answers only the question about the last action: a
violation earlier in the trace does not change it.
"""
import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

from lark import UnexpectedInput

sys.path.insert(0, str(Path(__file__).parent))
from triel_eval import (ScenarioError, Sym, default_evaluator, find_spec,  # noqa: E402
                        read_sexp, scenario_input)
from triel_to_core import Str, header, sexp, translate  # noqa: E402

EVALUATED, ERROR, REJECTED, BLOCKED, TRACE_REJECTED, NO_DECISION, VIOLATION = \
    0, 1, 2, 3, 4, 5, 6


# --- The trace in JSON --------------------------------------------------------
#
# The JSON form of a scenario is converted to the S-expression that read_sexp
# returns for the same scenario, and then read by scenario_input like a .scn
# file, so both forms are checked by the same code.

SYMBOL = re.compile(r'[^\s()";]+')  # what read_sexp reads as a symbol


def _no_duplicates(pairs):
    keys = [k for k, _ in pairs]
    for k in keys:
        if keys.count(k) > 1:
            raise ScenarioError(f"{k} is given twice")
    return dict(pairs)


def _no_constant(c):
    raise ScenarioError(f"not JSON: {c}")


def _show(x) -> str:
    return json.dumps(x, ensure_ascii=False)


def _symbol(x, what: str) -> Sym:
    if isinstance(x, str) and SYMBOL.fullmatch(x):
        return Sym(x)
    raise ScenarioError(f"not {what}: {_show(x)}")


def _object(x, keys, what: str) -> dict:
    if isinstance(x, dict) and set(x) == set(keys):
        return x
    raise ScenarioError(f"expected {what}, an object with the keys {', '.join(keys)}: {_show(x)}")


def _value(v):
    if isinstance(v, dict) and len(v) == 1:
        (k, x), = v.items()
        if k == "bool" and isinstance(x, bool):
            return [Sym("bool"), Sym("true" if x else "false")]
        if k == "int" and isinstance(x, int) and not isinstance(x, bool):
            return [Sym("int"), Sym(str(x))]
        if k == "dec" and isinstance(x, str) and SYMBOL.fullmatch(x):
            return [Sym("dec"), Sym(x)]
        if k in ("str", "time") and isinstance(x, str):
            return [Sym(k), Str(x)]
        if k == "record" and isinstance(x, dict):
            return [Sym("record")] + _fields(x)
    raise ScenarioError(f"not a value: {_show(v)}")


def _fields(d: dict):
    return [[_symbol(k, "a name"), _value(v)] for k, v in d.items()]


def _argument(x):
    if isinstance(x, dict) and set(x) == {"name"}:
        return [Sym("name"), _symbol(x["name"], "a name")]
    return _value(x)


def _action(a):
    if isinstance(a, str):
        return _symbol(a, "an action")
    a = _object(a, ("name", "args"), "an action")
    if not isinstance(a["args"], list):
        raise ScenarioError(f"expected a list of arguments: {_show(a['args'])}")
    return [_symbol(a["name"], "an action")] + [_argument(x) for x in a["args"]]


def _event(e):
    kind = e.get("kind") if isinstance(e, dict) else None
    if kind in ("activate", "tick"):
        _object(e, ("kind",), "an event")
        return [Sym(kind)]
    if kind == "arrive":
        _object(e, ("kind", "factor"), "an event")
        return [Sym("arrive"), _symbol(e["factor"], "a factor")]
    if kind == "act":
        _object(e, ("kind", "subject", "action", "polarity"), "an event")
        return [Sym("act"), _symbol(e["subject"], "a subject"), _action(e["action"]),
                _symbol(e["polarity"], "a polarity")]
    raise ScenarioError(f"not an event: {_show(e)}")


def _entry(e):
    e = _object(e, ("time", "event", "data"), "an entry")
    if not isinstance(e["time"], str):
        raise ScenarioError(f"not an ISO-8601 UTC time: {_show(e['time'])}")
    if not isinstance(e["data"], dict):
        raise ScenarioError(f"expected the data as an object: {_show(e['data'])}")
    return [Sym("entry"), Str(e["time"]), _event(e["event"]), [Sym("data")] + _fields(e["data"])]


def json_scenario(text: str):
    """The S-expression of a scenario given in JSON (evaluator/README.md)."""
    try:
        x = json.loads(text, object_pairs_hook=_no_duplicates, parse_constant=_no_constant)
    except json.JSONDecodeError as e:
        raise ScenarioError(f"not JSON: {e.msg} (line {e.lineno}, column {e.colno})") from None
    x = _object(x, ("scenario", "spec", "entries"), "a scenario")
    if not isinstance(x["spec"], str):
        raise ScenarioError(f"expected the path of the specification: {_show(x['spec'])}")
    if not isinstance(x["entries"], list):
        raise ScenarioError(f"expected a list of entries: {_show(x['entries'])}")
    return ([Sym("scenario"), _symbol(x["scenario"], "a scenario name"), [Sym("spec"), Str(x["spec"])]]
            + [_entry(e) for e in x["entries"]])


def read_trace(text: str):
    """The S-expression of a scenario, written as a .scn file or in JSON."""
    return json_scenario(text) if text.lstrip().startswith("{") else read_sexp(text)


# --- The report as JSON -------------------------------------------------------
#
# Each line of the report (examples/core/README.md, Output) is one JSON object.
# report_line(report_json(L)) == L for every line L; the command checks this for
# every line it converts, so the JSON carries exactly the text of the report.

class BadLine(Exception):
    pass


class _Cursor:
    """The words of a report line, separated by single spaces. A word extends
    over a string in quotes and over parentheses, so an action NAME(ARG, ...)
    is one word."""

    def __init__(self, line: str):
        self.s, self.i = line, 0

    def end(self) -> bool:
        return self.i >= len(self.s)

    def word(self) -> str:
        s, i = self.s, self.i
        start, depth = i, 0
        while i < len(s) and (depth > 0 or s[i] != " "):
            if s[i] == '"':
                i += 1
                while i < len(s) and s[i] != '"':
                    i += 2 if s[i] == "\\" else 1
                if i >= len(s):
                    raise BadLine("unterminated string")
            elif s[i] == "(":
                depth += 1
            elif s[i] == ")":
                depth -= 1
            i += 1
        if i == start:
            raise BadLine("expected a word")
        word = s[start:i]
        if i < len(s):
            i += 1
            if i == len(s):
                raise BadLine("space at the end of the line")
        self.i = i
        return word

    def peek(self):
        if self.end():
            return None
        i = self.i
        w = self.word()
        self.i = i
        return w

    def expect(self, *words):
        for w in words:
            if self.word() != w:
                raise BadLine(f"expected {w}")

    def one_of(self, *words) -> str:
        w = self.word()
        if w not in words:
            raise BadLine(f"expected one of {', '.join(words)}")
        return w

    def number(self) -> int:
        w = self.word()
        if not re.fullmatch(r"-?[0-9]+", w):
            raise BadLine("expected an integer")
        return int(w)

    def rest(self) -> str:
        if self.end():
            raise BadLine("expected a word")
        r, self.i = self.s[self.i:], len(self.s)
        return r

    def done(self):
        if not self.end():
            raise BadLine("text after the end of the line")


def _verdict(c: _Cursor) -> dict:
    v = c.one_of("FULFILLED", "PENDING", "BREACHED")
    return {"verdict": v, "time": c.number()} if v == "BREACHED" else {"verdict": v}


def _deadline(c: _Cursor):
    if c.peek() == "NONE":
        c.word()
        return None
    return c.number()


def _handler_actions(c: _Cursor) -> list:
    acts = []
    while c.peek() in ("NOTIFY", "PENALTY"):
        if c.word() == "NOTIFY":
            acts.append({"action": "NOTIFY", "subject": c.word()})
        elif c.peek() == "UNDEFINED":
            c.word()
            acts.append({"action": "PENALTY", "undefined": True})
        elif c.peek() == "NEGATIVE":
            c.word()
            acts.append({"action": "PENALTY", "negative": True, "amount": c.word()})
        else:
            a = {"action": "PENALTY", "amount": c.word()}
            if c.peek() == "CAPPED":
                c.word()
                a["capped"] = True
            acts.append(a)
    return acts


def _continuation(c: _Cursor) -> dict:
    k = c.one_of("CLOSED", "TERMINATED", "CURE", "ESCALATED")
    if k == "CURE":
        return {"continuation": k, **_verdict(c)}
    if k == "ESCALATED":
        return {"continuation": k, "subject": c.word(), **_verdict(c)}
    return {"continuation": k}


def _term(c: _Cursor) -> dict:
    o = {"line": "TERM", "term": c.number()}
    kind = c.one_of("MUST", "MUST_NOT", "MAY", "ON_BREACH", "COMPOSITE")
    o["kind"] = kind
    if kind == "MUST":
        o.update(subject=c.word(), action=c.word())
        c.expect("DEADLINE")
        o["deadline"] = _deadline(c)
        if c.one_of(":", "ELSE") == "ELSE":
            o["fallback"] = {"subject": c.word(), "action": c.word()}
            c.expect("DEADLINE")
            o["fallback"]["deadline"] = _deadline(c)
            c.expect(":")
            if c.peek() == "ELSE":
                c.word()
                o["status"] = {"verdict": "ELSE", "fallback": _verdict(c)}
            else:
                o["status"] = {"verdict": c.one_of("FULFILLED", "PENDING")}
        else:
            st = _verdict(c)
            if st["verdict"] == "BREACHED":
                st["actions"] = _handler_actions(c)
                st["continuation"] = _continuation(c)
            o["status"] = st
    elif kind == "MUST_NOT":
        o.update(subject=c.word(), action=c.word())
        c.expect(":")
        o["status"] = {**_verdict(c), "actions": _handler_actions(c)}
    elif kind == "MAY":
        o.update(subject=c.word(), action=c.word())
        c.expect(":")
        o["status"] = _verdict(c)
    elif kind == "ON_BREACH":
        o["subject"] = c.word()
        c.expect(":")
        o["bound"] = c.number() if c.one_of("BOUND", "UNBOUND") == "BOUND" else None
    else:
        c.expect(":")
        for k in ("DONE", "INTERRUPTED", "VIOLATED"):
            c.expect(k)
            o[k.lower()] = c.one_of("YES", "NO", "UNKNOWN")
        c.expect("STATUS")
        s = c.one_of("VIOLATED", "INTERRUPTED", "DONE", "OPEN", "UNKNOWN")
        if s in ("OPEN", "UNKNOWN"):
            o["status"] = {"outcome": s}
        else:
            c.expect("ENTRY")
            o["status"] = {"outcome": s, "entry": c.number()}
    return o


def _metadata(c: _Cursor) -> dict:
    key = c.word()
    o = {"line": "METADATA", "key": key}
    if key == "DID":
        o.update(subject=c.word(), did=c.rest())
    elif key == "PROVES":
        o.update(factor=c.word(), constraint=c.rest())
    elif key == "BOUND_TO":
        o.update(factor=c.word(), subject=c.word(), nonce=c.word())
    elif key == "SOURCE":
        o.update(factor=c.word(), subject=c.word())
    elif key in ("POLARITY", "THRESHOLD", "SENSITIVITY_BOUND"):
        o.update(factor=c.word(), number=c.rest())
    else:
        o["value"] = c.rest()
    return o


def _parse(line: str) -> dict:
    c = _Cursor(line)
    w = c.word()
    if w == "SPEC":
        o = {"line": "SPEC", "name": c.rest()}
    elif w == "METADATA":
        o = _metadata(c)
    elif w == "REJECTED:":
        o = {"line": "REJECTED", "constructs": c.rest().split("; ")}
    elif w == "TIME":
        c.expect("ORDER", "REJECTED", "ENTRY")
        o = {"line": "TIME ORDER REJECTED", "entry": c.number()}
    elif w in ("ACTIVATION", "BLOCK"):
        o = {"line": w, "result": c.one_of("OK", "REJECTED")}
    elif w == "TYPES":
        o = {"line": "TYPES", "result": c.one_of("OK", "ILL-TYPED")}
        if o["result"] == "ILL-TYPED":
            c.expect("ENTRY")
            o["entry"] = c.number()
            c.expect("FACTOR")
            o["factor"] = c.word()
    elif w == "TERM":
        o = _term(c)
    elif w == "INVARIANT":
        o = {"line": "INVARIANT", "name": c.word()}
        c.expect(":")
        o["value"] = c.one_of("T", "F", "U")
    elif w == "MONITOR":
        o = {"line": "MONITOR", "term": c.number(), "decisions": []}
        c.expect(":")
        if c.peek() == "NO":
            c.expect("NO", "ACTION")
        else:
            while True:
                c.expect("ENTRY")
                o["decisions"].append({"entry": c.number(), "decision": c.one_of("BLOCK", "ALLOW")})
                if c.end():
                    break
    elif w == "LAST":
        c.expect("ENTRY")
        o = {"line": "LAST", "entry": c.number(), "decisions": []}
        c.expect(":")
        if c.peek() == "NO":
            c.expect("NO", "DECISION")
        else:
            while True:
                c.expect("MONITOR")
                o["decisions"].append({"term": c.number(), "decision": c.one_of("BLOCK", "ALLOW")})
                if c.end():
                    break
    else:
        raise BadLine("unknown line")
    c.done()
    return o


def report_json(line: str) -> dict:
    """The JSON object of a line of the report; BadLine if the line is not one
    of the lines of examples/core/README.md, Output, or does not convert back
    to itself."""
    o = _parse(line)
    if report_line(o) != line:
        raise BadLine("the line does not convert back to itself")
    return o


def _verdict_text(v: dict) -> str:
    return f"BREACHED {v['time']}" if v["verdict"] == "BREACHED" else v["verdict"]


def _deadline_text(d) -> str:
    return "NONE" if d is None else str(d)


def _action_text(a: dict) -> str:
    if a["action"] == "NOTIFY":
        return f"NOTIFY {a['subject']}"
    if a.get("undefined"):
        return "PENALTY UNDEFINED"
    if a.get("negative"):
        return f"PENALTY NEGATIVE {a['amount']}"
    return f"PENALTY {a['amount']}" + (" CAPPED" if a.get("capped") else "")


def _continuation_text(k: dict) -> str:
    if k["continuation"] == "CURE":
        return f"CURE {_verdict_text(k)}"
    if k["continuation"] == "ESCALATED":
        return f"ESCALATED {k['subject']} {_verdict_text(k)}"
    return k["continuation"]


def _term_text(o: dict) -> str:
    head = f"TERM {o['term']} {o['kind']}"
    kind, st = o["kind"], o.get("status")
    if kind == "MUST" and "fallback" in o:
        f = o["fallback"]
        s = "ELSE " + _verdict_text(st["fallback"]) if st["verdict"] == "ELSE" else st["verdict"]
        return (f"{head} {o['subject']} {o['action']} DEADLINE {_deadline_text(o['deadline'])}"
                f" ELSE {f['subject']} {f['action']} DEADLINE {_deadline_text(f['deadline'])} : {s}")
    if kind == "MUST":
        s = _verdict_text(st)
        if st["verdict"] == "BREACHED":
            s = " ".join([s] + [_action_text(a) for a in st["actions"]]
                         + [_continuation_text(st["continuation"])])
        return f"{head} {o['subject']} {o['action']} DEADLINE {_deadline_text(o['deadline'])} : {s}"
    if kind == "MUST_NOT":
        s = " ".join([_verdict_text(st)] + [_action_text(a) for a in st["actions"]])
        return f"{head} {o['subject']} {o['action']} : {s}"
    if kind == "MAY":
        return f"{head} {o['subject']} {o['action']} : {_verdict_text(st)}"
    if kind == "ON_BREACH":
        b = "UNBOUND" if o["bound"] is None else f"BOUND {o['bound']}"
        return f"{head} {o['subject']} : {b}"
    s = st["outcome"] + (f" ENTRY {st['entry']}" if "entry" in st else "")
    return (f"{head} : DONE {o['done']} INTERRUPTED {o['interrupted']}"
            f" VIOLATED {o['violated']} STATUS {s}")


def report_line(o: dict) -> str:
    """The line of the report of a JSON object of report_json."""
    k = o["line"]
    if k == "SPEC":
        return f"SPEC {o['name']}"
    if k == "METADATA":
        rest = {"DID": ("subject", "did"), "PROVES": ("factor", "constraint"),
                "BOUND_TO": ("factor", "subject", "nonce"), "SOURCE": ("factor", "subject"),
                "POLARITY": ("factor", "number"), "THRESHOLD": ("factor", "number"),
                "SENSITIVITY_BOUND": ("factor", "number")}.get(o["key"], ("value",))
        return " ".join(["METADATA", o["key"]] + [o[f] for f in rest])
    if k == "REJECTED":
        return "REJECTED: " + "; ".join(o["constructs"])
    if k == "TIME ORDER REJECTED":
        return f"TIME ORDER REJECTED ENTRY {o['entry']}"
    if k in ("ACTIVATION", "BLOCK"):
        return f"{k} {o['result']}"
    if k == "TYPES":
        if o["result"] == "OK":
            return "TYPES OK"
        return f"TYPES ILL-TYPED ENTRY {o['entry']} FACTOR {o['factor']}"
    if k == "TERM":
        return _term_text(o)
    if k == "INVARIANT":
        return f"INVARIANT {o['name']} : {o['value']}"
    if k == "MONITOR":
        ds = "".join(f" ENTRY {d['entry']} {d['decision']}" for d in o["decisions"])
        return f"MONITOR {o['term']} :" + (ds or " NO ACTION")
    if k == "LAST":
        ds = "".join(f" MONITOR {d['term']} {d['decision']}" for d in o["decisions"])
        return f"LAST ENTRY {o['entry']} :" + (ds or " NO DECISION")
    raise BadLine(f"unknown line {k}")


# --- The exit code ----------------------------------------------------------------
#
# The exit code is read from the words of the report lines, through their JSON
# objects: nothing is computed here that the lines do not say.

def trace_rejected(o: dict) -> bool:
    """A line by which the evaluator rejects the trace: TIME ORDER REJECTED,
    ACTIVATION REJECTED, BLOCK REJECTED or TYPES ILL-TYPED."""
    return (o["line"] == "TIME ORDER REJECTED"
            or (o["line"] in ("ACTIVATION", "BLOCK") and o["result"] == "REJECTED")
            or (o["line"] == "TYPES" and o["result"] == "ILL-TYPED"))


def violation(o: dict) -> bool:
    """A line that reports a violation: a TERM line whose verdict, the word
    after its colon, is BREACHED, or ELSE followed by BREACHED; a composite
    line with STATUS VIOLATED; an invariant F."""
    if o["line"] == "INVARIANT":
        return o["value"] == "F"
    if o["line"] != "TERM" or "status" not in o:
        return False
    st = o["status"]
    if o["kind"] == "COMPOSITE":
        return st["outcome"] == "VIOLATED"
    return st["verdict"] == "BREACHED" or (st["verdict"] == "ELSE"
                                           and st["fallback"]["verdict"] == "BREACHED")


def exit_code(lines, last: bool) -> int:
    """The exit code of a report the evaluator printed (the module docstring);
    BadLine if a line is not recognised or, with --last, the LAST line is not
    the one last line."""
    objs = [report_json(line) for line in lines]
    lasts = [o for o in objs if o["line"] == "LAST"]
    if last and (len(lasts) != 1 or objs[-1]["line"] != "LAST"):
        raise BadLine("no LAST line at the end of the report")
    if not last and lasts:
        raise BadLine("a LAST line without --last")
    if any(trace_rejected(o) for o in objs):
        return TRACE_REJECTED
    if last:
        ds = [d["decision"] for d in objs[-1]["decisions"]]
        return BLOCKED if "BLOCK" in ds else NO_DECISION if not ds else EVALUATED
    if any(d["decision"] == "BLOCK" for o in objs if o["line"] == "MONITOR"
           for d in o["decisions"]):
        return BLOCKED
    return VIOLATION if any(violation(o) for o in objs) else EVALUATED


# --- The command --------------------------------------------------------------

def check(spec: str, trace: str, evaluator=None, last: bool = False):
    """The exit code and the lines of the report on a trace; the lines are
    empty for an error, which is printed to standard error."""
    def error(msg):
        print(f"{trace}: {msg}", file=sys.stderr)
        return ERROR, []

    try:
        spec_path = Path(spec)
        if not spec_path.is_file():
            raise ScenarioError(f"specification not found: {spec}")
        scn = read_trace(Path(trace).read_text(encoding="utf-8"))
        named, entries = scenario_input(scn)
        if not os.path.samefile(find_spec(named), spec_path):
            raise ScenarioError(f"the trace is a trace of {named}, not of {spec}")
        tr = translate(spec_path.read_text(encoding="utf-8"))
    except ScenarioError as e:
        return error(e)
    except OSError as e:
        return error(e.strerror or e)
    except UnexpectedInput as e:
        return error(f"the specification does not parse (line {e.line}, column {e.column})")
    except RecursionError:
        return error("nested too deeply")
    lines = header(tr)
    if tr.rejected:
        return REJECTED, lines + ["REJECTED: " + "; ".join(sorted(tr.rejected))]
    ev = evaluator or default_evaluator()
    try:
        res = subprocess.run([ev] + (["--last"] if last else []),
                             input=sexp(["input", tr.core, entries]),
                             capture_output=True, text=True, encoding="utf-8")
    except OSError as e:
        return error(f"cannot run the evaluator {ev}: {e.strerror or e}")
    if res.returncode != 0:
        print(res.stderr, file=sys.stderr, end="")
        return ERROR, []
    lines += res.stdout.splitlines()
    if last and not (lines[-1].startswith("LAST ") and
                     sum(line.startswith("LAST ") for line in lines) == 1):
        # An evaluator built before --last ignores the option.
        return error(f"the evaluator {ev} printed no LAST line; rebuild it (evaluator/README.md)")
    try:
        return exit_code(lines, last), lines
    except BadLine as e:
        return error(f"cannot read the report: {e}")


def main(argv=None) -> int:
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser(prog="triel", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="command", required=True)
    cp = sub.add_parser("check", help="the report of the evaluator on a trace")
    cp.add_argument("spec", metavar="SPEC.triel")
    cp.add_argument("trace", metavar="TRACE", help="a scenario, .scn or JSON")
    cp.add_argument("--json", action="store_true", help="print the report as JSON")
    cp.add_argument("--last", action="store_true",
                    help="add the decisions of the monitors on the last entry")
    cp.add_argument("--evaluator", default=None, help="the evaluator binary")
    args = ap.parse_args(argv)
    code, lines = check(args.spec, args.trace, args.evaluator, args.last)
    if code == ERROR:
        return code
    if args.json:
        try:
            objs = [report_json(line) for line in lines]
        except BadLine as e:
            print(f"{args.trace}: cannot convert the report to JSON: {e}", file=sys.stderr)
            return ERROR
        print("[\n" + ",\n".join(json.dumps(o, ensure_ascii=False) for o in objs) + "\n]")
    else:
        print("\n".join(lines))
    return code


if __name__ == "__main__":
    sys.exit(main())
