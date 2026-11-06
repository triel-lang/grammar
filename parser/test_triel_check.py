"""Tests of triel check (parser/triel.py).

Run from the repository root:  python3 -m pytest parser/test_triel_check.py
The tests that run the evaluator need the evaluator binary (see
parser/triel_eval.py); they are skipped when it is not built.

Most tests call the command in this process, with the translation of each
specification computed once; the tests of the exit codes run it as a program.
"""
import functools
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent))
import triel  # noqa: E402
from triel_eval import default_evaluator, find_spec, read_sexp, scenario_input  # noqa: E402
from triel_to_core import sexp, translate  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
TRIEL = str(REPO / "parser" / "triel.py")
SCENARIOS = sorted((REPO / "examples/core/scenarios").glob("*.scn"))
IDS = [s.stem for s in SCENARIOS]
MANDATE = "examples/core/merchant_mandate.triel"

needs_evaluator = pytest.mark.skipif(not os.path.exists(default_evaluator()),
                                     reason="evaluator not built")


@pytest.fixture(autouse=True)
def translate_once(monkeypatch):
    monkeypatch.setattr(triel, "translate", _translate)


@functools.lru_cache(maxsize=None)
def _translate(text):
    return translate(text)


def spec_of(scn: Path) -> str:
    named, _ = scenario_input(read_sexp(scn.read_text(encoding="utf-8")))
    return str(find_spec(named).relative_to(REPO))


def expected(scn: Path):
    return scn.with_suffix(".expected").read_text(encoding="utf-8").splitlines()


def check(capsys, *args):
    """triel check in this process: exit code, standard output, standard error."""
    code = triel.main(["check", *map(str, args)])
    out = capsys.readouterr()
    return code, out.out, out.err


def program(*args, **kw):
    """triel check as a program, from the root of the repository."""
    return subprocess.run([sys.executable, TRIEL, "check", *map(str, args)],
                          capture_output=True, text=True, encoding="utf-8", cwd=REPO, **kw)


def has_block(lines, kind="MONITOR"):
    return any(line.startswith(kind + " ") and " BLOCK" in line for line in lines)


# --- The .scn scenario in JSON, written independently of parser/triel.py --------

def json_value(v):
    tag = str(v[0])
    if tag == "bool":
        return {"bool": v[1] == "true"}
    if tag == "int":
        return {"int": int(v[1])}
    if tag == "record":
        return {"record": json_fields(v[1:])}
    return {tag: str(v[1])}  # dec, str, time


def json_fields(fs):
    return {str(f[0]): json_value(f[1]) for f in fs}


def json_action(a):
    if not isinstance(a, list):
        return str(a)
    return {"name": str(a[0]),
            "args": [{"name": str(x[1])} if x[0] == "name" else json_value(x) for x in a[1:]]}


def json_event(e):
    if e[0] in ("activate", "tick"):
        return {"kind": str(e[0])}
    if e[0] == "arrive":
        return {"kind": "arrive", "factor": str(e[1])}
    return {"kind": "act", "subject": str(e[1]), "action": json_action(e[2]), "polarity": str(e[3])}


def scn_to_json(text: str) -> str:
    scn = read_sexp(text)
    return json.dumps({
        "scenario": str(scn[1]),
        "spec": str(scn[2][1]),
        "entries": [{"time": str(e[1]), "event": json_event(e[2]), "data": json_fields(e[3][1:])}
                    for e in scn[3:]],
    }, ensure_ascii=False, indent=2)


# --- Every scenario -------------------------------------------------------------

@needs_evaluator
@pytest.mark.parametrize("scn", SCENARIOS, ids=IDS)
def test_text_is_the_expected_report(scn, capsys):
    code, out, err = check(capsys, spec_of(scn), scn)
    assert out.splitlines() == expected(scn), err
    assert code == (3 if has_block(expected(scn)) else 0)


@needs_evaluator
@pytest.mark.parametrize("scn", SCENARIOS, ids=IDS)
def test_json_converts_back_to_the_expected_report(scn, capsys):
    code, out, err = check(capsys, spec_of(scn), scn, "--json")
    objs = json.loads(out)
    assert isinstance(objs, list) and all(isinstance(o, dict) for o in objs)
    assert [triel.report_line(o) for o in objs] == expected(scn), err
    assert code == (3 if has_block(expected(scn)) else 0)


@needs_evaluator
@pytest.mark.parametrize("scn", SCENARIOS, ids=IDS)
def test_json_trace_gives_the_same_report(scn, tmp_path, capsys):
    text = scn.read_text(encoding="utf-8")
    trace = tmp_path / (scn.stem + ".json")
    trace.write_text(scn_to_json(text), encoding="utf-8")
    # The evaluator gets the same input from both forms.
    assert sexp(scenario_input(triel.read_trace(trace.read_text(encoding="utf-8")))) \
        == sexp(scenario_input(read_sexp(text)))
    code, out, err = check(capsys, spec_of(scn), trace)
    assert out.splitlines() == expected(scn), err
    code_json, out_json, _ = check(capsys, spec_of(scn), trace, "--json")
    assert [triel.report_line(o) for o in json.loads(out_json)] == expected(scn)
    assert code == code_json == (3 if has_block(expected(scn)) else 0)


@needs_evaluator
@pytest.mark.parametrize("scn", SCENARIOS, ids=IDS)
def test_last_line_selects_the_decisions_at_the_last_entry(scn, capsys):
    code, out, err = check(capsys, spec_of(scn), scn, "--last")
    lines = out.splitlines()
    assert lines[:-1] == expected(scn), err
    j = len(read_sexp(scn.read_text(encoding="utf-8"))) - 4
    ds = [(m["term"], d["decision"]) for m in map(triel.report_json, expected(scn))
          if m["line"] == "MONITOR" for d in m["decisions"] if d["entry"] == j]
    assert lines[-1] == f"LAST ENTRY {j} :" + ("".join(f" MONITOR {i} {d}" for i, d in ds)
                                               or " NO DECISION")
    assert code == (3 if ("BLOCK" in [d for _, d in ds]) else 0)


# --- --last on chosen scenarios ---------------------------------------------------

SCN = REPO / "examples/core/scenarios"


@needs_evaluator
def test_last_allowed(capsys):
    code, out, _ = check(capsys, MANDATE, SCN / "mandate_campaign_at_limit.scn", "--last")
    assert out.splitlines()[-1] == "LAST ENTRY 2 : MONITOR 4 ALLOW" and code == 0


@needs_evaluator
def test_last_blocked(capsys):
    code, out, _ = check(capsys, MANDATE, SCN / "mandate_campaign_budget.scn", "--last")
    assert out.splitlines()[-1] == "LAST ENTRY 4 : MONITOR 4 BLOCK" and code == 3
    code, out, _ = check(capsys, MANDATE, SCN / "mandate_campaign_budget.scn", "--last", "--json")
    assert json.loads(out)[-1] == {"line": "LAST", "entry": 4,
                                   "decisions": [{"term": 4, "decision": "BLOCK"}]} and code == 3


@needs_evaluator
def test_last_no_action(capsys):
    code, out, _ = check(capsys, MANDATE, SCN / "mandate_budget_limit_zero.scn", "--last")
    assert out.splitlines()[-1] == "LAST ENTRY 1 : NO DECISION" and code == 0


def campaign(*budgets):
    """A trace of merchant_mandate in JSON: one campaign per budget."""
    entries = [{"time": "2026-11-10T09:00:00Z", "event": {"kind": "activate"},
                "data": {"budget_limit": {"dec": "5000.00"}, "reorder_point": {"int": 10}}}]
    for k, b in enumerate(budgets):
        data = {"budget_limit": {"dec": "5000.00"}, "reorder_point": {"int": 10},
                "campaign_budget": {"dec": b}}
        entries += [{"time": f"2026-11-10T09:{20 + k:02d}:00Z", "event": {"kind": "tick"}, "data": data},
                    {"time": f"2026-11-10T09:{20 + k:02d}:01Z",
                     "event": {"kind": "act", "subject": "agent", "action": "apply_campaign",
                               "polarity": "must_not"}, "data": data}]
    return json.dumps({"scenario": "campaigns", "spec": MANDATE, "entries": entries})


@needs_evaluator
def test_last_allowed_after_an_earlier_block(tmp_path, capsys):
    trace = tmp_path / "campaigns.json"
    trace.write_text(campaign("7500.00", "3000.00"))
    code, out, _ = check(capsys, MANDATE, trace)
    assert "MONITOR 4 : ENTRY 2 BLOCK ENTRY 4 ALLOW" in out.splitlines() and code == 3
    code, out, _ = check(capsys, MANDATE, trace, "--last")
    assert out.splitlines()[-1] == "LAST ENTRY 4 : MONITOR 4 ALLOW" and code == 0


# --- Exit codes, as a program -------------------------------------------------------

@needs_evaluator
def test_exit_code_blocked():
    r = program(MANDATE, "examples/core/scenarios/mandate_campaign_budget.scn")
    assert r.returncode == 3, r.stderr
    assert r.stdout.splitlines() == expected(SCN / "mandate_campaign_budget.scn")


@needs_evaluator
def test_exit_code_not_blocked():
    r = program(MANDATE, "examples/core/scenarios/mandate_campaign_at_limit.scn", "--json")
    assert r.returncode == 0, r.stderr
    assert [triel.report_line(o) for o in json.loads(r.stdout)] \
        == expected(SCN / "mandate_campaign_at_limit.scn")


def test_exit_code_rejected_specification(tmp_path):
    scn = tmp_path / "rejected.scn"
    scn.write_text('(scenario rejected (spec "examples/semantics/execute_renaming.triel")\n'
                   '  (entry "2026-01-01T00:00:00Z" (activate) (data)))\n')
    r = program("examples/semantics/execute_renaming.triel", scn)
    assert r.returncode == 2 and r.stdout.splitlines()[-1] == "REJECTED: EXECUTE"
    r = program("examples/semantics/execute_renaming.triel", scn, "--json")
    assert r.returncode == 2
    assert json.loads(r.stdout)[-1] == {"line": "REJECTED", "constructs": ["EXECUTE"]}


def test_exit_code_other_errors(tmp_path):
    scn = "examples/core/scenarios/mandate_campaign_budget.scn"
    r = program(MANDATE, "no/such/trace.scn")
    assert r.returncode == 1 and r.stdout == ""
    r = program("examples/core/core_payment.triel", scn)
    assert r.returncode == 1 and "is a trace of examples/core/merchant_mandate.triel" in r.stderr
    r = program(MANDATE, scn, "--evaluator", tmp_path / "no-evaluator")
    assert r.returncode == 1 and "cannot run the evaluator" in r.stderr
    bad = tmp_path / "bad.json"
    bad.write_text('{"scenario": "s", "spec": "x", "entries": [], "extra": 1}')
    r = program(MANDATE, bad, "--json")
    assert r.returncode == 1 and r.stdout == "" and "expected a scenario" in r.stderr
    assert "Traceback" not in r.stderr


def test_evaluator_without_last(tmp_path):
    """An evaluator that ignores --last (one built before it) is an error, not
    a report without a decision."""
    fake = tmp_path / "old-evaluator"
    fake.write_text("#!/bin/sh\ncat > /dev/null\necho 'ACTIVATION OK'\necho 'MONITOR 4 : ENTRY 4 BLOCK'\n")
    fake.chmod(0o755)
    scn = "examples/core/scenarios/mandate_campaign_budget.scn"
    if os.name != "nt":
        assert program(MANDATE, scn, "--evaluator", fake).returncode == 3
        r = program(MANDATE, scn, "--last", "--evaluator", fake)
        assert r.returncode == 1 and "printed no LAST line" in r.stderr and r.stdout == ""


@needs_evaluator
def test_evaluator_path_order(tmp_path):
    scn = "examples/core/scenarios/mandate_campaign_at_limit.scn"
    env = dict(os.environ, TRIEL_EVALUATOR=str(tmp_path / "no-evaluator"))
    r = program(MANDATE, scn, env=env)
    assert r.returncode == 1 and "no-evaluator" in r.stderr
    r = program(MANDATE, scn, "--evaluator", default_evaluator(), env=env)
    assert r.returncode == 0, r.stderr


# --- The JSON trace is checked like a .scn file --------------------------------------

ACTIVATE = '{"time": "2026-11-10T09:00:00Z", "event": {"kind": "activate"}, "data": %s}'


@pytest.mark.parametrize("data, message", [
    ('{"a": {"int": 1}, "a": {"int": 2}}', "a is given twice"),
    ('{"a": {"bool": "true"}}', "not a value"),
    ('{"a": {"int": 1.0}}', "not a value"),
    ('{"a": {"int": true}}', "not a value"),
    ('{"a": {"dec": 1.5}}', "not a value"),
    ('{"a": {"dec": "1"}}', "not a value"),
    ('{"a": {"time": "2026-11-10 09:00:00"}}', "not an ISO-8601 UTC time"),
    ('{"a": {"int": 1, "dec": "1.0"}}', "not a value"),
    ('{"a b": {"int": 1}}', "not a name"),
    ('{"a": {"int": NaN}}', "not JSON"),
    ('[]', "expected the data as an object"),
])
def test_json_trace_errors(data, message, tmp_path, capsys):
    trace = tmp_path / "t.json"
    trace.write_text('{"scenario": "s", "spec": "%s", "entries": [%s]}' % (MANDATE, ACTIVATE % data))
    code, out, err = check(capsys, MANDATE, trace)
    assert code == 1 and out == "" and message in err


@pytest.mark.parametrize("text, message", [
    ('{"scenario": "s", "spec": "%s", "entries": []}' % MANDATE, "needs the activation entry"),
    ('{"scenario": "s", "spec": "%s", "entries": [%s], "x": 1}' % (MANDATE, ACTIVATE % "{}"),
     "expected a scenario"),
    ('{"scenario": "s", "spec": "%s", "entries": [{"time": "2026-11-10T09:00:00Z", '
     '"event": {"kind": "tick"}, "data": {}}]}' % MANDATE, "the first entry must be (activate)"),
    ('{"scenario": "s", "spec": "%s", "entries": [%s, {"time": "2026-11-10T09:00:00Z", '
     '"event": {"kind": "act", "subject": "agent", "action": "x", "polarity": "should"}, '
     '"data": {}}]}' % (MANDATE, ACTIVATE % "{}"), "not an event"),
    ('{"scenario": "s", "spec": "%s", "entries": [%s, {"time": "2026-11-10T09:00:00Z", '
     '"event": {"kind": "act", "subject": "agent", "action": {"name": "x", "args": '
     '[{"record": {}}]}, "polarity": "must"}, "data": {}}]}' % (MANDATE, ACTIVATE % "{}"),
     "not an argument"),
    ('{"scenario": "s", "spec": "%s", "entries": [%s, {"time": "2026-11-10T09:00:00Z", '
     '"event": {"kind": "activate"}, "data": {}}]}' % (MANDATE, ACTIVATE % "{}"),
     "only in the first entry"),
    ('{"scenario": "s", "spec": "x', "not JSON"),
])
def test_json_trace_structure_errors(text, message, tmp_path, capsys):
    trace = tmp_path / "t.json"
    trace.write_text(text)
    code, out, err = check(capsys, MANDATE, trace)
    assert code == 1 and out == "" and message in err


# --- Report lines and their JSON --------------------------------------------------------

@pytest.mark.parametrize("line", [
    "SPEC t",
    "METADATA JURISDICTION \"EU\"",
    "METADATA DID holder \"did:example:holder 17\"",
    "METADATA PROVES residence self IN SET {\"EU\", \"EEA\"}",
    "METADATA BOUND_TO income holder session_nonce",
    "METADATA SOURCE amount alice",
    "METADATA POLARITY delay_days -1.0",
    "REJECTED: AND (term); EXECUTE",
    "TIME ORDER REJECTED ENTRY 2",
    "ACTIVATION REJECTED",
    "BLOCK REJECTED",
    "TYPES ILL-TYPED ENTRY 1 FACTOR amount",
    "TERM 1 MUST a b DEADLINE NONE : PENDING",
    "TERM 1 MUST a b DEADLINE 10 : BREACHED 10 CLOSED",
    "TERM 1 MUST a b DEADLINE 10 : BREACHED 10 TERMINATED",
    "TERM 1 MUST a b DEADLINE 10 : BREACHED 10 NOTIFY c PENALTY 1/3 PENALTY 5 CAPPED ESCALATED d PENDING",
    "TERM 1 MUST a b DEADLINE 10 : BREACHED 10 PENALTY UNDEFINED PENALTY NEGATIVE -2.5 CURE BREACHED 20",
    'TERM 1 MUST a pay(c, "x : y", "(", "say \\"hi\\"", -1.5) DEADLINE -5 : FULFILLED',
    "TERM 1 MUST a b DEADLINE 10 ELSE c d DEADLINE NONE : ELSE PENDING",
    "TERM 2 MUST_NOT a b : PENDING",
    "TERM 2 MAY a b(x.y) : FULFILLED",
    "TERM 3 ON_BREACH a : UNBOUND",
    "TERM 4 COMPOSITE : DONE UNKNOWN INTERRUPTED NO VIOLATED YES STATUS UNKNOWN",
    "INVARIANT i : F",
    "MONITOR 2 : ENTRY 1 BLOCK",
    "LAST ENTRY 0 : NO DECISION",
    "LAST ENTRY 3 : MONITOR 1 ALLOW MONITOR 2 BLOCK",
])
def test_report_line_round_trip(line):
    o = triel.report_json(line)
    assert triel.report_line(o) == line
    assert triel.report_line(json.loads(json.dumps(o))) == line


@pytest.mark.parametrize("line", [
    "",
    "SPEC",
    "FOO bar",
    "ACTIVATION  OK",
    "ACTIVATION OK ",
    "ACTIVATION MAYBE",
    "TERM 1 MUST a b",
    "TERM 1 MAY a b : PENDING extra",
    "TERM x MAY a b : PENDING",
    "TERM 1 MUST a b DEADLINE 10 : BREACHED 10 NOTIFY c",
    'TERM 1 MUST a pay("x) DEADLINE 1 : PENDING',
    "MONITOR 1 :",
    "LAST ENTRY 1 : MONITOR 1 MAYBE",
])
def test_report_line_refused(line):
    with pytest.raises(triel.BadLine):
        triel.report_json(line)


def test_json_lines_describe_the_report_line_kinds():
    """Every kind of line of examples/core/README.md, Output, is named in the
    JSON section of evaluator/README.md with its fields."""
    doc = (REPO / "evaluator/README.md").read_text(encoding="utf-8")
    for kind in ["SPEC", "METADATA", "REJECTED", "TIME ORDER REJECTED", "ACTIVATION", "BLOCK",
                 "TYPES", "TERM", "INVARIANT", "MONITOR", "LAST"]:
        assert f'`"line": "{kind}"`' in doc, kind


def readme_blocks(lang: str):
    """The fenced blocks of evaluator/README.md whose info string is lang."""
    out, info = [], None
    for line in (REPO / "evaluator/README.md").read_text(encoding="utf-8").splitlines(keepends=True):
        if info is None and line.startswith("```"):
            info, body = line[3:].strip(), []
        elif info is not None and line.strip() == "```":
            if info == lang:
                out.append("".join(body))
            info = None
        elif info is not None:
            body.append(line)
    return out


@needs_evaluator
def test_readme_example(capsys):
    """The example of evaluator/README.md is the output of the command."""
    scn = SCN / "mandate_price_over_limit.scn"
    code, out, _ = check(capsys, MANDATE, scn, "--last")
    shown = [b for b in readme_blocks("") if b.startswith("SPEC merchant_mandate")]
    assert shown == [out] and code == 3


@needs_evaluator
def test_readme_json_trace(tmp_path, capsys):
    """The JSON trace of evaluator/README.md is mandate_price_over_limit.scn."""
    scn = SCN / "mandate_price_over_limit.scn"
    [text] = [b for b in readme_blocks("json") if b.startswith('{"scenario"')]
    assert sexp(scenario_input(triel.read_trace(text))) \
        == sexp(scenario_input(read_sexp(scn.read_text(encoding="utf-8"))))
    trace = tmp_path / "t.json"
    trace.write_text(text, encoding="utf-8")
    code, out, _ = check(capsys, MANDATE, trace)
    assert out.splitlines() == expected(scn) and code == 3
