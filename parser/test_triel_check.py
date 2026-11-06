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
import re
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


# The exit code of every scenario, without and with --last, written from the
# .expected files and the number of entries of the .scn files, independently of
# parser/triel.py: 4 if a line rejects the trace; then 3 if a MONITOR line (with
# --last: the decisions at the last entry) has BLOCK; then, without --last, 6 if
# a TERM line has BREACHED or ELSE BREACHED after its colon, a composite line
# STATUS VIOLATED or an invariant F, and with --last 5 if no monitor decided on
# the last entry; otherwise 0.
CODES = {
    "age_verification_breach": (6, 5), "commitment_boundary": (6, 5),
    "commitment_missing_data": (6, 5), "commitment_pending": (6, 5), "commitment_rejected": (4, 4),
    "conditional_cancelled": (0, 5), "conditional_elif": (0, 5), "conditional_express": (0, 5),
    "conditional_undefined": (0, 5), "deadline_cure_failed": (3, 3),
    "deadline_cure_ill_typed": (4, 4), "deadline_cure_ok": (6, 0),
    "deadline_cure_time_order": (4, 4), "fallback_breached": (6, 5), "fallback_on_time": (0, 5),
    "fallback_order_equal": (4, 4), "fallback_order_ok": (0, 5), "fallback_order_rejected": (4, 4),
    "fallback_pending": (0, 5), "fallback_taken": (0, 5), "gdpr_data_subjects_only": (6, 5),
    "gdpr_no_notification": (6, 5), "gdpr_notified_48h": (0, 5), "gdpr_notified_at_72h": (0, 5),
    "gdpr_notified_day_11": (6, 5), "gdpr_notified_day_5": (6, 5), "hidden_invalid_proof": (3, 3),
    "hidden_valid": (0, 0), "hidden_value_ignored": (0, 0), "hidden_visible_ill_typed": (4, 4),
    "invoice_approval_missing": (3, 3), "invoice_approved": (0, 0), "invoice_over_limit": (3, 3),
    "invoice_owner_fallback": (0, 5), "invoice_owner_late": (6, 5), "invoice_stale_quote": (3, 3),
    "invoice_within_limit": (0, 0), "low_stock_at_deadline": (0, 5),
    "low_stock_known_at_deadline": (0, 5), "low_stock_late_restock": (6, 5),
    "low_stock_missed": (6, 5), "low_stock_restocked": (0, 5),
    "mandate_budget_limit_absent": (3, 3), "mandate_budget_limit_zero": (6, 5),
    "mandate_campaign_at_limit": (0, 0), "mandate_campaign_budget": (3, 3),
    "mandate_price_approval_cleared": (3, 3), "mandate_price_approval_missing": (3, 3),
    "mandate_price_approved": (0, 0), "mandate_price_at_limit": (0, 0),
    "mandate_price_decrease_signed": (0, 0), "mandate_price_over_limit": (3, 3),
    "mandate_price_within_limit": (0, 0), "mandate_price_within_limit_no_approval": (0, 0),
    "mandate_restock_approved_fresh": (0, 0), "mandate_restock_at_reorder_point": (0, 0),
    "mandate_restock_fresh_low": (0, 0), "mandate_restock_max_age": (0, 0),
    "mandate_restock_max_age_passed": (3, 3), "mandate_restock_not_needed": (3, 3),
    "mandate_restock_stale": (3, 3), "mandate_restock_stale_approved": (0, 0),
    "mandate_restock_stale_no_approval": (3, 3), "mandate_two_changes": (3, 3),
    "numbers_breach": (3, 5), "numbers_exact": (6, 0), "numbers_ill_typed": (4, 4),
    "payment_capped": (3, 5), "payment_cured": (6, 5), "payment_negative": (3, 3),
    "payment_undefined": (3, 5), "prohibition_handler_breach": (3, 3), "purpose_consented": (0, 0),
    "purpose_no_route": (3, 3), "purpose_not_on_record": (3, 3),
    "purpose_stale_assessment": (3, 3), "readings_guard_after_pay": (6, 5),
    "readings_guard_at_pay": (0, 5), "readings_guard_at_pay_leak": (6, 5),
    "readings_leak_then_pay": (6, 5), "readings_or_pay_leak": (6, 5), "sensor_at_limit": (3, 5),
    "sensor_escalation_missed": (6, 5), "sensor_escalation_window": (6, 5),
    "sensor_handled": (0, 0), "sensor_max_age_boundary": (0, 0), "sensor_never_false": (0, 5),
    "sensor_not_stopped": (3, 5), "sensor_silent": (3, 5), "sensor_stale": (3, 3),
    "sensor_stop_at_deadline": (0, 5), "sequence_one_payment": (0, 5), "sequence_polarity": (6, 5),
    "sequence_prohibition_violated": (6, 5), "sequence_two_payments": (0, 5),
    "sequence_violation_not_last": (6, 5), "sequence_violation_then_done": (6, 5),
    "stale_block_fresh_breach": (3, 3), "stale_block_undefined_guard": (3, 5),
    "unless_records_cancelled": (0, 5), "unless_records_completed": (0, 5),
}


SCN = REPO / "examples/core/scenarios"

needs_sh = pytest.mark.skipif(os.name == "nt", reason="the stub evaluator is a shell script")


def stub(tmp_path, lines, last_line=None):
    """An evaluator that prints the given lines whatever its input, and with
    --last also last_line: for reports that no scenario of the repository has."""
    f = tmp_path / "stub-evaluator"
    script = ["#!/bin/sh", "cat > /dev/null"] + [f"echo '{line}'" for line in lines]
    if last_line is not None:
        script.append(f"[ \"$1\" = --last ] && echo '{last_line}'")
    f.write_text("\n".join(script + ["exit 0"]) + "\n")
    f.chmod(0o755)
    return f


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
    assert code == CODES[scn.stem][0]


@needs_evaluator
@pytest.mark.parametrize("scn", SCENARIOS, ids=IDS)
def test_json_converts_back_to_the_expected_report(scn, capsys):
    code, out, err = check(capsys, spec_of(scn), scn, "--json")
    objs = json.loads(out)
    assert isinstance(objs, list) and all(isinstance(o, dict) for o in objs)
    assert [triel.report_line(o) for o in objs] == expected(scn), err
    assert code == CODES[scn.stem][0]


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
    assert code == code_json == CODES[scn.stem][0]


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
    assert code == CODES[scn.stem][1]


def test_the_table_has_every_scenario():
    assert sorted(CODES) == IDS


# --- --last on chosen scenarios ---------------------------------------------------


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
def test_last_no_decision_on_a_tick(capsys):
    code, out, _ = check(capsys, MANDATE, SCN / "mandate_budget_limit_zero.scn", "--last")
    assert out.splitlines()[-1] == "LAST ENTRY 1 : NO DECISION" and code == 5


@needs_evaluator
def test_last_no_decision_on_a_nested_prohibition(capsys):
    """The leak violates a composite term, whose prohibition has no monitor."""
    scn = SCN / "sequence_prohibition_violated.scn"
    code, out, _ = check(capsys, "examples/core/core_sequence.triel", scn, "--last")
    lines = out.splitlines()
    assert "TERM 1 COMPOSITE : DONE NO INTERRUPTED NO VIOLATED YES STATUS VIOLATED ENTRY 2" in lines
    assert lines[-1] == "LAST ENTRY 2 : NO DECISION" and code == 5
    code, _, _ = check(capsys, "examples/core/core_sequence.triel", scn)
    assert code == 6


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


def with_tick(trace: str, time: str) -> str:
    """The JSON trace with a tick appended, with the data of its last entry."""
    x = json.loads(trace)
    x["entries"].append({"time": time, "event": {"kind": "tick"}, "data": x["entries"][-1]["data"]})
    return json.dumps(x)


@needs_evaluator
def test_last_no_decision_on_a_tick_after_a_block(tmp_path, capsys):
    trace = tmp_path / "campaign_then_tick.json"
    trace.write_text(with_tick(campaign("7500.00"), "2026-11-10T09:20:02Z"))
    code, out, _ = check(capsys, MANDATE, trace)
    assert "MONITOR 4 : ENTRY 2 BLOCK" in out.splitlines() and code == 3
    code, out, _ = check(capsys, MANDATE, trace, "--last")
    assert out.splitlines()[-1] == "LAST ENTRY 3 : NO DECISION" and code == 5


@needs_evaluator
def test_last_no_decision_on_the_activation_entry_alone(tmp_path, capsys):
    trace = tmp_path / "activation.json"
    trace.write_text(campaign())
    code, out, _ = check(capsys, MANDATE, trace, "--last")
    assert out.splitlines()[-1] == "LAST ENTRY 0 : NO DECISION" and code == 5
    code, out, _ = check(capsys, MANDATE, trace)
    assert code == 0, out


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
    # A specification rejected by the translator is 2, not the 4 of a rejected trace.
    r = program("examples/semantics/execute_renaming.triel", scn, "--last")
    assert r.returncode == 2 and r.stdout.splitlines()[-1] == "REJECTED: EXECUTE"


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


# --- Exit code 4: the evaluator rejects the trace --------------------------------------

@needs_evaluator
@pytest.mark.parametrize("spec, scn, line", [
    ("examples/core/core_deadline_cure.triel", "deadline_cure_time_order", "TIME ORDER REJECTED ENTRY 2"),
    ("examples/core/core_commitment.triel", "commitment_rejected", "ACTIVATION REJECTED"),
    ("examples/core/core_numbers.triel", "numbers_ill_typed", "TYPES ILL-TYPED ENTRY 0 FACTOR order"),
])
def test_rejected_trace(spec, scn, line):
    for args in ([], ["--last"]):
        r = program(spec, SCN / f"{scn}.scn", *args)
        assert r.returncode == 4, r.stderr
        assert line in r.stdout.splitlines()


@needs_sh
def test_rejected_trace_block(tmp_path):
    """BLOCK REJECTED, which no scenario has."""
    ev = stub(tmp_path, ["ACTIVATION OK", "BLOCK REJECTED"], "LAST ENTRY 4 : NO DECISION")
    for args in ([], ["--last"]):
        r = program(MANDATE, SCN / "mandate_campaign_budget.scn", "--evaluator", ev, *args)
        assert r.returncode == 4, r.stderr
        assert "BLOCK REJECTED" in r.stdout.splitlines()


@needs_evaluator
@pytest.mark.parametrize("old, new, line", [
    ("2026-11-10T09:10:01Z", "2026-11-10T09:09:59Z", "TIME ORDER REJECTED ENTRY 2"),
    ("(price_delta_pct (dec 35.0)) (price_change_approved (bool false))))\n  (entry",
     '(price_delta_pct (str "35")) (price_change_approved (bool false))))\n  (entry',
     "TYPES ILL-TYPED ENTRY 1 FACTOR price_delta_pct"),
])
def test_rejected_trace_is_not_allowed(old, new, line, tmp_path, capsys):
    """The traces of the review: the change blocked on the trace as recorded is
    neither 0 nor 3 when the trace is rejected."""
    text = (SCN / "mandate_price_over_limit.scn").read_text(encoding="utf-8")
    assert old in text
    trace = tmp_path / "rejected.scn"
    trace.write_text(text.replace(old, new, 1), encoding="utf-8")
    for args in ([], ["--last"]):
        code, out, _ = check(capsys, MANDATE, trace, *args)
        assert line in out.splitlines() and code == 4


# --- Exit code 6: a violation, without --last ---------------------------------------------

@needs_evaluator
@pytest.mark.parametrize("scn, form", [
    ("age_verification_breach", r"^TERM .* : BREACHED \d+ "),
    ("fallback_breached", r"^TERM .* : ELSE BREACHED \d+$"),
    ("gdpr_notified_day_5", r"^TERM .* : BREACHED \d+ CURE FULFILLED$"),
    ("sequence_violation_not_last", r"^TERM \d+ COMPOSITE : .* VIOLATED NO STATUS VIOLATED ENTRY \d+$"),
    ("numbers_exact", r"^INVARIANT \S+ : F$"),
])
def test_violation(scn, form, capsys):
    """Each form of a violation alone gives 6, with no BLOCK in the report."""
    code, out, _ = check(capsys, spec_of(SCN / f"{scn}.scn"), SCN / f"{scn}.scn")
    lines = out.splitlines()
    assert any(re.search(form, line) for line in lines)
    assert not any(line.startswith("MONITOR ") and " BLOCK" in line for line in lines)
    assert code == 6


@needs_evaluator
def test_composite_violated_no_is_not_a_violation(capsys):
    scn = SCN / "sequence_two_payments.scn"
    code, out, _ = check(capsys, spec_of(scn), scn)
    assert any(" VIOLATED NO STATUS " in line for line in out.splitlines()) and code == 0


@needs_sh
def test_composite_violated_yes_with_status_done_is_not_a_violation(tmp_path, capsys):
    ev = stub(tmp_path, ["ACTIVATION OK", "BLOCK OK", "TYPES OK",
                         "TERM 1 COMPOSITE : DONE NO INTERRUPTED NO VIOLATED YES STATUS DONE ENTRY 1"])
    code, _, _ = check(capsys, MANDATE, SCN / "mandate_campaign_budget.scn", "--evaluator", ev)
    assert code == 0


def test_violation_rule_catches_every_breach_line():
    """Against format drift: in the 101 .expected files, the rule catches
    exactly the TERM lines with the word BREACHED, the lines with the words
    STATUS VIOLATED, and the invariants F."""
    lines = [line for scn in SCENARIOS for line in expected(scn)]
    caught = [line for line in lines if triel.violation(triel.report_json(line))]
    breached = [line for line in lines if line.startswith("TERM ") and "BREACHED" in line.split()]
    status_violated = [line for line in lines if " STATUS VIOLATED " in f" {line} "]
    invariant_false = [line for line in lines if line.startswith("INVARIANT ") and line.endswith(" : F")]
    assert len(breached) == 34 and len(status_violated) == 15 and len(invariant_false) == 13
    assert sorted(caught) == sorted(breached + status_violated + invariant_false)
    assert sum(" COMPOSITE " in line for line in caught) == len(status_violated)


# --- The order of the codes ---------------------------------------------------------------

@needs_evaluator
@pytest.mark.parametrize("scn", ["purpose_no_route", "deadline_cure_failed"])
def test_block_before_violation(scn, capsys):
    code, out, _ = check(capsys, spec_of(SCN / f"{scn}.scn"), SCN / f"{scn}.scn")
    lines = out.splitlines()
    assert any(re.search(r"^TERM .* : BREACHED ", line) for line in lines)
    assert any(line.startswith("MONITOR ") and " BLOCK" in line for line in lines) and code == 3
    if scn == "purpose_no_route":
        assert "MONITOR 2 : ENTRY 3 BLOCK" in lines


CURED = "TERM 1 MUST a b DEADLINE 10 : BREACHED 10 CURE FULFILLED"


@needs_sh
@pytest.mark.parametrize("lines, last_line, codes", [
    # A cured breach and a block: 3; the cured breach alone: 6.
    ([CURED, "MONITOR 2 : ENTRY 4 BLOCK"], None, (3, 1)),
    ([CURED, "MONITOR 2 : ENTRY 4 ALLOW"], None, (6, 1)),
    # A rejected trace before a block.
    (["TYPES ILL-TYPED ENTRY 1 FACTOR f", "MONITOR 2 : ENTRY 4 BLOCK"], None, (4, 1)),
    # With --last only the LAST line counts, after a rejection.
    ([CURED, "MONITOR 2 : ENTRY 4 BLOCK"], "LAST ENTRY 4 : MONITOR 2 BLOCK", (3, 3)),
    ([CURED, "MONITOR 2 : ENTRY 2 BLOCK ENTRY 4 ALLOW"], "LAST ENTRY 4 : MONITOR 2 ALLOW", (3, 0)),
    ([CURED, "INVARIANT i : F"], "LAST ENTRY 4 : NO DECISION", (6, 5)),
    (["ACTIVATION REJECTED"], "LAST ENTRY 4 : NO DECISION", (4, 4)),
    (["MONITOR 2 : ENTRY 4 ALLOW", "MONITOR 3 : ENTRY 4 BLOCK"],
     "LAST ENTRY 4 : MONITOR 2 ALLOW MONITOR 3 BLOCK", (3, 3)),
])
def test_order_of_the_codes(lines, last_line, codes, tmp_path, capsys):
    ev = stub(tmp_path, lines, last_line)
    scn = SCN / "mandate_campaign_budget.scn"
    assert check(capsys, MANDATE, scn, "--evaluator", ev)[0] == codes[0]
    assert check(capsys, MANDATE, scn, "--evaluator", ev, "--last")[0] == codes[1]


@needs_sh
@pytest.mark.parametrize("lines, last_line, args", [
    (["MONITOR 4 : ENTRY 4 BLOCK"], "LAST ENTRY 4 : MONITOR 4 MAYBE", ["--last"]),
    (["MONITOR 4 : ENTRY 4 BLOCK"], "LAST ENTRY 4 :", ["--last"]),
    (["MONITOR 4 : ENTRY 4 BLOCK", "LAST ENTRY 4 : MONITOR 4 BLOCK"], None, []),
    (["MONITOR 4 : ENTRY 4 MAYBE"], None, []),
    (["SOMETHING ELSE"], None, []),
])
def test_report_not_recognised(lines, last_line, args, tmp_path, capsys):
    """A LAST line that is not one of its forms, or a line that is not a line
    of the report, is an error, 1, with nothing on standard output."""
    ev = stub(tmp_path, lines, last_line)
    code, out, err = check(capsys, MANDATE, SCN / "mandate_campaign_budget.scn", "--evaluator", ev, *args)
    assert code == 1 and out == "" and "cannot read the report" in err


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
