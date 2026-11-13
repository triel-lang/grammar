"""Tests of the trace of a host (parser/triel_host.py) and of the subcommand
--actions of the translator (parser/triel_to_core.py).

Run from the root of the repository, once the evaluator is built
(evaluator/README.md):

    python3 -m pytest -q parser/test_host.py

The test does not skip: without the evaluator it fails. Times are arguments;
nothing waits. Every trace that triel_host builds is run with triel check
--last in this process.
"""
import functools
import json
import os
import re
import subprocess
import sys
from decimal import Decimal
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent))
import triel  # noqa: E402
import triel_host as th  # noqa: E402
from triel_eval import default_evaluator  # noqa: E402
from triel_host import NO_NEW_READING, Reading, seconds  # noqa: E402
from triel_to_core import header, pretty, show_string, translate  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
TRANSLATOR = str(REPO / "parser" / "triel_to_core.py")
ACT = "2026-11-13T09:00:00Z"


@pytest.fixture(scope="session", autouse=True)
def evaluator():
    exe = default_evaluator()
    assert os.path.isfile(exe) and os.access(exe, os.X_OK), \
        f"no evaluator at {exe}: build it first (evaluator/README.md); this test does not skip"
    return exe


@functools.lru_cache(maxsize=None)
def _translate(text):
    return translate(text)


@pytest.fixture(autouse=True)
def translate_once(monkeypatch):
    monkeypatch.setattr(triel, "translate", _translate)


def spec_text(terms, factors, name="host_case"):
    return (f"SPECIFICATION {name} VERSION 1.0.0\n\nSUBJECTS {{\n  agent : SYSTEM,\n"
            f"  supplier : PARTY\n}}\n\nTERMS {{\n  {terms}\n}}\n\nFACTORS {{\n  {factors}\n}}\n\n"
            "INVARIANTS {\n  i : SAFETY : ALWAYS(true)\n}\n")


def write_spec(tmp_path, terms, factors, name="host_case"):
    p = tmp_path / f"{name}.triel"
    p.write_text(spec_text(terms, factors, name), encoding="utf-8")
    return p


def t(s):
    return seconds(s)


class Host:
    """A host that records the activation and the executed actions and asks
    triel check --last before each action."""

    def __init__(self, tmp_path, spec, answers, at=ACT):
        self.tmp, self.spec = tmp_path, spec
        self.factors = th.spec_factors(spec.read_text(encoding="utf-8"))
        self.activation, self.store, reasons = th.activation(self.factors, answers, t(at))
        assert reasons == []
        self.history, self.n = [], 0

    def decide(self, answers, h, action="pay", subject="agent"):
        """(2, reasons) if the host holds the action, else (exit code, report lines, trace)."""
        trace, self.store, reasons, data = th.decide(
            self.factors, str(self.spec), self.activation, self.history, self.store, answers,
            subject, action, t(h))
        self.data = data
        if reasons:
            return 2, reasons, None
        self.n += 1
        p = self.tmp / f"trace{self.n}.json"
        p.write_text(json.dumps(trace), encoding="utf-8")
        code, lines = triel.check(str(self.spec), str(p), last=True)
        return code, lines, trace

    def executed(self, h, at, action="pay", subject="agent"):
        self.history.append({"subject": subject, "action": action, "decided": th.exact(t(h)),
                             "executed": th.exact(t(at)), "data": self.data})


def run_trace(tmp_path, spec, entries):
    p = tmp_path / "hand.json"
    p.write_text(json.dumps({"scenario": "hand", "spec": str(spec), "entries": entries}),
                 encoding="utf-8")
    return triel.check(str(spec), str(p), last=True)


def entry(time, event, data):
    return {"time": time, "event": event, "data": data}


TICK, ARRIVE = {"kind": "tick"}, {"kind": "arrive", "factor": "f"}
PAY = {"kind": "act", "subject": "agent", "action": "pay", "polarity": "must_not"}
TRUE = {"bool": True}


# --- A.1 and A.2: the activation, the history, the tick and the action -------

def test_activation_history_tick_and_action(tmp_path):
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN limit < 10",
                      "limit : Integer METADATA")
    host = Host(tmp_path, spec, {"limit": 20}, at="2026-11-13T09:00:00.6Z")
    code, lines, trace = host.decide({"limit": 20}, "2026-11-13T09:10:00.2Z")
    assert code == 0 and lines[-1] == "LAST ENTRY 2 : MONITOR 1 ALLOW"
    e = trace["entries"]
    # entry 0: the activation, its time rounded down; then the tick and the act at T,
    # the host clock rounded up, with the same data
    assert [x["event"]["kind"] for x in e] == ["activate", "tick", "act"]
    assert e[0]["time"] == "2026-11-13T09:00:00Z" and e[0]["data"] == {"limit": {"int": 20}}
    assert e[1]["time"] == e[2]["time"] == "2026-11-13T09:10:01Z"
    assert e[1]["data"] == e[2]["data"] == {"limit": {"int": 20}}
    # a held action never enters the history; an executed one does, with its tick
    # entry, at the time of execution E, never earlier than T
    host.executed("2026-11-13T09:10:00.2Z", "2026-11-13T09:10:00.5Z")
    code, lines, trace = host.decide({"limit": 5}, "2026-11-13T09:20:00Z")
    assert code == 3 and lines[-1] == "LAST ENTRY 4 : MONITOR 1 BLOCK"
    e = trace["entries"]
    assert [(x["time"], x["event"]["kind"]) for x in e[1:3]] == [
        ("2026-11-13T09:10:01Z", "tick"), ("2026-11-13T09:10:01Z", "act")]
    host.executed("2026-11-13T09:20:00Z", "2026-11-13T09:25:07.1Z")
    code, lines, trace = host.decide({"limit": 20}, "2026-11-13T09:30:00Z")
    assert [(x["time"], x["event"]["kind"]) for x in trace["entries"][3:5]] == [
        ("2026-11-13T09:20:00Z", "tick"), ("2026-11-13T09:25:08Z", "act")]


def test_history_in_time_order(tmp_path):
    """An action executed late (a late PostToolUse) is placed by its time E."""
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN limit < 10", "limit : Integer METADATA")
    host = Host(tmp_path, spec, {"limit": 20})
    host.decide({"limit": 20}, "2026-11-13T09:10:00Z")
    host.executed("2026-11-13T09:10:00Z", "2026-11-13T09:40:00Z")
    host.decide({"limit": 20}, "2026-11-13T09:20:00Z")
    host.executed("2026-11-13T09:20:00Z", "2026-11-13T09:20:01Z")
    code, lines, trace = host.decide({"limit": 20}, "2026-11-13T09:50:00Z")
    times = [x["time"] for x in trace["entries"]]
    assert times == sorted(times) and code == 0
    assert [x["event"]["kind"] for x in trace["entries"]] == [
        "activate", "tick", "tick", "act", "act", "tick", "act"]


def test_the_clock_going_back_is_rejected_by_the_evaluator(tmp_path):
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN limit < 10", "limit : Integer METADATA")
    host = Host(tmp_path, spec, {"limit": 20})
    host.decide({"limit": 20}, "2026-11-13T09:10:00Z")
    host.executed("2026-11-13T09:10:00Z", "2026-11-13T09:10:00Z")
    code, lines, _ = host.decide({"limit": 20}, "2026-11-13T09:05:00Z")
    assert code == 4 and "TIME ORDER REJECTED ENTRY 3" in lines


# --- A.3 to A.5: readings of the factors with MAX_AGE --------------------------

BLOCK60 = "f : Boolean METADATA MAX_AGE 60 SECONDS ON_STALE BLOCK"


def test_a_value_without_a_source_time_is_held(tmp_path):
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN DEFAULT(f, false)", BLOCK60)
    host = Host(tmp_path, spec, {"f": NO_NEW_READING})
    for a in (True, Reading(True, None)):
        code, reasons, _ = host.decide({"f": a}, "2026-11-13T09:10:00Z")
        assert (code, reasons) == (2, ["factor f: a value without a source time"])


def test_readings_in_time_order_and_arrive_entries(tmp_path):
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN DEFAULT(f, false)", BLOCK60)
    host = Host(tmp_path, spec, {"f": Reading(False, "2026-11-13T08:59:00Z")})
    # a reading not later than the last accepted one is not accepted
    host.decide({"f": Reading(True, "2026-11-13T09:09:30.5Z")}, "2026-11-13T09:10:00Z")
    code, lines, trace = host.decide({"f": Reading(False, "2026-11-13T09:09:20Z")},
                                     "2026-11-13T09:10:10Z")
    assert code == 3
    assert [r[0] for r in host.store["f"]["accepted"]] == [th.exact(t("2026-11-13T08:59:00Z")),
                                                          th.exact(t("2026-11-13T09:09:30.5Z"))]
    # one arrive entry per accepted reading not earlier than the activation, at the
    # time of its source rounded down, with the value of the reading
    arr = [x for x in trace["entries"] if x["event"]["kind"] == "arrive"]
    assert [(x["time"], x["data"]["f"]) for x in arr] == [("2026-11-13T09:09:30Z", TRUE)]
    # the activation entry has the reading older than the activation as its value
    assert trace["entries"][0]["data"] == {"f": {"bool": False}}


def test_two_readings_with_one_time_hold_until_a_later_one(tmp_path):
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN DEFAULT(f, false)", BLOCK60)
    host = Host(tmp_path, spec, {"f": NO_NEW_READING})
    host.decide({"f": Reading(False, "2026-11-13T09:09:58.2Z")}, "2026-11-13T09:10:00Z")
    for h in ("2026-11-13T09:10:00Z", "2026-11-13T09:10:05Z"):
        a = Reading(True, "2026-11-13T09:09:58.2Z") if h.endswith("00Z") else NO_NEW_READING
        code, reasons, _ = host.decide({"f": a}, h)
        assert (code, reasons) == (2, ["factor f: two readings with one time"])
    # the same reading again is no conflict; a later reading ends the conflict
    code, lines, _ = host.decide({"f": Reading(True, "2026-11-13T09:10:06Z")},
                                 "2026-11-13T09:10:07Z")
    assert code == 3


def test_a_reading_from_the_future_is_kept_and_holds(tmp_path):
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN DEFAULT(f, false)", BLOCK60)
    host = Host(tmp_path, spec, {"f": NO_NEW_READING})
    code, reasons, _ = host.decide({"f": Reading(True, "2026-11-13T09:10:00.5Z")},
                                   "2026-11-13T09:10:00.4Z")
    assert (code, reasons) == (2, ["factor f: a reading from the future"])
    code, lines, trace = host.decide({"f": NO_NEW_READING}, "2026-11-13T09:10:00.5Z")
    assert code == 3 and trace["entries"][1]["time"] == "2026-11-13T09:10:00Z"


def test_use_last_has_no_arrive_entries_and_keeps_an_old_value(tmp_path):
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN DEFAULT(f, false)",
                      "f : Boolean METADATA MAX_AGE 60 SECONDS ON_STALE USE_LAST")
    assert th.spec_factors(spec.read_text())["f"]["stale"] == "use_last"
    host = Host(tmp_path, spec, {"f": NO_NEW_READING})
    code, lines, trace = host.decide({"f": Reading(True, "2026-11-13T09:09:59Z")},
                                     "2026-11-13T09:10:00Z")
    assert code == 3 and [x["event"]["kind"] for x in trace["entries"]] == [
        "activate", "tick", "act"]


def test_the_trace_never_shows_a_reading_fresher_than_it_is(tmp_path):
    """MAX_AGE 5 SECONDS: a reading 5.0 s old by the exact times is fresh in the
    trace when the times are whole seconds, and held when rounding makes it stale."""
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN DEFAULT(f, false)",
                      "f : Boolean METADATA MAX_AGE 5 SECONDS ON_STALE BLOCK")
    host = Host(tmp_path, spec, {"f": NO_NEW_READING})
    code, lines, _ = host.decide({"f": Reading(True, "2026-11-13T09:09:55Z")},
                                 "2026-11-13T09:10:00Z")
    assert code == 3
    # 5.2 s old: stale by the exact times; the trace says stale too, and the
    # action is allowed under DEFAULT(f, false), as the specification says
    host = Host(tmp_path, spec, {"f": NO_NEW_READING})
    code, lines, _ = host.decide({"f": Reading(True, "2026-11-13T09:09:55Z")},
                                 "2026-11-13T09:10:00.2Z")
    assert code == 0


# --- A.6: completeness and types ----------------------------------------------

def test_every_declared_factor_needs_an_answer_and_no_other_name(tmp_path):
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN DEFAULT(f, false)", "f : Boolean METADATA")
    host = Host(tmp_path, spec, {"f": None})
    assert host.decide({}, "2026-11-13T09:10:00Z")[:2] == (2, ["factor f: no answer from the host"])
    assert host.decide({"f": None, "ff": True}, "2026-11-13T09:10:00Z")[:2] == (
        2, ["ff: not a factor of the specification"])
    assert host.decide({"f": None}, "2026-11-13T09:10:00Z")[0] == 0
    assert host.decide({"f": True}, "2026-11-13T09:10:00Z")[0] == 3


def test_a_misspelt_factor_would_allow_and_is_held(tmp_path):
    """triel check does not reject an unknown name: the misspelt factor gives
    MONITOR 1 ALLOW and exit 0. The host holds the action instead."""
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN DEFAULT(f, false)", "f : Boolean METADATA")
    code, lines = run_trace(tmp_path, spec, [
        entry(ACT, {"kind": "activate"}, {}),
        entry("2026-11-13T09:10:00Z", TICK, {"g": TRUE}),
        entry("2026-11-13T09:10:00Z", PAY, {"g": TRUE})])
    assert code == 0 and lines[-1] == "LAST ENTRY 2 : MONITOR 1 ALLOW"
    host = Host(tmp_path, spec, {"f": None})
    assert host.decide({"g": True}, "2026-11-13T09:10:00Z")[:2] == (
        2, ["g: not a factor of the specification", "factor f: no answer from the host"])


def test_a_misspelt_field_of_a_record_would_allow_and_is_held(tmp_path):
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN DEFAULT(r.f, false)",
                      "r : Record { f : Optional<Boolean> } METADATA")
    code, lines = run_trace(tmp_path, spec, [
        entry(ACT, {"kind": "activate"}, {}),
        entry("2026-11-13T09:10:00Z", TICK, {"r": {"record": {"g": TRUE}}}),
        entry("2026-11-13T09:10:00Z", PAY, {"r": {"record": {"g": TRUE}}})])
    assert code == 0 and "TYPES OK" in lines and lines[-1] == "LAST ENTRY 2 : MONITOR 1 ALLOW"
    host = Host(tmp_path, spec, {"r": None})
    assert host.decide({"r": {"g": True}}, "2026-11-13T09:10:00Z")[:2] == (
        2, ["factor r: g is not a field of the record type"])
    assert host.decide({"r": {"f": True}}, "2026-11-13T09:10:00Z")[0] == 3
    assert host.decide({"r": {}}, "2026-11-13T09:10:00Z")[0] == 0


def test_nested_records(tmp_path):
    spec = write_spec(tmp_path, "agent MUST_NOT pay WHEN DEFAULT(r.s.f, false)",
                      "r : Record { s : Record { f : Optional<Boolean> }, n : Integer } METADATA")
    host = Host(tmp_path, spec, {"r": None})
    assert host.decide({"r": {"s": {"f": True, "x": 1}, "n": 1}}, "2026-11-13T09:10:00Z")[:2] == (
        2, ["factor r.s: x is not a field of the record type"])
    assert host.decide({"r": {"s": {"f": True}}}, "2026-11-13T09:10:00Z")[:2] == (
        2, ["factor r.n: no value for a field that is not Optional"])
    assert host.decide({"r": {"s": {"f": True}, "n": 1}}, "2026-11-13T09:10:00Z")[0] == 3


@pytest.mark.parametrize("value,expected", [
    (Decimal("12.50"), {"dec": "12.50"}), (12, {"dec": "12.0"}), ("12.5", {"dec": "12.5"}),
    ("-3", {"dec": "-3.0"}), (Decimal("1E+2"), {"dec": "100.0"}),
    (12.5, None), (True, None), (Decimal("NaN"), None), (Decimal("Infinity"), None),
    ("12,5", None), ("1e3", None)])
def test_decimal_values(value, expected):
    ty = ["prim", "decimal"]
    if expected is None:
        with pytest.raises(th.HostError, match="is not a value of the declared type Decimal"):
            th.typed(ty, value, "factor x")
    else:
        assert th.typed(ty, value, "factor x") == expected


@pytest.mark.parametrize("ty,value,expected", [
    (["prim", "bool"], True, {"bool": True}), (["prim", "bool"], 1, None),
    (["prim", "int"], 3, {"int": 3}), (["prim", "int"], True, None), (["prim", "int"], "3", None),
    (["prim", "int"], 3.0, None),
    (["prim", "string"], "EU", {"str": "EU"}), (["prim", "string"], 3, None),
    (["prim", "datetime"], "2026-11-13T09:00:00Z", {"time": "2026-11-13T09:00:00Z"}),
    (["prim", "datetime"], "2026-11-13T09:00:00.5Z", None),
    (["prim", "datetime"], 1794560400, None),
    (["optional", ["prim", "int"]], None, None), (["optional", ["prim", "int"]], 3, {"int": 3})])
def test_other_types(ty, value, expected):
    if expected is None and value is not None:
        with pytest.raises(th.HostError):
            th.typed(ty, value, "factor x")
    else:
        assert th.typed(ty, value, "factor x") == expected


def test_times():
    assert seconds("2026-11-13T09:09:55.9Z") == Decimal(1794561000 - 5) + Decimal("0.9")
    assert th.ceil_s(Decimal("10.1")) == 11 and th.floor_s(Decimal("10.9")) == 10
    for bad in (1.5, True, "2026-11-13T09:00:00", "yesterday"):
        with pytest.raises(ValueError):
            seconds(bad)


# --- A.7: the eight cases, under DEFAULT(f, false) and under PRESENT(f) AND f ----
#
# A reading true forbids the action; in none of the cases is the exit code 0.

CONDITIONS = {"DEFAULT": "DEFAULT(f, false)", "PRESENT": "PRESENT(f) AND f"}


def case_host(tmp_path, cond, clause="MAX_AGE 60 SECONDS ON_STALE BLOCK", at=ACT, first=None):
    spec = write_spec(tmp_path, f"agent MUST_NOT pay WHEN {cond}", f"f : Boolean METADATA {clause}")
    return Host(tmp_path, spec, {"f": first or NO_NEW_READING}, at=at)


def outcomes(host, steps, action="pay"):
    return [host.decide({"f": a}, h, action=action)[:2] for a, h in steps]


@pytest.fixture(params=sorted(CONDITIONS))
def cond(request):
    return CONDITIONS[request.param]


def test_case_a_a_later_false_out_of_order(tmp_path, cond):
    host = case_host(tmp_path, cond)
    out = outcomes(host, [(Reading(True, "2026-11-13T09:10:00.2Z"), "2026-11-13T09:10:00.5Z"),
                          (Reading(False, "2026-11-13T09:09:59Z"), "2026-11-13T09:10:05.5Z")])
    assert [c for c, _ in out] == [3, 3]


def test_case_b_a_value_without_a_source_time(tmp_path, cond):
    host = case_host(tmp_path, cond)
    assert outcomes(host, [(True, "2026-11-13T09:10:00Z")]) == [
        (2, ["factor f: a value without a source time"])]


def test_case_c_true_from_the_future_then_an_older_false(tmp_path, cond):
    host = case_host(tmp_path, cond)
    out = outcomes(host, [(Reading(True, "2026-11-13T09:10:30Z"), "2026-11-13T09:10:00Z"),
                          (Reading(False, "2026-11-13T09:10:05Z"), "2026-11-13T09:10:10Z"),
                          (NO_NEW_READING, "2026-11-13T09:10:31Z")])
    assert out[0] == out[1] == (2, ["factor f: a reading from the future"])
    assert out[2][0] == 3


@pytest.mark.parametrize("order", ["true first", "false first"])
def test_case_d_true_at_58_7_and_false_at_58_2(tmp_path, cond, order):
    true, false = Reading(True, "2026-11-13T09:09:58.7Z"), Reading(False, "2026-11-13T09:09:58.2Z")
    host = case_host(tmp_path, cond)
    first, second = (true, false) if order == "true first" else (false, true)
    # the first reading arrives with the decision on another action, which no
    # prohibition names (exit 5); the second with the decision on pay
    assert outcomes(host, [(first, "2026-11-13T09:10:00Z")], action="inspect")[0][0] == 5
    assert outcomes(host, [(second, "2026-11-13T09:10:01Z")])[0][0] == 3


def test_case_d_equal_times_with_different_values(tmp_path, cond):
    host = case_host(tmp_path, cond)
    out = outcomes(host, [(Reading(False, "2026-11-13T09:09:58.7Z"), "2026-11-13T09:10:00Z"),
                          (Reading(True, "2026-11-13T09:09:58.7Z"), "2026-11-13T09:10:01Z")])
    assert out[1] == (2, ["factor f: two readings with one time"])


def test_case_e_max_age_5_rounding(tmp_path, cond):
    host = case_host(tmp_path, cond, "MAX_AGE 5 SECONDS ON_STALE BLOCK")
    assert outcomes(host, [(Reading(True, "2026-11-13T09:09:55.9Z"), "2026-11-13T09:10:00.1Z")]) == [
        (2, ["factor f: a fresh reading that the trace cannot express"])]
    # the trace without the hold: the arrive entry at 09:09:55 and the tick at
    # 09:10:01 make f stale, and the action would be allowed
    spec = tmp_path / "host_case.triel"
    code, lines = run_trace(tmp_path, spec, [
        entry(ACT, {"kind": "activate"}, {}),
        entry("2026-11-13T09:09:55Z", ARRIVE, {"f": TRUE}),
        entry("2026-11-13T09:10:01Z", TICK, {"f": TRUE}),
        entry("2026-11-13T09:10:01Z", PAY, {"f": TRUE})])
    assert code == 0


def test_case_f_a_reading_before_the_activation(tmp_path, cond):
    host = case_host(tmp_path, cond)
    assert outcomes(host, [(Reading(True, "2026-11-13T08:59:30Z"), "2026-11-13T09:00:10Z")]) == [
        (2, ["factor f: a fresh reading that the trace cannot express"])]
    # given at the activation, the same reading holds too
    host = case_host(tmp_path, cond, first=Reading(True, "2026-11-13T08:59:30Z"))
    assert outcomes(host, [(NO_NEW_READING, "2026-11-13T09:00:10Z")]) == [
        (2, ["factor f: a fresh reading that the trace cannot express"])]
    # and stale by the exact times, the specification decides: f is absent
    assert outcomes(host, [(NO_NEW_READING, "2026-11-13T09:00:31Z")])[0][0] == 0


def test_case_g_use_last_of_any_age(tmp_path, cond):
    host = case_host(tmp_path, cond, "MAX_AGE 60 SECONDS ON_STALE USE_LAST",
                     first=Reading(True, "2026-11-12T09:00:00Z"))
    assert outcomes(host, [(NO_NEW_READING, "2026-11-13T09:10:00Z")])[0][0] == 3


def test_case_h_no_new_reading_after_a_fresh_true(tmp_path, cond):
    host = case_host(tmp_path, cond)
    out = outcomes(host, [(Reading(True, "2026-11-13T09:09:59.5Z"), "2026-11-13T09:10:00Z"),
                          (NO_NEW_READING, "2026-11-13T09:10:10Z")])
    assert [c for c, _ in out] == [3, 3]


# --- B: triel_to_core.py --actions -------------------------------------------------

def actions(path):
    r = subprocess.run([sys.executable, TRANSLATOR, "--actions", str(path)], capture_output=True,
                       text=True, encoding="utf-8", cwd=REPO)
    return r


def report_of(tmp_path, spec):
    """The report of triel check on the trace of the activation alone."""
    code, lines = run_trace(tmp_path, spec, [entry(ACT, {"kind": "activate"}, {})])
    assert code == 5, lines  # the activation entry: NO DECISION
    return lines


def check_against_report(tmp_path, spec):
    """--actions agrees with the TERM and MONITOR lines of the report."""
    r = actions(spec)
    assert r.returncode == 0 and r.stderr == ""
    objs = json.loads(r.stdout)
    report = [triel.report_json(x) for x in report_of(tmp_path, spec)]
    terms = {o["term"]: (o["kind"], o.get("subject"), o.get("action"))
             for o in report if o["line"] == "TERM"}
    monitors = {o["term"] for o in report if o["line"] == "MONITOR"}
    seen = set()
    for o in objs:
        assert set(o) == {"subject", "action", "monitors", "monitor_actions",
                          "composite_prohibitions"}
        assert (o["subject"], o["action"]) not in seen
        seen.add((o["subject"], o["action"]))
        assert sorted(o["monitor_actions"]) == sorted(str(i) for i in o["monitors"])
        for i in o["monitors"]:
            kind, subject, act = terms[i]
            assert kind == "MUST_NOT" and subject == o["subject"] and i in monitors
            assert act == o["monitor_actions"][str(i)]
            assert re.match(re.escape(o["action"]) + r"(\(|$)", act)
        for k in o["composite_prohibitions"]:
            assert terms[k][0] == "COMPOSITE"
    # every top-level prohibition is the monitor of exactly one object
    assert sorted(i for o in objs for i in o["monitors"]) == sorted(monitors) == sorted(
        i for i, x in terms.items() if x[0] == "MUST_NOT")
    return objs


NESTED = """
  paid := agent MUST_NOT pay(supplier) WHEN flag;
  agent MUST deliver THEN agent MUST_NOT leak;
  agent MUST deliver OR agent MUST_NOT refund;
  (agent MUST deliver UNLESS flag DO agent MUST_NOT cancel);
  IF flag THEN agent MUST_NOT pay ELSE agent MUST invoice;
  WHEN flag THEN agent MUST_NOT ship;
  REF paid THEN agent MUST deliver;
  (agent MUST_NOT pay WHEN amount > 100);
  agent MUST_NOT leak WHEN flag"""


def test_actions_of_nested_and_referenced_prohibitions(tmp_path):
    spec = write_spec(tmp_path, NESTED.strip(),
                      "flag : Boolean METADATA,\n  amount : Decimal METADATA", name="nested")
    objs = check_against_report(tmp_path, spec)
    assert objs == [
        {"subject": "agent", "action": "pay", "monitors": [1, 8],
         "monitor_actions": {"1": "pay(supplier)", "8": "pay"}, "composite_prohibitions": [5, 7]},
        {"subject": "agent", "action": "leak", "monitors": [9], "monitor_actions": {"9": "leak"},
         "composite_prohibitions": [2]},
        {"subject": "agent", "action": "refund", "monitors": [], "monitor_actions": {},
         "composite_prohibitions": [3]},
        {"subject": "agent", "action": "cancel", "monitors": [], "monitor_actions": {},
         "composite_prohibitions": [4]},
        {"subject": "agent", "action": "ship", "monitors": [], "monitor_actions": {},
         "composite_prohibitions": [6]}]


def test_actions_with_arguments_as_the_term_lines_print_them(tmp_path):
    terms = ('agent MUST_NOT pay(supplier, 12.50, -3, true, "a\\"b\\\\c é1 ☃") WHEN flag;\n'
             '  agent MUST_NOT pay(DATETIME("2026-11-13T09:00:00Z"), r.f, 0.0)')
    spec = write_spec(tmp_path, terms, "flag : Boolean METADATA,\n  r : Record { f : Integer } METADATA",
                      name="arguments")
    objs = check_against_report(tmp_path, spec)
    assert objs[0]["monitor_actions"] == {
        "1": 'pay(supplier, 12.5, -3, true, "a\\"b\\\\c \\233\\&1 \\9731")',
        "2": "pay(1794560400, r.f, 0)"}


def test_show_string_as_haskell():
    assert show_string("\x00\x0e" + "H\x7f\x0e1\t") == '"\\NUL\\SO\\&H\\DEL\\SO1\\t"'
    assert show_string("é") == '"\\233"' and show_string("é9") == '"\\233\\&9"'


def test_actions_on_examples_without_composite_terms(tmp_path):
    objs = check_against_report(tmp_path, REPO / "examples/core/merchant_mandate.triel")
    assert [(o["action"], o["monitors"], o["composite_prohibitions"]) for o in objs] == [
        ("apply_price_change", [1], []), ("apply_restock", [3], []), ("apply_campaign", [4], [])]


def test_actions_refusals(tmp_path):
    r = actions(REPO / "examples/semantics/prohibition_continuation.triel")
    assert r.returncode == 2
    assert r.stdout.splitlines()[-1] == "REJECTED: §2.6 defines continuations only for obligations"
    bad = tmp_path / "bad.triel"
    bad.write_text("SPECIFICATION bad VERSION 1.0.0\nTERMS {", encoding="utf-8")
    for p in (bad, tmp_path / "missing.triel"):
        r = actions(p)
        assert r.returncode == 1 and r.stdout == "" and "Traceback" not in r.stderr


def test_the_output_without_flags_is_unchanged():
    """--actions changes nothing else: the classification of the examples is the
    expected one (CI), and without flags the translator prints the header lines
    and the core AST."""
    r = subprocess.run([sys.executable, TRANSLATOR, "--classify", "examples"], capture_output=True,
                       text=True, encoding="utf-8", cwd=REPO)
    assert r.stdout == (REPO / "examples/core/classification.expected").read_text(encoding="utf-8")
    path = REPO / "examples/core/merchant_mandate.triel"
    r = subprocess.run([sys.executable, TRANSLATOR, str(path)], capture_output=True, text=True,
                       encoding="utf-8", cwd=REPO)
    tr = translate(path.read_text(encoding="utf-8"))
    assert r.returncode == 0 and r.stdout == "\n".join(header(tr) + [pretty(tr.core)]) + "\n"
