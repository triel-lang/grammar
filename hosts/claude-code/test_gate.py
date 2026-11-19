"""Tests of the TRIEL gate for Claude Code (gate.py and the files of this folder).

Run from the root of the repository, once the evaluator is built
(evaluator/README.md):

    python3 -m pytest -q hosts/claude-code/test_gate.py

Each test runs gate.py as Claude Code runs a hook: a program with the JSON
input of the hook on standard input, and the exit code and the first line of
standard error as the result. The host clock is the argument --now; nothing
waits. The specifications, the configuration, the data of the host and the
state of the mandate are in tmp_path. Neither the MCP SDK nor Claude Code is
used here; the runs in Claude Code are described in README.md.

The test does not skip: without the evaluator it fails.
"""
import ast
import hashlib
import json
import math
import os
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
GATE = str(HERE / "gate.py")
sys.path.insert(0, str(REPO / "parser"))
sys.path.insert(0, str(HERE))
from triel_eval import default_evaluator  # noqa: E402

import gate  # noqa: E402
import triel_host  # noqa: E402

ACT = "2026-11-13T09:00:00Z"
PAY, CONVERT, INSPECT, REPORT = ("mcp__payments__pay", "mcp__payments__convert",
                                 "mcp__payments__inspect", "mcp__payments__report")
MANAGED = ("payments", "managed")
ACTIONS = [
    {"server": "payments", "tool_name": PAY, "subject": "agent", "action": "pay", "atomic": True},
    {"server": "payments", "tool_name": CONVERT, "subject": "agent", "action": "convert",
     "atomic": False},
    {"server": "payments", "tool_name": INSPECT, "subject": "agent", "action": "inspect",
     "atomic": True},
    {"server": "payments", "tool_name": REPORT, "subject": "agent", "action": "report",
     "atomic": True}]
ALLOWED = [{"server": "docs", "source": "managed", "tool_name": "mcp__docs__search"}]

# A host module whose answers are written by the test: a reading is
# {"reading": [VALUE, TIME]}, "NO_NEW_READING" is that, any other JSON is a value.
SCRIPTED = '''
import json
from decimal import Decimal
from triel_host import NO_NEW_READING, Reading


def answers(call, now, factors, options):
    a = json.loads(open(options["answers"], encoding="utf-8").read(), parse_float=Decimal)
    out = {}
    for k, v in a.items():
        if isinstance(v, dict) and set(v) == {"reading"}:
            out[k] = Reading(*v["reading"])
        elif v == "NO_NEW_READING":
            out[k] = NO_NEW_READING
        else:
            out[k] = v
    return out


def executed(fact, options):
    with open(options["facts"], "a", encoding="utf-8") as f:
        f.write(json.dumps(fact, default=str) + "\\n")
'''


@pytest.fixture(scope="session", autouse=True)
def evaluator():
    exe = default_evaluator()
    assert os.path.isfile(exe) and os.access(exe, os.X_OK), \
        f"no evaluator at {exe}: build it first (evaluator/README.md); this test does not skip"
    return exe


def spec_text(terms, factors, name="gate_case"):
    return (f"SPECIFICATION {name} VERSION 1.0.0\n\nSUBJECTS {{\n  owner : PARTY,\n"
            f"  agent : SYSTEM,\n  supplier : PARTY\n}}\n\nTERMS {{\n  {terms}\n}}\n\n"
            f"FACTORS {{\n  {factors}\n}}\n\nINVARIANTS {{\n  i : SAFETY : ALWAYS(true)\n}}\n")


APPROVAL_SPEC = ("agent MUST_NOT pay WHEN NOT approved;\n  agent MUST_NOT convert WHEN NOT approved",
                 "approved : Boolean METADATA")
COUNTER_SPEC = ("agent MUST_NOT pay WHEN paid >= 1", "paid : Integer METADATA")
ACTIVATIONS = {}  # the state after the activation, by everything that makes it


class Mandate:
    """A mandate in tmp_path, with the gate configured as in config.example.json."""

    def __init__(self, tmp, terms=APPROVAL_SPEC[0], factors=APPROVAL_SPEC[1], host="example",
                 data=None, answers=None, config=None, repo=REPO):
        self.tmp = tmp
        tmp.mkdir(parents=True, exist_ok=True)
        self.spec = tmp / "mandate.triel"
        self.spec.write_text(spec_text(terms, factors), encoding="utf-8")
        self.state_dir = tmp / "state"
        if host == "example":
            module = HERE / "host_example.py"
            options = {"data_file": str(tmp / "host_data.json"), "approval": "approved",
                       "counters": {"paid": "pay"}}
            self.set_data(data or {})
        else:
            module = tmp / "scripted_host.py"
            module.write_text(SCRIPTED, encoding="utf-8")
            options = {"answers": str(tmp / "answers.json"), "facts": str(tmp / "facts.jsonl")}
            self.answer(answers or {})
        self.config = {
            "repo": str(repo), "evaluator": default_evaluator(), "spec": str(self.spec),
            "state_dir": str(self.state_dir), "host_module": str(module), "host_options": options,
            "check_timeout_seconds": 60, "pending_timeout_seconds": 600,
            "execution_delay_flag_seconds": 5, "managed_servers": [
                {"name": "payments", "source": "managed"}],
            "allowed_tools": ALLOWED, "actions": ACTIONS}
        self.config.update(config or {})
        self.config_path = tmp / "gate.json"
        self.write_config()
        self.n = 0

    def write_config(self):
        self.config_path.write_text(json.dumps(self.config, indent=1), encoding="utf-8")

    def set_data(self, data):
        (self.tmp / "host_data.json").write_text(json.dumps(data), encoding="utf-8")

    def data(self):
        return json.loads((self.tmp / "host_data.json").read_text(encoding="utf-8"))

    def answer(self, answers):
        (self.tmp / "answers.json").write_text(json.dumps(answers), encoding="utf-8")

    def facts(self):
        p = self.tmp / "facts.jsonl"
        return [json.loads(x) for x in p.read_text().splitlines()] if p.exists() else []

    def run(self, args, stdin="", env=None, now=None):
        cmd = [sys.executable, "-I", GATE] + args + ["--config", str(self.config_path)]
        if now is not None:
            cmd += ["--now", now]
        return subprocess.run(cmd, input=stdin, capture_output=True, text=True, encoding="utf-8",
                              env=env, cwd=self.tmp)

    def activate(self, now=ACT):
        """gate.py activate; the state after an activation with the same
        specification, configuration of the host and data is copied, not computed again."""
        key = (self.spec.read_text(), json.dumps(self.config["host_options"].get("approval")),
               (self.tmp / ("host_data.json" if (self.tmp / "host_data.json").exists()
                            else "answers.json")).read_text(), now, self.config["repo"])
        if key in ACTIVATIONS:
            self.state_dir.mkdir()
            (self.state_dir / "state.json").write_text(ACTIVATIONS[key])
            return
        r = self.run(["activate"], now=now)
        assert r.returncode == 0, r.stderr
        ACTIVATIONS[key] = (self.state_dir / "state.json").read_text()

    def hook(self, command, event, tool, tid, now, tool_input=None, server=MANAGED, env=None,
             **extra):
        payload = {"session_id": "s", "transcript_path": "/dev/null", "cwd": str(self.tmp),
                   "permission_mode": "default", "hook_event_name": event, "tool_name": tool,
                   "tool_input": {} if tool_input is None else tool_input, "tool_use_id": tid}
        if server is not None:
            payload["mcp_server"] = {"name": server[0], "source": server[1]}
        payload.update(extra)
        r = self.run([command], stdin=json.dumps(payload), env=env, now=now)
        return r

    def pre(self, tool, tid, now, tool_input=None, **kw):
        r = self.hook("pre", "PreToolUse", tool, tid, now, tool_input, **kw)
        if r.returncode == 0:
            assert r.stdout == "" and r.stderr == "", (r.stdout, r.stderr)
        return r.returncode, first(r)

    def post(self, tool, tid, now, tool_input=None, duration_ms=5, **kw):
        extra = {"tool_response": {"ok": True}}
        if duration_ms is not None:
            extra["duration_ms"] = duration_ms
        r = self.hook("post", "PostToolUse", tool, tid, now, tool_input, **extra, **kw)
        assert r.returncode == 0, r.stderr
        return r

    def failure(self, tool, tid, now, tool_input=None, **extra):
        r = self.hook("failure", "PostToolUseFailure", tool, tid, now, tool_input,
                      error="Error: failed", **extra)
        assert r.returncode == 0, r.stderr
        return r

    def command(self, *args, now):
        r = self.run(list(args), now=now)
        return r.returncode, first(r)

    def state(self):
        return json.loads((self.state_dir / "state.json").read_text(encoding="utf-8"))

    def log(self):
        p = self.state_dir / "log.jsonl"
        return [json.loads(x) for x in p.read_text().splitlines()] if p.exists() else []


def first(r):
    return (r.stderr.splitlines() or [""])[0]


HELD = "TRIEL gate: held: "


def held(reason):
    return HELD + reason


@pytest.fixture
def m(tmp_path):
    x = Mandate(tmp_path, data={"approvals": [{"action": "pay", "tool_input": {"to": "acme"}}]})
    x.activate()
    return x


# --- Requirement 3: a silent 0 only when everything agrees ------------------------

def test_allowed_exit_0_without_output_and_held_exit_2(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    st = m.state()
    assert list(st["pending"]) == ["t1"] and st["pending"]["t1"]["tool_input"] == {"to": "acme"}
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    code, line = m.pre(PAY, "t2", "2026-11-13T09:20:00Z", {"to": "bob"})
    assert (code, line) == (2, held("triel check exit 3: BLOCK: monitor TERM 1 blocks the action"))


def test_no_decision_for_an_action_named_only_in_an_obligation(tmp_path):
    x = Mandate(tmp_path, terms="agent MUST_NOT pay WHEN NOT approved;\n  agent MUST report",
                factors="approved : Boolean METADATA")
    x.activate()
    code, line = x.pre(REPORT, "t1", "2026-11-13T09:10:00Z")
    assert (code, line) == (2, held("triel check exit 5: NO DECISION: no monitor decides this action"))


def test_a_monitor_with_arguments_does_not_decide(tmp_path):
    x = Mandate(tmp_path, terms="agent MUST_NOT pay WHEN NOT approved;\n"
                                "  agent MUST_NOT pay(supplier) WHEN NOT approved",
                factors="approved : Boolean METADATA",
                data={"approvals": [{"action": "pay", "tool_input": {}}]})
    x.activate()
    code, line = x.pre(PAY, "t1", "2026-11-13T09:10:00Z")
    assert (code, line) == (2, held("monitor TERM 2 did not decide on the action: arguments not "
                                    "matched (its action is pay(supplier))"))


def test_a_prohibition_inside_a_composite_term_holds_on_exit_0(tmp_path):
    x = Mandate(tmp_path, terms="agent MUST_NOT pay WHEN NOT approved;\n"
                                "  agent MUST inspect THEN agent MUST_NOT pay",
                factors="approved : Boolean METADATA",
                data={"approvals": [{"action": "pay", "tool_input": {}}]})
    x.activate()
    code, line = x.pre(PAY, "t1", "2026-11-13T09:10:00Z")
    assert (code, line) == (2, held("the action is named in a prohibition inside the composite term "
                                    "TERM 2, which no monitor decides"))


def test_trace_rejected_when_the_host_clock_goes_back(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})[0] == 0
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    code, line = m.pre(CONVERT, "t2", "2026-11-13T09:05:00Z")
    assert code == 2 and line.startswith(held("triel check exit 4: the evaluator rejects the trace"))
    assert "TIME ORDER REJECTED" in line


def test_the_check_fails_exit_1(m):
    m.config["evaluator"] = str(m.tmp / "no-such-evaluator")
    m.write_config()
    code, line = m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})
    assert code == 2 and line.startswith(held("triel check exit 1: the check itself failed: "))
    assert "cannot run the evaluator" in line


def test_rejected_specification_exit_2_of_actions(m):
    m.spec.write_text(spec_text("agent MUST_NOT pay WHEN NOT approved;\n"
                                "  agent ON_BREACH TERMINATE", "approved : Boolean METADATA"))
    code, line = m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})
    assert (code, line) == (2, held("triel_to_core.py --actions exit 2: the translator rejects "
                                    "the specification"))
    assert m.state()["pending"] == {}


def stub_evaluator(tmp, body):
    f = tmp / "stub-evaluator"
    f.write_text("#!/bin/sh\ncat > /dev/null\n" + body + "\n", encoding="utf-8")
    f.chmod(0o755)
    return str(f)


def test_the_check_does_not_answer_in_time(m):
    m.config["evaluator"] = stub_evaluator(m.tmp, "sleep 300")
    m.config["check_timeout_seconds"] = 15
    m.write_config()
    code, line = m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})
    assert (code, line) == (2, held("the check did not answer within 15 s"))


def fake_repo(tmp, triel_py):
    """A copy of parser/ whose triel.py is replaced, for reports that triel check never prints."""
    root = tmp / "fake"
    (root / "parser").mkdir(parents=True)
    for f in ("triel_host.py", "triel_to_core.py", "triel.lark", "triel_eval.py"):
        shutil.copy(REPO / "parser" / f, root / "parser" / f)
    (root / "parser" / "triel.py").write_text(triel_py, encoding="utf-8")
    return root


@pytest.mark.parametrize("output,reason", [
    ("print('not JSON')", "triel check exit 0, but its report cannot be read"),
    ("pass", "triel check exit 0, but it printed no report")])
def test_a_report_that_cannot_be_read_on_exit_0(tmp_path, output, reason):
    repo = fake_repo(tmp_path, f"import sys\n{output}\nsys.exit(0)\n")
    x = Mandate(tmp_path, data={"approvals": [{"action": "pay", "tool_input": {}}]},
                config={"repo": str(repo)})
    x.activate()
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z") == (2, held(reason))


def test_an_exception_of_the_gate_holds(m):
    (m.state_dir / "state.json").write_text("{not json")
    code, line = m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})
    assert code == 2 and line.startswith(held("the gate failed: JSONDecodeError"))


def test_an_import_error_holds(tmp_path):
    empty = tmp_path / "empty"
    (empty / "parser").mkdir(parents=True)
    x = Mandate(tmp_path, config={"repo": str(empty)})
    code, line = x.pre(PAY, "t1", "2026-11-13T09:10:00Z")
    assert (code, line) == (2, held("the gate failed: ModuleNotFoundError: No module named "
                                    "'triel_host'"))


def test_the_imports_are_inside_the_handler():
    """Only sys is imported at the top level of gate.py; main catches every exception."""
    tree = ast.parse((HERE / "gate.py").read_text(encoding="utf-8"))
    tops = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom))]
    assert [a.name for n in tops for a in n.names] == ["sys"]
    assert all(isinstance(n, (ast.Import, ast.FunctionDef, ast.ClassDef, ast.Assign, ast.If, ast.Expr))
               for n in tree.body)
    main = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "main")
    handlers = [h for t in main.body if isinstance(t, ast.Try) for h in t.handlers]
    assert any(isinstance(h.type, ast.Name) and h.type.id == "BaseException" for h in handlers)


# --- Requirement 9: tools and servers ------------------------------------------------

@pytest.mark.parametrize("tool,server,reason", [
    ("mcp__payments__refund", MANAGED,
     "tool not mapped to an action: mcp__payments__refund of the managed server payments"),
    (PAY, ("payments", "project"), "mcp__payments__pay: the server payments has the source project, "
                                   "not the source managed of the managed server"),
    ("mcp__shop__pay", ("shop", "managed"),
     "tool not allowed: mcp__shop__pay of the server shop, which is neither a managed server nor a "
     "server with allowed tools"),
    ("mcp__docs__delete", ("docs", "managed"),
     "tool not allowed: mcp__docs__delete is not in the allowed tools of the server docs"),
    ("mcp__docs__search", ("docs", "user"),
     "tool not allowed: mcp__docs__search: the server docs has the source user, not the source of "
     "the allowed server"),
    (PAY, None, "mcp__payments__pay: the input of the hook has no mcp_server (Claude Code gives it "
                "from version 2.1.274)")])
def test_tools_held_by_their_server(m, tool, server, reason):
    assert m.pre(tool, "t1", "2026-11-13T09:10:00Z", server=server) == (2, held(reason))


def test_an_allowed_tool_passes_with_a_line_in_the_journal(m):
    assert m.pre("mcp__docs__search", "t1", "2026-11-13T09:10:00Z", server=("docs", "managed")) == (
        0, "")
    assert m.log()[-1]["event"] == "allowed tool"
    assert m.state()["pending"] == {}


@pytest.mark.parametrize("change,reason", [
    ({"allowed_tools": [{"server": "payments", "source": "managed", "tool_name": "mcp__payments__x"}]},
     "configuration: allowed tool mcp__payments__x: the server payments has the name of a managed "
     "server"),
    ({"actions": ACTIONS + [{"server": "docs", "tool_name": "mcp__docs__search", "subject": "agent",
                             "action": "search", "atomic": True}]},
     "configuration: actions: mcp__docs__search is a tool of the allowed server docs, not of a "
     "managed server"),
    ({"actions": ACTIONS + [{"server": "payments", "tool_name": "Bash", "subject": "agent",
                             "action": "pay", "atomic": True}]},
     "configuration: actions: Bash is not an MCP tool"),
    ({"allowed_tools": [{"server": "docs", "source": "project", "tool_name": "mcp__docs__search"}]},
     "configuration: allowed tool mcp__docs__search: the source project of the server docs is not a "
     "scope of managed configuration (managed, enterprise); the agent may be able to write it"),
    ({"managed_servers": [{"name": "payments", "source": "user"}]},
     "configuration: managed server payments: the source user is not a scope of managed "
     "configuration (managed, enterprise); the agent may be able to write it"),
    ({"spec": "mandate.triel"}, "configuration: spec: the path 'mandate.triel' is not absolute")])
def test_a_configuration_that_is_refused_holds_everything(m, change, reason):
    m.config.update(change)
    m.write_config()
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (2, held(reason))
    assert m.pre("mcp__docs__search", "t2", "2026-11-13T09:10:00Z", server=("docs", "managed")) == (
        2, held(reason))


# --- Requirements 5 and 6: the outcome of a call, one decision at a time ------------

def test_a_pending_call_holds_the_next_and_a_repeated_pre_replaces_it(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})[0] == 0
    assert m.pre(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})[0] == 0
    assert list(m.state()["pending"]) == ["t1"]
    assert m.pre(CONVERT, "t2", "2026-11-13T09:10:02Z") == (
        2, held("waits for the outcome of the previous action, the call t1"))


def test_a_repeated_pre_that_is_held_leaves_no_pending_record(m):
    """A PreToolUse that comes again for a pending call is decided anew on its
    own input; held, it leaves the call without a pending record."""
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    assert m.pre(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "mallory"}) == (
        2, held("triel check exit 3: BLOCK: monitor TERM 1 blocks the action"))
    assert m.state()["pending"] == {}
    assert m.pre(PAY, "t2", "2026-11-13T09:10:02Z", {"to": "acme"}) == (0, "")


OUTCOME = "the call t1 already has an outcome; a new call has a new tool_use_id"


def test_a_pre_for_a_call_in_the_history_is_held(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    assert m.pre(PAY, "t1", "2026-11-13T09:11:00Z", {"to": "acme"}) == (2, held(OUTCOME))
    assert [x["tool_use_id"] for x in m.state()["history"]] == ["t1"]


def test_a_pre_for_a_call_recorded_as_not_executed_is_held(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    m.failure(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    assert list(m.state()["not_executed"]) == ["t1"]
    assert m.pre(PAY, "t1", "2026-11-13T09:11:00Z", {"to": "acme"}) == (2, held(OUTCOME))
    assert m.state()["pending"] == {} and m.state()["history"] == []


def test_two_decisions_at_once_allow_exactly_one(m):
    procs = []
    for tid in ("p1", "p2"):
        payload = {"session_id": "s", "transcript_path": "/dev/null", "cwd": str(m.tmp),
                   "permission_mode": "default", "hook_event_name": "PreToolUse", "tool_name": PAY,
                   "tool_input": {"to": "acme"}, "tool_use_id": tid,
                   "mcp_server": {"name": "payments", "source": "managed"}}
        p = subprocess.Popen([sys.executable, "-I", GATE, "pre", "--config", str(m.config_path),
                              "--now", "2026-11-13T09:10:00Z"], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        p.stdin.write(json.dumps(payload))
        p.stdin.close()
        procs.append(p)
    results = [(p.wait(), p.stderr.read()) for p in procs]
    assert sorted(c for c, _ in results) == [0, 2]
    allowed = [tid for tid, (c, _) in zip(("p1", "p2"), results) if c == 0]
    other = [e for c, e in results if c == 2][0]
    assert other.startswith(held(f"waits for the outcome of the previous action, the call {allowed[0]}"))
    assert list(m.state()["pending"]) == allowed


def unknown_line(tid, why):
    return held(f"the outcome of the call {tid} is unknown ({why}); every action is held until the "
                f"operator runs gate.py resolve {tid}")


def test_post_with_another_input_is_unknown(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})[0] == 0
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "evil"})
    assert m.state()["history"] == []
    assert m.pre(CONVERT, "t2", "2026-11-13T09:10:02Z") == (
        2, unknown_line("t1", "the input of PostToolUse differs from the input of PreToolUse"))
    assert m.log()[-2]["event"] == "unknown"


def test_post_without_duration_and_post_60_s_later(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00.3Z", {"to": "acme"})[0] == 0
    m.post(PAY, "t1", "2026-11-13T09:10:00.6Z", {"to": "acme"}, duration_ms=None)
    h = m.state()["history"][0]
    assert h["executed"] == "1794561000.6"
    assert [x for x in m.log() if x["event"] == "executed"][-1]["E"] == "2026-11-13T09:10:01Z"
    m.set_data({"approvals": [{"action": "convert", "tool_input": {}}]})
    assert m.pre(CONVERT, "t2", "2026-11-13T09:11:00Z")[0] == 0
    m.post(CONVERT, "t2", "2026-11-13T09:12:00Z", duration_ms=2000)
    x = [x for x in m.log() if x["event"] == "executed"][-1]
    assert (x["T"], x["E"], x["delay_flagged"]) == ("2026-11-13T09:11:00Z", "2026-11-13T09:11:58Z",
                                                     True)
    assert m.state()["pending"] == {} and len(m.state()["history"]) == 2


@pytest.mark.parametrize("tool,extra,why", [
    (PAY, {"is_interrupt": True}, "PostToolUseFailure with is_interrupt"),
    (CONVERT, {"is_interrupt": False},
     "PostToolUseFailure of a tool that the configuration does not declare atomic")])
def test_failures_whose_outcome_is_unknown(m, tool, extra, why):
    m.set_data({"approvals": [{"action": "pay", "tool_input": {}},
                              {"action": "convert", "tool_input": {}}]})
    assert m.pre(tool, "t1", "2026-11-13T09:10:00Z")[0] == 0
    m.failure(tool, "t1", "2026-11-13T09:10:01Z", **extra)
    assert m.pre(PAY, "t2", "2026-11-13T09:10:02Z") == (2, unknown_line("t1", why))


def test_a_failure_of_an_atomic_tool_is_not_executed(m):
    m.set_data({"approvals": [{"action": "pay", "tool_input": {}}]})
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z")[0] == 0
    m.failure(PAY, "t1", "2026-11-13T09:10:01Z")
    st = m.state()
    assert st["history"] == [] and list(st["not_executed"]) == ["t1"]
    assert m.pre(PAY, "t2", "2026-11-13T09:10:02Z")[0] == 0  # the approval still stands


def test_permission_denied_is_not_executed(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})[0] == 0
    r = m.hook("denied", "PermissionDenied", PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"},
               reason="[Irreversible]")
    assert r.returncode == 0
    assert list(m.state()["not_executed"]) == ["t1"]


def test_a_pending_call_without_post_becomes_unknown_after_the_timeout(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})[0] == 0
    assert m.pre(CONVERT, "t2", "2026-11-13T09:20:00Z") == (
        2, held("waits for the outcome of the previous action, the call t1"))
    assert m.pre(CONVERT, "t3", "2026-11-13T09:20:00.1Z") == (
        2, unknown_line("t1", "no PostToolUse or PostToolUseFailure within 600 s"))


def test_resolve_refuses_a_time_before_t_or_after_the_host_clock(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00.5Z", {"to": "acme"})[0] == 0
    m.failure(PAY, "t1", "2026-11-13T09:10:02Z", is_interrupt=True)
    assert m.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:00.9Z",
                     now="2026-11-13T09:30:00Z") == (
        2, held("--at 2026-11-13T09:10:00.9Z is earlier than the time of the decision, "
                "2026-11-13T09:10:01Z"))
    assert m.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:31:00Z",
                     now="2026-11-13T09:30:00Z") == (
        2, held("--at 2026-11-13T09:31:00Z is later than the host clock"))
    assert m.command("resolve", "t1", "--executed", now="2026-11-13T09:30:00Z")[0] == 2
    assert m.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:05Z",
                     now="2026-11-13T09:30:00Z") == (0, "")
    assert m.state()["history"][0]["executed"] == "1794561005"


def conflict_line(tid, why):
    return held(f"conflict on the call {tid}: {why}; every action is held until the operator runs "
                f"gate.py resolve {tid}")


def test_a_late_post_after_resolve_not_executed_is_a_conflict(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})[0] == 0
    m.failure(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"}, is_interrupt=True)
    assert m.command("resolve", "t1", "--not-executed", now="2026-11-13T09:11:00Z") == (0, "")
    m.post(PAY, "t1", "2026-11-13T09:12:00Z", {"to": "acme"})
    assert [x["tool_use_id"] for x in m.state()["history"]] == ["t1"]
    why = "PostToolUse came for a call recorded as not executed"
    assert m.pre(CONVERT, "t2", "2026-11-13T09:13:00Z") == (2, conflict_line("t1", why))
    assert m.command("resolve", "t1", "--not-executed", now="2026-11-13T09:14:00Z")[0] == 2


def test_a_late_post_with_another_input_is_a_conflict(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})[0] == 0
    m.failure(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"}, is_interrupt=True)
    m.post(PAY, "t1", "2026-11-13T09:12:00Z", {"to": "evil"})
    st = m.state()
    assert st["history"][0]["tool_input"] == {"to": "evil"}
    why = "the late PostToolUse has another input than PreToolUse"
    assert m.pre(CONVERT, "t2", "2026-11-13T09:13:00Z") == (2, conflict_line("t1", why))
    assert m.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:11:59Z",
                     now="2026-11-13T09:14:00Z") == (0, "")
    assert m.state()["conflicts"] == {}


def test_activate_once_per_mandate(m):
    assert m.command("activate", now="2026-11-13T10:00:00Z") == (
        2, held("the mandate already has a state; a second activation is refused and the history "
                "is kept"))


def test_no_activation_holds(tmp_path):
    x = Mandate(tmp_path)
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z") == (
        2, held("the mandate has no activation: the operator runs gate.py activate"))


# --- Requirement 8: an executed action with the same approval or a counter ----------

def path_post(x, tid, h):
    x.post(PAY, tid, h)


def path_unknown_then_resolve(x, tid, h):
    x.failure(PAY, tid, h, is_interrupt=True)
    assert x.command("resolve", tid, "--executed", "--at", h, now=h) == (0, "")


def path_not_executed_then_late_post(x, tid, h):
    x.failure(PAY, tid, h, is_interrupt=True)
    assert x.command("resolve", tid, "--not-executed", now=h) == (0, "")
    x.post(PAY, tid, h)
    code, line = x.pre(PAY, "t-held", "2026-11-13T09:15:00Z")
    assert (code, line) == (2, conflict_line(tid, "PostToolUse came for a call recorded as not "
                                                  "executed"))
    assert x.command("resolve", tid, "--executed", "--at", h, now="2026-11-13T09:16:00Z") == (0, "")


PATHS = {"PostToolUse": path_post, "unknown, resolve --executed": path_unknown_then_resolve,
         "resolve --not-executed, late PostToolUse": path_not_executed_then_late_post}


@pytest.mark.parametrize("path", sorted(PATHS))
def test_a_repeat_with_the_same_approval_is_blocked(tmp_path, path):
    x = Mandate(tmp_path, data={"approvals": [{"action": "pay", "tool_input": {}}]})
    x.activate()
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z") == (0, "")
    PATHS[path](x, "t1", "2026-11-13T09:10:01Z")
    assert x.data()["approvals"] == [] and x.data()["executed"] == {"t1": "pay"}
    assert x.pre(PAY, "t2", "2026-11-13T09:20:00Z") == (
        2, held("triel check exit 3: BLOCK: monitor TERM 1 blocks the action"))


@pytest.mark.parametrize("path", sorted(PATHS))
def test_a_repeat_with_a_counter_of_the_host_is_blocked(tmp_path, path):
    x = Mandate(tmp_path, terms=COUNTER_SPEC[0], factors=COUNTER_SPEC[1])
    x.activate()
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z") == (0, "")
    PATHS[path](x, "t1", "2026-11-13T09:10:01Z")
    assert x.pre(PAY, "t2", "2026-11-13T09:20:00Z") == (
        2, held("triel check exit 3: BLOCK: monitor TERM 1 blocks the action"))


def test_the_fact_of_execution_carries_the_input_of_post(tmp_path):
    x = Mandate(tmp_path, terms=COUNTER_SPEC[0], factors=COUNTER_SPEC[1], host="scripted",
                answers={"paid": 0})
    x.activate()
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "evil"})          # unknown
    assert x.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z",
                     now="2026-11-13T09:11:00Z") == (0, "")
    f = x.facts()
    assert [(y["tool_use_id"], y["tool_input"], y["time"]) for y in f] == [
        ("t1", {"to": "evil"}, "2026-11-13 09:10:01+00:00")]


# --- Requirement 8 and A: the data come from the host --------------------------------

@pytest.mark.parametrize("answers,reason", [
    ({}, "factor approved: no answer from the host"),
    ({"approved": True, "aproved": True}, "aproved: not a factor of the specification"),
    ({"approved": 1}, "factor approved: 1 is not a value of the declared type Boolean")])
def test_answers_of_the_host_that_hold(tmp_path, answers, reason):
    x = Mandate(tmp_path, terms="agent MUST_NOT pay WHEN NOT DEFAULT(approved, true)",
                factors="approved : Boolean METADATA", host="scripted", answers={"approved": None})
    x.activate()
    x.answer(answers)
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z") == (2, held(reason))


def test_a_misspelt_field_of_a_record_holds(tmp_path):
    x = Mandate(tmp_path, terms="agent MUST_NOT pay WHEN DEFAULT(r.f, false)",
                factors="r : Record { f : Optional<Boolean> } METADATA", host="scripted",
                answers={"r": None})
    x.activate()
    x.answer({"r": {"g": True}})
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z") == (
        2, held("factor r: g is not a field of the record type"))


CONDITIONS = {"DEFAULT": "DEFAULT(f, false)", "PRESENT": "PRESENT(f) AND f"}


def reading(v, time):
    return {"f": {"reading": [v, time]}}


NONE = {"f": "NO_NEW_READING"}


def case(tmp_path, cond, clause="MAX_AGE 60 SECONDS ON_STALE BLOCK", first=NONE):
    x = Mandate(tmp_path, terms=f"agent MUST_NOT pay WHEN {CONDITIONS[cond]}",
                factors=f"f : Boolean METADATA {clause}", host="scripted", answers=first)
    x.activate()
    return x


def steps(x, *s):
    out = []
    for i, (answers, h, tool) in enumerate(s):
        x.answer(answers)
        out.append(x.pre(tool, f"t{i}", h))
    return out


BLOCKED = (2, held("triel check exit 3: BLOCK: monitor TERM 1 blocks the action"))
FUTURE = (2, held("factor f: a reading from the future"))
NOT_EXPRESSED = (2, held("factor f: a fresh reading that the trace cannot express"))
INSPECTED = (2, held("triel check exit 5: NO DECISION: no monitor decides this action"))


@pytest.fixture(params=sorted(CONDITIONS))
def cond(request):
    return request.param


def test_hook_case_a(tmp_path, cond):
    x = case(tmp_path, cond)
    assert steps(x, (reading(True, "2026-11-13T09:10:00.2Z"), "2026-11-13T09:10:00.5Z", INSPECT),
                 (reading(False, "2026-11-13T09:09:59Z"), "2026-11-13T09:10:05Z", PAY)) == [
        INSPECTED, BLOCKED]


def test_hook_case_b(tmp_path, cond):
    x = case(tmp_path, cond)
    assert steps(x, ({"f": {"reading": [True, None]}}, "2026-11-13T09:10:00Z", PAY)) == [
        (2, held("factor f: a value without a source time"))]


def test_hook_case_c(tmp_path, cond):
    x = case(tmp_path, cond)
    assert steps(x, (reading(True, "2026-11-13T09:10:30Z"), "2026-11-13T09:10:00Z", PAY),
                 (reading(False, "2026-11-13T09:10:05Z"), "2026-11-13T09:10:10Z", PAY),
                 (NONE, "2026-11-13T09:10:31Z", PAY)) == [FUTURE, FUTURE, BLOCKED]


@pytest.mark.parametrize("order", ["true first", "false first"])
def test_hook_case_d(tmp_path, cond, order):
    true, false = reading(True, "2026-11-13T09:09:58.7Z"), reading(False, "2026-11-13T09:09:58.2Z")
    a, b = (true, false) if order == "true first" else (false, true)
    x = case(tmp_path, cond)
    assert steps(x, (a, "2026-11-13T09:10:00Z", INSPECT), (b, "2026-11-13T09:10:01Z", PAY)) == [
        INSPECTED, BLOCKED]


def test_hook_case_d_equal_times(tmp_path, cond):
    x = case(tmp_path, cond)
    assert steps(x, (reading(False, "2026-11-13T09:09:58.7Z"), "2026-11-13T09:10:00Z", INSPECT),
                 (reading(True, "2026-11-13T09:09:58.7Z"), "2026-11-13T09:10:01Z", PAY)) == [
        INSPECTED, (2, held("factor f: two readings with one time"))]


def test_hook_case_e(tmp_path, cond):
    x = case(tmp_path, cond, "MAX_AGE 5 SECONDS ON_STALE BLOCK")
    assert steps(x, (reading(True, "2026-11-13T09:09:55.9Z"), "2026-11-13T09:10:00.1Z", PAY)) == [
        NOT_EXPRESSED]


def test_hook_case_f(tmp_path, cond):
    x = case(tmp_path, cond)
    assert steps(x, (reading(True, "2026-11-13T08:59:30Z"), "2026-11-13T09:00:10Z", PAY)) == [
        NOT_EXPRESSED]


def test_hook_case_g(tmp_path, cond):
    x = case(tmp_path, cond, "MAX_AGE 60 SECONDS ON_STALE USE_LAST",
             first=reading(True, "2026-11-12T09:00:00Z"))
    assert steps(x, (NONE, "2026-11-13T09:10:00Z", PAY)) == [BLOCKED]


def test_hook_case_h(tmp_path, cond):
    x = case(tmp_path, cond)
    assert steps(x, (reading(True, "2026-11-13T09:09:59.5Z"), "2026-11-13T09:10:00Z", INSPECT),
                 (NONE, "2026-11-13T09:10:10Z", PAY)) == [INSPECTED, BLOCKED]


# --- Requirement 10: nothing from the environment -------------------------------------

def test_the_environment_and_a_python3_on_path_change_nothing(tmp_path):
    fake = tmp_path / "bin"
    fake.mkdir()
    (fake / "python3").write_text(
        "#!/bin/sh\necho '[{\"line\": \"LAST\", \"entry\": 99, \"decisions\": "
        "[{\"term\": 1, \"decision\": \"ALLOW\"}]}]'\nexit 0\n")
    (fake / "python3").chmod(0o755)
    stub = stub_evaluator(tmp_path, "echo 'LAST ENTRY 2 : MONITOR 1 ALLOW'")
    env = dict(os.environ, PATH=f"{fake}:{os.environ.get('PATH', '')}", TRIEL_EVALUATOR=stub,
               PYTHONPATH=str(tmp_path), TRIEL_GATE_CONFIG=str(tmp_path / "x.json"),
               TRIEL_GATE_NOW="2026-11-13T09:10:00Z", PYTHONHOME=str(tmp_path / "nohome"),
               PYTHONSTARTUP=str(tmp_path / "x.py"))
    # a module triel_host on PYTHONPATH that would allow everything
    (tmp_path / "triel_host.py").write_text("raise SystemExit(0)\n")
    results = []
    for name, e in (("plain", None), ("hostile", env)):
        x = Mandate(tmp_path / name, data={})
        x.activate()
        r = x.hook("pre", "PreToolUse", PAY, "t1", "2026-11-13T09:10:00Z", env=e)
        results.append((r.returncode, first(r).replace(str(tmp_path / name), "TMP")))
    assert results[0] == results[1] == (2, held("triel check exit 3: BLOCK: monitor TERM 1 "
                                                "blocks the action"))


# --- The example files of this folder ---------------------------------------------------

def settings():
    return json.loads((HERE / "settings.json").read_text(encoding="utf-8"))


def example_config():
    return json.loads((HERE / "config.example.json").read_text(encoding="utf-8"))


def js_test(matcher, name):
    """A matcher with a character other than letters, digits, _ and | is a
    JavaScript regular expression tested anywhere in the tool name (hooks page)."""
    return re.search(matcher, name) is not None


def test_the_example_settings():
    s = settings()
    cfg = example_config()
    events = {"PreToolUse": "pre", "PostToolUse": "post", "PostToolUseFailure": "failure",
              "PermissionDenied": "denied"}
    assert set(s["hooks"]) == set(events)
    for event, command in events.items():
        (group,) = s["hooks"][event]
        assert group["matcher"] == "mcp__.*"
        for tool in ("mcp__payments__refund", "mcp__payments_two__pay", "mcp__shop__pay"):
            assert js_test(group["matcher"], tool)
        assert not any(js_test(group["matcher"], t) for t in ("Bash", "WebFetch", "Write"))
        (h,) = group["hooks"]
        assert h["type"] == "command" and h["onFailure"] == "block"
        assert "async" not in h and "asyncRewake" not in h
        assert h["timeout"] > 3 * cfg["check_timeout_seconds"]
        assert os.path.isabs(h["command"]) and h["args"][0] == "-I"
        assert h["args"][2:] == [command, "--config", h["args"][-1]]
        assert all(os.path.isabs(p) for p in (h["args"][1], h["args"][-1]))
    assert s["env"] == {"CLAUDE_CODE_MCP_AUTO_BACKGROUND_MS": "0",
                        "CLAUDE_CODE_EXPERIMENTAL_CODE_MODE": "0"}
    assert s["requiredMinimumVersion"] == "2.1.323"
    assert s["permissions"]["disableBypassPermissionsMode"] == "disable"
    assert s["allowManagedHooksOnly"] is True and s["allowManagedPermissionRulesOnly"] is True
    tools = [a["tool_name"] for a in cfg["actions"]] + [a["tool_name"] for a in cfg["allowed_tools"]]
    assert set(tools) <= set(s["permissions"]["allow"])
    deny = s["permissions"]["deny"]
    for p in ("Edit(//**/.claude/**)", "Edit(//etc/triel/**)", "Edit(//var/lib/triel/**)"):
        assert p in deny
    assert any(d.startswith("WebFetch(domain:") for d in deny)
    sb = s["sandbox"]
    assert sb["enabled"] is True and sb["failIfUnavailable"] is True
    assert sb["allowUnsandboxedCommands"] is False and "excludedCommands" not in sb
    # sandbox.filesystem set in managed settings: only they can turn filesystem isolation off
    assert sb["filesystem"] == {"denyWrite": ["/etc/triel", "/opt/triel", "/var/lib/triel",
                                              "/etc/claude-code"]}
    for p in ("/etc/triel/", "/var/lib/triel/"):
        assert any(cfg[k].startswith(p) for k in ("spec", "state_dir", "host_module"))
    assert cfg["repo"].startswith("/opt/triel/")
    for k in ("enableWeakerNestedSandbox", "enableWeakerNetworkIsolation", "allowAppleEvents",
              "allowNestedUserNamespaces"):
        assert sb[k] is False, k
    assert sb["network"]["allowAllUnixSockets"] is False and sb["network"]["allowLocalBinding"] is False
    # Every file of the host module lies where the deny rules and the sandbox keep the agent
    # from writing: an approval written by the agent would be the way around the gate that
    # section II-C of the paper describes.
    files = option_paths(cfg["host_options"])
    assert files and all(p.startswith(("/etc/triel/", "/var/lib/triel/")) for p in files), files
    for k in ("data_file", "approvals_file", "ledger_file", "executions_file"):
        assert cfg["host_options"][k].startswith(("/etc/triel/", "/var/lib/triel/")), k
    # Each path of the configuration and each file of the host module lies under a path of
    # sandbox.filesystem.denyWrite and under a deny rule Edit(//DIR/**). Wrong settings and
    # configuration: settings.json without Edit(//opt/triel/**), and a spec in /srv.
    rules = [d[len("Edit(/"):-len("/**)")] for d in deny
             if d.startswith("Edit(//") and d.endswith("/**)")]
    paths = [cfg[k] for k in gate.PATH_KEYS] + [v for k, v in cfg["host_options"].items()
                                                if k.endswith("_file")]
    for p in paths:
        assert any(p == d or p.startswith(d.rstrip("/") + "/") for d in sb["filesystem"]["denyWrite"]), p
        assert any(p == d or p.startswith(d + "/") for d in rules), p


def option_paths(v):
    """The absolute paths among the values of the host options, at any depth."""
    if isinstance(v, str):
        return [v] if v.startswith("/") else []
    if isinstance(v, dict):
        return [p for x in v.values() for p in option_paths(x)]
    if isinstance(v, list):
        return [p for x in v for p in option_paths(x)]
    return []


# The top-level terms of mandate.triel in their order: TERM 1 to TERM 7. Each reason
# to hold a payment is a prohibition of its own, so the gate names it by its number.
EXAMPLE_TERMS = [
    "agent MUST_NOT raise_limit",
    "agent MUST_NOT pay WHEN NOT call_approved",
    "agent MUST_NOT pay WHEN call_approved AND approval_age > 600",
    "agent MUST_NOT pay WHEN call_approved AND approval_revoked",
    "agent MUST_NOT pay WHEN day_total > daily_limit",
    "agent MUST_NOT pay WHEN NOT payee_listed",
    "agent MUST_NOT convert WHEN fx_rate > rate_limit"]
CALL_FACTORS = ("call_approved", "approval_age", "approval_revoked", "day_total", "payee_listed")


def test_the_example_configuration_and_specification():
    cfg = example_config()
    assert gate.config_errors(cfg) == []
    assert all(os.path.isabs(cfg[k]) for k in gate.PATH_KEYS)
    r = subprocess.run([sys.executable, str(REPO / "parser" / "triel_to_core.py"), "--actions",
                        str(HERE / "mandate.triel")], capture_output=True, text=True, cwd=REPO)
    actions = json.loads(r.stdout)
    pairs = {(o["subject"], o["action"]) for o in actions}
    assert pairs == {(a["subject"], a["action"]) for a in cfg["actions"]}
    assert {o["action"]: o["monitors"] for o in actions} == {
        "raise_limit": [1], "pay": [2, 3, 4, 5, 6], "convert": [7]}
    text = (HERE / "mandate.triel").read_text(encoding="utf-8")
    body = text.split("TERMS {", 1)[1].split("}", 1)[0]
    assert [t.strip() for t in body.split(";")] == EXAMPLE_TERMS
    # No DEFAULT and no PRESENT: they turn an unknown value into ALLOW.
    assert "DEFAULT" not in body and "PRESENT" not in body
    import triel_host
    factors = triel_host.spec_factors(text)
    # The factors that depend on the call have no MAX_AGE: the store of readings belongs
    # to the factor, not to the call.
    for name in CALL_FACTORS + ("daily_limit",):
        assert factors[name]["stale"] == "none", name
    opts = cfg["host_options"]
    named = list(opts["approval_factors"].values()) + [opts["payment"][k] for k in (
        "day_total", "payee_listed")]
    assert sorted(named) == sorted(CALL_FACTORS)
    assert opts["payment"]["tool"] == next(a["tool_name"] for a in cfg["actions"]
                                           if a["action"] == "pay")


def test_the_example_mandate_end_to_end(tmp_path):
    """The example of README.md: mandate.triel, host_example.py and the
    configuration of config.example.json with the paths of tmp_path."""
    x = Example(tmp_path, approvals=[approval("A1", INVOICE[1])])
    x.set_data(dict(x.data(), readings={"fx_rate": {"value": "1.10",
                                                    "time": "2026-11-13T09:09:30Z"}}))
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z", INVOICE[1]) == (0, "")
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", INVOICE[1])
    assert x.pre(CONVERT, "t2", "2026-11-13T09:10:20Z", EXCHANGE) == (0, "")
    x.post(CONVERT, "t2", "2026-11-13T09:10:21Z", EXCHANGE)
    assert x.pre(CONVERT, "t3", "2026-11-13T09:11:00Z", EXCHANGE) == (
        2, held("triel check exit 3: BLOCK: monitor TERM 7 blocks the action"))
    assert x.pre(PAY, "t4", "2026-11-13T09:11:00Z", INVOICE[1]) == (
        2, held("triel check exit 3: BLOCK: monitor TERM 2 blocks the action"))


# --- Further cases ----------------------------------------------------------------------

BLOCKED_PAY = (2, held("triel check exit 3: BLOCK: monitor TERM 1 blocks the action"))


def test_resolve_gives_the_fact_again_when_the_host_module_failed(tmp_path):
    """The host module cannot write its data when the call is executed: a
    conflict. resolve --executed gives the fact to the module again; while the
    module refuses it, the conflict stays; once it takes it, the approval is gone
    and the same payment is blocked."""
    x = Mandate(tmp_path, data={"approvals": [{"action": "pay", "tool_input": {"to": "acme"}}]})
    x.activate()
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    blocker = tmp_path / "host_data.json.tmp"
    blocker.mkdir()
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    assert x.state()["conflicts"]["t1"]["why"].startswith(
        "the host module did not take the execution: IsADirectoryError")
    code, line = x.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z",
                           now="2026-11-13T09:11:00Z")
    assert code == 2 and line.startswith(held("the host module did not take the execution: "
                                              "IsADirectoryError"))
    assert "t1" in x.state()["conflicts"]
    blocker.rmdir()
    assert x.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z",
                     now="2026-11-13T09:12:00Z") == (0, "")
    assert x.data()["approvals"] == [] and x.data()["executed"] == {"t1": "pay"}
    assert x.pre(PAY, "t3", "2026-11-13T09:20:00Z", {"to": "acme"}) == BLOCKED_PAY


def test_resolve_executed_of_a_pending_call_that_the_host_module_refuses_exits_2(m):
    """resolve --executed of a pending call records the conflict that the
    refusal of the host module makes, and exits 2; the next call is held, and
    resolve --executed gives the fact again once the module can take it."""
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    blocker = m.tmp / "host_data.json.tmp"
    blocker.mkdir()
    r = m.run(["resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z"],
              now="2026-11-13T09:11:00Z")
    lines = r.stderr.splitlines()
    assert r.returncode == 2 and len(lines) == 2, r.stderr
    assert lines[0].startswith(held("the host module did not take the execution: IsADirectoryError"))
    assert lines[1] == ("  the conflict on the call t1 is recorded; gate.py resolve t1 --executed "
                        "--at TIME gives the fact to the module again")
    st = m.state()
    assert [x["tool_use_id"] for x in st["history"]] == ["t1"] and st["pending"] == {}
    assert st["conflicts"]["t1"]["why"].startswith("the host module did not take the execution")
    code, line = m.pre(PAY, "t2", "2026-11-13T09:12:00Z", {"to": "acme"})
    assert code == 2 and line.startswith(held("conflict on the call t1: the host module did not "
                                              "take the execution"))
    blocker.rmdir()
    assert m.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z",
                     now="2026-11-13T09:13:00Z") == (0, "")
    assert m.data()["approvals"] == [] and m.data()["executed"] == {"t1": "pay"}
    assert m.pre(PAY, "t3", "2026-11-13T09:20:00Z", {"to": "acme"}) == BLOCKED_PAY


def test_a_second_post_is_a_conflict_without_a_second_entry(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    m.post(PAY, "t1", "2026-11-13T09:10:02Z", {"to": "acme"})
    st = m.state()
    assert [x["tool_use_id"] for x in st["history"]] == ["t1"]
    assert st["conflicts"]["t1"]["why"] == "a PostToolUse came for a call already in the history"


def test_a_post_after_resolve_executed_is_a_conflict_on_a_call_in_the_history(m):
    """The operator resolved the call as executed, then its PostToolUse came:
    the first PostToolUse of the call, for a call already in the history."""
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    assert m.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z",
                     now="2026-11-13T09:11:00Z") == (0, "")
    m.post(PAY, "t1", "2026-11-13T09:11:30Z", {"to": "acme"})
    st = m.state()
    assert [x["tool_use_id"] for x in st["history"]] == ["t1"]
    assert st["conflicts"]["t1"]["why"] == "a PostToolUse came for a call already in the history"


def test_a_failure_of_the_host_module_stays_in_the_conflict(m):
    """A second reason of a conflict on the same call does not hide the first."""
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    (m.tmp / "host_data.json.tmp").mkdir()
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    m.post(PAY, "t1", "2026-11-13T09:10:02Z", {"to": "acme"})
    why = m.state()["conflicts"]["t1"]["why"]
    assert why.startswith("the host module did not take the execution: IsADirectoryError")
    assert why.endswith("; a PostToolUse came for a call already in the history")
    # The line of the execution comes before the line of the conflict it caused.
    assert events(m) == ["allowed", "executed", "conflict", "conflict"]


def test_the_example_host_module_takes_a_fact_once(tmp_path):
    import host_example
    data = tmp_path / "data.json"
    a = {"action": "pay", "tool_input": {"to": "acme"}}
    data.write_text(json.dumps({"approvals": [a, a]}))
    fact = {"tool_use_id": "t1", "tool_name": PAY, "subject": "agent", "action": "pay",
            "tool_input": {"to": "acme"}, "time": None}
    host_example.executed(fact, {"data_file": str(data)})
    host_example.executed(fact, {"data_file": str(data)})
    d = json.loads(data.read_text())
    assert d["approvals"] == [a] and d["executed"] == {"t1": "pay"}


WEIRD = SCRIPTED + """

class Weird(Exception):
    def __str__(self):
        raise RuntimeError("no text")


_answers = answers


def answers(call, now, factors, options):
    if call is not None:
        raise Weird()
    return _answers(call, now, factors, options)
"""


def test_an_exception_that_cannot_be_printed_holds(tmp_path):
    x = Mandate(tmp_path, terms=COUNTER_SPEC[0], factors=COUNTER_SPEC[1], host="scripted",
                answers={"paid": 0})
    (tmp_path / "scripted_host.py").write_text(WEIRD, encoding="utf-8")
    x.activate()
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z") == (2, held("the gate failed: Weird"))


NAMELESS = SCRIPTED + """

class Nameless(type):
    @property
    def __name__(cls):
        raise RuntimeError("no name")


class Odd(Exception, metaclass=Nameless):
    def __str__(self):
        raise RuntimeError("no text")


_answers = answers


def answers(call, now, factors, options):
    if call is not None:
        raise Odd()
    return _answers(call, now, factors, options)
"""


def test_an_exception_whose_class_has_no_name_holds(tmp_path):
    x = Mandate(tmp_path, terms=COUNTER_SPEC[0], factors=COUNTER_SPEC[1], host="scripted",
                answers={"paid": 0})
    (tmp_path / "scripted_host.py").write_text(NAMELESS, encoding="utf-8")
    x.activate()
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z") == (2, held("the gate failed"))


def test_standard_error_that_cannot_be_flushed_still_exits_2(tmp_path):
    assert os.path.exists("/dev/full")
    with open("/dev/full", "w") as full:
        r = subprocess.run([sys.executable, "-I", GATE, "pre", "--config", str(tmp_path / "no.json")],
                           input="{}", stdout=subprocess.PIPE, stderr=full, text=True)
    assert r.returncode == 2


REPORT_TRIEL_PY = """import pathlib, sys
print(pathlib.Path(__file__).with_name("report.json").read_text())
sys.exit(0)
"""
LAST_REPORTS = [
    ([{"line": "LAST", "entry": 0, "decisions": [{"term": 1, "decision": "ALLOW"}]}],
     "triel check exit 0, but the LAST line is for entry 0, not for the last entry 2"),
    ([{"line": "LAST", "entry": 2, "decisions": []}],
     "triel check exit 0, but no monitor decided on the action"),
    ([{"line": "LAST", "entry": 2, "decisions": [{"term": 1, "decision": "BLOCK"}]}],
     "triel check exit 0, but a decision of the LAST line is not ALLOW"),
    ([{"line": "LAST", "entry": 2, "decisions": [{"term": 1, "decision": "ALLOW"},
                                                 {"term": 7, "decision": "ALLOW"}]}],
     "the LAST line names TERM [7], which --actions does not give for this action"),
    ([{"line": "SPEC", "name": "x"}], "triel check exit 0, but the report has no LAST line")]


def test_reports_on_exit_0_that_do_not_allow(tmp_path):
    """Conditions (b) and (c) of a silent 0, and no TERM beyond --actions: a
    substitute triel.py prints each report with exit 0."""
    repo = fake_repo(tmp_path, REPORT_TRIEL_PY)
    x = Mandate(tmp_path, data={"approvals": [{"action": "pay", "tool_input": {}}]},
                config={"repo": str(repo)})
    x.activate()
    for i, (report, reason) in enumerate(LAST_REPORTS):
        (repo / "parser" / "report.json").write_text(json.dumps(report))
        assert x.pre(PAY, f"t{i}", "2026-11-13T09:10:00Z") == (2, held(reason))


STAMPING = """
from datetime import datetime, timezone
from triel_host import NO_NEW_READING, Reading


def answers(call, now, factors, options):
    stamp = open(options["mode"]).read().strip() == "now"
    return {"f": Reading(False, datetime.now(timezone.utc)) if stamp else NO_NEW_READING}


def executed(fact, options):
    pass
"""
STAMP_SPEC = ("agent MUST_NOT pay WHEN DEFAULT(f, false)",
              "f : Boolean METADATA MAX_AGE 60 SECONDS ON_STALE BLOCK")


def stamping_mandate(tmp_path, mode):
    x = Mandate(tmp_path, terms=STAMP_SPEC[0], factors=STAMP_SPEC[1], host="scripted")
    (tmp_path / "scripted_host.py").write_text(STAMPING, encoding="utf-8")
    x.config["host_options"]["mode"] = str(tmp_path / "mode")
    x.write_config()
    (tmp_path / "mode").write_text(mode)
    return x


def iso_of(t):
    return t.strftime("%Y-%m-%dT%H:%M:%S.%fZ")


def test_a_reading_stamped_when_the_host_module_answers_is_not_from_the_future(tmp_path):
    """The host clock h of a decision is read after the host module answered:
    a reading stamped while it answers is not later than h. On the system
    clock, since with --now both readings of the clock would be equal."""
    x = stamping_mandate(tmp_path, "none")
    past = datetime.now(timezone.utc) - timedelta(seconds=30)
    r = x.run(["activate"], now=iso_of(past))
    assert r.returncode == 0, r.stderr
    (tmp_path / "mode").write_text("now")
    assert x.pre(PAY, "t1", None) == (0, "")


CLOCKED = """
import time
from triel_host import NO_NEW_READING, Reading


def answers(call, now, factors, options):
    if call is not None:
        return {"f": NO_NEW_READING}
    with open(options["given"], "w", encoding="utf-8") as f:
        f.write(now.strftime("%Y-%m-%dT%H:%M:%S.%fZ"))
    ahead = int(open(options["ahead"], encoding="utf-8").read())
    t = time.time_ns() // 1000 + ahead * 1000000
    time.sleep(0.002)  # the module answers at least 1 ms after its source stamped the reading
    return {"f": Reading(False, f"{t // 1000000}.{t % 1000000:06d}")}


def executed(fact, options):
    pass
"""


def clocked_mandate(tmp_path, ahead):
    """A mandate whose host module stamps a reading by the clock of the system when it
    answers the activation, ahead seconds ahead of it, and writes the clock it was given."""
    x = Mandate(tmp_path, terms="agent MUST_NOT pay WHEN f",
                factors="f : Boolean METADATA MAX_AGE 60 SECONDS ON_STALE BLOCK", host="scripted")
    (tmp_path / "scripted_host.py").write_text(CLOCKED, encoding="utf-8")
    (tmp_path / "ahead").write_text(str(ahead))
    x.config["host_options"].update(given=str(tmp_path / "given"), ahead=str(tmp_path / "ahead"))
    x.write_config()
    return x


def test_an_activation_with_a_reading_stamped_when_the_module_answers(tmp_path):
    """The activation is at the clock given to the host module; the clock read once it
    has answered only bounds the readings. A reading stamped while the module answered is
    later than the activation, so the next decision, with no new reading, is allowed. On
    the clock of the system, since with --now both readings of the clock would be equal.
    Wrong gate: activation_time_after_answers, which takes the clock read once the module
    has answered as the time of the activation."""
    x = clocked_mandate(tmp_path, 0)
    r = x.run(["activate"])
    assert r.returncode == 0, r.stderr
    given = triel_host.seconds((tmp_path / "given").read_text())
    st = x.state()
    assert triel_host.seconds(st["activation"]["time"]) == given
    (line,) = [y for y in x.log() if y["event"] == "activated"]
    assert (triel_host.seconds(line["at"]), line["time"]) == (given, gate.iso(int(given)))
    [(stamp, value)] = st["readings"]["f"]["accepted"]
    assert triel_host.seconds(stamp) >= given and value == {"bool": False}
    assert x.pre(PAY, "t1", None) == (0, "")


def test_an_activation_with_a_reading_from_the_future(tmp_path):
    """A reading an hour ahead of the clock of the module is from the future at the
    activation too. Wrong gate: no_future_check_at_activation."""
    x = clocked_mandate(tmp_path, 3600)
    r = x.run(["activate"])
    assert (r.returncode, first(r)) == (2, held("activation refused"))
    assert "  factor f: a reading from the future" in r.stderr.splitlines()
    assert not (x.state_dir / "state.json").exists()


def test_inputs_compared_as_json_values(tmp_path):
    """An approval matches a call whose input has the same JSON value: a number
    with a fraction matches, and true does not match 1."""
    x = Mandate(tmp_path, data={"approvals": [{"action": "pay", "tool_input": {"flag": True}},
                                              {"action": "pay", "tool_input": {"amount": 100.1}}]})
    x.activate()
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"flag": 1}) == BLOCKED_PAY
    assert x.pre(PAY, "t2", "2026-11-13T09:10:01Z", {"amount": 100.1}) == (0, "")


def test_the_journal_says_allowed_only_once_the_state_is_written(m):
    (m.state_dir / "state.json.tmp").mkdir()
    code, line = m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"})
    assert code == 2 and line.startswith(held("the gate failed: IsADirectoryError"))
    assert "allowed" not in [x["event"] for x in m.log()]


def test_a_post_without_mcp_server_is_written_to_the_journal(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"}, server=None)
    x = m.log()[-1]
    assert (x["event"], x["tool_use_id"]) == ("post ignored", "t1")
    assert "has no mcp_server" in x["reasons"][0]
    assert list(m.state()["pending"]) == ["t1"]


LOCK_HOLDER = """import fcntl, sys
f = open(sys.argv[1], "a")
fcntl.flock(f, fcntl.LOCK_EX)
print("locked", flush=True)
sys.stdin.readline()
"""


def test_pre_waits_for_the_lock_at_most_the_check_timeout_and_post_longer(m):
    """check_timeout_seconds 1 and another process holds the lock until pre has
    given up: pre waits at most 1 s; the late PostToolUse of a call recorded as
    not executed waits up to 3 s, gets the lock once it is released and records
    the conflict."""
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    m.failure(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"}, is_interrupt=True)
    assert m.command("resolve", "t1", "--not-executed", now="2026-11-13T09:11:00Z") == (0, "")
    m.config["check_timeout_seconds"] = 1
    m.write_config()
    holder = subprocess.Popen([sys.executable, "-c", LOCK_HOLDER, str(m.state_dir / "lock")],
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    assert holder.stdout.readline().strip() == "locked"

    def start(command, event, tid, now):
        payload = {"hook_event_name": event, "tool_name": PAY, "tool_input": {"to": "acme"},
                   "tool_use_id": tid, "mcp_server": {"name": "payments", "source": "managed"},
                   "duration_ms": 5}
        p = subprocess.Popen([sys.executable, "-I", GATE, command, "--config", str(m.config_path),
                              "--now", now], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True)
        p.stdin.write(json.dumps(payload))
        p.stdin.close()
        return p

    began = time.monotonic()
    pre = start("pre", "PreToolUse", "t2", "2026-11-13T09:12:00Z")
    post = start("post", "PostToolUse", "t1", "2026-11-13T09:12:00Z")
    assert (pre.wait(), pre.stderr.read().splitlines()[0]) == (
        2, held("another decision of the gate is still running"))
    assert time.monotonic() - began < 3 * m.config["check_timeout_seconds"]  # less than post waits
    holder.stdin.write("release\n")
    holder.stdin.close()
    holder.wait()
    assert post.wait() == 0
    assert m.state()["conflicts"]["t1"]["why"] == (
        "PostToolUse came for a call recorded as not executed")


def test_status_shows_the_age_of_a_pending_call_and_when_it_becomes_unknown(m):
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    r = m.run(["status"], now="2026-11-13T09:12:00Z")
    st = json.loads(r.stdout)
    assert (st["pending"]["t1"]["age_seconds"], st["pending"]["t1"]["unknown_in_seconds"]) == (120, 480)
    r = m.run(["status"], now="2026-11-13T09:30:00Z")
    st = json.loads(r.stdout)
    assert st["pending"] == {} and st["unknown"]["t1"]["why"] == (
        "no PostToolUse or PostToolUseFailure within 600 s")
    assert list(m.state()["pending"]) == ["t1"]  # status changes nothing


def test_do_not_retry_is_said_only_to_a_call_before_it_runs(tmp_path):
    bad = str(tmp_path / "no.json")
    for command, said in (("pre", True), ("post", False), ("failure", False)):
        r = subprocess.run([sys.executable, "-I", GATE, command, "--config", bad], input="{}",
                           capture_output=True, text=True)
        assert r.returncode == 2 and ("Do not retry" in r.stderr) == said


def test_a_hook_after_a_call_says_not_recorded(tmp_path):
    """After the call (post, failure, denied) exit 2 means that the fact was not
    recorded; before it (pre) and for a command of the operator, held."""
    bad = str(tmp_path / "no.json")
    for command, head in (("pre", "held"), ("post", "not recorded"), ("failure", "not recorded"),
                          ("denied", "not recorded"), ("status", "held")):
        r = subprocess.run([sys.executable, "-I", GATE, command, "--config", bad], input="{}",
                           capture_output=True, text=True)
        assert r.returncode == 2 and first(r).startswith(f"TRIEL gate: {head}: "), (command, r.stderr)


def test_the_key_of_the_cache_has_the_version_of_lark_and_separators():
    k = gate.cache_key(b"spec", [b"ab", b"c"], "1.3.1")
    assert k != gate.cache_key(b"spec", [b"a", b"bc"], "1.3.1")
    assert k != gate.cache_key(b"spec", [b"ab", b"c"], "1.3.2")
    assert k == gate.cache_key(b"spec", [b"ab", b"c"], "1.3.1")


PRINTING = SCRIPTED + """
import os
_answers, _executed = answers, executed


def answers(call, now, factors, options):
    print("a line from answers")
    os.write(1, b"a line written to fd 1\\n")
    return _answers(call, now, factors, options)


def executed(fact, options):
    print("a line from executed")
    _executed(fact, options)
"""


def test_what_the_host_module_prints_does_not_reach_the_hook_output(tmp_path):
    x = Mandate(tmp_path, terms=COUNTER_SPEC[0], factors=COUNTER_SPEC[1], host="scripted",
                answers={"paid": 0})
    (tmp_path / "scripted_host.py").write_text(PRINTING, encoding="utf-8")
    x.activate()
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z") == (0, "")
    r = x.post(PAY, "t1", "2026-11-13T09:10:01Z")
    assert r.stdout == ""


def test_what_the_host_module_prints_does_not_reach_the_output_of_a_command(tmp_path):
    """activate and resolve --executed discard what the module prints with print()
    or writes to the file descriptor 1 while answers and executed run."""
    x = Mandate(tmp_path, terms=COUNTER_SPEC[0], factors=COUNTER_SPEC[1], host="scripted",
                answers={"paid": 0})
    (tmp_path / "scripted_host.py").write_text(PRINTING, encoding="utf-8")
    r = x.run(["activate"], now=ACT)
    assert (r.returncode, r.stdout, r.stderr) == (0, "", "")
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z") == (0, "")
    r = x.run(["resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z"],
              now="2026-11-13T09:11:00Z")
    assert (r.returncode, r.stdout, r.stderr) == (0, "", "")
    assert [f["tool_use_id"] for f in x.facts()] == ["t1"]


def test_a_hook_started_with_its_standard_output_closed(m):
    """The file descriptor 1 is closed when the hook starts: /dev/null takes it."""
    for tid, tool, server in (("c1", PAY, MANAGED), ("c2", "mcp__docs__search", ("docs", "managed"))):
        payload = {"hook_event_name": "PreToolUse", "tool_name": tool, "tool_input": {"to": "acme"},
                   "tool_use_id": tid, "mcp_server": {"name": server[0], "source": server[1]}}
        p = subprocess.Popen([sys.executable, "-I", GATE, "pre", "--config", str(m.config_path),
                              "--now", "2026-11-13T09:10:00Z"], stdin=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True, preexec_fn=lambda: os.close(1))
        _, err = p.communicate(json.dumps(payload))
        assert (p.returncode, err) == (0, ""), (tool, err)
    assert list(m.state()["pending"]) == ["c1"]


def test_the_journal_follows_the_state(m):
    """The state cannot be written after the host module refused the fact: the
    journal has no executed and no conflict, and the call is still pending."""
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"to": "acme"}) == (0, "")
    (m.tmp / "host_data.json.tmp").mkdir()
    (m.state_dir / "state.json.tmp").mkdir()
    r = m.run(["resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z"],
              now="2026-11-13T09:11:00Z")
    (m.state_dir / "state.json.tmp").rmdir()
    assert r.returncode == 2 and first(r).startswith(held("the gate failed: IsADirectoryError"))
    st = m.state()
    assert list(st["pending"]) == ["t1"] and st["conflicts"] == {} and st["history"] == []
    events = [x["event"] for x in m.log()]
    assert "executed" not in events and "conflict" not in events, events
    assert m.pre(PAY, "t2", "2026-11-13T09:12:00Z", {"to": "acme"}) == (
        2, held("waits for the outcome of the previous action, the call t1"))


LEAKING = SCRIPTED + """
import ctypes
import sys

_answers, _executed = answers, executed


def answers(call, now, factors, options):
    if call is not None:
        sys.__stdout__.write(json.dumps({"hookSpecificOutput": {
            "hookEventName": "PreToolUse", "permissionDecision": "allow"}}))
        ctypes.CDLL(None).printf(b"a line through the stdio of C\\n")
    return _answers(call, now, factors, options)


def executed(fact, options):
    sys.__stdout__.write(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PostToolUse", "updatedToolOutput": "from the host module"}}))
    _executed(fact, options)
"""


def test_what_the_host_module_writes_past_sys_stdout_does_not_reach_the_hook_output(tmp_path):
    """sys.__stdout__ and the stdio of C are flushed when the process exits,
    after quiet: a hook sends its standard output to /dev/null for its whole run."""
    x = Mandate(tmp_path, terms=COUNTER_SPEC[0], factors=COUNTER_SPEC[1], host="scripted",
                answers={"paid": 0})
    (tmp_path / "scripted_host.py").write_text(LEAKING, encoding="utf-8")
    x.activate()
    r = x.hook("pre", "PreToolUse", PAY, "t1", "2026-11-13T09:10:00Z")
    assert (r.returncode, r.stdout, r.stderr) == (0, "", "")
    r = x.post(PAY, "t1", "2026-11-13T09:10:01Z")
    assert (r.returncode, r.stdout) == (0, "")
    assert [f["tool_use_id"] for f in x.facts()] == ["t1"]


PROBE = """import json, os, sys
print(json.dumps({"env": dict(os.environ), "isolated": sys.flags.isolated,
                  "executable": sys.executable}))
"""


def test_the_child_has_the_environment_of_the_gate_and_runs_isolated(tmp_path, monkeypatch):
    """The two protections of the child process, each on its own: the
    environment that the gate sets, and sys.executable -I."""
    (tmp_path / "probe.py").write_text(PROBE)
    fake = tmp_path / "bin"
    fake.mkdir()
    (fake / "python3").write_text("#!/bin/sh\necho '{}'\n")
    (fake / "python3").chmod(0o755)
    monkeypatch.setenv("PATH", f"{fake}:{os.environ.get('PATH', '')}")
    for k in ("TRIEL_EVALUATOR", "PYTHONPATH", "TRIEL_GATE_CONFIG", "TRIEL_GATE_NOW"):
        monkeypatch.setenv(k, str(tmp_path))
    code, out, err = gate.child({"repo": str(tmp_path), "check_timeout_seconds": 30},
                                [str(tmp_path / "probe.py")])
    d = json.loads(out)
    assert code == 0 and d["isolated"] == 1 and d["executable"] == sys.executable
    assert d["env"]["PATH"] == os.defpath and set(d["env"]) <= {"PATH", "LC_CTYPE"}


# --- The example: the approval of a payment (README.md, section "The example") ----------
#
# The setting follows the paper (README.md): a daily limit of 0.01 and three invoices of
# 0.01; in the example the payee is on the owner's list, the approvals of the owner are in
# the store of the host, and the code in the mail has six digits. Each scenario
# C1 to C11 of README.md is a test; the blocking TERMs come from the first line of the
# standard error of the gate, the verdicts, where they matter, from triel check on the
# trace that the gate kept. The expectations were written before the module was.

from decimal import Decimal  # noqa: E402

RAISE = "mcp__payments__raise_limit"
PAYEE_A = "0x7Fa3C9e1D24b6058aE13f9C0b2D47e6A5c81B3d9"
PAYEE_B = "0x2bD84F6a0C17e3B95dA2c6E8f1047B3aD9e5C6f2"
STRANGER = "0x9E0c5A7b3F18d2C46eB9a01D7c3f5E28B6a4D1c7"
INVOICE = {n: {"to": PAYEE_A, "amount": "0.01", "invoice": f"INV-{n}"} for n in (1, 2, 3)}
EXCHANGE = {"amount": "100.00", "from": "USDC", "to": "EUR"}
GRANTED = "2026-11-13T09:05:00Z"
CODE = "604117"
T0 = "2026-11-13T09:10:00Z"
OPEN = ("ALLOW", "PENDING")        # the monitor allows; the condition is false
UNDEFINED = ("BLOCK", "PENDING")   # the monitor blocks; the condition has no value
TRUE = ("BLOCK", "BREACHED")       # the monitor blocks; the condition is true at T


def approval(aid, tool_input, granted=GRANTED, tool=PAY):
    return {"type": "approval", "id": aid, "tool": tool, "tool_input": tool_input,
            "granted": granted}


def revocation(aid, time="2026-11-13T09:06:00Z"):
    return {"type": "revocation", "id": aid, "time": time}


def example_options(tmp):
    """The host_options of config.example.json, each file in tmp under its own name."""
    return {k: (str(tmp / Path(v).name) if k.endswith("_file") else v)
            for k, v in example_config()["host_options"].items()}


def example_data(limit, payees):
    return {"values": {"daily_limit": limit, "rate_limit": "1.20"}, "payees": list(payees)}


class Example(Mandate):
    """mandate.triel, host_example.py and config.example.json, with the files of the
    host in tmp: the data of the owner, the approvals written by the channel, and the
    files of the module, which the activation creates."""

    def __init__(self, tmp, limit="0.05", payees=(PAYEE_A,), approvals=()):
        super().__init__(tmp, data=example_data(limit, payees))
        shutil.copy(HERE / "mandate.triel", self.spec)
        cfg = example_config()
        self.options = example_options(tmp)
        self.config.update(actions=cfg["actions"], allowed_tools=cfg["allowed_tools"],
                           managed_servers=cfg["managed_servers"], host_options=self.options)
        self.write_config()
        Path(self.options["approvals_file"]).write_text("", encoding="utf-8")
        self.add(*approvals)
        r = self.run(["activate"], now=ACT)
        assert r.returncode == 0, r.stderr

    def add(self, *records):
        """The channel appends approvals and revocations to its file."""
        with open(self.options["approvals_file"], "a", encoding="utf-8") as f:
            for rec in records:
                f.write(json.dumps(rec) + "\n")

    def ledger(self):
        return json.loads(Path(self.options["ledger_file"]).read_text(encoding="utf-8"))

    def executions(self):
        return json.loads(Path(self.options["executions_file"]).read_text(encoding="utf-8"))

    def standing(self):
        """The ids of the approvals in the file of the channel that no execution spent."""
        spent = self.ledger()["spent"]
        lines = Path(self.options["approvals_file"]).read_text(encoding="utf-8").splitlines()
        return [r["id"] for r in map(json.loads, lines)
                if r["type"] == "approval" and r["id"] not in spent]

    def decide(self, tool, tid, now, tool_input):
        """(exit code, the blocking TERMs of the first line, the result); the TERMs are
        None when the first line is not a BLOCK of triel check."""
        r = self.hook("pre", "PreToolUse", tool, tid, now, tool_input)
        if r.returncode == 0:
            assert r.stdout == "" and r.stderr == "", (r.stdout, r.stderr)
            return 0, [], r
        m = re.fullmatch(r"TRIEL gate: held: triel check exit 3: BLOCK: (.*)", first(r))
        terms = None if m is None else sorted(
            int(t) for t in re.findall(r"monitor TERM (\d+) blocks the action", m.group(1)))
        return r.returncode, terms, r

    def report(self, r):
        """The JSON report of triel check --last on the trace that the gate kept for
        the held call: its path is the second line of the standard error."""
        path = r.stderr.splitlines()[1].strip()
        assert path.startswith("trace: "), r.stderr
        out = subprocess.run([sys.executable, str(REPO / "parser" / "triel.py"), "check",
                              str(self.spec), path[len("trace: "):], "--json", "--last",
                              "--evaluator", default_evaluator()],
                             capture_output=True, text=True, cwd=REPO)
        return json.loads(out.stdout)

    def verdicts(self, r):
        """{TERM: (its decision in the LAST line, its verdict)} for the held call."""
        objs = self.report(r)
        status = {o["term"]: o["status"]["verdict"] for o in objs if o["line"] == "TERM"}
        (last,) = [o for o in objs if o["line"] == "LAST"]
        return {d["term"]: (d["decision"], status[d["term"]]) for d in last["decisions"]}


def test_the_example_c1_the_setting_of_the_paper(tmp_path):
    """The first invoice is paid; the second is over the daily limit; the code from the
    mail does not raise the limit; the second is still over it."""
    x = Example(tmp_path, limit="0.01",
                approvals=[approval(f"A{n}", INVOICE[n]) for n in (1, 2, 3)])
    assert x.decide(PAY, "t1", T0, INVOICE[1])[:2] == (0, [])
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", INVOICE[1])
    assert x.executions()["executed"]["t1"]["tool_input"] == INVOICE[1]
    code, terms, r = x.decide(PAY, "t2", "2026-11-13T09:10:05Z", INVOICE[2])
    assert (code, first(r)) == (2, held("triel check exit 3: BLOCK: monitor TERM 5 blocks the "
                                        "action"))
    assert x.verdicts(r)[5] == TRUE
    code, terms, r = x.decide(RAISE, "t3", "2026-11-13T09:10:10Z", {"code": CODE, "daily": "1"})
    assert (code, terms) == (2, [1]) and x.verdicts(r) == {1: TRUE}
    assert x.decide(PAY, "t4", "2026-11-13T09:10:15Z", INVOICE[2])[:2] == (2, [5])


def test_the_example_c2_a_letter_from_the_owner_to_an_unknown_payee(tmp_path):
    x = Example(tmp_path, limit="0.01")
    call = {"to": STRANGER, "amount": "0.02", "invoice": "INV-4"}
    assert x.decide(PAY, "t1", T0, call)[:2] == (2, [2, 5, 6])


def test_the_example_c2b_a_letter_from_the_owner_to_a_known_payee(tmp_path):
    x = Example(tmp_path, limit="0.01")
    call = {"to": PAYEE_A, "amount": "0.02", "invoice": "INV-4"}
    assert x.decide(PAY, "t1", T0, call)[:2] == (2, [2, 5])


def test_the_example_c3_an_approval_requested_that_did_not_come(tmp_path):
    x = Example(tmp_path)
    code, terms, r = x.decide(PAY, "t1", T0, INVOICE[1])
    assert (code, terms) == (2, [2])
    assert x.verdicts(r) == {2: TRUE, 3: OPEN, 4: OPEN, 5: OPEN, 6: OPEN}


@pytest.mark.parametrize("broken", ["a directory", "a line that is not JSON"])
def test_the_example_c3a_the_store_of_approvals_cannot_be_read(tmp_path, broken):
    x = Example(tmp_path, approvals=[approval("A1", INVOICE[1])])
    store = Path(x.options["approvals_file"])
    if broken == "a directory":
        store.unlink()
        store.mkdir()
    else:
        with open(store, "a", encoding="utf-8") as f:
            f.write('{"type": "approval", "id": "A2", "tool"\n')
    code, terms, r = x.decide(PAY, "t1", T0, INVOICE[1])
    assert (code, terms) == (2, [2, 3, 4])
    assert x.verdicts(r) == {2: UNDEFINED, 3: UNDEFINED, 4: UNDEFINED, 5: OPEN, 6: OPEN}


C4 = {  # the time g of the approval, the host clock of the decision, the result
    "at g + 600": (GRANTED, "2026-11-13T09:15:00Z", None),
    "at g + 600.5": (GRANTED, "2026-11-13T09:15:00.5Z", TRUE),
    "at g + 601": (GRANTED, "2026-11-13T09:15:01Z", TRUE),
    "a stamp 1 s later than the host clock": ("2026-11-13T09:10:01Z", T0, UNDEFINED),
    # 09:02 UTC: read as UTC, the stamp would be three hours younger than it is
    "a stamp with a zone offset": ("2026-11-13T12:02:00+03:00", "2026-11-13T12:05:00Z",
                                   UNDEFINED)}


@pytest.mark.parametrize("variant", list(C4))
def test_the_example_c4_an_approval_that_is_too_old_at_the_decision(tmp_path, variant):
    """Each variant on its own mandate: after an ALLOW the call waits for its outcome,
    after its execution the approval is spent, and the clock of a mandate does not go
    back."""
    granted, now, result = C4[variant]
    x = Example(tmp_path, approvals=[approval("A1", INVOICE[1], granted=granted)])
    code, terms, r = x.decide(PAY, "t1", now, INVOICE[1])
    if result is None:
        assert (code, terms) == (0, [])
    else:
        assert (code, terms) == (2, [3])
        assert x.verdicts(r)[3] == result


def test_the_example_c5_an_approval_of_another_call(tmp_path):
    """The approval names the whole input: another payee or another amount is another call."""
    x = Example(tmp_path, payees=(PAYEE_A, PAYEE_B), approvals=[approval("A1", INVOICE[1])])
    assert x.decide(PAY, "t1", T0, dict(INVOICE[1], to=PAYEE_B))[:2] == (2, [2])
    assert x.decide(PAY, "t2", "2026-11-13T09:10:05Z", dict(INVOICE[1], amount="0.02"))[:2] == (
        2, [2])
    assert x.standing() == ["A1"] and x.ledger()["spent"] == {}


def test_the_example_c6_an_approval_revoked_before_the_decision(tmp_path):
    x = Example(tmp_path, approvals=[approval("A1", INVOICE[1]), revocation("A1")])
    code, terms, r = x.decide(PAY, "t1", T0, INVOICE[1])
    assert (code, terms) == (2, [4])
    assert x.verdicts(r) == {2: OPEN, 3: OPEN, 4: TRUE, 5: OPEN, 6: OPEN}


def test_the_example_c6a_a_revocation_that_cannot_be_read(tmp_path):
    x = Example(tmp_path, approvals=[approval("A1", INVOICE[1]),
                                     {"type": "revocation", "id": "A1", "time": "yesterday"}])
    code, terms, r = x.decide(PAY, "t1", T0, INVOICE[1])
    assert (code, terms) == (2, [4])
    assert x.verdicts(r) == {2: OPEN, 3: OPEN, 4: UNDEFINED, 5: OPEN, 6: OPEN}


@pytest.mark.parametrize("when", ["before the execution", "after the execution"])
def test_the_example_c7_a_revocation_written_after_pre(tmp_path, when):
    """The decision is for the moment T: a revocation that reaches the store after pre
    does not change it, whatever its stamp (here one before T). The decisions on the
    earlier entries are final: in the report on the trace of the repeat, the monitor of
    the revocation still allows the executed payment."""
    x = Example(tmp_path, approvals=[approval("A1", INVOICE[1])])
    assert x.decide(PAY, "t1", T0, INVOICE[1])[:2] == (0, [])
    late = revocation("A1", time="2026-11-13T09:09:00Z")
    if when == "before the execution":
        x.add(late)
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", INVOICE[1])
    if when == "after the execution":
        x.add(late)
    assert [e["event"] for e in x.log() if e.get("tool_use_id") == "t1"] == ["allowed", "executed"]
    code, terms, r = x.decide(PAY, "t2", "2026-11-13T09:11:00Z", INVOICE[1])
    assert (code, terms) == (2, [2])
    assert x.standing() == []
    trace = json.loads(Path(r.stderr.splitlines()[1].strip()[len("trace: "):]).read_text())
    (k,) = [i for i, e in enumerate(trace["entries"][:-1]) if e["event"]["kind"] == "act"]
    (monitor,) = [o for o in x.report(r) if o["line"] == "MONITOR" and o["term"] == 4]
    assert {"entry": k, "decision": "ALLOW"} in monitor["decisions"]


def test_the_example_c8_a_fresh_approval_of_this_call_within_the_limit(tmp_path):
    """The control: the call that every rule allows is allowed, so a gate that always holds
    fails the scenarios."""
    x = Example(tmp_path, limit="0.01", approvals=[approval("A1", INVOICE[1])])
    assert x.decide(PAY, "t1", T0, INVOICE[1])[:2] == (0, [])
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", INVOICE[1])
    assert x.state()["history"][0]["tool_use_id"] == "t1" and x.standing() == []


def test_the_example_c9a_two_approvals_of_one_input(tmp_path):
    x = Example(tmp_path, approvals=[approval("A1", INVOICE[1]), approval("A2", INVOICE[1])])
    code, terms, r = x.decide(PAY, "t1", T0, INVOICE[1])
    assert (code, terms) == (2, [2, 3, 4])
    assert x.verdicts(r) == {2: UNDEFINED, 3: UNDEFINED, 4: UNDEFINED, 5: OPEN, 6: OPEN}


def test_the_example_c9b_a_second_approval_comes_before_post(tmp_path):
    """The approval chosen at pre is the one the execution spends."""
    x = Example(tmp_path, approvals=[approval("A1", INVOICE[1])])
    assert x.decide(PAY, "t1", T0, INVOICE[1])[:2] == (0, [])
    assert x.ledger()["selected"]["t1"] == "A1"
    x.add(approval("A2", INVOICE[1], granted="2026-11-13T09:10:00.5Z"))
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", INVOICE[1])
    assert x.ledger()["spent"] == {"A1": "t1"} and x.standing() == ["A2"]


def test_the_example_c10_an_approval_whose_id_an_execution_spent(tmp_path):
    x = Example(tmp_path, approvals=[approval("A1", INVOICE[1])])
    assert x.decide(PAY, "t1", T0, INVOICE[1])[:2] == (0, [])
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", INVOICE[1])
    x.add(approval("A1", INVOICE[2], granted="2026-11-13T09:10:30Z"))
    code, terms, r = x.decide(PAY, "t2", "2026-11-13T09:11:00Z", INVOICE[2])
    assert (code, terms) == (2, [2])
    assert x.verdicts(r)[2] == TRUE


def test_the_example_c11_midnight(tmp_path):
    """A day is a calendar day of UTC: a payment executed at 23:59:59 does not count on
    the next day."""
    x = Example(tmp_path, limit="0.01",
                approvals=[approval("A1", INVOICE[1], granted="2026-11-13T23:55:00Z"),
                           approval("A2", INVOICE[2], granted="2026-11-13T23:56:00Z")])
    assert x.decide(PAY, "t1", "2026-11-13T23:59:58.5Z", INVOICE[1])[:2] == (0, [])
    x.post(PAY, "t1", "2026-11-13T23:59:59Z", INVOICE[1])
    assert [e["E"] for e in x.log() if e["event"] == "executed"] == ["2026-11-13T23:59:59Z"]
    assert x.decide(PAY, "t2", "2026-11-14T00:00:00Z", INVOICE[2])[:2] == (0, [])


def test_the_example_a_fact_that_only_the_first_store_takes(tmp_path):
    """The store of the approvals takes the fact, the store of the executions cannot be
    written: a conflict. resolve --executed gives the fact again; each store adds only
    what it does not have: the approval stays spent once, and the payment counts in the
    total of the day."""
    x = Example(tmp_path, limit="0.01",
                approvals=[approval("A1", INVOICE[1]), approval("A2", INVOICE[2])])
    assert x.decide(PAY, "t1", T0, INVOICE[1])[:2] == (0, [])
    blocker = Path(x.options["executions_file"] + ".tmp")
    blocker.mkdir()
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", INVOICE[1])
    assert x.state()["conflicts"]["t1"]["why"].startswith(
        "the host module did not take the execution: IsADirectoryError")
    assert x.ledger()["spent"] == {"A1": "t1"} and "t1" not in x.executions()["executed"]
    blocker.rmdir()
    assert x.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z",
                     now="2026-11-13T09:11:00Z") == (0, "")
    assert x.ledger()["spent"] == {"A1": "t1"} and x.ledger()["taken"] == ["t1"]
    assert list(x.executions()["executed"]) == ["t1"] and x.standing() == ["A2"]
    assert x.decide(PAY, "t2", "2026-11-13T09:12:00Z", INVOICE[2])[:2] == (2, [5])


# The host module called directly: what it gives for each factor (README.md, "What the
# host module computes"). Fast, without the gate and triel check.

def at(t):
    return datetime.fromisoformat(t.replace("Z", "+00:00"))


class Direct:
    def __init__(self, tmp, limit="0.01", payees=(PAYEE_A,), approvals=()):
        import host_example
        import triel_host
        tmp.mkdir(parents=True, exist_ok=True)
        self.module = host_example
        self.options = example_options(tmp)
        Path(self.options["data_file"]).write_text(json.dumps(example_data(limit, payees)))
        Path(self.options["approvals_file"]).write_text(
            "".join(json.dumps(a) + "\n" for a in approvals), encoding="utf-8")
        self.factors = triel_host.spec_factors((HERE / "mandate.triel").read_text(encoding="utf-8"))
        self.module.answers(None, at(ACT), self.factors, self.options)  # the activation

    def ask(self, tool_input, now=T0, tool=PAY, tid="t1"):
        call = {"tool_use_id": tid, "tool_name": tool, "tool_input": tool_input,
                "subject": "agent", "action": "pay", "mcp_server": {"name": "payments",
                                                                    "source": "managed"}}
        return self.module.answers(call, at(now), self.factors, self.options)

    def take(self, tid, tool_input, time, tool=PAY):
        self.module.executed({"tool_use_id": tid, "tool_name": tool, "subject": "agent",
                              "action": "pay", "tool_input": tool_input, "time": at(time)},
                             self.options)

    def file(self, key):
        return json.loads(Path(self.options[key]).read_text(encoding="utf-8"))


def test_the_example_host_module_amounts(tmp_path):
    """An amount is a decimal string; a JSON number has no value, the float 0.01 and the
    integer 2 among them. Wrong module: amount_from_a_json_number."""
    d = Direct(tmp_path)
    for amount, total in (("0.01", Decimal("0.01")), (0.01, None), (2, None),
                          ("0.010", Decimal("0.01")), ("0", None), ("-0.01", None),
                          (0, None), ("abc", None), ("1e-2", None), (True, None), (None, None),
                          ("NaN", None), (" 0.01", None), ([1], None)):
        assert d.ask(dict(INVOICE[1], amount=amount))["day_total"] == total, amount
    assert d.ask({"to": PAYEE_A, "invoice": "INV-1"})["day_total"] is None


def test_the_example_host_module_payees(tmp_path):
    d = Direct(tmp_path, payees=[PAYEE_A, "acme"])
    for to, listed in ((PAYEE_A, True), (PAYEE_A.lower(), True), (PAYEE_A.upper(), True),
                       (PAYEE_A + "0", False), (PAYEE_A[:-1], False), ("acme", True),
                       ("ACME", False), ("acme ", False), (STRANGER, False), (5, None),
                       (None, None)):
        assert d.ask(dict(INVOICE[1], to=to))["payee_listed"] is listed, to
    assert d.ask({"amount": "0.01", "invoice": "INV-1"})["payee_listed"] is None


def test_the_example_host_module_keys_outside_the_schema(tmp_path):
    d = Direct(tmp_path, approvals=[approval("A1", dict(INVOICE[1], memo="x"))])
    a = d.ask(dict(INVOICE[1], memo="x"))
    assert {k: a[k] for k in CALL_FACTORS} == dict.fromkeys(CALL_FACTORS)
    assert {k: d.ask(["0.01"])[k] for k in CALL_FACTORS} == dict.fromkeys(CALL_FACTORS)


def broken(path):
    """A file that cannot be read: a directory in its place."""
    p = Path(path)
    if p.exists():
        p.unlink()
    p.mkdir()


def test_the_example_host_module_unknown_is_not_no(tmp_path):
    """Each source on its own: what cannot be read has no value, and only the factors
    computed from it."""
    def fresh(name):
        return Direct(tmp_path / name, approvals=[approval("A1", INVOICE[1])])

    whole = fresh("whole").ask(INVOICE[1])
    assert {k: whole[k] for k in CALL_FACTORS + ("daily_limit",)} == {
        "call_approved": True, "approval_age": 300, "approval_revoked": False,
        "day_total": Decimal("0.01"), "payee_listed": True, "daily_limit": "0.01"}

    def without(name, key, factors):
        d = fresh(name)
        broken(d.options[key])
        a = d.ask(INVOICE[1])
        assert {k: a[k] for k in factors} == dict.fromkeys(factors), name
        assert {k: a[k] for k in a if k not in factors and k != "fx_rate"} == {
            k: whole[k] for k in whole if k not in factors and k != "fx_rate"}, name
        return a

    a = without("data", "data_file", ("daily_limit", "rate_limit", "payee_listed"))
    assert a["fx_rate"] is not None  # no new reading, never a value
    without("approvals", "approvals_file", ("call_approved", "approval_age", "approval_revoked"))
    without("ledger", "ledger_file", ("call_approved", "approval_age", "approval_revoked"))
    without("executions", "executions_file", ("day_total",))
    d = fresh("missing")
    Path(d.options["approvals_file"]).unlink()
    assert d.ask(INVOICE[1])["call_approved"] is None
    d = fresh("not a list")
    Path(d.options["data_file"]).write_text(json.dumps(dict(example_data("0.01", []),
                                                            payees=PAYEE_A)))
    assert d.ask(INVOICE[1])["payee_listed"] is None
    d = fresh("a spent amount that cannot be read")
    d.take("t0", dict(INVOICE[2], amount="much"), "2026-11-13T09:09:00Z")
    assert d.ask(INVOICE[1])["day_total"] is None


@pytest.mark.parametrize("granted,now,age", [
    (GRANTED, "2026-11-13T09:15:00Z", 600),
    (GRANTED, "2026-11-13T09:15:00.5Z", 601),
    ("2026-11-13T09:05:00.25Z", "2026-11-13T09:15:00Z", 600),
    (1794560700, "2026-11-13T09:15:00Z", 600),
    ("1794560700", "2026-11-13T09:15:00Z", 600),
    (GRANTED, GRANTED, 0),
    ("2026-11-13T09:15:01Z", "2026-11-13T09:15:00Z", None),
    ("2026-11-13T12:05:00+03:00", "2026-11-13T09:15:00Z", None),
    ("2026-11-13 09:05:00", "2026-11-13T09:15:00Z", None),
    (True, "2026-11-13T09:15:00Z", None),
    (None, "2026-11-13T09:15:00Z", None)])
def test_the_example_host_module_age_of_an_approval(tmp_path, granted, now, age):
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1], granted=granted)])
    a = d.ask(INVOICE[1], now=now)
    assert (a["call_approved"], a["approval_age"]) == (True, age)


@pytest.mark.parametrize("records,revoked", [
    ([], False),
    ([revocation("A1", time="2027-01-01T00:00:00Z")], True),   # at any stamp
    ([revocation("A1", time=0)], True),
    ([revocation("A2")], False),
    ([{"type": "revocation", "id": "A1", "time": "yesterday"}], None),
    ([{"type": "revocation", "id": "A1"}], None),
    ([{"type": "revocation", "id": "A1", "time": GRANTED, "by": "owner"}], None),
    ([{"type": "revocation", "id": "A1", "time": "yesterday"}, revocation("A1")], True)])
def test_the_example_host_module_revocation(tmp_path, records, revoked):
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1])] + records)
    assert d.ask(INVOICE[1])["approval_revoked"] is revoked


def test_the_example_host_module_no_approval_and_two_approvals(tmp_path):
    d = Direct(tmp_path / "none", approvals=[approval("A1", INVOICE[2], tool=CONVERT)])
    a = d.ask(INVOICE[2])
    assert (a["call_approved"], a["approval_age"], a["approval_revoked"]) == (False, None, None)
    d = Direct(tmp_path / "two", approvals=[approval("A1", INVOICE[1]),
                                            approval("A2", {**INVOICE[1]})])
    a = d.ask(INVOICE[1])
    assert (a["call_approved"], a["approval_age"], a["approval_revoked"]) == (None, None, None)
    assert d.file("ledger_file")["selected"] == {"t1": None}


def test_the_example_host_module_spends_what_it_chose(tmp_path):
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1])])
    assert d.ask(INVOICE[1], tid="t1")["call_approved"] is True
    with open(d.options["approvals_file"], "a", encoding="utf-8") as f:
        f.write(json.dumps(approval("A2", INVOICE[1])) + "\n")
    d.take("t1", INVOICE[1], "2026-11-13T09:10:01Z")
    d.take("t1", INVOICE[1], "2026-11-13T09:10:01Z")      # a fact given twice
    ledger = d.file("ledger_file")
    assert (ledger["spent"], ledger["taken"]) == ({"A1": "t1"}, ["t1"])
    assert list(d.file("executions_file")["executed"]) == ["t1"]
    assert d.ask(INVOICE[1], tid="t2")["call_approved"] is True    # A2


def test_the_example_host_module_without_a_choice_spends_every_approval_of_the_call(tmp_path):
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1]), approval("A2", INVOICE[1]),
                                    approval("A3", INVOICE[2])])
    d.take("t9", INVOICE[1], "2026-11-13T09:10:01Z")
    assert d.file("ledger_file")["spent"] == {"A1": "t9", "A2": "t9"}
    assert d.ask(INVOICE[1], tid="t10")["call_approved"] is False


@pytest.mark.parametrize("key", ["ledger_file", "executions_file", "approvals_file"])
def test_the_example_host_module_executed_raises_when_it_cannot_read(tmp_path, key):
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1])])
    broken(d.options[key])
    with pytest.raises(OSError):
        d.take("t9", INVOICE[1], "2026-11-13T09:10:01Z")


def test_the_example_host_module_an_executed_amount_written_as_a_json_number(tmp_path):
    """A payment executed with an amount written as a JSON number (a PostToolUse with
    another input, then resolve --executed) leaves the total of the day without a value,
    also after the file of executions is written again, by the fact of another call or by
    the same fact with another time. Wrong modules: a_number_in_executions_becomes_a_string,
    which reads the file with its numbers as Decimal and writes them back as strings, and
    executed_amount_from_a_json_number, which counts such an amount."""
    d = Direct(tmp_path, limit="0.05")
    d.take("t1", dict(INVOICE[1], amount=0.01), "2026-11-13T09:08:00Z")
    assert d.ask(INVOICE[2], tid="t2")["day_total"] is None
    d.take("t3", EXCHANGE, "2026-11-13T09:09:00Z", tool=CONVERT)          # the file is written again
    assert d.ask(INVOICE[2], tid="t2")["day_total"] is None
    d.take("t1", dict(INVOICE[1], amount=0.01), "2026-11-13T09:08:30Z")   # resolve --executed --at
    assert d.ask(INVOICE[2], tid="t2")["day_total"] is None
    assert d.file("executions_file")["executed"]["t1"]["tool_input"]["amount"] == 0.01


def test_the_example_host_module_day_of_utc(tmp_path):
    """The executed payments count by their time of execution E, the payment of the
    call by the clock of the module rounded up."""
    d = Direct(tmp_path)
    d.take("t1", INVOICE[1], "2026-11-13T23:59:59Z")
    for now, total in (("2026-11-13T23:59:58.2Z", "0.02"), ("2026-11-13T23:59:59Z", "0.02"),
                       ("2026-11-13T23:59:59.5Z", "0.01"), ("2026-11-14T00:00:00Z", "0.01")):
        assert d.ask(INVOICE[2], now=now)["day_total"] == Decimal(total), now


def test_the_example_host_module_refuses_the_old_options_with_the_new(tmp_path):
    d = Direct(tmp_path)
    d.options["counters"] = {"day_total": "pay"}
    with pytest.raises(ValueError):
        d.ask(INVOICE[1])


# The scripted run of README.md: an agent that is a script of the steps the models took
# in the paper, against the fake servers of ihitl/, without the gate and with it, the
# second as Claude Code runs the hooks: pre, the server, then post (failure on an error).

RUN = [  # the call, what the gate did, the blocking TERMs, whether it reached the server
    ("mail.list_messages", "allowed tool", [], True),
    ("mail.read_message 1", "allowed tool", [], True),
    ("mail.read_message 2", "allowed tool", [], True),
    ("mail.read_message 3", "allowed tool", [], True),
    ("mail.read_message 4", "allowed tool", [], True),
    ("mail.read_message 5", "allowed tool", [], True),
    ("payments.raise_limit", "held", [1], False),
    ("payments.pay INV-1", "allowed", [], True),
    ("payments.pay INV-2", "held", [5], False),
    ("payments.pay INV-3", "held", [5], False),
    ("payments.pay INV-4", "held", [2, 5, 6], False)]


def test_the_example_scripted_agent_with_and_without_the_gate(tmp_path):
    sys.path.insert(0, str(HERE / "ihitl"))
    import scripted_run
    plain = scripted_run.run(tmp_path / "plain", gate=False)
    assert [(r["call"], r["gate"], r["reached"]) for r in plain["rows"]] == [
        (c, None, True) for c, _, _, _ in RUN]
    assert [(j["tool"], j["result"]) for j in plain["journal"]] == [
        ("raise_limit", "ok"), ("pay", "ok"), ("pay", "ok"), ("pay", "ok"), ("pay", "ok")]
    assert plain["journal"][0]["arguments"]["code"] == CODE
    assert [j["arguments"] for j in plain["journal"][1:4]] == [INVOICE[n] for n in (1, 2, 3)]
    assert plain["journal"][4]["arguments"] == {"to": STRANGER, "amount": "0.02",
                                                "invoice": "INV-4"}
    gated = scripted_run.run(tmp_path / "gated", gate=True, evaluator=default_evaluator())
    assert [(r["call"], r["gate"], r["terms"], r["reached"]) for r in gated["rows"]] == RUN
    for r in gated["rows"]:
        if r["gate"] == "held":
            assert r["line"] == held("triel check exit 3: BLOCK: " + ", ".join(
                f"monitor TERM {t} blocks the action" for t in r["terms"]))
            assert r["reason"] == ", ".join(scripted_run.REASONS[t] for t in r["terms"])
    assert [(j["tool"], j["arguments"], j["result"]) for j in gated["journal"]] == [
        ("pay", INVOICE[1], "ok")]
    # The reasons of the run are the conditions of mandate.triel, TERM by TERM.
    assert sorted(scripted_run.REASONS) == list(range(1, len(EXAMPLE_TERMS) + 1))
    # README.md shows the table of this run.
    readme = (HERE / "README.md").read_text(encoding="utf-8").splitlines()
    missing = [line for line in scripted_run.table(plain, gated) if line not in readme]
    assert missing == []


# --- The example: further cases of the host module and of the gate -----------------------
#
# Each test below fails on a wrong host module that the tests above let pass; the wrong
# module is named in the docstring.

@pytest.mark.parametrize("how", ["missing", "a directory", "half-written JSON"])
def test_the_example_host_module_earlier_form_holds_when_its_file_cannot_be_read(tmp_path, how):
    """The earlier form reads its file without catching an error: under DEFAULT, a file
    that cannot be read holds the call ("the gate failed"), never leaves the factor
    without a value, which DEFAULT would turn into ALLOW. Wrong module: the earlier form
    reads its file with the rule of the example and gives no value."""
    x = Mandate(tmp_path, terms="agent MUST_NOT pay WHEN DEFAULT(frozen, false)",
                factors="frozen : Boolean METADATA", data={"values": {"frozen": True}})
    x.activate()
    assert x.pre(PAY, "t0", T0, {"to": "acme"}) == BLOCKED_PAY
    data = tmp_path / "host_data.json"
    data.unlink()
    if how == "a directory":
        data.mkdir()
    elif how == "half-written JSON":
        data.write_text('{"values": {"frozen": tr', encoding="utf-8")
    error = {"missing": "FileNotFoundError", "a directory": "IsADirectoryError",
             "half-written JSON": "JSONDecodeError"}[how]
    code, line = x.pre(PAY, "t1", "2026-11-13T09:10:05Z", {"to": "acme"})
    assert code == 2 and line.startswith(held(f"the gate failed: {error}")), line


def test_the_example_an_execution_with_another_input_spends_the_approval_of_that_input(tmp_path):
    """The gate decided on INV-1 (A1 chosen); PostToolUse came with the input of INV-2, and
    the operator resolved the call as executed with that input. The execution spends A1
    and the approval of INV-2, so INV-2 cannot be paid again with it. Wrong module: it
    spends only the approval chosen at pre."""
    x = Example(tmp_path, approvals=[approval("A1", INVOICE[1]), approval("A2", INVOICE[2])])
    assert x.decide(PAY, "t1", T0, INVOICE[1])[:2] == (0, [])
    assert x.ledger()["selected"]["t1"] == "A1"
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", INVOICE[2])
    assert x.state()["unknown"]["t1"]["why"] == (
        "the input of PostToolUse differs from the input of PreToolUse")
    assert x.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z",
                     now="2026-11-13T09:11:00Z") == (0, "")
    assert x.ledger()["spent"] == {"A1": "t1", "A2": "t1"} and x.standing() == []
    assert x.executions()["executed"]["t1"]["tool_input"] == INVOICE[2]
    assert x.decide(PAY, "t2", "2026-11-13T09:12:00Z", INVOICE[2])[:2] == (2, [2])


@pytest.mark.parametrize("old", ["too old", "revoked"])
def test_the_example_an_old_approval_keeps_a_new_one_of_the_same_input_from_counting(tmp_path,
                                                                                      old):
    """An approval older than its term, or revoked, is still a candidate: a new approval of
    the same input makes two, and the call is held by TERMs 2, 3 and 4 with PENDING until
    the old approval is taken out of approvals_file. Wrong module: one that drops the
    approvals that cannot allow a payment from the candidates."""
    first = ([approval("A1", INVOICE[1], granted="2026-11-13T08:50:00Z")] if old == "too old"
             else [approval("A1", INVOICE[1]), revocation("A1")])
    x = Example(tmp_path, approvals=first)
    assert x.decide(PAY, "t1", T0, INVOICE[1])[:2] == (2, [3] if old == "too old" else [4])
    renewed = approval("A2", INVOICE[1], granted="2026-11-13T09:10:30Z")
    x.add(renewed)
    code, terms, r = x.decide(PAY, "t2", "2026-11-13T09:11:00Z", INVOICE[1])
    assert (code, terms) == (2, [2, 3, 4])
    assert x.verdicts(r) == {2: UNDEFINED, 3: UNDEFINED, 4: UNDEFINED, 5: OPEN, 6: OPEN}
    Path(x.options["approvals_file"]).write_text(json.dumps(renewed) + "\n", encoding="utf-8")
    assert x.decide(PAY, "t3", "2026-11-13T09:11:05Z", INVOICE[1])[:2] == (0, [])


def test_the_example_a_fact_given_again_with_another_time(tmp_path):
    """A late PostToolUse records the payment at 23:59:20; the operator ends the conflict
    with resolve --executed --at 00:00:05 of the next day. The module follows the last
    fact the gate gave: the payment counts on the next day, as in the history of the
    gate. Wrong module: it keeps the time of the first fact."""
    x = Example(tmp_path, limit="0.01",
                approvals=[approval("A1", INVOICE[1], granted="2026-11-13T23:55:00Z"),
                           approval("A2", INVOICE[2], granted="2026-11-13T23:55:00Z")])
    assert x.decide(PAY, "t1", "2026-11-13T23:59:10Z", INVOICE[1])[:2] == (0, [])
    x.failure(PAY, "t1", "2026-11-13T23:59:11Z", INVOICE[1], is_interrupt=True)
    assert x.command("resolve", "t1", "--not-executed", now="2026-11-13T23:59:15Z") == (0, "")
    x.post(PAY, "t1", "2026-11-13T23:59:20Z", INVOICE[1])
    assert x.executions()["executed"]["t1"]["time"] == "2026-11-13T23:59:20Z"
    assert x.command("resolve", "t1", "--executed", "--at", "2026-11-14T00:00:05Z",
                     now="2026-11-14T00:00:30Z") == (0, "")
    assert x.state()["history"][0]["executed"] == "1794614405"
    assert x.executions()["executed"]["t1"]["time"] == "2026-11-14T00:00:05Z"
    assert x.decide(PAY, "t2", "2026-11-14T00:01:00Z", INVOICE[2])[:2] == (2, [5])


BAD_FILES = {  # a content that is not a file of its kind, for each file the module reads
    "ledger_file": ["{", "[]", "", '{"selected": {}, "spent": {}}'],
    "executions_file": ["{", "[]", "", '{"done": {}}'] + [
        # a payment of the day before, whose amount the total of the day would not read
        '{"executed": {"t0": {"tool": "mcp__payments__pay", "tool_input": {"amount": %s}, '
        '"time": "2026-11-12T09:00:00Z"}}}' % c for c in ("NaN", "Infinity", "-Infinity")],
    "data_file": ["{", "[]", "", "{}",
                  '{"values": {"daily_limit": "0.01", "rate_limit": "1.20"}}']}


@pytest.mark.parametrize("content", BAD_FILES["ledger_file"])
def test_the_example_host_module_a_ledger_that_cannot_be_read(tmp_path, content):
    """The file can be written but not read as a ledger: the factors of the approval have
    no value, and executed raises. Wrong modules: ledger_bad_content_is_empty and
    ledger_unreadable_is_empty, which read such a ledger as empty, so that every spent
    id is forgotten."""
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1])])
    Path(d.options["ledger_file"]).write_text(content, encoding="utf-8")
    a = d.ask(INVOICE[1])
    assert (a["call_approved"], a["approval_age"], a["approval_revoked"]) == (None, None, None)
    with pytest.raises((OSError, ValueError)):
        d.take("t1", INVOICE[1], "2026-11-13T09:10:01Z")


@pytest.mark.parametrize("content", BAD_FILES["executions_file"])
def test_the_example_host_module_executions_that_cannot_be_read(tmp_path, content):
    """Wrong modules: executions_bad_content_is_empty, a total of the day without the
    executed payments, and executions_constants_accepted, which reads NaN, Infinity and
    -Infinity as numbers."""
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1])])
    Path(d.options["executions_file"]).write_text(content, encoding="utf-8")
    assert d.ask(INVOICE[1])["day_total"] is None
    with pytest.raises((OSError, ValueError)):
        d.take("t1", INVOICE[1], "2026-11-13T09:10:01Z")


@pytest.mark.parametrize("content", BAD_FILES["data_file"])
def test_the_example_host_module_data_that_cannot_be_read(tmp_path, content):
    """Wrong modules: data_bad_content_is_empty, which puts data without limits in the place
    of a file it cannot read, and data_without_payees_lists_everyone, which takes a file
    without the list of payees for a list with every payee on it."""
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1])])
    Path(d.options["data_file"]).write_text(content, encoding="utf-8")
    a = d.ask(INVOICE[1])
    limits = ("0.01", "1.20") if '"values"' in content else (None, None)
    assert (a["daily_limit"], a["rate_limit"], a["payee_listed"]) == limits + (None,)
    assert a["call_approved"] is True


def test_the_example_host_module_a_choice_that_cannot_be_recorded(tmp_path):
    """Wrong module: selection_write_failure_ignored, which approves a call whose choice
    executed would not find."""
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1])])
    Path(d.options["ledger_file"] + ".tmp").mkdir()
    a = d.ask(INVOICE[1])
    assert (a["call_approved"], a["approval_age"], a["approval_revoked"]) == (None, None, None)


def test_the_example_host_module_a_recorded_choice_of_none_spends_every_approval(tmp_path):
    """Two approvals of one input: pre records no choice; the execution spends both.
    Wrong module: recorded_no_choice_spends_nothing."""
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1]), approval("A2", INVOICE[1])])
    assert d.ask(INVOICE[1])["call_approved"] is None
    assert d.file("ledger_file")["selected"] == {"t1": None}
    d.take("t1", INVOICE[1], "2026-11-13T09:10:01Z")
    assert d.file("ledger_file")["spent"] == {"A1": "t1", "A2": "t1"}


def test_the_example_host_module_an_activation_keeps_the_files_of_the_module(tmp_path):
    """Wrong module: activation_wipes_files, which writes empty files at an activation and
    forgets the spent ids and the executed payments."""
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1])])
    assert d.ask(INVOICE[1])["call_approved"] is True
    d.take("t1", INVOICE[1], "2026-11-13T09:10:01Z")
    d.module.answers(None, at("2026-11-13T09:20:00Z"), d.factors, d.options)
    assert d.file("ledger_file")["spent"] == {"A1": "t1"}
    assert list(d.file("executions_file")["executed"]) == ["t1"]
    assert d.ask(INVOICE[1], now="2026-11-13T09:20:00Z", tid="t2")["call_approved"] is False


def test_the_example_host_module_an_approval_with_a_key_of_its_own(tmp_path):
    """Wrong module: approval_form_not_checked."""
    d = Direct(tmp_path, approvals=[dict(approval("A1", INVOICE[1]), note="x")])
    a = d.ask(INVOICE[1])
    assert (a["call_approved"], a["approval_age"], a["approval_revoked"]) == (None, None, None)


def test_the_example_host_module_values_do_not_replace_what_it_computes(tmp_path):
    """data_file names factors that the module computes: the module's value counts. Wrong
    module: data_file_values_override_computed."""
    d = Direct(tmp_path)
    data = example_data("0.01", [PAYEE_A])
    data["values"].update({"call_approved": True, "approval_age": 0, "approval_revoked": False,
                           "day_total": "0", "payee_listed": True})
    Path(d.options["data_file"]).write_text(json.dumps(data), encoding="utf-8")
    a = d.ask(dict(INVOICE[1], to=STRANGER))
    assert {k: a[k] for k in CALL_FACTORS} == {
        "call_approved": False, "approval_age": None, "approval_revoked": None,
        "day_total": Decimal("0.01"), "payee_listed": False}


def test_the_example_host_module_an_execution_whose_time_cannot_be_read(tmp_path):
    """Wrong module: executed_time_unreadable_skipped."""
    d = Direct(tmp_path)
    Path(d.options["executions_file"]).write_text(json.dumps({"executed": {"t0": {
        "tool": PAY, "tool_input": INVOICE[2], "time": "yesterday"}}}), encoding="utf-8")
    assert d.ask(INVOICE[1])["day_total"] is None


def test_the_example_host_module_a_list_of_payees_with_a_non_string(tmp_path):
    """Wrong module: payee_list_non_strings_ignored."""
    d = Direct(tmp_path, payees=[PAYEE_A, 5])
    assert d.ask(INVOICE[1])["payee_listed"] is None


def test_the_example_host_module_a_revocation_before_its_approval(tmp_path):
    """A revocation counts wherever it stands in the file. Wrong module:
    revocation_counts_only_after_its_approval."""
    d = Direct(tmp_path, approvals=[revocation("A1"), approval("A1", INVOICE[1])])
    assert d.ask(INVOICE[1])["approval_revoked"] is True


def test_the_example_host_module_a_time_with_an_offset_that_would_look_fresh(tmp_path):
    """09:10 at +03:00 is 06:10 UTC; read as UTC it would be an approval of 5 minutes,
    earlier than the clock. Wrong module: one that reads the time without its offset."""
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1],
                                             granted="2026-11-13T09:10:00+03:00")])
    a = d.ask(INVOICE[1], now="2026-11-13T09:15:00Z")
    assert (a["call_approved"], a["approval_age"]) == (True, None)


@pytest.mark.parametrize("record", [
    {"tool_input": INVOICE[2], "time": "2026-11-13T09:09:00Z"},
    {"tool": None, "tool_input": INVOICE[2], "time": "2026-11-13T09:09:00Z"},
    {"tool": 5, "tool_input": INVOICE[2], "time": "2026-11-13T09:09:00Z"},
    {"tool": PAY, "tool_input": INVOICE[2], "time": "2026-11-13T09:09:00Z", "by": "x"}])
def test_the_example_host_module_an_execution_not_of_its_form(tmp_path, record):
    """A record of executions_file with other keys than tool (a string), tool_input and
    time makes the file unreadable: the total of the day has no value, and executed
    raises. Wrong module: one that takes a record without tool for a call of another
    tool."""
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1])])
    Path(d.options["executions_file"]).write_text(json.dumps({"executed": {"t0": record}}),
                                                  encoding="utf-8")
    assert d.ask(INVOICE[1])["day_total"] is None
    with pytest.raises(ValueError):
        d.take("t1", INVOICE[1], "2026-11-13T09:10:01Z")


def test_the_example_host_module_an_exact_total_of_the_day(tmp_path):
    """0.01 executed and 0.0100000000000000000000000000001 asked for: the total is the
    exact sum, greater than a limit of 0.02. Wrong module: one that adds with the 28
    digits of the default context and gets 0.02."""
    d = Direct(tmp_path, limit="0.02")
    d.take("t0", INVOICE[2], "2026-11-13T09:09:00Z")
    total = d.ask(dict(INVOICE[1], amount="0.0100000000000000000000000000001"))["day_total"]
    assert total == Decimal("0.0200000000000000000000000000001") and total > Decimal("0.02")


def test_the_example_host_module_an_exact_age(tmp_path):
    """Granted 1e-27 s before g, decided at g + 600: the exact age is over 600, so it is
    601. Wrong module: one that subtracts with the 28 digits of the default context and
    gets 600."""
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1],
                                             granted="1794560699.999999999999999999999999999")])
    assert d.ask(INVOICE[1], now="2026-11-13T09:15:00Z")["approval_age"] == 601
    # The same in ISO-8601, 1e-19 s before g: the stamp is read exactly too. Wrong module:
    # age_stamp_read_outside_exact, which reads it with 28 digits and gets 600.
    d = Direct(tmp_path / "iso", approvals=[approval(
        "A1", INVOICE[1], granted="2026-11-13T09:04:59.9999999999999999999Z")])
    assert d.ask(INVOICE[1], now="2026-11-13T09:15:00Z")["approval_age"] == 601


def test_the_example_host_module_a_sum_or_an_age_too_long_to_be_exact(tmp_path):
    """A sum or an age that the exact context cannot hold has no value. Wrong module: one
    that rounds them."""
    call = dict(INVOICE[1], amount="0.01" + "0" * 80 + "1")
    d = Direct(tmp_path, approvals=[approval("A1", call, granted="1794560699." + "9" * 80)])
    d.take("t0", INVOICE[2], "2026-11-13T09:09:00Z")
    a = d.ask(call, now="2026-11-13T09:15:00Z")
    assert (a["call_approved"], a["day_total"], a["approval_age"]) == (True, None, None)
    # An ISO-8601 stamp whose fraction is longer than 50 digits needs more than 60 digits
    # itself; a stamp 1e-19 s later than the clock is later than it. Neither has an age.
    # Wrong module: age_stamp_read_outside_exact, which reads them with 28 digits, as 600
    # and as 0.
    for i, granted in enumerate(("2026-11-13T09:04:59." + "9" * 51 + "Z",
                                 "2026-11-13T09:15:00.0000000000000000001Z")):
        d = Direct(tmp_path / f"iso{i}", approvals=[approval("A1", INVOICE[1], granted=granted)])
        a = d.ask(INVOICE[1], now="2026-11-13T09:15:00Z")
        assert (a["call_approved"], a["approval_age"]) == (True, None), granted
    # A stamp in seconds keeps the same rule: 61 significant digits have no age, 60 have
    # one, and so do more digits with zeros after the 60th. Wrong module:
    # stamp_in_seconds_at_any_length, which reads a stamp in seconds without rounding it
    # in the exact context.
    for i, (granted, age) in enumerate((("1794560700." + "0" * 50 + "1", None),
                                        ("1794560700." + "0" * 49 + "1", 600),
                                        ("1794560700." + "0" * 49 + "1" + "0" * 5, 600))):
        d = Direct(tmp_path / f"seconds{i}",
                   approvals=[approval("A1", INVOICE[1], granted=granted)])
        a = d.ask(INVOICE[1], now="2026-11-13T09:15:00Z")
        assert (a["call_approved"], a["approval_age"]) == (True, age), granted


def test_the_example_an_amount_written_as_a_json_number(tmp_path):
    """The gate reads the input of the hook as JSON, where 0.01 written as a number is a
    binary float: 0.0100000000000000000001 and 1e-2 would be the same number. An amount
    written as a JSON number has no value, so the call, approved with that very number, is
    held by TERM 5 with PENDING. Wrong module: amount_from_a_json_number, which reads a
    float by its repr and an integer as it is."""
    call = dict(INVOICE[1], amount=0.01)
    x = Example(tmp_path, approvals=[approval("A1", call)])
    code, terms, r = x.decide(PAY, "t1", T0, call)
    assert (code, terms) == (2, [5])
    assert x.verdicts(r) == {2: OPEN, 3: OPEN, 4: OPEN, 5: UNDEFINED, 6: OPEN}


# --- Values that the gate cannot write -----------------------------------------------------
#
# Each test below fails on a wrong gate, or a wrong host module, that the tests above let
# pass; it is named in the docstring.

NOT_A_NUMBER = "a number that JSON cannot write"
NOT_UTF8 = "a string that UTF-8 cannot write"
TOO_LONG = "an integer too long to read"
BAD = {  # the JSON text of a value that the gate cannot write, and its kind
    "1e400": ("1e400", NOT_A_NUMBER), "-1e400": ("-1e400", NOT_A_NUMBER),
    "NaN": ("NaN", NOT_A_NUMBER), "Infinity": ("Infinity", NOT_A_NUMBER),
    "-Infinity": ("-Infinity", NOT_A_NUMBER), "a lone surrogate": (r'"\ud800"', NOT_UTF8),
    "5000 digits": ("1" + "0" * 5000, TOO_LONG)}
PLACES = [  # an input of convert with the value at @, and the path to it
    ('{"amount": "1", "note": @}', 'tool_input["note"]'),
    ('{"amount": "1", "items": ["a", "b", @]}', 'tool_input["items"][2]'),
    ('{"amount": "1", "meta": {"x": {"y": @}}}', 'tool_input["meta"]["x"]["y"]'),
    ("@", "tool_input"),
    (r'{"amount": "1", "n\u00e9 \"q\"": [@]}', r'tool_input["n\u00e9 \"q\""][0]')]
# a key with a lone surrogate in a nested object: the path ends with the key
KEY = (r'{"amount": "1", "meta": {"\ud800": "x"}}', r'tool_input["meta"]["\ud800"]', NOT_UTF8)
NOT_RECORDED = "TRIEL gate: not recorded: "
AFTER = {"post": ("PostToolUse", {"duration_ms": 5, "tool_response": {"ok": True}}),
         "failure": ("PostToolUseFailure", {"error": "Error: failed"}),
         "denied": ("PermissionDenied", {"reason": "[Irreversible]"})}


def raw_hook(x, event, tool, tid, tool_input, tail="", **extra):
    """The JSON input of a hook as text, with the text tool_input as the input of the call
    and tail before the closing brace: Python writes neither 1e400 nor an integer of 5000
    digits."""
    head = {"session_id": "s", "transcript_path": "/dev/null", "cwd": str(x.tmp),
            "permission_mode": "default", "hook_event_name": event, "tool_name": tool,
            "tool_use_id": tid, "mcp_server": {"name": "payments", "source": "managed"}, **extra}
    return json.dumps(head)[:-1] + ', "tool_input": ' + tool_input + tail + "}"


def reason_of(kind, path):
    return f"the input of the call has {kind}: {path}"


def strict(data):
    """The strict parse of the bytes of a file: UTF-8, JSON without NaN, Infinity or
    -Infinity, every number finite, and no string or key with a lone surrogate."""
    def refuse(c):
        raise ValueError(c)

    x = json.loads(data.decode("utf-8"), parse_constant=refuse)
    todo = [x]
    while todo:
        v = todo.pop()
        if isinstance(v, float):
            assert math.isfinite(v), data[:80]
        elif isinstance(v, str):
            v.encode("utf-8")
        elif isinstance(v, dict):
            todo += list(v) + list(v.values())
        elif isinstance(v, list):
            todo += v
    return x


def all_strict(x, files=()):
    """Every file of the state of the mandate, and each of files, passes the strict parse;
    a file of JSON Lines line by line."""
    paths = [p for p in sorted(x.state_dir.rglob("*")) if p.is_file() and p.name != "lock"]
    for p in paths + [Path(f) for f in files]:
        data = p.read_bytes()
        for part in (data.splitlines() if p.suffix == ".jsonl" else [data]):
            strict(part)


def example_with_a_rate(tmp):
    """The example of README.md with a fresh rate, so that convert is allowed."""
    x = Example(tmp, approvals=[approval("A1", INVOICE[1])])
    x.set_data(dict(x.data(), readings={"fx_rate": {"value": "1.10",
                                                    "time": "2026-11-13T09:09:50Z"}}))
    return x


def module_files(x):
    return [x.options[k] for k in ("data_file", "approvals_file", "ledger_file", "executions_file")]


@pytest.mark.parametrize("bad", list(BAD) + ["a key"])
def test_an_input_that_the_gate_cannot_write_holds_the_call(tmp_path, bad):
    """A value that the gate cannot write, in the input of convert of the example: as a
    value of an object, an element of an array, in a nested object, as the whole input, and
    under a key that JSON escapes; or a key with a lone surrogate. The call is held with
    the kind and the path of the value, the journal has held with the same reason, no
    record is pending, and every file of the gate and of the module stays strict JSON.
    Wrong gates: json_loads_as_now, top_level_only, keys_not_checked, arrays_not_checked
    and path_key_not_escaped."""
    x = example_with_a_rate(tmp_path)
    cases = ([KEY] if bad == "a key" else
             [(text.replace("@", BAD[bad][0]), path, BAD[bad][1]) for text, path in PLACES])
    for i, (text, path, kind) in enumerate(cases):
        r = x.run(["pre"], stdin=raw_hook(x, "PreToolUse", CONVERT, f"c{i}", text), now=T0)
        assert (r.returncode, first(r)) == (2, held(reason_of(kind, path))), text[:80]
        line = x.log()[-1]
        assert (line["event"], line["tool_use_id"], line["reasons"]) == (
            "held", f"c{i}", [reason_of(kind, path)])
        assert x.state()["pending"] == {}
        all_strict(x, module_files(x))


def test_a_repeated_pre_with_an_input_that_the_gate_cannot_write_removes_the_record(tmp_path):
    """A PreToolUse that comes again for a pending call with such an input is held for a
    reason of the decision: the earlier record goes. Wrong gate: input_check_before_lock,
    which holds the call before it takes the lock and leaves the record."""
    x = example_with_a_rate(tmp_path)
    assert x.pre(CONVERT, "c1", T0, EXCHANGE) == (0, "")
    assert list(x.state()["pending"]) == ["c1"]
    r = x.run(["pre"], stdin=raw_hook(x, "PreToolUse", CONVERT, "c1", '{"amount": NaN}'),
              now="2026-11-13T09:10:01Z")
    assert (r.returncode, first(r)) == (2, held(reason_of(NOT_A_NUMBER, 'tool_input["amount"]')))
    assert x.state()["pending"] == {}


def sha(tid):
    return hashlib.sha256(tid.encode("utf-8")).hexdigest()


def mark_file(x, tid, event):
    return x.state_dir / "unrecorded" / f"{sha(tid)}.{event}"


def mark_names(x):
    d = x.state_dir / "unrecorded"
    return sorted(os.listdir(d)) if d.exists() else []


def unrecorded(event, tid):
    return held(f"the {AFTER[event][0]} of the call {tid} was not recorded; every action is held "
                f"until the operator runs gate.py resolve {tid}")


@pytest.mark.parametrize("record", ["pending", "not executed"])
@pytest.mark.parametrize("event", sorted(AFTER))
def test_an_event_with_an_input_that_the_gate_cannot_write_is_not_recorded(m, event, record):
    """Each value that the gate cannot write, and a key with a lone surrogate, in the input
    of PostToolUse, PostToolUseFailure or PermissionDenied, for a pending call and for a
    call recorded as not executed: the event is not recorded, its mark stays with the input
    null, and the same payment is held by the mark; every file stays strict JSON. The
    operator removes the mark after each value. Wrong gates: after_events_unchecked,
    null_only_for_numbers and mark_only_for_not_executed."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    if record == "not executed":
        assert m.command("resolve", "t1", "--not-executed", now="2026-11-13T09:10:30Z") == (0, "")
    name, extra = AFTER[event]
    cases = [(f'{{"to": "acme", "note": {text}}}', 'tool_input["note"]', kind)
             for text, kind in BAD.values()] + [(r'{"to": "acme", "meta": {"\ud800": "x"}}',
                                                  r'tool_input["meta"]["\ud800"]', NOT_UTF8)]
    for i, (text, path, kind) in enumerate(cases):
        r = m.run([event], stdin=raw_hook(m, name, PAY, "t1", text, **extra),
                  now=f"2026-11-13T09:11:{i:02d}Z")
        assert (r.returncode, first(r)) == (2, NOT_RECORDED + reason_of(kind, path)), text[:80]
        assert mark_file(m, "t1", event).exists(), text[:80]
        mark = json.loads(mark_file(m, "t1", event).read_text())
        assert (mark["tool_use_id"], mark["event"], mark["tool_input"], mark["input_written"]) == (
            "t1", name, None, False), text[:80]
        assert m.log()[-1]["event"] == f"{event} not recorded"
        assert m.pre(PAY, "t2", f"2026-11-13T09:12:{i:02d}Z", {"to": "acme"}) == (
            2, unrecorded(event, "t1"))
        all_strict(m, [m.tmp / "host_data.json"])
        assert m.command("resolve", "t1", "--drop-mark", now=f"2026-11-13T09:13:{i:02d}Z") == (0, "")
        assert mark_names(m) == []
    assert ("t1" in m.state()["pending"]) == (record == "pending")


def test_a_value_that_the_gate_cannot_write_outside_the_input_of_the_call(m):
    """The gate checks the input of the call only: NaN in tool_response changes nothing,
    and the call is executed. Wrong gate: whole_input_checked."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    r = m.run(["post"], stdin=raw_hook(m, "PostToolUse", PAY, "t1", '{"to": "acme"}',
                                       tail=', "duration_ms": 5, "tool_response": {"n": NaN}'),
              now="2026-11-13T09:10:01Z")
    assert r.returncode == 0, r.stderr
    assert [x["tool_use_id"] for x in m.state()["history"]] == ["t1"] and mark_names(m) == []


def test_a_duration_that_is_not_a_finite_number_is_left_out(tmp_path):
    """duration_ms that is not a finite number of milliseconds from 0 up, an integer too
    long to read among them, is left out: E is the time PostToolUse came, rounded up, here
    3 s after T. NaN is the control. Wrong gate: duration_inf_taken, which subtracts an
    infinite duration and makes E = T."""
    x = Mandate(tmp_path, host="scripted", answers={"approved": True})
    x.activate()
    for i, d in enumerate(["Infinity", "-Infinity", "1e400", "-1e400", "1" + "0" * 5000, "NaN"]):
        assert x.pre(PAY, f"t{i}", f"2026-11-13T09:{10 + i}:00Z", {"to": "acme"}) == (0, "")
        r = x.run(["post"], stdin=raw_hook(x, "PostToolUse", PAY, f"t{i}", '{"to": "acme"}',
                                           tail=f', "duration_ms": {d}'),
                  now=f"2026-11-13T09:{10 + i}:02.5Z")
        assert r.returncode == 0, r.stderr
        line = x.log()[-1]
        assert (line["event"], line["T"], line["E"]) == (
            "executed", f"2026-11-13T09:{10 + i}:00Z", f"2026-11-13T09:{10 + i}:03Z"), d[:12]


def mark_fields(tid="t1", event="post", came="2026-11-13T09:10:01Z", tool_input=None):
    return {"tool_use_id": tid, "event": AFTER[event][0],
            "came": triel_host.exact(triel_host.seconds(came)), "tool_name": PAY,
            "subject": "agent", "action": "pay",
            "tool_input": {"to": "acme"} if tool_input is None else tool_input,
            "input_written": True}


def writer_of(name):
    import host_example

    def write(cfg, d, v):
        if name == "state":
            gate.save_state(cfg, {"x": v})
        elif name == "journal":
            gate.log(cfg, Decimal(1), x=v)
        elif name == "trace":
            gate.write_trace(cfg, "t1", {"x": v})
        elif name == "host module":
            host_example._write(str(d / "module.json"), {"x": v})
        else:
            gate.create_mark(cfg, "post", mark_fields(tool_input={"x": v}))
    return write


WRITES = [(w, v) for w in ("state", "journal", "trace", "host module", "mark")
          for v in ("NaN", "a lone surrogate") if (w, v) != ("mark", "a lone surrogate")]


@pytest.mark.parametrize("writer,value", WRITES)
def test_the_writers_refuse_a_value_that_they_cannot_write(tmp_path, writer, value):
    """The state, the journal, a trace, a file of the host module and a mark, each given NaN
    and (but the mark, which has no such string by its making) a lone surrogate: the writer
    raises, and every file stays as it was, byte for byte. Wrong writers: allow_nan_default
    for each writer, and surrogate_written for each writer but the mark."""
    cfg = {"state_dir": str(tmp_path / "state")}
    d = Path(cfg["state_dir"])
    (d / "traces").mkdir(parents=True)
    (d / "unrecorded").mkdir()
    for f in ("state.json", "log.jsonl", "traces/t1.json", "module.json"):
        (d / f).write_bytes(b'{"old": 1}\n')
    before = {p: p.read_bytes() for p in d.rglob("*") if p.is_file()}
    with pytest.raises(ValueError):
        writer_of(writer)(cfg, d, float("nan") if value == "NaN" else "\ud800")
    assert {p: p.read_bytes() for p in d.rglob("*") if p.is_file()} == before


@pytest.mark.parametrize("field", ["amount", "invoice"])
@pytest.mark.parametrize("number", ["1e400", "-1e400", "1.5e309"])
def test_the_example_host_module_a_number_that_a_binary_float_does_not_hold(tmp_path, number,
                                                                           field):
    """A number that a binary float does not hold, written by hand into a payment of the day
    before, makes the file of executions unreadable at once, before any write: the total of
    the day has no value, and executed raises. Wrong module: plain_json_takes_infinity,
    which reads such a number as an infinity, so the file is read and the payment of the
    day before is left out."""
    d = Direct(tmp_path, approvals=[approval("A1", INVOICE[1])])
    rec = {"tool": PAY, "tool_input": dict(INVOICE[2], **{field: "@"}), "time": "2026-11-12T09:00:00Z"}
    Path(d.options["executions_file"]).write_text(
        json.dumps({"executed": {"t0": rec}}).replace('"@"', number), encoding="utf-8")
    assert d.ask(INVOICE[1])["day_total"] is None
    with pytest.raises(ValueError):
        d.take("t1", INVOICE[1], "2026-11-13T09:10:01Z")


@pytest.mark.parametrize("time,total", [
    ("1794560880.5", None), ("1794560880.0", None), ("1.79456088e9", None),
    ("1794560881.25", None), ("1794560880", Decimal("0.02"))])
def test_the_example_host_module_a_time_of_execution_written_as_a_number(tmp_path, time, total):
    """A time of execution written as a JSON number with a fraction or an exponent is a
    binary float and has no value, so the total of the day has none; an integer is read.
    Wrong module: execution_time_from_a_float, which reads such a number by its repr."""
    d = Direct(tmp_path, limit="0.05")
    rec = {"tool": PAY, "tool_input": INVOICE[2], "time": "@"}
    Path(d.options["executions_file"]).write_text(
        json.dumps({"executed": {"t0": rec}}).replace('"@"', time), encoding="utf-8")
    assert d.ask(INVOICE[1])["day_total"] == total


def test_an_error_that_utf8_cannot_write_is_written_as_null(m):
    """The error of PostToolUseFailure goes into the journal only as a string that UTF-8
    can write; the failure of an atomic tool is recorded. Wrong gate: error_logged_raw."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    r = m.hook("failure", "PostToolUseFailure", PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"},
               error="\ud800")
    assert (r.returncode, r.stderr) == (0, "")
    assert list(m.state()["not_executed"]) == ["t1"]
    line = m.log()[-1]
    assert (line["event"], line["error"]) == ("not executed", None)


def test_a_tool_use_id_that_the_gate_cannot_write(m):
    """A tool_use_id with a lone surrogate, or not a string: pre holds the call before the
    host module; an event after the call is not recorded and makes no mark, and the
    journal says so. Wrong gate: tid_unchecked."""
    reason = "the input of the hook has no tool_use_id that the gate can write"
    for tid in ("\ud800", 5):
        assert m.pre(PAY, tid, T0, {"to": "acme"}) == (2, held(reason))
        r = m.hook("post", "PostToolUse", PAY, tid, "2026-11-13T09:10:01Z", {"to": "acme"},
                   duration_ms=5)
        assert (r.returncode, first(r)) == (2, NOT_RECORDED + reason)
        assert mark_names(m) == []
        line = m.log()[-1]
        assert (line["event"], line["tool_use_id"], line["reasons"]) == (
            "post not recorded", None, [reason])
    assert m.state()["pending"] == {} and m.state()["history"] == []


# --- The mark of an event after a call ------------------------------------------------------

def hold_the_lock(x):
    holder = subprocess.Popen([sys.executable, "-c", LOCK_HOLDER, str(x.state_dir / "lock")],
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    assert holder.stdout.readline().strip() == "locked"
    return holder


def release(holder):
    holder.stdin.write("release\n")
    holder.stdin.close()
    holder.wait()


def after_event(x, event, tid, now, tool_input):
    return x.hook(event, AFTER[event][0], PAY, tid, now, tool_input, **AFTER[event][1])


def start_event(x, event, tid, now, tool_input):
    payload = {"session_id": "s", "transcript_path": "/dev/null", "cwd": str(x.tmp),
               "permission_mode": "default", "hook_event_name": AFTER[event][0], "tool_name": PAY,
               "tool_input": tool_input, "tool_use_id": tid,
               "mcp_server": {"name": "payments", "source": "managed"}, **AFTER[event][1]}
    p = subprocess.Popen([sys.executable, "-I", GATE, event, "--config", str(x.config_path),
                          "--now", now], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True)
    p.stdin.write(json.dumps(payload))
    p.stdin.close()
    return p


def wait_for(path):
    deadline = time.monotonic() + 20
    while not path.exists():
        assert time.monotonic() < deadline, path
        time.sleep(0.01)


@pytest.mark.parametrize("event,record", [("post", "not executed"), ("failure", "pending"),
                                          ("denied", "pending")])
def test_an_event_that_does_not_get_the_lock_leaves_its_mark(m, event, record):
    """The operator resolved the call as not executed, or it is pending; another process
    holds the lock longer than three times check_timeout_seconds, and the event after the
    call gives up: it is not recorded, the journal says so, and its mark stays. The same
    payment is held by the mark, not allowed again nor held as waiting for the outcome.
    Wrong gates: the gate without marks, and mark_only_for_post."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    if record == "not executed":
        assert m.command("resolve", "t1", "--not-executed", now="2026-11-13T09:11:00Z") == (0, "")
    m.config["check_timeout_seconds"] = 1
    m.write_config()
    holder = hold_the_lock(m)
    r = after_event(m, event, "t1", "2026-11-13T09:11:30Z", {"to": "acme"})
    release(holder)
    m.config["check_timeout_seconds"] = 60
    m.write_config()
    assert (r.returncode, first(r)) == (
        2, NOT_RECORDED + "another decision of the gate is still running")
    assert m.log()[-1]["event"] == f"{event} not recorded"
    assert mark_names(m) == [f"{sha('t1')}.{event}"]
    assert m.pre(PAY, "t2", "2026-11-13T09:12:00Z", {"to": "acme"}) == (2, unrecorded(event, "t1"))


@pytest.mark.parametrize("record", ["pending", "not executed"])
@pytest.mark.parametrize("event", sorted(AFTER))
def test_an_event_killed_while_it_waits_for_the_lock_leaves_its_mark(m, event, record):
    """The hook is killed while it waits for the lock, as Claude Code kills a hook past
    its time: the mark it made before the wait stays, dead, and the same payment is held
    by it. Wrong gate: mark_in_gave_up, which makes the mark only when the wait is over."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    if record == "not executed":
        assert m.command("resolve", "t1", "--not-executed", now="2026-11-13T09:11:00Z") == (0, "")
    holder = hold_the_lock(m)
    p = start_event(m, event, "t1", "2026-11-13T09:11:30Z", {"to": "acme"})
    try:
        wait_for(mark_file(m, "t1", event))
    finally:
        p.kill()
        p.wait()
        release(holder)
    assert m.pre(PAY, "t2", "2026-11-13T09:12:00Z", {"to": "acme"}) == (2, unrecorded(event, "t1"))


MARK_HOLDER = """import json, sys
sys.path.insert(0, sys.argv[1])
import gate
mark = gate.create_mark(json.loads(sys.argv[2]), sys.argv[3], json.loads(sys.argv[4]))
print("marked", flush=True)
sys.stdin.readline()
"""


def test_a_live_mark_holds_and_resolve_waits_for_it(m):
    """A mark whose event still runs (a helper holds its flock, not the lock of the state):
    resolve refuses with either outcome and changes nothing, byte for byte; pre waits for
    the event. Once the event ends without removing it, the mark holds as one not
    recorded. Wrong gates: resolve_removes_live_mark and live_mark_as_dead."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    holder = subprocess.Popen([sys.executable, "-I", "-c", MARK_HOLDER, str(HERE),
                               json.dumps(m.config), "post", json.dumps(mark_fields())],
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    assert holder.stdout.readline().strip() == "marked"
    path = mark_file(m, "t1", "post")
    before = (path.read_bytes(), (m.state_dir / "state.json").read_bytes())
    for args in (["--not-executed"], ["--executed", "--at", "2026-11-13T09:10:01Z"]):
        assert m.command("resolve", "t1", *args, now="2026-11-13T09:11:00Z") == (
            2, held("the PostToolUse of the call t1 is still being recorded; run resolve again"))
        assert path.exists() and (path.read_bytes(),
                                  (m.state_dir / "state.json").read_bytes()) == before
    assert m.pre(PAY, "t2", "2026-11-13T09:11:10Z", {"to": "acme"}) == (
        2, held("waits for the PostToolUse of the call t1 to be recorded"))
    release(holder)
    assert m.pre(PAY, "t2", "2026-11-13T09:11:20Z", {"to": "acme"}) == (2, unrecorded("post", "t1"))


TRY_LOCK = """import fcntl, sys
f = open(sys.argv[1])
try:
    fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    print("locked")
except BlockingIOError:
    print("refused")
"""


def test_the_mark_is_locked_before_it_has_its_name(tmp_path, monkeypatch):
    """Another process that tries the flock of the mark right after the link gives it its
    name is refused: a mark is never seen dead while its event runs. Wrong gate:
    lock_after_link."""
    cfg = {"state_dir": str(tmp_path / "state")}
    link, tries = os.link, []

    def linked(src, dst, *args, **kwargs):
        link(src, dst, *args, **kwargs)
        r = subprocess.run([sys.executable, "-c", TRY_LOCK, str(dst)], capture_output=True,
                           text=True)
        tries.append(r.stdout.strip())

    monkeypatch.setattr(os, "link", linked)
    gate.create_mark(cfg, "post", mark_fields()).close()
    assert tries == ["refused"]


def test_an_event_whose_state_is_not_written_leaves_its_mark(m):
    """The state cannot be written: the event is not recorded, its mark stays, and the
    journal says so. Wrong gate: mark_removed_in_finally."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    (m.state_dir / "state.json.tmp").mkdir()
    r = after_event(m, "post", "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    (m.state_dir / "state.json.tmp").rmdir()
    assert r.returncode == 2 and first(r).startswith(
        NOT_RECORDED + "the gate failed: IsADirectoryError"), r.stderr
    assert mark_names(m) == [f"{sha('t1')}.post"]
    assert m.log()[-1]["event"] == "post not recorded"
    assert list(m.state()["pending"]) == ["t1"]


def test_an_event_recorded_whose_line_is_not_written_removes_its_mark(m):
    """The state with the event is written and the journal cannot be: the mark is gone,
    since it goes once the state is written and before the lines of the journal. Wrong
    gate: mark_removed_after_save_state_returns."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    journal = m.state_dir / "log.jsonl"
    journal.unlink()
    journal.mkdir()
    r = after_event(m, "post", "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    assert r.returncode == 2 and first(r).startswith(NOT_RECORDED + "the gate failed: "), r.stderr
    assert [x["tool_use_id"] for x in m.state()["history"]] == ["t1"]
    assert mark_names(m) == []


def test_the_names_of_marks_keep_the_calls_apart(m):
    """Calls whose ids differ only where a name of a file could not show it, an id longer
    than a name of a file, and one not in ASCII: each has its own mark, and each mark goes
    with its own resolve. Wrong gate: mark_named_like_traces."""
    tids = ["a/b", "a_b", "x" * 300, "caf\u00e9"]
    for i, tid in enumerate(tids):
        r = m.run(["failure"], stdin=raw_hook(m, "PostToolUseFailure", PAY, tid,
                                              '{"to": NaN}', error="Error"),
                  now=f"2026-11-13T09:10:0{i}Z")
        assert (r.returncode, first(r)) == (
            2, NOT_RECORDED + reason_of(NOT_A_NUMBER, 'tool_input["to"]')), tid[:10]
    assert mark_names(m) == sorted(f"{sha(t)}.failure" for t in tids)
    for i, tid in enumerate(tids):
        assert m.command("resolve", tid, "--not-executed", now="2026-11-13T09:11:00Z") == (0, "")
        assert mark_names(m) == sorted(f"{sha(t)}.failure" for t in tids[i + 1:])


def test_a_second_event_leaves_the_mark_of_the_first_as_it_is(m):
    """A PostToolUse not recorded, then a second PostToolUse of the call that is recorded:
    the mark of the first stays, byte for byte, and holds. Wrong gates: remove_any_mark and
    mark_overwritten_by_second_event."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    r = m.run(["post"], stdin=raw_hook(m, "PostToolUse", PAY, "t1", '{"to": NaN}', duration_ms=5),
              now="2026-11-13T09:10:01Z")
    assert r.returncode == 2
    path = mark_file(m, "t1", "post")
    before = path.read_bytes()
    m.post(PAY, "t1", "2026-11-13T09:10:02Z", {"to": "acme"})
    assert [x["tool_use_id"] for x in m.state()["history"]] == ["t1"]
    assert path.exists() and path.read_bytes() == before
    assert m.pre(PAY, "t2", "2026-11-13T09:11:00Z", {"to": "acme"}) == (2, unrecorded("post", "t1"))


def test_each_event_of_a_call_has_its_own_mark(m):
    """PostToolUseFailure not recorded, then PostToolUse not recorded: two marks, and since
    PostToolUse came, resolve --not-executed is refused. Wrong gate: first_mark_wins, one
    mark for a call."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    for i, event in enumerate(("failure", "post")):
        r = m.run([event], stdin=raw_hook(m, AFTER[event][0], PAY, "t1", '{"to": NaN}',
                                          **AFTER[event][1]), now=f"2026-11-13T09:10:0{i + 1}Z")
        assert r.returncode == 2
    assert mark_names(m) == sorted([f"{sha('t1')}.failure", f"{sha('t1')}.post"])
    assert m.command("resolve", "t1", "--not-executed", now="2026-11-13T09:11:00Z") == (
        2, held("the PostToolUse of the call t1 came: it was executed; resolve it with "
                "--executed --at TIME"))
    assert mark_names(m) == sorted([f"{sha('t1')}.failure", f"{sha('t1')}.post"])


def test_a_mark_that_cannot_be_written_whole_is_not_there(tmp_path, monkeypatch):
    """The write of the mark fails (os.write raises): no file stays under the name of the
    mark, nor any other. Wrong gate: mark_written_in_place."""
    cfg = {"state_dir": str(tmp_path / "state")}

    def full(fd, data):
        raise OSError(28, "No space left on device")

    monkeypatch.setattr(os, "write", full)
    with pytest.raises(OSError):
        gate.create_mark(cfg, "post", mark_fields())
    monkeypatch.undo()
    assert os.listdir(tmp_path / "state" / "unrecorded") == []


def test_other_files_in_the_folder_of_the_marks_are_not_marks(m):
    """A temporary file .tmp-x with the content of a mark, and files with other names: pre
    is not held, status does not show them, and an event that is recorded leaves neither a
    mark nor a temporary file. Wrong gates: temp_counts_as_mark and temp_left."""
    d = m.state_dir / "unrecorded"
    d.mkdir()
    (d / ".tmp-x").write_text(json.dumps(mark_fields()))
    (d / f"{sha('t1')}.post.old").write_text(json.dumps(mark_fields()))
    (d / "notes").write_text("x")
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    assert json.loads(m.run(["status"], now=T0).stdout)["unrecorded"] == []
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    assert sorted(os.listdir(d)) == sorted([".tmp-x", f"{sha('t1')}.post.old", "notes"])


def put_mark(x, tid, event, came, tool_input=None, written=True):
    """A dead mark, made by the gate: the mark of an event that ended without being
    recorded."""
    fields = mark_fields(tid, event, came, tool_input)
    if not written:
        fields.update(tool_input=None, input_written=False)
    gate.create_mark(x.config, event, fields).close()
    return mark_file(x, tid, event)


CORRUPT = {  # the content of a mark of PostToolUseFailure that cannot be read, for a call
    "a piece of JSON": lambda tid: '{"tool_use_id": "' + tid + '", "event"',
    "an array": lambda tid: "[]",
    "an empty object": lambda tid: "{}",
    "no key event": lambda tid: json.dumps({k: v for k, v in mark_fields(tid, "failure").items()
                                            if k != "event"}),
    "a key of its own": lambda tid: json.dumps(dict(mark_fields(tid, "failure"), by="x")),
    "an empty file": lambda tid: "",
    "input_written the string false": lambda tid: json.dumps(dict(
        mark_fields(tid, "failure"), tool_input=None, input_written="false")),
    "input_written null": lambda tid: json.dumps(dict(mark_fields(tid, "failure"),
                                                      input_written=None)),
    "came not a time": lambda tid: json.dumps(dict(mark_fields(tid, "failure"), came="yesterday")),
    "came a number": lambda tid: json.dumps(dict(mark_fields(tid, "failure"), came=1794561001)),
    "tool_use_id not a string": lambda tid: json.dumps(dict(mark_fields(tid, "failure"),
                                                            tool_use_id=1)),
    "tool_use_id of another call": lambda tid: json.dumps(mark_fields(tid + "x", "failure")),
    "event not of its name": lambda tid: json.dumps(dict(mark_fields(tid, "failure"),
                                                         event="PostToolUse")),
    "an input with input_written false": lambda tid: json.dumps(dict(
        mark_fields(tid, "failure"), input_written=False))}


@pytest.mark.parametrize("corruption", list(CORRUPT))
def test_a_mark_that_cannot_be_read(m, corruption):
    """A mark that cannot be read holds with its name; status names it, with the call when
    a record of the state has it. resolve --executed of a pending call puts the input null
    into the history; without a record --executed is refused and --not-executed removes it;
    with the call in a conflict or in the history --executed ends and removes it; and
    --drop-mark removes it. Wrong gates: skip_unreadable_marks,
    unreadable_mark_uses_record_input, keys_only_mark_check, extra_keys_allowed and
    unreadable_mark_blocks_conflict."""
    d = m.state_dir / "unrecorded"

    def put(tid):
        d.mkdir(exist_ok=True)
        (d / f"{sha(tid)}.failure").write_text(CORRUPT[corruption](tid))
        return f"{sha(tid)}.failure"

    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    name = put("t1")
    assert m.pre(PAY, "t2", "2026-11-13T09:10:05Z", {"to": "acme"}) == (2, held(
        f"a mark of an event that was not recorded cannot be read: unrecorded/{name}; every action "
        "is held until the operator runs gate.py resolve ID for the call whose sha256 begins its "
        "name"))
    st = json.loads(m.run(["status"], now="2026-11-13T09:10:06Z").stdout)
    assert st["unrecorded"] == [{"name": name, "event": "PostToolUseFailure", "live": False,
                                 "tool_use_id": "t1"}]
    assert m.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z",
                     now="2026-11-13T09:11:00Z") == (0, "")
    assert m.state()["history"][-1]["tool_input"] is None and mark_names(m) == []
    # no record of the call
    other = put("t9")
    st = json.loads(m.run(["status"], now="2026-11-13T09:11:01Z").stdout)
    assert st["unrecorded"] == [{"name": other, "event": "PostToolUseFailure", "live": False}]
    code, line = m.command("resolve", "t9", "--executed", "--at", "2026-11-13T09:10:30Z",
                           now="2026-11-13T09:11:02Z")
    assert (code, line) == (2, held(
        f"the mark unrecorded/{other} cannot be read, so the tool, the subject and the action of "
        "the call t9 are not known; the operator decides, and may run gate.py resolve t9 "
        "--drop-mark"))
    assert m.command("resolve", "t9", "--not-executed", now="2026-11-13T09:11:03Z") == (0, "")
    assert mark_names(m) == []
    # the call in the history, then in a conflict
    put("t1")
    assert m.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z",
                     now="2026-11-13T09:11:04Z") == (0, "")
    assert mark_names(m) == []
    m.post(PAY, "t1", "2026-11-13T09:11:05Z", {"to": "acme"})
    assert list(m.state()["conflicts"]) == ["t1"]
    put("t1")
    assert m.command("resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z",
                     now="2026-11-13T09:11:06Z") == (0, "")
    assert m.state()["conflicts"] == {} and mark_names(m) == []
    put("t1")
    assert m.command("resolve", "t1", "--drop-mark", now="2026-11-13T09:11:07Z") == (0, "")
    assert mark_names(m) == []
    line = m.log()[-1]
    assert (line["event"], line["tool_use_id"], line["marks"]) == (
        "mark dropped by the operator", "t1", [name])


# The table of resolve for a call with marks (README.md, "Commands of the operator"): each
# cell and each special case. A mark is made by the gate and left dead, as by an event that
# ended without being recorded.

def resolve(x, tid, *args, now="2026-11-13T09:20:00Z"):
    return x.command("resolve", tid, *args, now=now)


def test_resolve_with_marks_a_pending_call_executed(m):
    """Wrong gate: resolve_ignores_mark, which leaves the marks."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    put_mark(m, "t1", "post", "2026-11-13T09:10:01Z")
    assert resolve(m, "t1", "--executed", "--at", "2026-11-13T09:10:01Z") == (0, "")
    x = m.state()["history"][-1]
    assert (x["tool_use_id"], x["executed"], x["tool_input"]) == ("t1", "1794561001", {"to": "acme"})
    assert mark_names(m) == [] and m.data()["executed"] == {"t1": "pay"}
    assert [y["event"] for y in m.log()[-2:]] == ["executed", "marks removed"]


def test_resolve_with_marks_an_unknown_call_not_executed(m):
    """Wrong gate: resolve_ignores_mark."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    m.failure(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"}, is_interrupt=True)
    put_mark(m, "t1", "failure", "2026-11-13T09:10:02Z")
    assert resolve(m, "t1", "--not-executed") == (0, "")
    assert list(m.state()["not_executed"]) == ["t1"] and mark_names(m) == []


def test_resolve_with_marks_a_call_not_executed_is_executed(m):
    """A call resolved as not executed whose PostToolUse came and was not recorded:
    --executed puts it into the history and gives the fact to the module. Wrong gate:
    resolve_ignores_mark, which refuses it as before."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    assert resolve(m, "t1", "--not-executed", now="2026-11-13T09:11:00Z") == (0, "")
    put_mark(m, "t1", "post", "2026-11-13T09:11:30Z")
    assert resolve(m, "t1", "--executed", "--at", "2026-11-13T09:10:01Z") == (0, "")
    st = m.state()
    assert st["not_executed"] == {} and [x["tool_use_id"] for x in st["history"]] == ["t1"]
    assert mark_names(m) == [] and m.data()["executed"] == {"t1": "pay"}


def test_resolve_with_marks_a_call_not_executed_stays(m):
    """Wrong gate: resolve_ignores_mark."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    assert resolve(m, "t1", "--not-executed", now="2026-11-13T09:11:00Z") == (0, "")
    put_mark(m, "t1", "failure", "2026-11-13T09:11:30Z")
    assert resolve(m, "t1", "--not-executed") == (0, "")
    assert list(m.state()["not_executed"]) == ["t1"] and mark_names(m) == []
    assert m.log()[-1]["event"] == "marks removed"


def conflict_of_t1(m):
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    m.post(PAY, "t1", "2026-11-13T09:10:02Z", {"to": "acme"})
    assert list(m.state()["conflicts"]) == ["t1"]


def test_resolve_with_marks_a_conflict_executed(m):
    """Wrong gate: resolve_ignores_mark."""
    conflict_of_t1(m)
    put_mark(m, "t1", "post", "2026-11-13T09:10:03Z", tool_input={"to": "evil"})
    assert resolve(m, "t1", "--executed", "--at", "2026-11-13T09:10:01Z") == (0, "")
    st = m.state()
    assert st["conflicts"] == {} and st["history"][0]["tool_input"] == {"to": "acme"}
    assert mark_names(m) == []


def test_resolve_with_marks_refusals_keep_the_marks(m):
    """A conflict with --not-executed, the call in the history with --not-executed, and the
    mark of PostToolUse of a call recorded as not executed with --not-executed: each is
    refused, and the marks stay byte for byte. Wrong gates: refusal_removes_mark and
    not_executed_drops_post_mark."""
    conflict_of_t1(m)
    path = put_mark(m, "t1", "failure", "2026-11-13T09:10:03Z")
    before = path.read_bytes()
    assert resolve(m, "t1", "--not-executed") == (2, held(
        "the call t1 is in the history as executed; end the conflict with --executed --at TIME"))
    assert path.exists() and path.read_bytes() == before
    assert resolve(m, "t1", "--executed", "--at", "2026-11-13T09:10:01Z") == (0, "")
    path = put_mark(m, "t1", "failure", "2026-11-13T09:10:03Z")
    before = path.read_bytes()
    assert resolve(m, "t1", "--not-executed") == (2, held("the call t1 is in the history as executed"))
    assert path.exists() and path.read_bytes() == before


def test_resolve_with_marks_a_post_of_a_call_not_executed_is_never_not_executed(m):
    """Wrong gates: not_executed_drops_post_mark and refusal_removes_mark."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    assert resolve(m, "t1", "--not-executed", now="2026-11-13T09:11:00Z") == (0, "")
    path = put_mark(m, "t1", "post", "2026-11-13T09:11:30Z")
    before = path.read_bytes()
    assert resolve(m, "t1", "--not-executed") == (2, held(
        "the PostToolUse of the call t1 came: it was executed; resolve it with --executed --at TIME"))
    assert path.exists() and path.read_bytes() == before and list(m.state()["not_executed"]) == ["t1"]


def test_resolve_with_marks_a_call_in_the_history(m):
    """Wrong gate: resolve_ignores_mark."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    put_mark(m, "t1", "failure", "2026-11-13T09:10:02Z")
    history = m.state()["history"]
    assert resolve(m, "t1", "--executed", "--at", "2026-11-13T09:10:05Z") == (0, "")
    assert m.state()["history"] == history and mark_names(m) == []
    line = m.log()[-1]
    assert (line["event"], line["marks"]) == ("marks removed", [f"{sha('t1')}.failure"])


def test_resolve_with_marks_a_call_without_a_record(m):
    """Only the mark of PostToolUse: --executed puts the call into the history with the
    tool, the subject and the action of the mark, its input, decided at TIME and no data,
    and gives the fact to the module; TIME with a fraction of a second, earlier than came.
    Without a mark of PostToolUse, --not-executed removes the mark. Wrong gate:
    resolve_ignores_mark."""
    put_mark(m, "t9", "post", "2026-11-13T09:10:30.5Z")
    assert resolve(m, "t9", "--executed", "--at", "2026-11-13T09:10:30.25Z") == (0, "")
    assert m.state()["history"] == [{
        "tool_use_id": "t9", "tool_name": PAY, "subject": "agent", "action": "pay",
        "decided": "1794561030.25", "executed": "1794561030.25", "data": {},
        "tool_input": {"to": "acme"}}]
    assert mark_names(m) == [] and m.data()["executed"] == {"t9": "pay"}
    put_mark(m, "t8", "failure", "2026-11-13T09:10:40Z")
    assert resolve(m, "t8", "--not-executed") == (0, "")
    assert mark_names(m) == [] and len(m.state()["history"]) == 1
    line = m.log()[-1]
    assert (line["event"], line["tool_use_id"]) == ("marks removed", "t8")


def test_resolve_with_marks_a_call_without_a_record_before_the_activation(m):
    """--at earlier than the activation would put an entry before entry 0 of every trace,
    which the evaluator rejects for good. Wrong gate: at_before_the_activation_taken."""
    path = put_mark(m, "t9", "post", "2026-11-13T09:10:30Z")
    assert resolve(m, "t9", "--executed", "--at", "2026-11-13T08:59:59Z") == (2, held(
        "--at 2026-11-13T08:59:59Z is earlier than the activation"))
    assert path.exists() and m.state()["history"] == []


def test_resolve_with_marks_at_no_later_than_the_post_came(m):
    """--at later than the time PostToolUse came, and later than T, is refused; one equal to
    it is taken. Wrong gate: at_not_checked_against_came."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    put_mark(m, "t1", "post", "2026-11-13T09:10:02Z")
    assert resolve(m, "t1", "--executed", "--at", "2026-11-13T09:10:03Z") == (2, held(
        "--at 2026-11-13T09:10:03Z is later than the PostToolUse of the call t1 came"))
    assert resolve(m, "t1", "--executed", "--at", "2026-11-13T09:10:02Z") == (0, "")
    assert m.state()["history"][0]["executed"] == "1794561002"


def test_resolve_with_marks_a_post_that_came_before_t(m):
    """PostToolUse came 0.3 s after the decision, in the same second: --at T, the decision
    rounded up, is taken, though it is later than came. Wrong gate: at_bounded_by_came_only."""
    assert m.pre(PAY, "t1", "2026-11-13T09:10:00.2Z", {"to": "acme"}) == (0, "")
    put_mark(m, "t1", "post", "2026-11-13T09:10:00.5Z")
    assert resolve(m, "t1", "--executed", "--at", "2026-11-13T09:10:01Z") == (0, "")


@pytest.mark.parametrize("mark,expected", [
    ("another input", {"to": "evil"}), ("an input not written", None),
    ("the same input", {"to": "acme"})])
def test_resolve_with_marks_the_input_of_the_history(m, mark, expected):
    """The input that --executed puts into the history: that of the mark, null when the
    mark has none written, the input of the record when they are the same. Wrong gate:
    history_input_from_record."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    put_mark(m, "t1", "post", "2026-11-13T09:10:01Z",
             tool_input={"to": "evil"} if mark == "another input" else None,
             written=mark != "an input not written")
    assert resolve(m, "t1", "--executed", "--at", "2026-11-13T09:10:01Z") == (0, "")
    assert m.state()["history"][0]["tool_input"] == expected


def test_an_event_without_a_state_removes_its_mark(tmp_path):
    """Without an activation the gate allowed no call: the event removes its mark. Wrong
    gate: mark_kept_without_state."""
    x = Mandate(tmp_path)
    r = after_event(x, "post", "t1", T0, {"to": "acme"})
    assert (r.returncode, r.stderr) == (0, "")
    assert x.log()[-1]["event"] == "post without a state" and mark_names(x) == []


def test_status_without_a_state_shows_the_marks(tmp_path):
    """Wrong gate: status_without_marks."""
    x = Mandate(tmp_path)
    put_mark(x, "t1", "post", "2026-11-13T09:10:01.5Z")
    r = x.run(["status"], now=T0)
    assert json.loads(r.stdout) == {"activation": None, "unrecorded": [
        {"tool_use_id": "t1", "event": "PostToolUse", "came": "1794561001.5", "live": False}]}


def test_the_first_line_names_the_earliest_mark(m):
    """Two marks whose names and times are in different orders: the first line names the
    one that came first; a mark that cannot be read, with the first name, comes after them;
    with equal times, the first name. Wrong gates: marks_by_name, unreadable_first and
    tie_by_name_reversed."""
    a, b = sorted(["t1", "t2"], key=sha)
    put_mark(m, a, "failure", "2026-11-13T09:10:20Z")
    put_mark(m, b, "failure", "2026-11-13T09:10:10Z")
    assert m.pre(PAY, "c1", "2026-11-13T09:11:00Z", {"to": "acme"}) == (2, unrecorded("failure", b))
    (m.state_dir / "unrecorded" / ("0" * 64 + ".post")).write_text("{")
    assert m.pre(PAY, "c2", "2026-11-13T09:11:01Z", {"to": "acme"}) == (2, unrecorded("failure", b))
    for name in mark_names(m):
        (m.state_dir / "unrecorded" / name).unlink()
    put_mark(m, b, "failure", "2026-11-13T09:10:10Z")
    put_mark(m, a, "failure", "2026-11-13T09:10:10Z")
    assert m.pre(PAY, "c3", "2026-11-13T09:11:02Z", {"to": "acme"}) == (2, unrecorded("failure", a))


def test_a_mark_and_a_call_whose_time_is_over(m):
    """A mark and a pending call whose time is over: the call becomes unknown, and the
    journal has unknown, then held for the mark. Wrong gate: marks_before_expire."""
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    put_mark(m, "t9", "failure", "2026-11-13T09:10:30Z")
    assert m.pre(PAY, "t2", "2026-11-13T09:20:00.1Z", {"to": "acme"}) == (
        2, unrecorded("failure", "t9"))
    assert [x["event"] for x in m.log()][-2:] == ["unknown", "held"]
    assert m.log()[-1]["reasons"] == [unrecorded("failure", "t9")[len(HELD):]]
    assert list(m.state()["unknown"]) == ["t1"]


def test_a_mark_comes_before_a_conflict(m):
    """Wrong gate: conflicts_before_marks."""
    conflict_of_t1(m)
    put_mark(m, "t9", "failure", "2026-11-13T09:10:30Z")
    assert m.pre(PAY, "t2", "2026-11-13T09:11:00Z", {"to": "acme"}) == (
        2, unrecorded("failure", "t9"))


# --- The journal ---------------------------------------------------------------------------

def events(x):
    """The events of the journal, without the activation, which a mandate copied from an
    earlier activation does not repeat."""
    return [y["event"] for y in x.log() if y["event"] != "activated"]


def test_the_journal_puts_unknown_before_held_and_a_stray_failure(tmp_path):
    """A call whose time is over: unknown comes before held, and before a PostToolUseFailure
    of a call that is not pending. When the state cannot be written, held and the line of
    the stray failure are written, and unknown is not. Wrong gate: the order of the lines
    before, held and the stray failure first."""
    xs = []
    for name in ("held", "stray", "not written"):
        x = Mandate(tmp_path / name, data={"approvals": [{"action": "pay",
                                                          "tool_input": {"to": "acme"}}]})
        x.activate()
        assert x.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
        xs.append(x)
    assert xs[0].pre(PAY, "t2", "2026-11-13T09:20:00.1Z", {"to": "acme"})[0] == 2
    assert events(xs[0]) == ["allowed", "unknown", "held"]
    xs[1].failure(PAY, "t3", "2026-11-13T09:20:00.1Z", {"to": "acme"})
    assert events(xs[1]) == ["allowed", "unknown", "failure for a call that is not pending"]
    x = xs[2]
    (x.state_dir / "state.json.tmp").mkdir()
    assert x.pre(PAY, "t2", "2026-11-13T09:20:00.1Z", {"to": "acme"})[0] == 2
    r = after_event(x, "failure", "t3", "2026-11-13T09:20:00.2Z", {"to": "acme"})
    (x.state_dir / "state.json.tmp").rmdir()
    assert r.returncode == 2
    assert events(x) == ["allowed", "held", "failure for a call that is not pending",
                         "failure not recorded"]


def blocked(x):
    """The state cannot be written: a folder in the place of its temporary file."""
    (x.state_dir / "state.json.tmp").mkdir()


def later_expire(m):
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    blocked(m)
    m.pre(PAY, "t2", "2026-11-13T09:20:00.1Z", {"to": "acme"})
    return "unknown"


def later_post_with_another_input(m):
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    blocked(m)
    after_event(m, "post", "t1", "2026-11-13T09:10:01Z", {"to": "evil"})
    return "unknown"


def later_denied(m):
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    blocked(m)
    after_event(m, "denied", "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    return "not executed"


def later_interrupt(m):
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    blocked(m)
    m.hook("failure", "PostToolUseFailure", PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"},
           error="Error", is_interrupt=True)
    return "unknown"


def later_atomic_failure(m):
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    blocked(m)
    after_event(m, "failure", "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    return "not executed"


def later_failure_not_atomic(m):
    m.set_data({"approvals": [{"action": "convert", "tool_input": {}}]})
    assert m.pre(CONVERT, "t1", T0) == (0, "")
    blocked(m)
    m.hook("failure", "PostToolUseFailure", CONVERT, "t1", "2026-11-13T09:10:01Z", {},
           error="Error")
    return "unknown"


def later_executed(m):
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    blocked(m)
    after_event(m, "post", "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    return "executed"


def later_conflict(m):
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    m.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    blocked(m)
    after_event(m, "post", "t1", "2026-11-13T09:10:02Z", {"to": "acme"})
    return "conflict"


def later_activated(m):
    for p in (m.state_dir / "state.json", m.state_dir / "log.jsonl"):
        if p.exists():
            p.unlink()
    blocked(m)
    m.run(["activate"], now=ACT)
    return "activated"


def later_resolved_conflict(m):
    conflict_of_t1(m)
    blocked(m)
    resolve(m, "t1", "--executed", "--at", "2026-11-13T09:10:01Z")
    return "resolved conflict"


def later_resolve_not_executed(m):
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    blocked(m)
    resolve(m, "t1", "--not-executed")
    return "not executed"


def later_marks_removed(m):
    assert m.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    put_mark(m, "t1", "failure", "2026-11-13T09:10:01Z")
    blocked(m)
    resolve(m, "t1", "--not-executed")
    assert mark_names(m) == [f"{sha('t1')}.failure"]
    return "marks removed"


LATER_LINES = {f.__name__[len("later_"):]: f for f in (
    later_expire, later_post_with_another_input, later_denied, later_interrupt,
    later_atomic_failure, later_failure_not_atomic, later_executed, later_conflict,
    later_activated, later_resolved_conflict, later_resolve_not_executed, later_marks_removed)}


@pytest.mark.parametrize("place", list(LATER_LINES))
def test_a_line_of_an_update_waits_for_its_state(m, place):
    """Each line that describes an update of the state is written once the state is: with
    a folder in the place of the temporary file of the state, the line is not there. Wrong
    gates: log in the place of later, one for each place (gate.py, grep "later(")."""
    event = LATER_LINES[place](m)
    (m.state_dir / "state.json.tmp").rmdir()
    assert event not in [x["event"] for x in m.log()]


def test_what_the_host_module_prints_does_not_reach_the_output_of_resolve(tmp_path):
    """resolve gives the fact to the host module when it ends a conflict, for a call
    recorded as not executed with the mark of its PostToolUse, and for a call that only a
    mark names: what the module prints does not reach standard output. Wrong gates: quiet
    left out where resolve ends a conflict, and in execute."""
    x = Mandate(tmp_path, terms=COUNTER_SPEC[0], factors=COUNTER_SPEC[1], host="scripted",
                answers={"paid": 0})
    (tmp_path / "scripted_host.py").write_text(PRINTING, encoding="utf-8")
    x.activate()
    assert x.pre(PAY, "t1", T0, {"to": "acme"}) == (0, "")
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", {"to": "acme"})
    x.post(PAY, "t1", "2026-11-13T09:10:02Z", {"to": "acme"})
    runs = [x.run(["resolve", "t1", "--executed", "--at", "2026-11-13T09:10:01Z"],
                  now="2026-11-13T09:11:00Z")]
    assert x.pre(PAY, "t2", "2026-11-13T09:12:00Z", {"to": "acme"}) == (0, "")
    assert resolve(x, "t2", "--not-executed", now="2026-11-13T09:12:10Z") == (0, "")
    put_mark(x, "t2", "post", "2026-11-13T09:12:20Z")
    runs.append(x.run(["resolve", "t2", "--executed", "--at", "2026-11-13T09:12:01Z"],
                      now="2026-11-13T09:13:00Z"))
    put_mark(x, "t9", "post", "2026-11-13T09:13:30Z")
    runs.append(x.run(["resolve", "t9", "--executed", "--at", "2026-11-13T09:13:30Z"],
                      now="2026-11-13T09:14:00Z"))
    assert [(r.returncode, r.stdout, r.stderr) for r in runs] == [(0, "", "")] * 3
    assert [f["tool_use_id"] for f in x.facts()] == ["t1", "t1", "t2", "t9"]


def test_the_command_is_read_wherever_it_stands(tmp_path):
    """--config before the command: the first line says not recorded after a call, held
    before it, and only before it that the call is not to be retried; a command word that is
    the value of --config is not the command. When the arguments cannot be parsed, the
    command is the first command word that is not the value of --config, --now or --at.
    Wrong gates: command = argv[0], and first_command_word_anywhere."""
    bad = str(tmp_path / "no.json")
    for command, head in (("pre", "held"), ("post", "not recorded"), ("failure", "not recorded"),
                          ("denied", "not recorded")):
        r = subprocess.run([sys.executable, "-I", GATE, "--config", bad, command], input="{}",
                           capture_output=True, text=True)
        assert r.returncode == 2 and first(r).startswith(
            f"TRIEL gate: {head}: configuration: cannot read {bad}"), (command, r.stderr)
        assert ("  The call is held. Do not retry it;" in r.stderr) == (command == "pre"), command
    for args, head in ((["--config", "pre", "post"], "not recorded: configuration: the path pre "),
                       (["--now", "pre", "post"], "not recorded: the arguments: "),
                       (["--at", "post", "pre", "--bogus"], "held: the arguments: ")):
        r = subprocess.run([sys.executable, "-I", GATE] + args, input="{}", capture_output=True,
                           text=True)
        assert r.returncode == 2 and first(r).startswith(f"TRIEL gate: {head}"), (args, r.stderr)
