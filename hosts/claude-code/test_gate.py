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
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
GATE = str(HERE / "gate.py")
sys.path.insert(0, str(REPO / "parser"))
sys.path.insert(0, str(HERE))
from triel_eval import default_evaluator  # noqa: E402

import gate  # noqa: E402

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
        return [json.loads(x) for x in (self.state_dir / "log.jsonl").read_text().splitlines()]


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
        assert h["timeout"] > 2 * cfg["check_timeout_seconds"]
        assert os.path.isabs(h["command"]) and h["args"][0] == "-I"
        assert h["args"][2:] == [command, "--config", h["args"][-1]]
        assert all(os.path.isabs(p) for p in (h["args"][1], h["args"][-1]))
    assert s["env"] == {"CLAUDE_CODE_MCP_AUTO_BACKGROUND_MS": "0"}
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


def test_the_example_configuration_and_specification():
    cfg = example_config()
    assert gate.config_errors(cfg) == []
    assert all(os.path.isabs(cfg[k]) for k in gate.PATH_KEYS)
    r = subprocess.run([sys.executable, str(REPO / "parser" / "triel_to_core.py"), "--actions",
                        str(HERE / "mandate.triel")], capture_output=True, text=True, cwd=REPO)
    pairs = {(o["subject"], o["action"]) for o in json.loads(r.stdout)}
    assert pairs == {(a["subject"], a["action"]) for a in cfg["actions"]}


def test_the_example_mandate_end_to_end(tmp_path):
    """The example of README.md: mandate.triel, host_example.py and the
    configuration of config.example.json with the paths of tmp_path."""
    cfg = example_config()
    data = {"values": {"rate_limit": "1.20"},
            "approvals": [{"action": "pay", "tool_input": {"amount": "100.00"}}]}
    x = Mandate(tmp_path, data=data)
    shutil.copy(HERE / "mandate.triel", x.spec)
    x.config.update(actions=cfg["actions"],
                    host_options=dict(cfg["host_options"], data_file=str(tmp_path / "host_data.json")))
    x.write_config()
    x.activate()
    x.set_data(dict(data, readings={"fx_rate": {"value": "1.10", "time": "2026-11-13T09:09:30Z"}}))
    assert x.pre(PAY, "t1", "2026-11-13T09:10:00Z", {"amount": "100.00"}) == (0, "")
    x.post(PAY, "t1", "2026-11-13T09:10:01Z", {"amount": "100.00"})
    assert x.pre(CONVERT, "t2", "2026-11-13T09:10:20Z") == (0, "")
    x.post(CONVERT, "t2", "2026-11-13T09:10:21Z")
    assert x.pre(CONVERT, "t3", "2026-11-13T09:11:00Z") == (
        2, held("triel check exit 3: BLOCK: monitor TERM 3 blocks the action"))
    assert x.pre(PAY, "t4", "2026-11-13T09:11:00Z", {"amount": "100.00"}) == (
        2, held("triel check exit 3: BLOCK: monitor TERM 1 blocks the action"))
