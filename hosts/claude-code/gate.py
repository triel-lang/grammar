#!/usr/bin/env python3
"""
The TRIEL gate for Claude Code: hooks that hold a call of an MCP tool unless
triel check --last allows the action the call maps to, and the commands of the
operator of the host (README.md in this folder).

Hooks (managed settings, settings.json in this folder), each with
--config CONFIG, the JSON input of the hook on standard input:
  pre       PreToolUse: decide on the call
  post      PostToolUse: the call was executed
  failure   PostToolUseFailure: the call failed
  denied    PermissionDenied: auto mode denied the call
Commands of the operator, never available to the agent:
  activate                                 record the activation of the mandate, once
  resolve ID --executed --at TIME          the call ID was executed at TIME
  resolve ID --not-executed                the call ID was not executed
  status                                   print the state of the mandate
--now TIME fixes the host clock (ISO-8601 UTC, a fraction of a second allowed);
without it the clock of the system is read: by pre and activate once they hold
the lock, as the time they give the host module, and again once the module has
answered, as the time of the decision or of the activation, so that a reading
its source stamped while the module answered is not from the future; by post,
failure and denied when they start, as the time the event came. The gate reads
nothing else from the environment; the interpreter and the dynamic loader read
theirs (README.md, "The command of the hook").

Exit code: 0 lets the call go on to the permission flow of Claude Code, with
nothing on standard output, or a command succeeded. 2 gives the reason on
standard error: before a call (pre) the call is held, and the first line is
"TRIEL gate: held: REASON"; after a call (post, failure, denied) its fact was
not recorded, and the first line is "TRIEL gate: not recorded: REASON"; a
command of the operator is refused, and the first line is "TRIEL gate: held:
REASON". Any failure of the gate
itself, an import included, gives 2: every import but sys is made inside the
handler of main, an exception whose text cannot be printed gives 2 too, and so
does a standard error that cannot be written, or an exception whose class has
no readable name. A hook sends its standard output to /dev/null for its whole
run, so nothing that the host module prints there reaches Claude Code. For the
commands of the operator, what the module prints through sys.stdout or writes to
the file descriptor 1 while it runs is discarded; what it leaves in a buffer of
its own can still come out when the command ends.
"""
import sys

HOLD = 2
# The values of mcp_server.source that name a scope of managed configuration,
# which the agent cannot write. Every other value, an unknown one included, is
# a scope the agent may be able to write (user, project, local, dynamic, plugin,
# claudeai, agent) or a server registered by an application (sdk).
UNWRITABLE_SOURCES = ("managed", "enterprise")
CONFIG_KEYS = {"repo", "evaluator", "spec", "state_dir", "host_module", "host_options",
               "check_timeout_seconds", "pending_timeout_seconds",
               "execution_delay_flag_seconds", "managed_servers", "allowed_tools", "actions"}
PATH_KEYS = ("repo", "evaluator", "spec", "state_dir", "host_module")
CODE_REASONS = {
    1: "triel check exit 1: the check itself failed",
    2: "triel check exit 2: REJECTED: the translator rejects the specification",
    3: "triel check exit 3: BLOCK",
    4: "triel check exit 4: the evaluator rejects the trace the host built",
    5: "triel check exit 5: NO DECISION: no monitor decides this action",
    6: "triel check exit 6: a code that --last never gives",
}


class Held(Exception):
    """The call is held, or the command refused, for these reasons."""

    def __init__(self, reasons):
        super().__init__("; ".join(reasons))
        self.reasons = list(reasons)


def main(argv=None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    command = argv[0] if argv else None
    try:
        return run(argv)
    except Held as e:
        say(e.reasons, command)
        return HOLD
    except BaseException as e:  # noqa: B902 - any failure of the gate holds the call
        try:
            reason = f"the gate failed: {type(e).__name__}: {e}"
        except BaseException:  # noqa: B902 - an exception whose text cannot be printed
            try:
                reason = f"the gate failed: {type(e).__name__}"
            except BaseException:  # noqa: B902 - nor the name of its class
                reason = "the gate failed"
        say([reason], command)
        return HOLD


def say(reasons, command=None):
    """The reasons on standard error. After a call (post, failure, denied) the
    fact of the call was not recorded; before it (pre) and for a command of the
    operator, the call or the command is held, and before a call also that it is
    not to be retried."""
    try:
        head = "not recorded" if command in ("post", "failure", "denied") else "held"
        lines = [f"TRIEL gate: {head}: {reasons[0]}"] + [f"  {r}" for r in reasons[1:]]
        if command == "pre":
            lines.append("  The call is held. Do not retry it; the operator of the host decides.")
        sys.stderr.write("\n".join(lines) + "\n")
    except BaseException:  # noqa: B902
        pass


def run(argv) -> int:
    import argparse
    import json
    ap = argparse.ArgumentParser(prog="gate.py", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("command",
                    choices=["pre", "post", "failure", "denied", "activate", "resolve", "status"])
    ap.add_argument("id", nargs="?")
    ap.add_argument("--config", required=True)
    ap.add_argument("--now")
    ap.add_argument("--executed", action="store_true")
    ap.add_argument("--not-executed", action="store_true")
    ap.add_argument("--at")
    args = ap.parse_args(argv)
    if args.command in ("pre", "post", "failure", "denied"):
        # A hook prints nothing on standard output, and Claude Code reads what a hook prints
        # there on exit 0 as its JSON output: whatever the host module writes, through
        # sys.__stdout__ or the stdio of C, goes to /dev/null for the whole run of the hook.
        import os
        null = os.open(os.devnull, os.O_WRONLY)
        if null != 1:  # 1 when the hook started with its standard output closed
            os.dup2(null, 1)
            os.close(null)
    cfg = load_config(args.config)
    sys.path.insert(0, cfg["repo"] + "/parser")
    import triel_host  # the library of the trace, from the clone of the configuration

    def now():
        return clock(args.now, triel_host)

    h = now()
    if args.command in ("pre", "post", "failure", "denied"):
        hook = json.loads(sys.stdin.buffer.read().decode("utf-8"))
        if not isinstance(hook, dict):
            raise Held(["the input of the hook is not a JSON object"])
        if args.command == "pre":
            return pre(cfg, hook, h, now)
        return after(cfg, hook, h, args.command)
    if args.command == "activate":
        return activate(cfg, now)
    if args.command == "resolve":
        return resolve(cfg, args, h)
    return status(cfg, h)


# --- Clock and configuration ---------------------------------------------------

def clock(now, triel_host):
    """The host clock in exact seconds, to the microsecond."""
    from decimal import Decimal
    if now is not None:
        return triel_host.seconds(now)
    import time
    return Decimal(time.time_ns() // 1000) / 1000000


def load_config(path):
    import json
    import os
    if not os.path.isabs(path):
        raise Held([f"configuration: the path {path} is not absolute"])
    try:
        cfg = json.loads(open(path, encoding="utf-8").read())
    except (OSError, ValueError) as e:
        raise Held([f"configuration: cannot read {path}: {e}"]) from None
    errors = config_errors(cfg)
    if errors:
        raise Held([f"configuration: {e}" for e in errors])
    return cfg


def config_errors(cfg):
    """What is wrong with the configuration; empty if nothing."""
    import os
    if not isinstance(cfg, dict):
        return ["not a JSON object"]
    errors = [f"unknown key {k}" for k in sorted(set(cfg) - CONFIG_KEYS)]
    errors += [f"missing key {k}" for k in sorted(CONFIG_KEYS - set(cfg))]
    if errors:
        return errors
    for k in PATH_KEYS:
        if not (isinstance(cfg[k], str) and os.path.isabs(cfg[k])):
            errors.append(f"{k}: the path {cfg[k]!r} is not absolute")
    for k in ("check_timeout_seconds", "pending_timeout_seconds", "execution_delay_flag_seconds"):
        if isinstance(cfg[k], bool) or not isinstance(cfg[k], (int, float)) or cfg[k] <= 0:
            errors.append(f"{k}: not a positive number")
    if not isinstance(cfg["host_options"], dict):
        errors.append("host_options: not a JSON object")

    def entries(key, fields):
        xs = cfg[key]
        ok = isinstance(xs, list) and all(isinstance(x, dict) and set(x) == set(fields)
                                          and all(isinstance(x[f], str) for f in fields
                                                  if f != "atomic") for x in xs)
        if not ok:
            errors.append(f"{key}: a list of objects with the keys {', '.join(fields)}")
            return []
        return xs

    managed = entries("managed_servers", ("name", "source"))
    allowed = entries("allowed_tools", ("server", "source", "tool_name"))
    actions = entries("actions", ("server", "tool_name", "subject", "action", "atomic"))
    names = [m["name"] for m in managed]
    if len(set(names)) != len(names):
        errors.append("managed_servers: a server is listed twice")
    for m in managed:
        if m["source"] not in UNWRITABLE_SOURCES:
            errors.append(f"managed server {m['name']}: the source {m['source']} is not a scope of "
                          f"managed configuration ({', '.join(UNWRITABLE_SOURCES)}); "
                          "the agent may be able to write it")
    for a in allowed:
        if a["server"] in names:
            errors.append(f"allowed tool {a['tool_name']}: the server {a['server']} has the name "
                          "of a managed server")
        if a["source"] not in UNWRITABLE_SOURCES:
            errors.append(f"allowed tool {a['tool_name']}: the source {a['source']} of the server "
                          f"{a['server']} is not a scope of managed configuration "
                          f"({', '.join(UNWRITABLE_SOURCES)}); the agent may be able to write it")
        if not a["tool_name"].startswith("mcp__"):
            errors.append(f"allowed tool {a['tool_name']}: not an MCP tool")
    allowed_servers = {a["server"] for a in allowed}
    seen = set()
    for a in actions:
        if not a["tool_name"].startswith("mcp__"):
            errors.append(f"actions: {a['tool_name']} is not an MCP tool")
        if a["server"] in allowed_servers:
            errors.append(f"actions: {a['tool_name']} is a tool of the allowed server {a['server']}, "
                          "not of a managed server")
        elif a["server"] not in names:
            errors.append(f"actions: {a['tool_name']}: {a['server']} is not a managed server")
        if not isinstance(a["atomic"], bool):
            errors.append(f"actions: {a['tool_name']}: atomic is not true or false")
        if (a["server"], a["tool_name"]) in seen:
            errors.append(f"actions: {a['tool_name']} is mapped twice")
        seen.add((a["server"], a["tool_name"]))
    return errors


def classify(cfg, hook):
    """("managed", its entry of actions), ("allowed", None) or ("hold", reason)."""
    tool, server = hook.get("tool_name"), hook.get("mcp_server")
    if not (isinstance(tool, str) and tool.startswith("mcp__")):
        return "hold", f"{tool}: not an MCP tool; the gate decides only on MCP tools"
    if not (isinstance(server, dict) and isinstance(server.get("name"), str)
            and isinstance(server.get("source"), str)):
        return "hold", (f"{tool}: the input of the hook has no mcp_server "
                        "(Claude Code gives it from version 2.1.274)")
    name, source = server["name"], server["source"]
    managed = {m["name"]: m["source"] for m in cfg["managed_servers"]}
    if name in managed:
        if source != managed[name]:
            return "hold", (f"{tool}: the server {name} has the source {source}, not the source "
                            f"{managed[name]} of the managed server")
        for a in cfg["actions"]:
            if a["server"] == name and a["tool_name"] == tool:
                return "managed", a
        return "hold", f"tool not mapped to an action: {tool} of the managed server {name}"
    allowed = [a for a in cfg["allowed_tools"] if a["server"] == name]
    if any(a["source"] == source and a["tool_name"] == tool for a in allowed):
        return "allowed", None
    if allowed and all(a["source"] != source for a in allowed):
        return "hold", (f"tool not allowed: {tool}: the server {name} has the source {source}, "
                        "not the source of the allowed server")
    if allowed:
        return "hold", f"tool not allowed: {tool} is not in the allowed tools of the server {name}"
    return "hold", (f"tool not allowed: {tool} of the server {name}, which is neither a managed "
                    "server nor a server with allowed tools")


# --- State of the mandate ----------------------------------------------------------

def state_dir(cfg):
    from pathlib import Path
    d = Path(cfg["state_dir"])
    d.mkdir(parents=True, exist_ok=True, mode=0o700)
    return d


class locked:
    """One decision or one update of the state at a time, on this machine. pre
    waits for the lock at most check_timeout_seconds, so that it can still run
    its two child processes within the timeout of the hook; the events after a
    call and the commands of the operator wait up to three times as long, since
    a fact of execution they do not record is lost."""

    def __init__(self, cfg, waits=3, gave_up=None):
        self.cfg, self.waits, self.gave_up = cfg, waits, gave_up

    def __enter__(self):
        import fcntl
        import time
        self.f = open(state_dir(self.cfg) / "lock", "a")
        deadline = time.monotonic() + self.waits * self.cfg["check_timeout_seconds"]
        while True:
            try:
                fcntl.flock(self.f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return self
            except BlockingIOError:
                if time.monotonic() > deadline:
                    self.f.close()
                    reasons = ["another decision of the gate is still running"]
                    if self.gave_up:
                        self.gave_up(reasons)
                    raise Held(reasons) from None
                time.sleep(0.05)

    def __exit__(self, *exc):
        import fcntl
        fcntl.flock(self.f, fcntl.LOCK_UN)
        self.f.close()
        return False


class quiet:
    """What the host module prints through sys.stdout or writes to the file
    descriptor 1 while it runs is discarded; what it leaves in a buffer of its
    own, such as that of sys.__stdout__ or of the stdio of C, can still come out
    when the process ends. A hook has sent its standard output to /dev/null for
    its whole run already (run)."""

    def __enter__(self):
        import contextlib
        import io
        import os
        if sys.stdout is not None:
            sys.stdout.flush()
        self.fd = os.dup(1)
        null = os.open(os.devnull, os.O_WRONLY)
        os.dup2(null, 1)
        os.close(null)
        self.redirect = contextlib.redirect_stdout(io.StringIO())
        self.redirect.__enter__()
        return self

    def __exit__(self, *exc):
        import os
        self.redirect.__exit__(*exc)
        os.dup2(self.fd, 1)
        os.close(self.fd)
        return False


def empty_state():
    return {"version": 1, "activation": None, "history": [], "readings": {}, "pending": {},
            "unknown": {}, "not_executed": {}, "conflicts": {}, "cache": None}


def load_state(cfg):
    import json
    p = state_dir(cfg) / "state.json"
    if not p.exists():
        return None
    st = json.loads(p.read_text(encoding="utf-8"))
    if not (isinstance(st, dict) and set(st) == set(empty_state())):
        raise Held([f"the state {p} is not a state of the gate"])
    return st


def save_state(cfg, st):
    import json
    import os
    d = state_dir(cfg)
    tmp = d / "state.json.tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(json.dumps(st, ensure_ascii=False, indent=1))
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, d / "state.json")
    lines = LATER[:]
    LATER.clear()
    for at, fields in lines:  # the journal of this update, once the state is written
        log(cfg, at, **fields)


# The lines of the journal that describe an update of the state, written by
# save_state once the state is: a line without its change never stands alone.
LATER = []


def later(h, **fields):
    LATER.append((h, fields))


def log(cfg, h, **fields):
    """A line of the journal of the host, state_dir/log.jsonl."""
    import json
    import os
    import triel_host
    line = json.dumps({"at": triel_host.exact(h), **fields}, ensure_ascii=False, default=str)
    with open(state_dir(cfg) / "log.jsonl", "a", encoding="utf-8") as f:
        f.write(line + "\n")
        f.flush()
        os.fsync(f.fileno())


def canonical(x) -> str:
    import json
    return json.dumps(x, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def iso(n) -> str:
    import triel_host
    return triel_host.iso(n)


def expire(cfg, st, h):
    """A pending call without a Post event for longer than pending_timeout_seconds
    becomes unknown, never not executed."""
    from decimal import Decimal
    limit = Decimal(str(cfg["pending_timeout_seconds"]))
    for tid, p in list(st["pending"].items()):
        if h - Decimal(p["decided"]) > limit:
            del st["pending"][tid]
            why = expired(cfg)
            st["unknown"][tid] = dict(p, why=why)
            later(h, event="unknown", tool_use_id=tid, tool_name=p["tool_name"], why=why)


def expired(cfg):
    return f"no PostToolUse or PostToolUseFailure within {cfg['pending_timeout_seconds']} s"


def find(st, tid):
    for where in ("pending", "unknown", "not_executed"):
        if tid in st[where]:
            return st[where][tid], where
    return None, None


# --- The specification and the host module -------------------------------------

def child(cfg, args):
    """A program of the clone, run as sys.executable -I with the environment the
    gate sets; (exit code, stdout, stderr), or (None, ...) after the timeout."""
    import os
    import signal
    import subprocess
    p = subprocess.Popen([sys.executable, "-I"] + args, cwd=cfg["repo"], env={"PATH": os.defpath},
                         stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         start_new_session=True)
    try:
        out, err = p.communicate(timeout=cfg["check_timeout_seconds"])
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        return None, "", ""
    return p.returncode, out.decode("utf-8", "replace"), err.decode("utf-8", "replace")


def spec_info(cfg, st):
    """The factors of the specification (triel_host.spec_factors) and the output
    of triel_to_core.py --actions, kept in the state by the sha256 of the
    specification and of the programs that read it."""
    import json
    from pathlib import Path
    import lark
    import triel_host
    parser = Path(cfg["repo"]) / "parser"
    text = Path(cfg["spec"]).read_bytes()
    key = cache_key(text, [(parser / f).read_bytes() for f in (
        "triel_to_core.py", "triel.lark", "triel_host.py", "triel.py", "triel_eval.py")],
        lark.__version__)
    if st["cache"] and st["cache"]["key"] == key:
        return st["cache"]["factors"], st["cache"]["actions"]
    code, out, err = child(cfg, [str(parser / "triel_to_core.py"), "--actions", cfg["spec"]])
    if code is None:
        raise Held([f"triel_to_core.py --actions did not answer within "
                    f"{cfg['check_timeout_seconds']} s"])
    if code == 2:
        rej = [line for line in out.splitlines() if line.startswith("REJECTED:")]
        raise Held(["triel_to_core.py --actions exit 2: the translator rejects the specification"]
                   + rej)
    if code != 0:
        raise Held([f"triel_to_core.py --actions exit {code}: "
                    + (err.strip().splitlines() or ["no message"])[-1]])
    actions = json.loads(out)
    factors = triel_host.spec_factors(text.decode("utf-8"))
    st["cache"] = {"key": key, "factors": factors, "actions": actions}
    return factors, actions


def cache_key(spec, files, lark_version):
    """The sha256 of the specification, of the programs that read it, of the
    version of lark and of Python, each part with its length before it."""
    import hashlib
    h = hashlib.sha256()
    for part in [lark_version.encode(), sys.version.encode(), spec] + list(files):
        h.update(len(part).to_bytes(8, "big"))
        h.update(part)
    return h.hexdigest()


def host_module(cfg):
    import importlib.util
    spec = importlib.util.spec_from_file_location("triel_gate_host_module", cfg["host_module"])
    if spec is None:
        raise Held([f"cannot load the host module {cfg['host_module']}"])
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    for f in ("answers", "executed"):
        if not callable(getattr(mod, f, None)):
            raise Held([f"the host module {cfg['host_module']} has no function {f}"])
    return mod


def moment(h):
    """The host clock as an aware datetime, for the host module."""
    from datetime import timedelta
    import triel_host
    return triel_host.EPOCH + timedelta(microseconds=int(h * 1000000))


# --- PreToolUse ---------------------------------------------------------------------

def pre(cfg, hook, h, now) -> int:
    import json
    from pathlib import Path
    import triel_host
    kind, info = classify(cfg, hook)
    tool, tid = hook.get("tool_name"), hook.get("tool_use_id")
    if kind == "allowed":
        log(cfg, h, event="allowed tool", tool_use_id=tid, tool_name=tool,
            mcp_server=hook.get("mcp_server"))
        return 0
    if kind == "hold":
        log(cfg, h, event="held", tool_use_id=tid, tool_name=tool, reasons=[info])
        raise Held([info])
    if not (isinstance(tid, str) and tid):
        raise Held([f"{tool}: the input of the hook has no tool_use_id"])
    m = info
    with locked(cfg, waits=1):
        h = now()
        st = load_state(cfg)
        if st is None or st["activation"] is None:
            reasons = ["the mandate has no activation: the operator runs gate.py activate"]
            log(cfg, h, event="held", tool_use_id=tid, tool_name=tool, reasons=reasons)
            raise Held(reasons)
        try:
            expire(cfg, st, h)
            if st["conflicts"]:
                c, x = next(iter(st["conflicts"].items()))
                raise Held([f"conflict on the call {c}: {x['why']}; every action is held until "
                            f"the operator runs gate.py resolve {c}"])
            if st["unknown"]:
                u, x = next(iter(st["unknown"].items()))
                raise Held([f"the outcome of the call {u} is unknown ({x['why']}); every action is "
                            f"held until the operator runs gate.py resolve {u}"])
            others = [p for p in st["pending"] if p != tid]
            if others:
                raise Held([f"waits for the outcome of the previous action, the call {others[0]}"])
            if tid in st["not_executed"] or any(x["tool_use_id"] == tid for x in st["history"]):
                raise Held([f"the call {tid} already has an outcome; a new call has a new "
                            "tool_use_id"])
            st["pending"].pop(tid, None)  # a repeated PreToolUse replaces the record
            factors, actions = spec_info(cfg, st)
            pair = next((a for a in actions if a["subject"] == m["subject"]
                         and a["action"] == m["action"]), None)
            call = {"tool_use_id": tid, "tool_name": tool, "tool_input": hook.get("tool_input"),
                    "subject": m["subject"], "action": m["action"], "mcp_server": hook["mcp_server"]}
            with quiet():
                answers = host_module(cfg).answers(call, moment(h), factors, cfg["host_options"])
            h = now()  # after the answers: a reading stamped while they were made is not later
            trace, st["readings"], reasons, data = triel_host.decide(
                factors, cfg["spec"], st["activation"], st["history"], st["readings"], answers,
                m["subject"], m["action"], h)
            if reasons:
                raise Held(reasons)
            safe = "".join(c if c.isalnum() or c in "_-" else "_" for c in tid)
            trace_path = state_dir(cfg) / "traces" / f"{safe}.json"
            trace_path.parent.mkdir(exist_ok=True)
            trace_path.write_text(json.dumps(trace, ensure_ascii=False, indent=1), encoding="utf-8")
            code, out, err = child(cfg, [str(Path(cfg["repo"]) / "parser" / "triel.py"), "check",
                                         cfg["spec"], str(trace_path), "--last", "--json",
                                         "--evaluator", cfg["evaluator"]])
            reasons = judge(cfg, code, out, err, trace, pair)
            if reasons:
                raise Held(reasons + [f"trace: {trace_path}"])
        except Held as e:
            log(cfg, h, event="held", tool_use_id=tid, tool_name=tool, reasons=e.reasons)
            save_state(cfg, st)
            raise
        st["pending"][tid] = {"tool_name": tool, "tool_input": hook.get("tool_input"),
                              "subject": m["subject"], "action": m["action"],
                              "decided": triel_host.exact(h), "data": data}
        save_state(cfg, st)  # the pending record, then the line of the journal, then exit 0
        log(cfg, h, event="allowed", tool_use_id=tid, tool_name=tool, subject=m["subject"],
            action=m["action"], T=iso(triel_host.decision_time(h)))
    return 0


def judge(cfg, code, out, err, trace, pair):
    """The reasons to hold the call after triel check; empty only when exit 0,
    the LAST line is for the last entry, its decisions are not empty and all
    ALLOW, its monitors are exactly the monitors of --actions for the action,
    and no prohibition inside a composite term names the action."""
    import json
    if code is None:
        return [f"the check did not answer within {cfg['check_timeout_seconds']} s"]
    report = None
    try:
        report = json.loads(out) if out.strip() else None
    except ValueError:
        report = None
    objs = report if isinstance(report, list) else []
    lasts = [o for o in objs if isinstance(o, dict) and o.get("line") == "LAST"]
    last = lasts[-1] if lasts else None
    j = len(trace["entries"]) - 1
    monitors = pair["monitors"] if pair else []
    reasons = []
    if code != 0:
        r = CODE_REASONS.get(code, f"triel check exit {code}")
        if code == 3 and last:
            r += ": " + ", ".join(f"monitor TERM {d['term']} blocks the action"
                                  for d in last.get("decisions", []) if d.get("decision") == "BLOCK")
        if code == 4:
            bad = [o for o in objs if isinstance(o, dict) and (
                o.get("line") == "TIME ORDER REJECTED" or o.get("result") in ("REJECTED", "ILL-TYPED"))]
            r += f": {rejection(bad[0])}" if bad else ""
        if code == 1:
            r += ": " + (err.strip().splitlines() or ["no message"])[-1]
        if code == 2:
            r += "".join(f": {', '.join(o['constructs'])}" for o in objs
                         if isinstance(o, dict) and o.get("line") == "REJECTED")
        reasons.append(r)
    elif report is None:
        reasons.append("triel check exit 0, but it printed no report" if not out.strip()
                       else "triel check exit 0, but its report cannot be read")
    elif last is None:
        reasons.append("triel check exit 0, but the report has no LAST line")
    elif last.get("entry") != j:
        reasons.append(f"triel check exit 0, but the LAST line is for entry {last.get('entry')}, "
                       f"not for the last entry {j}")
    else:
        ds = last.get("decisions") or []
        terms = {d.get("term") for d in ds}
        if not ds:
            reasons.append("triel check exit 0, but no monitor decided on the action")
        elif any(d.get("decision") != "ALLOW" for d in ds):
            reasons.append("triel check exit 0, but a decision of the LAST line is not ALLOW")
        for i in monitors:
            if i not in terms:
                reasons.append(f"monitor TERM {i} did not decide on the action: arguments not "
                               f"matched (its action is {pair['monitor_actions'][str(i)]})")
        extra = sorted(t for t in terms if t not in monitors)
        if extra:
            reasons.append(f"the LAST line names TERM {extra}, which --actions does not give "
                           "for this action")
    if pair and pair["composite_prohibitions"]:
        reasons.append("the action is named in a prohibition inside the composite term "
                       + ", ".join(f"TERM {k}" for k in pair["composite_prohibitions"])
                       + ", which no monitor decides")
    return reasons


def rejection(o) -> str:
    """The line of the report by which the evaluator rejects the trace."""
    if o.get("line") == "TIME ORDER REJECTED":
        return f"TIME ORDER REJECTED ENTRY {o.get('entry')}"
    if o.get("line") == "TYPES":
        return f"TYPES ILL-TYPED ENTRY {o.get('entry')} FACTOR {o.get('factor')}"
    return f"{o.get('line')} {o.get('result')}"


# --- PostToolUse, PostToolUseFailure, PermissionDenied ---------------------------

def after(cfg, hook, h, event) -> int:
    """Record the outcome of a call of a mapped tool of a managed server."""
    from decimal import Decimal, InvalidOperation
    import triel_host
    kind, m = classify(cfg, hook)
    tid = hook.get("tool_use_id")
    if kind == "hold":
        log(cfg, h, event=f"{event} ignored", tool_use_id=tid, tool_name=hook.get("tool_name"),
            reasons=[m])
        return 0
    if kind != "managed":
        return 0

    def gave_up(reasons):  # the fact is not recorded: the journal says so, without the lock
        log(cfg, h, event=f"{event} not recorded", tool_use_id=tid, tool_name=hook["tool_name"],
            reasons=reasons)

    with locked(cfg, gave_up=gave_up):
        st = load_state(cfg)
        if st is None:
            log(cfg, h, event=f"{event} without a state", tool_use_id=tid, tool_name=hook["tool_name"])
            return 0
        expire(cfg, st, h)
        rec, where = find(st, tid)
        if event == "post":
            executed_at = h
            d = hook.get("duration_ms")
            if isinstance(d, (int, float)) and not isinstance(d, bool) and d >= 0:
                try:
                    executed_at = h - Decimal(str(d)) / 1000
                except InvalidOperation:
                    pass
            same = rec is not None and canonical(hook.get("tool_input")) == canonical(rec["tool_input"])
            if where == "pending":
                del st["pending"][tid]
                if same:
                    execute(cfg, st, tid, rec, executed_at, hook.get("tool_input"), h)
                else:
                    why = "the input of PostToolUse differs from the input of PreToolUse"
                    st["unknown"][tid] = dict(rec, why=why, post_input=hook.get("tool_input"))
                    later(h, event="unknown", tool_use_id=tid, tool_name=rec["tool_name"],
                          why=why, pre_input=rec["tool_input"], post_input=hook.get("tool_input"))
            elif where in ("unknown", "not_executed"):
                del st[where][tid]
                execute(cfg, st, tid, rec, executed_at, hook.get("tool_input"), h)
                if where == "not_executed":
                    conflict(cfg, st, tid, h, "PostToolUse came for a call recorded as not executed")
                elif not same:
                    conflict(cfg, st, tid, h, "the late PostToolUse has another input than "
                                              "PreToolUse")
            elif any(x["tool_use_id"] == tid for x in st["history"]):
                conflict(cfg, st, tid, h, "a PostToolUse came for a call already in the history")
            else:
                rec = {"tool_name": hook["tool_name"], "tool_input": hook.get("tool_input"),
                       "subject": m["subject"], "action": m["action"],
                       "decided": triel_host.exact(executed_at), "data": {}}
                execute(cfg, st, tid, rec, executed_at, hook.get("tool_input"), h)
                conflict(cfg, st, tid, h, "PostToolUse came for a call the gate did not allow")
        elif where == "pending":
            del st["pending"][tid]
            if event == "denied":
                why = "PermissionDenied: auto mode denied the call"
                st["not_executed"][tid] = dict(rec, why=why)
                later(h, event="not executed", tool_use_id=tid, tool_name=rec["tool_name"], why=why)
            elif hook.get("is_interrupt") is True:
                why = "PostToolUseFailure with is_interrupt"
                st["unknown"][tid] = dict(rec, why=why)
                later(h, event="unknown", tool_use_id=tid, tool_name=rec["tool_name"], why=why)
            elif m["atomic"]:
                why = "PostToolUseFailure of a tool that the configuration declares atomic"
                st["not_executed"][tid] = dict(rec, why=why)
                later(h, event="not executed", tool_use_id=tid, tool_name=rec["tool_name"],
                      why=why, error=hook.get("error"))
            else:
                why = "PostToolUseFailure of a tool that the configuration does not declare atomic"
                st["unknown"][tid] = dict(rec, why=why)
                later(h, event="unknown", tool_use_id=tid, tool_name=rec["tool_name"], why=why)
        else:
            log(cfg, h, event=f"{event} for a call that is not pending", tool_use_id=tid,
                tool_name=hook["tool_name"], recorded_as=where)
        save_state(cfg, st)
    return 0


def execute(cfg, st, tid, rec, executed_at, tool_input, h):
    """The call is executed: into the history with the time of execution E, and
    the fact of the execution to the host module."""
    from decimal import Decimal
    import triel_host
    decided = Decimal(rec["decided"])
    executed_at = max(executed_at, decided)
    st["history"].append({"tool_use_id": tid, "tool_name": rec["tool_name"],
                          "subject": rec["subject"], "action": rec["action"],
                          "decided": rec["decided"], "executed": triel_host.exact(executed_at),
                          "data": rec["data"], "tool_input": tool_input})
    t = triel_host.decision_time(decided)
    e = triel_host.execution_time(decided, executed_at)
    flag = e - t > cfg["execution_delay_flag_seconds"]
    later(h, event="executed", tool_use_id=tid, tool_name=rec["tool_name"], T=iso(t), E=iso(e),
          delay_flagged=flag)
    fact = {"tool_use_id": tid, "tool_name": rec["tool_name"], "subject": rec["subject"],
            "action": rec["action"], "tool_input": tool_input, "time": moment(Decimal(e))}
    try:
        with quiet():
            host_module(cfg).executed(fact, cfg["host_options"])
    except Exception as e:  # noqa: B902 - an approval left in place must not allow a repeat
        conflict(cfg, st, tid, h, f"the host module did not take the execution: "
                                  f"{type(e).__name__}: {e}")


def conflict(cfg, st, tid, h, why):
    """A conflict on the call tid; a second reason does not hide the first."""
    old = st["conflicts"].get(tid)
    st["conflicts"][tid] = {"why": why if old is None else f"{old['why']}; {why}"}
    later(h, event="conflict", tool_use_id=tid, why=why)


# --- Commands of the operator ----------------------------------------------------

def activate(cfg, now) -> int:
    import triel_host
    with locked(cfg):
        if load_state(cfg) is not None:
            raise Held(["the mandate already has a state; a second activation is refused and "
                        "the history is kept"])
        st = empty_state()
        factors, _ = spec_info(cfg, st)
        with quiet():
            answers = host_module(cfg).answers(None, moment(now()), factors, cfg["host_options"])
        h = now()  # after the answers, as for a decision
        rec, st["readings"], reasons = triel_host.activation(factors, answers, h)
        if reasons:
            raise Held(["activation refused"] + reasons)
        st["activation"] = rec
        later(h, event="activated", time=iso(triel_host.floor_s(h)))
        save_state(cfg, st)
    return 0


def resolve(cfg, args, h) -> int:
    from decimal import Decimal
    import triel_host
    tid = args.id
    if not tid or args.executed == args.not_executed:
        raise Held(["resolve ID takes --executed --at TIME or --not-executed"])
    if args.executed != (args.at is not None):
        raise Held(["--at TIME goes with --executed, and only with it"])
    with locked(cfg):
        st = load_state(cfg)
        if st is None:
            raise Held(["the mandate has no state"])

        def at_time(decided):
            at = triel_host.seconds(args.at)
            t = triel_host.decision_time(Decimal(decided))
            if at < t:
                raise Held([f"--at {args.at} is earlier than the time of the decision, {iso(t)}"])
            if at > h:
                raise Held([f"--at {args.at} is later than the host clock"])
            return at

        if tid in st["conflicts"]:
            if not args.executed:
                raise Held([f"the call {tid} is in the history as executed; end the conflict "
                            "with --executed --at TIME"])
            x = next(x for x in st["history"] if x["tool_use_id"] == tid)
            x["executed"] = triel_host.exact(at_time(x["decided"]))
            # The host module takes the fact again: the conflict may be that it did not take it.
            e = triel_host.execution_time(Decimal(x["decided"]), Decimal(x["executed"]))
            fact = {"tool_use_id": tid, "tool_name": x["tool_name"], "subject": x["subject"],
                    "action": x["action"], "tool_input": x["tool_input"],
                    "time": moment(Decimal(e))}
            try:
                with quiet():
                    host_module(cfg).executed(fact, cfg["host_options"])
            except Exception as err:  # noqa: B902 - the conflict stays
                raise Held([f"the host module did not take the execution: "
                            f"{type(err).__name__}: {err}",
                            f"the conflict on the call {tid} stays"]) from None
            del st["conflicts"][tid]
            later(h, event="resolved conflict", tool_use_id=tid, executed=x["executed"])
            save_state(cfg, st)
            return 0
        rec, where = find(st, tid)
        if where not in ("pending", "unknown"):
            raise Held([f"no pending or unknown call {tid}"])
        if args.executed:
            at = at_time(rec["decided"])
            del st[where][tid]
            execute(cfg, st, tid, rec, at, rec.get("post_input", rec["tool_input"]), h)
            if tid in st["conflicts"]:  # the host module did not take the fact
                save_state(cfg, st)
                raise Held([st["conflicts"][tid]["why"],
                            f"the conflict on the call {tid} is recorded; gate.py resolve {tid} "
                            "--executed --at TIME gives the fact to the module again"])
        else:
            del st[where][tid]
            st["not_executed"][tid] = dict(rec, why="resolve --not-executed")
            later(h, event="not executed", tool_use_id=tid, why="resolve --not-executed")
        save_state(cfg, st)
    return 0


def status(cfg, h) -> int:
    """The state at the host clock h, without changing it: the age of each
    pending call and the seconds until its outcome becomes unknown; a pending
    call whose time is over is shown as unknown."""
    import json
    from decimal import Decimal
    with locked(cfg):
        st = load_state(cfg)
    if st is None:
        print(json.dumps({"activation": None}))
        return 0

    def number(x):
        return int(x) if x == int(x) else float(x)

    limit = Decimal(str(cfg["pending_timeout_seconds"]))
    pending, unknown = {}, dict(st["unknown"])
    for tid, p in st["pending"].items():
        age = h - Decimal(p["decided"])
        if age > limit:
            unknown[tid] = dict(p, why=expired(cfg))
        else:
            pending[tid] = dict(p, age_seconds=number(age), unknown_in_seconds=number(limit - age))
    print(json.dumps({"activation": st["activation"], "pending": pending, "unknown": unknown,
                      "conflicts": st["conflicts"], "executed": len(st["history"]),
                      "not_executed": sorted(st["not_executed"])}, ensure_ascii=False, indent=1))
    return 0


if __name__ == "__main__":
    code = main()
    if code == HOLD:
        # Exit 2 even when standard error cannot be flushed, where Python would exit 120.
        try:
            sys.stderr.flush()
        except BaseException:  # noqa: B902
            pass
        try:
            import os
            os._exit(HOLD)
        except BaseException:  # noqa: B902
            sys.exit(HOLD)
    sys.exit(code)
