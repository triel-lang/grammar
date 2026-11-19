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
  resolve ID --drop-mark                   remove the marks of the call ID, nothing else
  status                                   print the state of the mandate
--now TIME fixes the host clock (ISO-8601 UTC, a fraction of a second allowed);
without it the clock of the system is read: by pre and activate once they hold
the lock, as the time they give the host module, and again once the module has
answered. For pre the second is the time of the decision, so that a reading its
source stamped while the module answered is not from the future; for activate
the first is the time of the activation, and the second only bounds the
readings, so that such a reading is later than the activation and not from the
future. post, failure and denied read it when they start, as the time the
event came. The gate reads nothing else from the environment; the interpreter
and the dynamic loader read theirs (README.md, "The command of the hook").

Every value of the input of the hook is read without an exception; a value
that the gate cannot write (a number that JSON cannot write, a string with a
lone surrogate, an integer too long to read) in the input of the call holds
the call, or leaves its event not recorded, and the gate writes no such value
to any file (README.md, "The outcome of a call").

An event after a call (post, failure, denied) of a managed server creates its
mark, state_dir/unrecorded/<sha256 of the tool_use_id>.<post|failure|denied>,
before it waits for the lock, and removes it once the state with the event is
written. While a mark is there every action is held: a mark whose event still
runs, until the event ends; a mark whose event ended without recording it,
until the operator runs resolve.

Exit code: 0 lets the call go on to the permission flow of Claude Code, with
nothing on standard output, or a command succeeded. 2 gives the reason on
standard error: before a call (pre) the call is held, and the first line is
"TRIEL gate: held: REASON"; after a call (post, failure, denied) its fact was
not recorded, or it was recorded and its line of the journal was not written,
and the first line is "TRIEL gate: not recorded: REASON"; a command of the
operator is refused, and the first line is "TRIEL gate: held: REASON". Any
failure of the gate itself, an import included, gives 2: every import but sys
is made inside the handler of main, an exception whose text cannot be printed
gives 2 too, and so does a standard error that cannot be written, or an
exception whose class has no readable name. A hook sends its standard output to
/dev/null for its whole run, so nothing that the host module prints there
reaches Claude Code. For the commands of the operator, what the module prints
through sys.stdout or writes to the file descriptor 1 while it runs is
discarded; what it leaves in a buffer of its own can still come out when the
command ends.
"""
import sys

HOLD = 2
# The values of mcp_server.source that name a scope of managed configuration,
# which the agent cannot write. Every other value, an unknown one included, is
# a scope the agent may be able to write (user, project, local, dynamic, plugin,
# claudeai, agent) or a server registered by an application (sdk).
UNWRITABLE_SOURCES = ("managed", "enterprise")
COMMANDS = ("pre", "post", "failure", "denied", "activate", "resolve", "status")
HOOKS = ("pre", "post", "failure", "denied")
# The events after a call, by the command of their hook, which ends the name of their mark.
EVENTS = {"post": "PostToolUse", "failure": "PostToolUseFailure", "denied": "PermissionDenied"}
MARK_KEYS = ("tool_use_id", "event", "came", "tool_name", "subject", "action", "tool_input",
             "input_written")
# The kinds of a value that the gate cannot write.
NOT_A_NUMBER = "a number that JSON cannot write"
NOT_UTF8 = "a string that UTF-8 cannot write"
TOO_LONG = "an integer too long to read"
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


class LongInteger:
    """An integer of the input of the hook with more digits than Python reads
    (sys.get_int_max_str_digits): the input is read without an exception, and
    the gate writes no such integer."""

    def __init__(self, text):
        self.text = text

    def __repr__(self):
        return f"<an integer of {len(self.text)} characters>"


def main(argv=None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    ctx = {"command": None}
    try:
        ctx["command"] = command_word(argv)
        return run(argv, ctx)
    except Held as e:
        say(e.reasons, ctx["command"])
        return HOLD
    except BaseException as e:  # noqa: B902 - any failure of the gate holds the call
        say([failed(e)], ctx["command"])
        return HOLD


def failed(e) -> str:
    """The reason of a failure of the gate, also for an exception whose text or
    whose class cannot be printed."""
    d = described(e)
    return "the gate failed" if d is None else f"the gate failed: {d}"


def described(e):
    """The class and the text of an exception; the class alone when its text cannot
    be printed; None when neither can."""
    try:
        return f"{type(e).__name__}: {e}"
    except BaseException:  # noqa: B902 - an exception whose text cannot be printed
        try:
            return f"{type(e).__name__}"
        except BaseException:  # noqa: B902 - nor the name of its class
            return None


def command_word(argv):
    """The command for the first line of a failure before the arguments are
    parsed: the first argument that is a command and does not stand right
    after --config, --now or --at. Once they are parsed, it is the command
    that argparse read."""
    value = False
    for a in argv:
        if not value and a in COMMANDS:
            return a
        value = a in ("--config", "--now", "--at")
    return None


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


def run(argv, ctx) -> int:
    import argparse

    class Arguments(argparse.ArgumentParser):
        def error(self, message):  # the reason on the first line, as for any refusal
            raise Held([f"the arguments: {message}"])

    ap = Arguments(prog="gate.py", description=__doc__,
                   formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("command", choices=list(COMMANDS))
    ap.add_argument("id", nargs="?")
    ap.add_argument("--config", required=True)
    ap.add_argument("--now")
    ap.add_argument("--executed", action="store_true")
    ap.add_argument("--not-executed", action="store_true")
    ap.add_argument("--drop-mark", action="store_true")
    ap.add_argument("--at")
    args = ap.parse_args(argv)
    ctx["command"] = args.command
    if args.command in HOOKS:
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
    if args.command in HOOKS:
        hook = read_hook(sys.stdin.buffer.read())
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


# --- The input of the hook, and the values the gate cannot write ---------------------

def read_hook(data):
    """The JSON input of the hook, every value read without an exception: NaN,
    Infinity, -Infinity and a number out of the range of a binary float as
    Python reads them (a float that is not finite), an integer longer than
    Python reads as a LongInteger."""
    import json

    def integer(text):
        try:
            return int(text)
        except ValueError:
            return LongInteger(text)

    return json.loads(data.decode("utf-8"), parse_int=integer)


def unwritable(x, path="tool_input"):
    """(KIND, PATH) of the first value in x, in the order of its text, that the
    gate cannot write; None if there is none. KIND is NOT_A_NUMBER for a float
    that is not finite, NOT_UTF8 for a string, or a key of an object, with a
    lone surrogate, TOO_LONG for a LongInteger. PATH is path, then for each step
    [the key as a JSON string written with ensure_ascii] or [the index]; for a
    key that cannot be written it ends with that key."""
    import json
    import math
    todo = [(x, None)]
    while todo:  # depth first, without recursion: the input may be deep
        v, at = todo.pop()
        kind = None
        if isinstance(v, str):
            try:
                v.encode("utf-8")
            except UnicodeEncodeError:
                kind = NOT_UTF8
        elif isinstance(v, float):
            if not math.isfinite(v):
                kind = NOT_A_NUMBER
        elif isinstance(v, LongInteger):
            kind = TOO_LONG
        elif isinstance(v, dict):
            for k, y in reversed(list(v.items())):
                step = (at, "[" + json.dumps(k, ensure_ascii=True) + "]")
                todo.append((y, step))
                todo.append((k, step))
        elif isinstance(v, list):
            for i in range(len(v) - 1, -1, -1):
                todo.append((v[i], (at, f"[{i}]")))
        if kind is not None:
            steps = []
            while at is not None:
                at, step = at
                steps.append(step)
            return kind, path + "".join(reversed(steps))
    return None


def writable_text(x) -> bool:
    return isinstance(x, str) and unwritable(x) is None


def input_reason(bad) -> str:
    return f"the input of the call has {bad[0]}: {bad[1]}"


# --- State of the mandate ----------------------------------------------------------

def state_dir(cfg):
    from pathlib import Path
    d = Path(cfg["state_dir"])
    d.mkdir(parents=True, exist_ok=True, mode=0o700)
    return d


def sync_dir(d):
    import os
    fd = os.open(d, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


class locked:
    """One decision or one update of the state at a time, on this machine. pre
    waits for the lock at most check_timeout_seconds, so that it can still run
    its two child processes within the timeout of the hook; the events after a
    call and the commands of the operator wait up to three times as long, since
    a fact of execution they do not record is lost."""

    def __init__(self, cfg, waits=3):
        self.cfg, self.waits = cfg, waits

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
                    raise Held(["another decision of the gate is still running"]) from None
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


def save_state(cfg, st, then=None):
    """Write the state whole and sync its folder; then call then (the marks of
    the events that the state records are removed there); then write the lines
    of the journal of this update (later). A state with a value that JSON or
    UTF-8 cannot write is refused before the file is opened, and the file stays
    as it was."""
    import json
    import os
    lines = LATER[:]
    LATER.clear()
    data = json.dumps(st, ensure_ascii=False, indent=1, allow_nan=False).encode("utf-8")
    d = state_dir(cfg)
    tmp = d / "state.json.tmp"
    with open(tmp, "wb") as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, d / "state.json")
    sync_dir(d)
    if then is not None:
        then()
    for at, fields in lines:  # the journal of this update, once the state is written
        log(cfg, at, **fields)


# The lines of the journal that describe an update of the state, written by
# save_state once the state is: a line without its change never stands alone.
LATER = []


def later(h, **fields):
    LATER.append((h, fields))


def log(cfg, h, **fields):
    """A line of the journal of the host, state_dir/log.jsonl. A line with a
    value that JSON or UTF-8 cannot write is refused before the file is opened."""
    import json
    import os
    import triel_host

    def text(x):  # a value of no JSON type as its text; an integer too long to read is refused
        if isinstance(x, LongInteger):
            raise TypeError(f"{x!r} cannot be written")
        return str(x)

    line = json.dumps({"at": triel_host.exact(h), **fields}, ensure_ascii=False, default=text,
                      allow_nan=False)
    data = (line + "\n").encode("utf-8")
    with open(state_dir(cfg) / "log.jsonl", "ab") as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())


def note(cfg, h, **fields):
    """A line of the journal that is written if it can be: the reason of the
    exit is said on standard error in any case."""
    try:
        log(cfg, h, **fields)
    except Exception:  # noqa: B902
        pass


def write_trace(cfg, tid, trace):
    """The trace of the decision on the call tid in state_dir/traces; a trace
    with a value that JSON or UTF-8 cannot write is refused before the file is
    opened."""
    import json
    safe = "".join(c if c.isalnum() or c in "_-" else "_" for c in tid)
    path = state_dir(cfg) / "traces" / f"{safe}.json"
    data = json.dumps(trace, ensure_ascii=False, indent=1, allow_nan=False).encode("utf-8")
    path.parent.mkdir(exist_ok=True)
    path.write_bytes(data)
    return path


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


# --- Marks of the events after a call -------------------------------------------------

def mark_name(tid, event) -> str:
    """<sha256 of the UTF-8 of tool_use_id, 64 hexadecimal digits>.<post|failure|denied>."""
    import hashlib
    return hashlib.sha256(tid.encode("utf-8")).hexdigest() + "." + event


class Mark:
    """A mark that this process created: its path, and the descriptor that holds
    its flock until the event ends."""

    def __init__(self, path, fd):
        self.path, self.fd = path, fd

    def remove(self):
        import os
        os.unlink(self.path)
        sync_dir(self.path.parent)

    def close(self):
        import os
        if self.fd is not None:
            os.close(self.fd)
            self.fd = None


def create_mark(cfg, event, fields):
    """The mark of an event after a call, created whole: its fields (MARK_KEYS)
    as one JSON object, written with ensure_ascii and allow_nan=False to a
    temporary file unrecorded/.tmp-SUFFIX that this process locks with flock,
    synced, then linked to the name of the mark; the lock belongs to the inode
    and stays on the mark. Returns the Mark, or None when the mark of this event
    of the call is there already (it is left as it is); raises OSError or
    ValueError when it cannot be created, also on a filesystem without hard
    links."""
    import fcntl
    import json
    import os
    import secrets
    d = state_dir(cfg) / "unrecorded"
    d.mkdir(mode=0o700, exist_ok=True)
    data = json.dumps(fields, ensure_ascii=True, allow_nan=False).encode("ascii")
    path = d / mark_name(fields["tool_use_id"], event)
    tmp = d / f".tmp-{secrets.token_hex(8)}"
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
        view = memoryview(data)
        while view:
            view = view[os.write(fd, view):]
        os.fsync(fd)
        try:
            os.link(tmp, path)
            created = True
        except FileExistsError:
            created = False
        os.unlink(tmp)
        sync_dir(d)
    except BaseException:  # noqa: B902 - no part of a mark stays under any name
        os.close(fd)
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise
    if not created:
        os.close(fd)
        return None
    return Mark(path, fd)


def probe_mark(path):
    """(live, the bytes of the mark or None): a mark is live while the event that
    created it holds its flock."""
    import fcntl
    import os
    try:
        fd = os.open(path, os.O_RDONLY)
    except FileNotFoundError:
        raise
    except OSError:
        return False, None
    try:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            live = True
        else:
            live = False
            fcntl.flock(fd, fcntl.LOCK_UN)
        chunks = []
        try:
            while True:
                b = os.read(fd, 65536)
                if not b:
                    break
                chunks.append(b)
            data = b"".join(chunks)
        except OSError:
            data = None
    finally:
        os.close(fd)
    return live, data


def no_constant(c):
    raise ValueError(f"not JSON: {c}")


def mark_fields(data, name):
    """The fields of a mark, with came as exact seconds under the key exact; None
    when the mark cannot be read: its content does not pass the strict parse
    (UTF-8, JSON without NaN, Infinity or -Infinity, a finite number, no
    value that the gate cannot write), is not an object with exactly the keys
    MARK_KEYS, or does not agree with its name and its form."""
    import json
    import triel_host
    if data is None:
        return None
    try:
        x = json.loads(data.decode("utf-8"), parse_constant=no_constant)
    except (ValueError, RecursionError):
        return None
    if not (isinstance(x, dict) and set(x) == set(MARK_KEYS)) or unwritable(x, "") is not None:
        return None
    sha, event = name.split(".")
    if not (isinstance(x["tool_use_id"], str) and mark_name(x["tool_use_id"], event) == name
            and x["event"] == EVENTS[event]):
        return None
    if not all(isinstance(x[k], str) for k in ("came", "tool_name", "subject", "action")):
        return None
    if not isinstance(x["input_written"], bool) or (not x["input_written"]
                                                    and x["tool_input"] is not None):
        return None
    try:
        exact = triel_host.seconds(x["came"])
    except (ValueError, ArithmeticError):
        return None
    return dict(x, exact=exact)


def marks(cfg, tid=None):
    """The marks in state_dir/unrecorded, of the call tid or of every call: each
    {"name", "path", "event", "live", "fields"} (fields None when the mark cannot
    be read), the readable ones by came, then by name, then the others by name.
    Only a name <64 hexadecimal digits>.<post|failure|denied> is a mark; a mark
    that is removed while it is read is left out."""
    import os
    import re
    d = state_dir(cfg) / "unrecorded"
    if not os.path.lexists(d):
        return []
    pattern = re.compile(r"[0-9a-f]{64}\.(post|failure|denied)")
    prefix = None if tid is None else mark_name(tid, "")
    found = []
    for name in os.listdir(d):
        m = pattern.fullmatch(name)
        if m is None or (prefix is not None and not name.startswith(prefix)):
            continue
        try:
            live, data = probe_mark(d / name)
        except FileNotFoundError:
            continue
        found.append({"name": name, "path": d / name, "event": EVENTS[m.group(1)], "live": live,
                      "fields": mark_fields(data, name)})
    readable = sorted((k for k in found if k["fields"] is not None),
                      key=lambda k: (k["fields"]["exact"], k["name"]))
    return readable + sorted((k for k in found if k["fields"] is None), key=lambda k: k["name"])


def mark_reason(k) -> str:
    f = k["fields"]
    if f is None:
        return (f"a mark of an event that was not recorded cannot be read: unrecorded/{k['name']}; "
                "every action is held until the operator runs gate.py resolve ID for the call "
                "whose sha256 begins its name")
    if k["live"]:
        return f"waits for the {k['event']} of the call {f['tool_use_id']} to be recorded"
    return (f"the {k['event']} of the call {f['tool_use_id']} was not recorded; every action is "
            f"held until the operator runs gate.py resolve {f['tool_use_id']}")


def remove_marks(ks):
    import os
    for k in ks:
        os.unlink(k["path"])
    if ks:
        sync_dir(ks[0]["path"].parent)


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
    for name, x in (("tool_name", tool), ("tool_use_id", tid)):
        if not (writable_text(x) and x):
            raise Held([f"the input of the hook has no {name} that the gate can write"])
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
            ks = marks(cfg)
            if ks:
                raise Held([mark_reason(ks[0])])
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
            bad = unwritable(hook.get("tool_input"))
            if bad:
                raise Held([input_reason(bad)])
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
            trace_path = write_trace(cfg, tid, trace)
            code, out, err = child(cfg, [str(Path(cfg["repo"]) / "parser" / "triel.py"), "check",
                                         cfg["spec"], str(trace_path), "--last", "--json",
                                         "--evaluator", cfg["evaluator"]])
            reasons = judge(cfg, code, out, err, trace, pair)
            if reasons:
                raise Held(reasons + [f"trace: {trace_path}"])
        except Held as e:
            try:
                save_state(cfg, st)  # the lines of its update (unknown) come before held
            finally:
                log(cfg, h, event="held", tool_use_id=tid, tool_name=tool, reasons=e.reasons)
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
    """Record the outcome of a call of a mapped tool of a managed server. The
    mark of the event is created before the wait for the lock and removed once
    the state with the event is written; an event that is not recorded leaves
    its mark and a line "EVENT not recorded" in the journal, if it can be
    written."""
    import triel_host
    kind, m = classify(cfg, hook)
    tid, tool = hook.get("tool_use_id"), hook.get("tool_name")
    if kind == "hold":
        log(cfg, h, event=f"{event} ignored", tool_use_id=tid, tool_name=tool, reasons=[m])
        return 0
    if kind != "managed":
        return 0
    for name, x in (("tool_name", tool), ("tool_use_id", tid)):
        if not (writable_text(x) and x):
            reasons = [f"the input of the hook has no {name} that the gate can write"]
            note(cfg, h, event=f"{event} not recorded",
                 tool_use_id=tid if writable_text(tid) else None,
                 tool_name=tool if writable_text(tool) else None, reasons=reasons)
            raise Held(reasons)
    tool_input = hook.get("tool_input")
    bad = unwritable(tool_input)
    no_mark, mark, recorded = [], None, []
    try:
        mark = create_mark(cfg, event, {
            "tool_use_id": tid, "event": EVENTS[event], "came": triel_host.exact(h),
            "tool_name": tool, "subject": m["subject"], "action": m["action"],
            "tool_input": None if bad else tool_input, "input_written": bad is None})
    except Exception as e:  # noqa: B902 - the event goes on without its mark
        no_mark.append(f"the mark of the event was not created: {described(e) or 'an exception'}")
    try:
        if bad:
            raise Held([input_reason(bad)])
        with locked(cfg):
            st = load_state(cfg)
            if st is None:  # without an activation the gate allowed no call
                recorded.append(True)
                if mark:
                    mark.remove()
                log(cfg, h, event=f"{event} without a state", tool_use_id=tid, tool_name=tool)
                return 0
            stray = record(cfg, st, hook, h, event, m, tid, tool)

            def written():  # the state with the event is written: its mark goes
                recorded.append(True)
                if mark:
                    mark.remove()

            try:
                save_state(cfg, st, then=written)
            finally:  # a line that describes no change of the state, after those that do
                if stray:
                    log(cfg, h, **stray)
        return 0
    except Exception as e:  # noqa: B902 - not recorded: the mark stays, and the journal says so
        if recorded:
            raise
        reasons = (e.reasons if isinstance(e, Held) else [failed(e)]) + no_mark
        note(cfg, h, event=f"{event} not recorded", tool_use_id=tid, tool_name=tool, reasons=reasons)
        raise Held(reasons) from None
    finally:
        if mark:
            mark.close()


def record(cfg, st, hook, h, event, m, tid, tool):
    """The event in the state; the line of the journal of an event for a call
    that is not pending, which describes no change of the state, or None."""
    import math
    from decimal import Decimal, InvalidOperation
    import triel_host
    expire(cfg, st, h)
    rec, where = find(st, tid)
    if event == "post":
        executed_at = h
        d = hook.get("duration_ms")
        finite = isinstance(d, int) or (isinstance(d, float) and math.isfinite(d))
        if finite and not isinstance(d, bool) and d >= 0:
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
                conflict(st, tid, h, "PostToolUse came for a call recorded as not executed")
            elif not same:
                conflict(st, tid, h, "the late PostToolUse has another input than PreToolUse")
        elif any(x["tool_use_id"] == tid for x in st["history"]):
            conflict(st, tid, h, "a PostToolUse came for a call already in the history")
        else:
            rec = {"tool_name": tool, "tool_input": hook.get("tool_input"),
                   "subject": m["subject"], "action": m["action"],
                   "decided": triel_host.exact(executed_at), "data": {}}
            execute(cfg, st, tid, rec, executed_at, hook.get("tool_input"), h)
            conflict(st, tid, h, "PostToolUse came for a call the gate did not allow")
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
            error = hook.get("error")
            later(h, event="not executed", tool_use_id=tid, tool_name=rec["tool_name"],
                  why=why, error=error if writable_text(error) else None)
        else:
            why = "PostToolUseFailure of a tool that the configuration does not declare atomic"
            st["unknown"][tid] = dict(rec, why=why)
            later(h, event="unknown", tool_use_id=tid, tool_name=rec["tool_name"], why=why)
    else:
        return {"event": f"{event} for a call that is not pending", "tool_use_id": tid,
                "tool_name": tool, "recorded_as": where}
    return None


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
        conflict(st, tid, h, f"the host module did not take the execution: "
                             f"{type(e).__name__}: {e}")


def conflict(st, tid, h, why):
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
        h = now()  # the time of the activation, given to the host module
        with quiet():
            answers = host_module(cfg).answers(None, moment(h), factors, cfg["host_options"])
        # Once the module has answered, the clock bounds the readings: one its source stamped
        # while the module answered is later than the activation, and not from the future.
        rec, st["readings"], reasons = triel_host.activation(factors, answers, h, until=now())
        if reasons:
            raise Held(["activation refused"] + reasons)
        st["activation"] = rec
        later(h, event="activated", time=iso(triel_host.floor_s(h)))
        save_state(cfg, st)
    return 0


def resolve(cfg, args, h) -> int:
    """The outcome of the call ID that the operator gives, also for a call with
    marks of events that were not recorded (README.md, "Commands of the
    operator")."""
    from decimal import Decimal
    import triel_host
    tid = args.id
    if not tid or [args.executed, args.not_executed, args.drop_mark].count(True) != 1:
        raise Held(["resolve ID takes --executed --at TIME, --not-executed or --drop-mark"])
    if args.executed != (args.at is not None):
        raise Held(["--at TIME goes with --executed, and only with it"])
    with locked(cfg):
        st = load_state(cfg)
        ks = marks(cfg, tid)
        live = [k for k in ks if k["live"]]
        if live:
            raise Held([f"the {live[0]['event']} of the call {tid} is still being recorded; run "
                        "resolve again"])
        names = [k["name"] for k in ks]
        if args.drop_mark:
            if not ks:
                raise Held([f"the call {tid} has no mark of an event that was not recorded"])
            log(cfg, h, event="mark dropped by the operator", tool_use_id=tid, marks=names)
            remove_marks(ks)
            return 0
        if st is None:
            raise Held(["the mandate has no state"])
        post = next((k for k in ks if k["event"] == "PostToolUse"), None)
        if post is not None and args.not_executed:
            raise Held([f"the PostToolUse of the call {tid} came: it was executed; resolve it with "
                        "--executed --at TIME"])

        def at_time(decided):
            at = triel_host.seconds(args.at)
            t = None if decided is None else triel_host.decision_time(Decimal(decided))
            if t is not None and at < t:
                raise Held([f"--at {args.at} is earlier than the time of the decision, {iso(t)}"])
            if t is None and st["activation"] and at < Decimal(st["activation"]["time"]):
                raise Held([f"--at {args.at} is earlier than the activation"])
            if at > h:
                raise Held([f"--at {args.at} is later than the host clock"])
            if post is not None and post["fields"] is not None:
                came = post["fields"]["exact"]
                if at > (came if t is None else max(came, t)):
                    raise Held([f"--at {args.at} is later than the PostToolUse of the call {tid} "
                                "came"])
            return at

        def done():  # the state with the outcome, then the marks of the call go, then the journal
            if ks:
                later(h, event="marks removed", tool_use_id=tid, marks=names)
            save_state(cfg, st, then=(lambda: remove_marks(ks)) if ks else None)

        def refused_by_the_module():
            return Held([st["conflicts"][tid]["why"],
                         f"the conflict on the call {tid} is recorded; gate.py resolve {tid} "
                         "--executed --at TIME gives the fact to the module again"])

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
            done()
            return 0
        rec, where = find(st, tid)
        executed = next((x for x in st["history"] if x["tool_use_id"] == tid), None)
        if ks and executed is not None:  # in the history, without a conflict
            if not args.executed:
                raise Held([f"the call {tid} is in the history as executed"])
            at_time(executed["decided"])
            done()
            return 0
        if ks and rec is None:  # no record of the call: only its marks
            if args.executed:
                k = post or ks[0]
                if k["fields"] is None:
                    raise Held([f"the mark unrecorded/{k['name']} cannot be read, so the tool, the "
                                f"subject and the action of the call {tid} are not known; the "
                                f"operator decides, and may run gate.py resolve {tid} --drop-mark"])
                at = at_time(None)
                f = k["fields"]
                rec = {"tool_name": f["tool_name"], "tool_input": None, "subject": f["subject"],
                       "action": f["action"], "decided": triel_host.exact(at), "data": {}}
                execute(cfg, st, tid, rec, at, history_input(ks, None), h)
                if tid in st["conflicts"]:  # the host module did not take the fact
                    done()
                    raise refused_by_the_module()
            done()
            return 0
        if where not in ("pending", "unknown") and not (ks and where == "not_executed"):
            raise Held([f"no pending or unknown call {tid}"])
        if args.executed:
            at = at_time(rec["decided"])
            del st[where][tid]
            execute(cfg, st, tid, rec, at, history_input(ks, rec) if ks
                    else rec.get("post_input", rec["tool_input"]), h)
            if tid in st["conflicts"]:  # the host module did not take the fact
                done()
                raise refused_by_the_module()
        elif where != "not_executed":
            del st[where][tid]
            st["not_executed"][tid] = dict(rec, why="resolve --not-executed")
            later(h, event="not executed", tool_use_id=tid, why="resolve --not-executed")
        done()
    return 0


def history_input(ks, rec):
    """The input that resolve --executed gives the history of a call with marks:
    that of its mark of PostToolUse, or else of its other mark, when it is
    written; null when it is not written or the mark cannot be read, never the
    input of the record, since the host module would count an input the call may
    not have had."""
    k = next((k for k in ks if k["event"] == "PostToolUse"), ks[0])
    f = k["fields"]
    if f is None or not f["input_written"]:
        return None
    if rec is not None:
        recorded = rec.get("post_input", rec["tool_input"])
        if canonical(recorded) == canonical(f["tool_input"]):
            return recorded
    return f["tool_input"]


def status(cfg, h) -> int:
    """The state at the host clock h, without changing it: the age of each
    pending call and the seconds until its outcome becomes unknown; a pending
    call whose time is over is shown as unknown; and the marks of the events
    that were not recorded, read under the same lock as the state."""
    import json
    from decimal import Decimal
    with locked(cfg):
        st = load_state(cfg)
        ks = marks(cfg)
    ids = set()
    if st is not None:
        for where in ("pending", "unknown", "not_executed", "conflicts"):
            ids |= set(st[where])
        ids |= {x["tool_use_id"] for x in st["history"]}
    unrecorded = []
    for k in ks:
        f = k["fields"]
        if f is not None:
            unrecorded.append({"tool_use_id": f["tool_use_id"], "event": k["event"],
                               "came": f["came"], "live": k["live"]})
            continue
        u = {"name": k["name"], "event": k["event"], "live": k["live"]}
        known = sorted(i for i in ids if isinstance(i, str) and k["name"].startswith(mark_name(i, "")))
        if known:
            u["tool_use_id"] = known[0]
        unrecorded.append(u)
    if st is None:
        print(json.dumps({"activation": None, "unrecorded": unrecorded}, ensure_ascii=False,
                         indent=1))
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
                      "not_executed": sorted(st["not_executed"]), "unrecorded": unrecorded},
                     ensure_ascii=False, indent=1))
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
