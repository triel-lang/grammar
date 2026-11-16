"""
An example host module for the TRIEL gate (README.md in this folder): the data
of the host in files that the host and its channel of approval write and the
agent cannot (README.md, "What the agent must not be able to change").

The gate calls two functions:

  answers(call, now, factors, options)
      The answers of the host for the decision on call (None for the
      activation) at the host clock now (an aware datetime): for each
      declared factor of factors, its value or None for a factor without
      MAX_AGE, and a triel_host.Reading or triel_host.NO_NEW_READING for a
      factor with MAX_AGE (parser/triel_host.py). Derived values are computed
      here, never taken from the agent.

  executed(fact, options)
      A call was executed: fact has tool_use_id, tool_name, subject, action,
      tool_input (the input it was executed with) and time (the time of
      execution E). Everything that depends on executed actions is updated
      from these facts only. The gate may give the same fact twice; each file
      that the module writes remembers the tool_use_ids it has taken, and a
      fact given again adds only what a file does not have yet, except the
      time of execution, which follows the last fact.

The options are the host_options of the configuration, in one of two forms.

The example of README.md (config.example.json, mandate.triel):
  data_file         the data of the owner, written by the host:
                      {"values":   {FACTOR: VALUE},                factors without MAX_AGE
                       "readings": {FACTOR: {"value": V, "time": TIME}},
                       "payees":   [PAYEE]}                        the owner's list
  approvals_file    the approvals and revocations of the owner, JSON Lines that
                    the channel of approval appends and nothing else writes:
                      {"type": "approval", "id": ID, "tool": TOOL,
                       "tool_input": {...}, "granted": TIME}
                      {"type": "revocation", "id": ID, "time": TIME}
  ledger_file       written by this module only, never by the channel:
                      {"selected": {TOOL_USE_ID: ID or null},   the approval chosen
                       "spent":    {ID: TOOL_USE_ID},           ids spent by executions
                       "taken":    [TOOL_USE_ID]}               facts taken
  executions_file   written by this module only:
                      {"executed": {TOOL_USE_ID: {"tool": TOOL, "tool_input": {...},
                                                  "time": E}}}
                    a record with other keys, or whose tool is not a string,
                    makes the file unreadable
  approval_factors  {"approved": F, "age": F, "revoked": F}: the Boolean, the
                    Integer and the Boolean factor of the approval of the call
  payment           {"tool": TOOL, "fields": [KEY], "day_total": F,
                     "payee_listed": F}: the payment tool, the keys of its input
                    (among them "to" and "amount"), the Decimal factor of the
                    total of the day with this payment, and the Boolean factor of
                    the payee
The activation creates ledger_file and executions_file if they do not exist;
later a missing file cannot be read. approvals_file must exist (it may be empty).

What answers gives for the call (README.md, "What the host module computes and what
the monitor decides"):
  - the approval: among the approvals of the tool of the call whose tool_input
    has the same JSON value as the input of the call and whose id no execution
    has spent, exactly one is chosen, and its id is recorded for the
    tool_use_id in ledger_file; approved is true, age is the whole number of
    seconds ceil(now - granted), revoked is true when approvals_file holds a
    revocation of its id, whatever its time. With none, approved is false and
    age and revoked have no value; with more than one, none of the three has a
    value. granted is read as triel_host.seconds reads a time (ISO-8601 UTC
    with Z, or seconds); any other form, or a time later than now, gives the
    age no value. A revocation of the id that is not of the form above gives
    revoked no value, unless a revocation of the id of that form is there too.
  - the total of the day: the amount of the call and the amounts of the
    executed calls of the payment tool whose E is on the calendar day of UTC
    of ceil(now), the clock of the module rounded up (T, the clock of the
    decision rounded up, is read later). An amount is a decimal string of
    digits with an optional fraction, or a JSON number; it must be greater
    than 0. A float is read as Decimal(repr(x)).
  - the total and the age are computed exactly, in the context EXACT; a
    result that 60 significant digits do not hold has no value.
  - the payee: true when "to" is on the owner's list. A string is the same
    payee only if it is the whole string; two hexadecimal addresses (0x and
    hexadecimal digits) are compared without regard to case.
Unknown is not no: a factor the module cannot compute has no value (None),
never false or 0. approvals_file or ledger_file that cannot be read leaves the
three factors of the approval without a value; data_file, the daily limit, the
list and the payee; executions_file, the total of the day. A call of the
payment tool whose input is not an object or has a key outside fields leaves
all five factors of the call without a value. answers raises no exception on
reading the data; it raises ValueError for options it cannot use, and the gate
then holds every call.

What executed does with a fact: in ledger_file, unless the tool_use_id is
taken, the approval chosen for it is spent; when no approval was chosen for it,
or the call was executed with another input than that of the chosen approval,
every standing approval of the tool and the input of the fact is spent too.
The ids spent and the tool_use_id are written in one replacement of the file.
Then, in executions_file, the call with its time E, or, for a tool_use_id that
is there, the time of the last fact. executed reads approvals_file, ledger_file
and executions_file; if a file cannot be read or written, it raises the
exception, and the gate records a conflict and holds every action (README.md,
"The host module").

The earlier form, without the keys above:
  data_file  the absolute path of the JSON file;
  approval   the name of a Boolean factor (no MAX_AGE) that is true when the
             file holds an approval of this very call: its action and its input;
  counters   {FACTOR: ACTION}: an Integer factor (no MAX_AGE) that is the
             number of executed calls of ACTION.
  The JSON file, read with its numbers as Decimal:
    {"values":    {FACTOR: VALUE},                       factors without MAX_AGE
     "readings":  {FACTOR: {"value": V, "time": TIME}},  the last reading of a
                                                         factor with MAX_AGE, with
                                                         the time its source stamped
     "approvals": [{"action": A, "tool_input": {...}}],
     "executed":  {TOOL_USE_ID: ACTION}}
  executed removes the approval of the call, counts the call, and ignores a
  fact whose tool_use_id is known; it reads, changes and replaces the whole
  file. The host changes the file only while no call is pending (gate.py
  status), or under a lock of its own that this module takes too. In this
  form answers reads the file without catching an error: a file that cannot
  be read raises, and the gate holds the call, since under DEFAULT or PRESENT
  a factor without a value could allow it.

In both forms, a factor without MAX_AGE that is not in values has no value; a
factor with MAX_AGE that is not in readings has no new reading.
"""
import json
import os
import re
from decimal import (ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN, Context, Decimal, Inexact,
                     InvalidOperation, Overflow, localcontext)

from triel_host import NO_NEW_READING, Reading, exact, iso, seconds

DAY = 86400
HEX = re.compile(r"0[xX][0-9a-fA-F]+")
AMOUNT = re.compile(r"[0-9]+(\.[0-9]+)?")
NEW_KEYS = ("approvals_file", "ledger_file", "executions_file", "approval_factors", "payment")
APPROVAL = {"type", "id", "tool", "tool_input", "granted"}
REVOCATION = {"type", "id", "time"}
EXECUTION = {"tool", "tool_input", "time"}
# The arithmetic of the total of the day and of the age of an approval: exact, or no
# value. A result that 60 significant digits do not hold raises Inexact.
EXACT = Context(prec=60, rounding=ROUND_HALF_EVEN, traps=[Inexact, InvalidOperation, Overflow])


def answers(call, now, factors, options):
    if any(k in options for k in NEW_KEYS):
        return _answers(call, now, factors, options)
    return _answers_earlier(call, factors, options)


def executed(fact, options):
    if any(k in options for k in NEW_KEYS):
        return _executed(fact, options)
    return _executed_earlier(fact, options)


# --- Files ------------------------------------------------------------------------

def _no_constant(c):
    raise ValueError(f"not JSON: {c}")


def _json(text):
    return json.loads(text, parse_float=Decimal, parse_constant=_no_constant)


def _load(path, what, keys):
    """The JSON object of a file with exactly these keys; the exception of open or
    of json, or ValueError, when it cannot be read."""
    with open(path, encoding="utf-8") as f:
        x = _json(f.read())
    if not (isinstance(x, dict) and set(x) == set(keys)):
        raise ValueError(f"{path} is not {what}")
    return x


def _ledger(options):
    x = _load(options["ledger_file"], "a ledger of approvals", ("selected", "spent", "taken"))
    if not (isinstance(x["selected"], dict) and isinstance(x["spent"], dict)
            and isinstance(x["taken"], list)):
        raise ValueError(f"{options['ledger_file']} is not a ledger of approvals")
    return x


def _executions(options):
    x = _load(options["executions_file"], "a record of executions", ("executed",))
    if not (isinstance(x["executed"], dict)
            and all(isinstance(v, dict) and set(v) == EXECUTION and isinstance(v["tool"], str)
                    for v in x["executed"].values())):
        raise ValueError(f"{options['executions_file']} is not a record of executions")
    return x


def _channel(options):
    """The approvals of approvals_file, and for each id the revocations of it, each
    True when it has the form of a revocation and False otherwise. A line that is
    not a JSON object with a string id and a type, or an approval not of its form,
    makes the whole file unreadable (ValueError)."""
    with open(options["approvals_file"], encoding="utf-8") as f:
        text = f.read()
    approvals, revocations = [], {}
    for line in text.split("\n"):
        if not line.strip():
            continue
        r = _json(line)
        if not (isinstance(r, dict) and isinstance(r.get("id"), str)
                and r.get("type") in ("approval", "revocation")):
            raise ValueError(f"{options['approvals_file']}: a line that is not an approval "
                             "or a revocation")
        if r["type"] == "approval":
            if not (set(r) == APPROVAL and isinstance(r["tool"], str)
                    and isinstance(r["tool_input"], dict)):
                raise ValueError(f"{options['approvals_file']}: an approval not of its form")
            approvals.append(r)
        else:
            revocations.setdefault(r["id"], []).append(set(r) == REVOCATION and _time(r["time"]))
    return approvals, revocations


def _time(t):
    try:
        seconds(t)
        return True
    except Exception:  # noqa: B902 - any form that is not a time
        return False


def _write(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(json.dumps(data, default=str, indent=1))
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def _or_none(read, *args):
    """What read gives, or None when it raises: on reading, unknown is not no."""
    try:
        return read(*args)
    except Exception:  # noqa: B902 - whatever the failure, the data are unknown
        return None


# --- Values ------------------------------------------------------------------------

def _norm(x):
    """A JSON value for comparison: numbers as Decimal (a float by its repr), and
    true and false apart from the numbers 1 and 0."""
    if isinstance(x, bool) or x is None:
        return ("literal", x)
    if isinstance(x, float):
        return ("number", Decimal(repr(x)))
    if isinstance(x, (int, Decimal)):
        return ("number", Decimal(x))
    if isinstance(x, str):
        return ("string", x)
    if isinstance(x, list):
        return ("array", [_norm(y) for y in x])
    if isinstance(x, dict):
        return ("object", {k: _norm(v) for k, v in x.items()})
    return ("other", repr(x))


def _same_input(a, b):
    """Two inputs with the same JSON value."""
    return _norm(a) == _norm(b)


def _amount(x):
    """A positive amount as Decimal, or None."""
    if isinstance(x, bool):
        return None
    if isinstance(x, float):
        d = Decimal(repr(x))
    elif isinstance(x, (int, Decimal)):
        d = Decimal(x)
    elif isinstance(x, str) and AMOUNT.fullmatch(x):
        d = Decimal(x)
    else:
        return None
    return d if d.is_finite() and d > 0 else None


def _payee(s):
    return ("hex", s.lower()) if HEX.fullmatch(s) else ("text", s)


def _ceil(x):
    return int(x.to_integral_value(rounding=ROUND_CEILING))


def _floor(x):
    return int(x.to_integral_value(rounding=ROUND_FLOOR))


# --- The example of README.md -----------------------------------------------------------

def _check(factors, options):
    """The options of the example, or ValueError."""
    if "approval" in options or "counters" in options:
        raise ValueError("host_options: approval and counters belong to the earlier form, "
                         "not to approvals_file")
    for k in ("data_file", "approvals_file", "ledger_file", "executions_file"):
        if not (isinstance(options.get(k), str) and os.path.isabs(options[k])):
            raise ValueError(f"host_options: {k} is not an absolute path")
    af = options.get("approval_factors")
    if not (isinstance(af, dict) and set(af) == {"approved", "age", "revoked"}):
        raise ValueError("host_options: approval_factors names approved, age and revoked")
    pay = options.get("payment")
    if not (isinstance(pay, dict) and set(pay) == {"tool", "fields", "day_total", "payee_listed"}
            and isinstance(pay["fields"], list) and {"to", "amount"} <= set(pay["fields"])):
        raise ValueError("host_options: payment names tool, fields (with to and amount), "
                         "day_total and payee_listed")
    named = list(af.values()) + [pay["day_total"], pay["payee_listed"]]
    for name in named:
        if name not in factors or factors[name]["stale"] != "none":
            raise ValueError(f"host_options: {name} is not a factor without MAX_AGE")
    return af, pay


def _answers(call, now, factors, options):
    af, pay = _check(factors, options)
    data = _or_none(_data, options)
    computed = dict.fromkeys(list(af.values()) + [pay["day_total"], pay["payee_listed"]])
    if call is None:  # the activation
        _start(options)
    else:
        now_s = seconds(now)
        tool_input = call.get("tool_input")
        if call.get("tool_name") != pay["tool"] or _in_schema(tool_input, pay):
            computed.update(_approval(call, now_s, options, af))
        if call.get("tool_name") == pay["tool"] and _in_schema(tool_input, pay):
            computed[pay["day_total"]] = _day_total(tool_input, now_s, options, pay)
            computed[pay["payee_listed"]] = _listed(tool_input, data)
    out = {}
    for name, f in factors.items():
        if name in computed:
            out[name] = computed[name]
        elif f["stale"] == "none":
            out[name] = _value(data, name)
        else:
            out[name] = _reading(data, name)
    return out


def _data(options):
    with open(options["data_file"], encoding="utf-8") as f:
        x = _json(f.read())
    if not isinstance(x, dict):
        raise ValueError(f"{options['data_file']} is not a JSON object")
    return x


def _value(data, name):
    values = data.get("values") if data is not None else None
    return values.get(name) if isinstance(values, dict) else None


def _reading(data, name):
    readings = data.get("readings") if data is not None else None
    if not isinstance(readings, dict) or name not in readings:
        return NO_NEW_READING
    r = readings[name]
    return Reading(r.get("value"), r.get("time")) if isinstance(r, dict) else Reading(None, None)


def _start(options):
    """At the activation, the files of the module, if they do not exist yet."""
    for key, empty in (("ledger_file", {"selected": {}, "spent": {}, "taken": []}),
                       ("executions_file", {"executed": {}})):
        if not os.path.lexists(options[key]):
            try:
                _write(options[key], empty)
            except Exception:  # noqa: B902 - the file then cannot be read, and is unknown
                pass


def _in_schema(tool_input, pay):
    return isinstance(tool_input, dict) and set(tool_input) <= set(pay["fields"])


def _approval(call, now_s, options, af):
    """The three factors of the approval of the call, and the choice recorded."""
    unknown = dict.fromkeys(af.values())
    ledger = _or_none(_ledger, options)
    channel = _or_none(_channel, options)
    if ledger is None or channel is None:
        return unknown
    approvals, revocations = channel
    found = [a for a in approvals if a["tool"] == call.get("tool_name")
             and a["id"] not in ledger["spent"]
             and _same_input(a["tool_input"], call.get("tool_input"))]
    chosen = found[0] if len(found) == 1 else None
    ledger["selected"][call["tool_use_id"]] = chosen["id"] if chosen else None
    try:
        _write(options["ledger_file"], ledger)
    except Exception:  # noqa: B902 - the execution could not spend what was not recorded
        return unknown
    if len(found) > 1:
        return unknown
    if not found:
        return {af["approved"]: False, af["age"]: None, af["revoked"]: None}
    revs = revocations.get(chosen["id"], [])
    revoked = True if any(revs) else (None if revs else False)
    return {af["approved"]: True, af["age"]: _age(chosen["granted"], now_s),
            af["revoked"]: revoked}


def _age(granted, now_s):
    try:
        g = seconds(granted)
        if g > now_s:
            return None
        with localcontext(EXACT):
            return _ceil(now_s - g)
    except Exception:  # noqa: B902 - not a time of the channel, or no exact age: no value
        return None


def _day_total(tool_input, now_s, options, pay):
    amount = _amount(tool_input.get("amount"))
    ex = _or_none(_executions, options)
    if amount is None or ex is None:
        return None
    day = _ceil(now_s) // DAY  # the clock of the module rounded up, as T is in the trace
    total = amount
    for rec in ex["executed"].values():
        if rec["tool"] != pay["tool"]:
            continue
        try:
            e = seconds(rec["time"])
        except Exception:  # noqa: B902 - an execution whose day is unknown
            return None
        if _floor(e) // DAY != day:
            continue
        spent = rec["tool_input"]
        a = _amount(spent.get("amount")) if isinstance(spent, dict) else None
        if a is None:
            return None
        try:
            with localcontext(EXACT):
                total += a
        except ArithmeticError:  # Inexact among them: a total that is not exact is unknown
            return None
    return total


def _listed(tool_input, data):
    to = tool_input.get("to")
    payees = data.get("payees") if data is not None else None
    if not (isinstance(to, str) and isinstance(payees, list)
            and all(isinstance(p, str) for p in payees)):
        return None
    return any(_payee(p) == _payee(to) for p in payees)


def _executed(fact, options):
    tid = fact["tool_use_id"]
    ledger = _ledger(options)
    if tid not in ledger["taken"]:
        approvals, _ = _channel(options)

        def of(a):  # an approval of the tool and the input that were executed
            return a["tool"] == fact["tool_name"] and _same_input(a["tool_input"],
                                                                  fact["tool_input"])
        chosen = ledger["selected"].get(tid)
        ids = [chosen] if chosen is not None else []
        if chosen is None or not any(a["id"] == chosen and of(a) for a in approvals):
            # No choice, or the call was executed with another input than the one
            # decided on: every standing approval of the executed input is spent too.
            ids += [a["id"] for a in approvals if of(a) and a["id"] not in ledger["spent"]]
        for i in ids:
            ledger["spent"].setdefault(i, tid)
        ledger["taken"].append(tid)
        _write(options["ledger_file"], ledger)  # the ids spent and the fact taken, at once
    ex = _executions(options)
    e = seconds(fact["time"])
    time = iso(int(e)) if e == int(e) else exact(e)
    rec = ex["executed"].get(tid)
    if rec is None:
        ex["executed"][tid] = {"tool": fact["tool_name"], "tool_input": fact["tool_input"],
                               "time": time}
        _write(options["executions_file"], ex)
    elif rec["time"] != time:  # the last fact the gate gave: resolve --executed --at
        rec["time"] = time
        _write(options["executions_file"], ex)


# --- The earlier form ---------------------------------------------------------------------

def _read(options):
    with open(options["data_file"], encoding="utf-8") as f:
        data = json.loads(f.read(), parse_float=Decimal)
    for k in ("values", "readings", "approvals", "executed"):
        data.setdefault(k, [] if k == "approvals" else {})
    return data


def _approved(data, call):
    return call is not None and any(
        a.get("action") == call["action"] and _same_input(a.get("tool_input"), call["tool_input"])
        for a in data["approvals"])


def _answers_earlier(call, factors, options):
    """As before: a file that cannot be read raises, and the gate holds the call. Under
    DEFAULT or PRESENT, a factor without a value could allow it."""
    data = _read(options)
    counters = options.get("counters", {})
    out = {}
    for name, f in factors.items():
        if name == options.get("approval"):
            out[name] = _approved(data, call)
        elif name in counters:
            out[name] = sum(1 for a in data["executed"].values() if a == counters[name])
        elif f["stale"] == "none":
            out[name] = data["values"].get(name)
        elif name in data["readings"]:
            r = data["readings"][name]
            out[name] = Reading(r.get("value"), r.get("time"))
        else:
            out[name] = NO_NEW_READING
    return out


def _executed_earlier(fact, options):
    data = _read(options)
    if fact["tool_use_id"] in data["executed"]:
        return
    data["executed"][fact["tool_use_id"]] = fact["action"]
    for i, a in enumerate(data["approvals"]):
        if a.get("action") == fact["action"] and _same_input(a.get("tool_input"), fact["tool_input"]):
            del data["approvals"][i]
            break
    _write(options["data_file"], data)
