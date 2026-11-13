"""
An example host module for the TRIEL gate (README.md in this folder): the data
of the host in one JSON file that the host writes and the agent cannot.

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
      from these facts only: here, the approval of the call is removed and the
      count of the executed calls of its action goes up. The gate may give the
      same fact twice; a fact whose tool_use_id is known is ignored.

options, the host_options of the configuration:
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
A factor without MAX_AGE that is not in values has no value; a factor with
MAX_AGE that is not in readings has no new reading.

executed reads, changes and replaces the whole file. The host changes the file
only while no call is pending (gate.py status), or under a lock of its own
that this module takes too.
"""
import json
import os
from decimal import Decimal

from triel_host import NO_NEW_READING, Reading


def _read(options):
    with open(options["data_file"], encoding="utf-8") as f:
        data = json.loads(f.read(), parse_float=Decimal)
    for k in ("values", "readings", "approvals", "executed"):
        data.setdefault(k, [] if k == "approvals" else {})
    return data


def _write(options, data):
    tmp = options["data_file"] + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(json.dumps(data, default=str, indent=1))
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, options["data_file"])


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


def _approved(data, call):
    return call is not None and any(
        a.get("action") == call["action"] and _same_input(a.get("tool_input"), call["tool_input"])
        for a in data["approvals"])


def answers(call, now, factors, options):
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


def executed(fact, options):
    data = _read(options)
    if fact["tool_use_id"] in data["executed"]:
        return
    data["executed"][fact["tool_use_id"]] = fact["action"]
    for i, a in enumerate(data["approvals"]):
        if a.get("action") == fact["action"] and _same_input(a.get("tool_input"), fact["tool_input"]):
            del data["approvals"][i]
            break
    _write(options, data)
