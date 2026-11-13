#!/usr/bin/env python3
"""
triel_host: the trace that a host, the system that runs an agent, builds
from its own records for the command triel check --last before an action of
the agent.

The trace is the JSON trace of evaluator/README.md ("The trace in JSON"):

  entry 0     the activation: the time and the data the host recorded when it
              gave the mandate;
  then        the actions the host recognised as executed, each with its tick
              entry, and an arrive entry for every accepted reading of a
              factor under MAX_AGE ... ON_STALE BLOCK, all in time order;
  last        a tick entry and the action, both at the time T of the decision
              and with the same data.

The functions are pure: the host clock, the records and the data are their
arguments, and nothing here reads a clock, a file or the environment. A time
is the exact number of seconds since 1970-01-01T00:00:00Z (a Decimal); the
trace counts whole seconds, so the time T of the decision is the host clock
rounded up, and the time of an arrive entry is the time of its source rounded
down: the trace never shows a reading fresher than it is. Where the trace
would say something other than the readings, the action is held: the reasons
are returned, and the host holds the action whenever there is one.

What the host gives for each declared factor (answers):
  - a factor without MAX_AGE: its value, or None for "no value";
  - a factor with MAX_AGE (ON_STALE BLOCK or ON_STALE USE_LAST): a Reading,
    its value and the unrounded time its source stamped it, or NO_NEW_READING.
A name that is not a declared factor, a field that its record type does not
declare, a declared factor without an answer and a value of another type are
errors, never coerced: triel check does not reject an unknown name in the
data, and under DEFAULT(f, d) or PRESENT(f) AND ... a factor that is missing
or misspelt would allow the action.

The readings of the factors with MAX_AGE are kept in a store (a dict that the
host keeps between decisions): for each factor the accepted readings, their
unrounded times in increasing order, and the time of two readings with one
time and different values, if any.
"""
import re
import sys
from datetime import datetime, timedelta, timezone
from decimal import ROUND_CEILING, ROUND_FLOOR, Decimal, InvalidOperation
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from triel_to_core import Translation, ident, parser, subtrees, tokens  # noqa: E402

EPOCH = datetime(1970, 1, 1, tzinfo=timezone.utc)
ISO = re.compile(r"([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})(\.[0-9]+)?Z")
DECIMAL = re.compile(r"-?[0-9]+(\.[0-9]+)?")


class HostError(Exception):
    """The host holds the action: the specification, the configuration or the
    host's data cannot give a trace."""


class Reading:
    """A reading of a factor with MAX_AGE: its value and the unrounded time
    its source stamped it (an aware datetime, an ISO-8601 UTC string with or
    without a fraction of a second, an int or a Decimal of seconds)."""

    def __init__(self, value, time):
        self.value, self.time = value, time

    def __repr__(self):
        return f"Reading({self.value!r}, {self.time!r})"


class _NoNewReading:
    def __repr__(self):
        return "NO_NEW_READING"


NO_NEW_READING = _NoNewReading()


# --- Times ------------------------------------------------------------------

def seconds(t) -> Decimal:
    """The exact seconds since the epoch of a time; ValueError otherwise. A
    float or a bool is not a time: a float is not exact."""
    if isinstance(t, bool) or isinstance(t, float):
        raise ValueError(f"not a time: {t!r}")
    if isinstance(t, int):
        return Decimal(t)
    if isinstance(t, Decimal):
        if not t.is_finite():
            raise ValueError(f"not a time: {t!r}")
        return t
    if isinstance(t, datetime):
        if t.tzinfo is None:
            raise ValueError(f"a time without a time zone: {t!r}")
        d = t - EPOCH
        whole = Decimal(d.days * 86400 + d.seconds)
        return whole + Decimal(d.microseconds) / 1000000 if d.microseconds else whole
    if isinstance(t, str):
        m = ISO.fullmatch(t)
        if m:
            try:
                base = datetime(*map(int, m.groups()[:6]), tzinfo=timezone.utc)
            except ValueError:
                raise ValueError(f"not a time: {t!r}") from None
            return seconds(base) + (Decimal("0" + m.group(7)) if m.group(7) else 0)
        try:
            return seconds(Decimal(t))
        except InvalidOperation:
            pass
    raise ValueError(f"not a time: {t!r}")


def ceil_s(x: Decimal) -> int:
    return int(x.to_integral_value(rounding=ROUND_CEILING))


def floor_s(x: Decimal) -> int:
    return int(x.to_integral_value(rounding=ROUND_FLOOR))


def iso(n: int) -> str:
    """A whole number of seconds as the ISO-8601 UTC time of a trace."""
    return (EPOCH + timedelta(seconds=n)).strftime("%Y-%m-%dT%H:%M:%SZ")


def exact(x: Decimal) -> str:
    """An exact time as it is kept in the host's records."""
    return format(x, "f")


# --- The factors of the specification ---------------------------------------

def spec_factors(source: str) -> dict:
    """The declared factors, read with the translator: name -> {"type": the
    type of the core, "stale": "block" (MAX_AGE ... ON_STALE BLOCK), "use_last"
    (MAX_AGE ... ON_STALE USE_LAST) or "none", "max_age": seconds or None}.
    HostError if the translator rejects the specification."""
    tree = parser().parse(source)
    tr = Translation()
    tr.specification(subtrees(tree)[0])
    if tr.rejected:
        raise HostError("the translator rejects the specification: REJECTED: "
                        + "; ".join(sorted(tr.rejected)))
    kinds = {}
    blocks = {b.data: b for b in subtrees(subtrees(tree)[0])}
    for f in subtrees(blocks["factors_block"]):
        stale = [s for s in subtrees(f) if s.data == "stale_action"]
        kinds[ident(subtrees(f)[0])] = tokens(stale[0])[0] if stale else None
    out = {}
    for _, name, ty, age in tr.core[1][1:]:
        if age[0] == "block":
            out[str(name)] = {"type": ty, "stale": "block", "max_age": age[1]}
        elif kinds.get(name) == "USE_LAST":
            out[str(name)] = {"type": ty, "stale": "use_last", "max_age": None}
        else:
            out[str(name)] = {"type": ty, "stale": "none", "max_age": None}
    return out


def with_max_age(f: dict) -> bool:
    return f["stale"] in ("block", "use_last")


# --- Values -----------------------------------------------------------------

def typed(ty, v, where: str):
    """The JSON value of a trace (evaluator/README.md) for a value v of the host
    and the declared type ty; HostError for a value of another type. None is
    "no value": allowed for a factor and for an Optional field, and then the
    name is left out of the data."""
    if ty[0] == "optional":
        return None if v is None else typed(ty[1], v, where)
    if v is None:
        raise HostError(f"{where}: no value for a field that is not Optional")
    if ty[0] == "record":
        if not isinstance(v, dict) or not all(isinstance(k, str) for k in v):
            raise HostError(f"{where}: expected a record, got {v!r}")
        fields = dict((str(n), t) for n, t in ty[1:])
        for k in v:
            if k not in fields:
                raise HostError(f"{where}: {k} is not a field of the record type")
        out = {}
        for n, t in fields.items():
            if n not in v and t[0] != "optional":
                raise HostError(f"{where}.{n}: no value for a field that is not Optional")
            x = typed(t, v.get(n), f"{where}.{n}")
            if x is not None:
                out[n] = x
        return {"record": out}
    kind = ty[1]
    if kind == "bool" and isinstance(v, bool):
        return {"bool": v}
    if kind == "int" and isinstance(v, int) and not isinstance(v, bool):
        return {"int": v}
    if kind == "decimal" and not isinstance(v, (bool, float)):
        d = None
        if isinstance(v, int):
            d = Decimal(v)
        elif isinstance(v, Decimal) and v.is_finite():
            d = v
        elif isinstance(v, str) and DECIMAL.fullmatch(v):
            d = Decimal(v)
        if d is not None:
            text = format(d, "f")
            return {"dec": text if "." in text else text + ".0"}
    if kind == "string" and isinstance(v, str):
        if any(0xD800 <= ord(c) <= 0xDFFF for c in v):
            raise HostError(f"{where}: a string with a surrogate")
        return {"str": v}
    if kind == "datetime":
        try:
            if isinstance(v, (datetime, str)):
                s = seconds(v)
                if s == int(s):
                    return {"time": iso(int(s))}
        except ValueError:
            pass
    raise HostError(f"{where}: {v!r} is not a value of the declared type {_type_text(ty)}")


def _type_text(ty) -> str:
    if ty[0] == "prim":
        return {"bool": "Boolean", "int": "Integer", "decimal": "Decimal", "string": "String",
                "datetime": "DateTime"}[ty[1]]
    if ty[0] == "optional":
        return f"Optional<{_type_text(ty[1])}>"
    return "Record { " + ", ".join(f"{n} : {_type_text(t)}" for n, t in ty[1:]) + " }"


def check_names(factors: dict, answers: dict, reasons: list):
    """Every declared factor has an answer, and every answer is of a declared factor."""
    if not isinstance(answers, dict):
        raise HostError(f"the answers of the host are not a dict: {answers!r}")
    for name in answers:
        if name not in factors:
            reasons.append(f"{name}: not a factor of the specification")
    for name in factors:
        if name not in answers:
            reasons.append(f"factor {name}: no answer from the host")


# --- Readings of the factors with MAX_AGE ------------------------------------

def accept(factors: dict, store: dict, answers: dict, h: Decimal):
    """The store after the answers of the host at the host clock h, and the
    reasons to hold the action:
      - a value without the time of its source: "factor F: a value without a
        source time";
      - a reading not later than the last accepted one is not accepted and
        changes nothing; with the same time and another value the action is
        held until a later reading: "factor F: two readings with one time";
      - a reading later than h is kept, and the action is held while any kept
        reading is later than h: "factor F: a reading from the future"."""
    store = {f: {"accepted": [list(r) for r in s["accepted"]], "conflict": s["conflict"]}
             for f, s in store.items()}
    reasons = []
    for name, f in factors.items():
        if not with_max_age(f) or name not in answers:
            continue
        a = answers[name]
        s = store.setdefault(name, {"accepted": [], "conflict": None})
        if a is NO_NEW_READING:
            pass
        elif not isinstance(a, Reading) or a.time is None:
            reasons.append(f"factor {name}: a value without a source time")
        else:
            try:
                t = seconds(a.time)
                v = typed(f["type"], a.value, f"factor {name}")
                if v is None:
                    raise HostError(f"factor {name}: a reading without a value")
            except ValueError as e:
                reasons.append(f"factor {name}: {e}")
                continue
            except HostError as e:
                reasons.append(str(e))
                continue
            last = Decimal(s["accepted"][-1][0]) if s["accepted"] else None
            if last is None or t > last:
                s["accepted"].append([exact(t), v])
                if s["conflict"] is not None and t > Decimal(s["conflict"]):
                    s["conflict"] = None
            elif t == last and v != s["accepted"][-1][1]:
                s["conflict"] = exact(t)
        if s["conflict"] is not None:
            reasons.append(f"factor {name}: two readings with one time")
        if s["accepted"] and Decimal(s["accepted"][-1][0]) > h:
            reasons.append(f"factor {name}: a reading from the future")
    return store, reasons


def latest(store: dict, name: str, h: Decimal):
    """The accepted reading of the factor with the greatest unrounded time not
    later than h, as (time, value), or None."""
    best = None
    for t, v in store.get(name, {"accepted": []})["accepted"]:
        if Decimal(t) <= h:
            best = (Decimal(t), v)
    return best


def state_data(factors: dict, store: dict, answers: dict, h: Decimal, reasons: list) -> dict:
    """The data of a tick entry at the host clock h: the value the host gives
    for a factor without MAX_AGE; for a factor with MAX_AGE the value of its
    reading with the greatest time not later than h, however old (under USE_LAST
    also one older than the activation); absent while there is none."""
    data = {}
    for name, f in factors.items():
        if with_max_age(f):
            r = latest(store, name, h)
            if r is not None:
                data[name] = r[1]
        elif name in answers:
            a = answers[name]
            if isinstance(a, Reading) or a is NO_NEW_READING:
                reasons.append(f"factor {name}: has no MAX_AGE, so the host gives a value or None")
                continue
            if a is None:  # "no value": the factor is absent, whatever its type
                continue
            try:
                v = typed(f["type"], a, f"factor {name}")
            except HostError as e:
                reasons.append(str(e))
                continue
            if v is not None:
                data[name] = v
    return data


# --- The activation -------------------------------------------------------------

def activation(factors: dict, answers: dict, h: Decimal, store: dict = None):
    """The record of the activation at the host clock h: (record, store, reasons).
    The record is {"time": exact h, "data": the data of entry 0}; the trace
    gives entry 0 the time h rounded down, so that no later entry is earlier."""
    reasons = []
    check_names(factors, answers, reasons)
    store, more = accept(factors, store or {}, answers, h)
    reasons += more
    data = state_data(factors, store, answers, h, reasons)
    return {"time": exact(h), "data": data}, store, reasons


# --- The trace ----------------------------------------------------------------

def decision_time(decided: Decimal) -> int:
    """T: the host clock of the decision rounded up."""
    return ceil_s(decided)


def execution_time(decided: Decimal, executed: Decimal) -> int:
    """E: the time of execution rounded up, and not earlier than T."""
    return max(decision_time(decided), ceil_s(executed))


def _entry(t: int, event: dict, data: dict) -> dict:
    return {"time": iso(t), "event": event, "data": data}


def _act(subject: str, action: str) -> dict:
    return {"kind": "act", "subject": subject, "action": action, "polarity": "must_not"}


def decide(factors: dict, spec_path: str, activation_record: dict, history: list,
           store: dict, answers: dict, subject: str, action: str, h: Decimal):
    """The trace for the decision on the action of subject at the host clock h.

    history: the executed actions, each {"subject", "action", "decided": exact
    host clock of its decision, "executed": exact time of its execution,
    "data": the data of its tick entry}.

    Returns (trace or None, store, reasons, data): the trace is None whenever
    there is a reason to hold the action; the store is to be kept in either
    case; data is the data of the tick entry of the decision."""
    reasons = []
    check_names(factors, answers, reasons)
    store, more = accept(factors, store, answers, h)
    reasons += more
    data = state_data(factors, store, answers, h, reasons)
    t_now = decision_time(h)
    act_at = Decimal(activation_record["time"])

    # Freshness by the exact times: a reading under ON_STALE BLOCK not older
    # than MAX_AGE must be fresh in the trace at T as well.
    for name, f in factors.items():
        if f["stale"] != "block":
            continue
        r = latest(store, name, h)
        if r is None:
            continue
        fresh_exact = h - r[0] <= f["max_age"]
        fresh_trace = r[0] >= act_at and t_now - floor_s(r[0]) <= f["max_age"]
        if fresh_exact and not fresh_trace:
            reasons.append(f"factor {name}: a fresh reading that the trace cannot express")
    if reasons:
        return None, store, reasons, data

    # The recorded entries in time order: (whole seconds, exact time, order, entry).
    rows = []
    for k, x in enumerate(history):
        decided, executed = Decimal(x["decided"]), Decimal(x["executed"])
        rows.append((decision_time(decided), decided, 2 * k,
                     _entry(decision_time(decided), {"kind": "tick"}, x["data"])))
        rows.append((execution_time(decided, executed), max(decided, executed), 2 * k + 1,
                     _entry(execution_time(decided, executed), _act(x["subject"], x["action"]),
                            x["data"])))
    arrivals = []
    for name, f in factors.items():
        if f["stale"] != "block":
            continue
        for t, v in store.get(name, {"accepted": []})["accepted"]:
            t = Decimal(t)
            if act_at <= t <= h:
                arrivals.append((floor_s(t), t, name, v))
    rows.sort(key=lambda r: r[:3])
    entries = [_entry(floor_s(act_at), {"kind": "activate"}, activation_record["data"])]
    keys = [(floor_s(act_at), act_at)]
    for row in rows:
        entries.append(row[3])
        keys.append(row[:2])
    for ts, t, name, v in sorted(arrivals, key=lambda a: a[:2]):
        i = len(entries)
        while i > 1 and keys[i - 1] > (ts, t):
            i -= 1
        d = dict(entries[i - 1]["data"])
        d[name] = v
        entries.insert(i, _entry(ts, {"kind": "arrive", "factor": name}, d))
        keys.insert(i, (ts, t))
    entries.append(_entry(t_now, {"kind": "tick"}, data))
    entries.append(_entry(t_now, _act(subject, action), data))
    return {"scenario": "host", "spec": spec_path, "entries": entries}, store, [], data
