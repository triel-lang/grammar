#!/usr/bin/env python3
"""
Run a scenario (an implementation trace, examples/core/README.md) through the
evaluator exported from formal/core.

Usage:
    python3 triel_eval.py SCENARIO.scn [--evaluator PATH] [--input]

The specification named in the scenario is translated by triel_to_core.py;
the scenario is converted to the input of the evaluator (times to seconds
since the epoch); the report is the translator's header lines followed by the
evaluator's lines. --input prints the evaluator input instead of running it.

The evaluator binary is taken from --evaluator, else from the environment
variable TRIEL_EVALUATOR, else evaluator/triel-eval (triel-eval.exe on Windows).

Exit codes: 0 evaluated, 2 the specification is rejected, 1 any other error.
"""
import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

from lark import UnexpectedInput

sys.path.insert(0, str(Path(__file__).parent))
from triel_to_core import Str, header, iso_seconds, sexp, translate  # noqa: E402

REPO = Path(__file__).resolve().parent.parent


class ScenarioError(Exception):
    pass


class Sym(str):
    pass


def read_sexp(text: str):
    pos = 0

    def skip():
        nonlocal pos
        while pos < len(text):
            if text[pos].isspace():
                pos += 1
            elif text[pos] == ";":
                while pos < len(text) and text[pos] != "\n":
                    pos += 1
            else:
                break

    def one():
        nonlocal pos
        skip()
        if pos >= len(text):
            raise ScenarioError("unexpected end of scenario")
        c = text[pos]
        if c == "(":
            pos += 1
            xs = []
            while True:
                skip()
                if pos < len(text) and text[pos] == ")":
                    pos += 1
                    return xs
                xs.append(one())
        if c == ")":
            raise ScenarioError("unexpected )")
        if c == '"':
            # The escapes of evaluator/Main.hs: \n and \t, and \c is c.
            pos += 1
            out = []
            while True:
                if pos >= len(text):
                    raise ScenarioError("unterminated string")
                if text[pos] == '"':
                    pos += 1
                    return Str("".join(out))
                if text[pos] == "\\":
                    pos += 1
                    if pos >= len(text):
                        raise ScenarioError("unterminated string")
                    out.append({"n": "\n", "t": "\t"}.get(text[pos], text[pos]))
                else:
                    out.append(text[pos])
                pos += 1
        start = pos
        while pos < len(text) and not text[pos].isspace() and text[pos] not in '()";':
            pos += 1
        return Sym(text[start:pos])

    x = one()
    skip()
    if pos != len(text):
        raise ScenarioError("text after the scenario")
    return x


def time_of(x) -> int:
    if not isinstance(x, Str) or iso_seconds(x) is None:
        raise ScenarioError(f"not an ISO-8601 UTC time: {x}")
    return iso_seconds(x)


def value(x):
    if isinstance(x, list) and len(x) == 2 and x[0] == "bool" and x[1] in ("true", "false"):
        return ["bool", Sym(x[1])]
    if isinstance(x, list) and len(x) == 2 and x[0] == "int" and isinstance(x[1], Sym) \
            and re.fullmatch(r"-?[0-9]+", x[1]):
        return ["int", int(x[1])]
    if isinstance(x, list) and len(x) == 2 and x[0] == "dec" and isinstance(x[1], Sym):
        m = re.fullmatch(r"(-?)([0-9]+)\.([0-9]+)", x[1])
        if m:
            return ["dec", int(m.group(1) + m.group(2) + m.group(3)), len(m.group(3))]
    if isinstance(x, list) and len(x) == 2 and x[0] == "str" and isinstance(x[1], Str):
        return ["str", x[1]]
    if isinstance(x, list) and len(x) == 2 and x[0] == "time":
        return ["time", time_of(x[1])]
    if isinstance(x, list) and x and x[0] == "record":
        return ["record"] + fields(x[1:])
    raise ScenarioError(f"not a value: {sexp(x)}")


def field(f):
    if isinstance(f, list) and len(f) == 2 and isinstance(f[0], Sym):
        return [Str(f[0]), value(f[1])]
    raise ScenarioError(f"not a field: {sexp(f)}")


def fields(fs):
    """The fields of (data ...) or (record ...); a name may be given only once."""
    out = [field(f) for f in fs]
    names = [f[0] for f in out]
    for n in names:
        if names.count(n) > 1:
            raise ScenarioError(f"{n} is given twice")
    return out


def event(x, first: bool):
    if x == ["activate"]:
        if not first:
            raise ScenarioError("(activate) is allowed only in the first entry")
        return ["tick"]
    if first:
        raise ScenarioError("the first entry must be (activate)")
    if x == ["tick"]:
        return ["tick"]
    if isinstance(x, list) and len(x) == 2 and x[0] == "arrive":
        return ["arrive", Str(x[1])]
    if isinstance(x, list) and len(x) == 4 and x[0] == "act" and x[3] in ("must", "may", "must_not"):
        return ["act", Str(x[1]), action(x[2]), Sym(x[3])]
    raise ScenarioError(f"not an event: {sexp(x)}")


def action(x):
    """An action: NAME, or (NAME ARG ...) with ARG (name X) or a value."""
    if isinstance(x, Sym):
        return Str(x)
    if isinstance(x, list) and x and isinstance(x[0], Sym):
        args = []
        for a in x[1:]:
            if isinstance(a, list) and len(a) == 2 and a[0] == "name" and isinstance(a[1], Sym):
                args.append(["path"] + [Str(n) for n in a[1].split(".")])
            elif isinstance(a, list) and a and a[0] != "record":
                args.append(value(a))
            else:
                raise ScenarioError(f"not an argument: {sexp(a)}")
        return ["action", Str(x[0])] + args
    raise ScenarioError(f"not an action: {sexp(x)}")


def scenario_input(scn):
    """The specification path and the trace part of the evaluator input."""
    if not (isinstance(scn, list) and len(scn) >= 3 and scn[0] == "scenario"):
        raise ScenarioError("expected (scenario NAME (spec PATH) (entry ...) ...)")
    spec = scn[2]
    if not (isinstance(spec, list) and len(spec) == 2 and spec[0] == "spec"):
        raise ScenarioError("expected (spec PATH)")
    # The order of the times is not checked here: the evaluator rejects a list of
    # entries whose times decrease (TIME ORDER REJECTED, TRIEL_Exec.thy).
    entries = []
    for i, e in enumerate(scn[3:]):
        if not (isinstance(e, list) and len(e) == 4 and e[0] == "entry"):
            raise ScenarioError(f"not an entry: {sexp(e)}")
        t = time_of(e[1])
        data = e[3]
        if not (isinstance(data, list) and data and data[0] == "data"):
            raise ScenarioError(f"expected (data ...) in entry {i}")
        try:
            fs = fields(data[1:])
        except ScenarioError as err:
            raise ScenarioError(f"entry {i}: {err}") from None
        entries.append(["entry", t, event(e[2], i == 0), ["data"] + fs])
    if not entries:
        raise ScenarioError("a scenario needs the activation entry")
    return spec[1], ["trace"] + entries


def find_spec(path) -> Path:
    """The specification of (spec PATH): PATH is relative to the root of the
    repository, whatever the current directory."""
    if not isinstance(path, Str):
        raise ScenarioError("expected (spec \"PATH\")")
    p = Path(path)
    q = p if p.is_absolute() else REPO / p
    if q.is_file():
        return q
    raise ScenarioError(f"specification not found: {path}")


def default_evaluator() -> str:
    exe = "triel-eval.exe" if os.name == "nt" else "triel-eval"
    return os.environ.get("TRIEL_EVALUATOR", str(REPO / "evaluator" / exe))


def main() -> int:
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("scenario")
    ap.add_argument("--evaluator", default=None)
    ap.add_argument("--input", action="store_true", help="print the evaluator input and stop")
    args = ap.parse_args()
    try:
        scn = read_sexp(Path(args.scenario).read_text(encoding="utf-8"))
        spec_path, trace = scenario_input(scn)
        tr = translate(find_spec(spec_path).read_text(encoding="utf-8"))
    except ScenarioError as e:
        print(f"{args.scenario}: {e}", file=sys.stderr)
        return 1
    except UnexpectedInput as e:
        print(f"{args.scenario}: the specification does not parse "
              f"(line {e.line}, column {e.column})", file=sys.stderr)
        return 1
    except RecursionError:
        print(f"{args.scenario}: nested too deeply", file=sys.stderr)
        return 1
    lines = header(tr)
    if tr.rejected:
        print("\n".join(lines + ["REJECTED: " + "; ".join(sorted(tr.rejected))]))
        return 2
    inp = sexp(["input", tr.core, trace])
    if args.input:
        print(inp)
        return 0
    ev = args.evaluator or default_evaluator()
    res = subprocess.run([ev], input=inp, capture_output=True, text=True)
    if res.returncode != 0:
        print(res.stderr, file=sys.stderr, end="")
        return 1
    print("\n".join(lines + res.stdout.splitlines()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
