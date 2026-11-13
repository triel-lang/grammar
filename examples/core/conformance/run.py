#!/usr/bin/env python3
"""
Run an implementation of TRIEL on the core conformance suite (manifest.json).

Usage:
    python3 examples/core/conformance/run.py [--impl "COMMAND"] [--level verdicts|monitor]

For every case of manifest.json the command is run from the root of the
repository with a time-out of 60 seconds. The command is split with
shlex.split; in every token, {spec} is replaced by the path of the
specification and {trace} by the path of the scenario, both relative to the
root of the repository, as in manifest.json. The default command is the
reference: python3 parser/triel_eval.py {trace}

From the standard output of the command and from the .expected file, the lines
of the level are selected and compared line by line, exactly. A line belongs to
a level if its first word, or for TIME ORDER its first two words, is one of the
lines of the level in manifest.json. "\\r\\n" and "\\n" are the same line end,
and a last empty line is not counted. The exit code of the command does not
matter; a command that cannot be started, or that runs out of time, fails the
case.

Prints PASS or FAIL for every case, the first line that differs for a FAIL, and
"N/M passed" at the end. Exit code: 0 if every case passes, 1 if any fails,
2 on a usage error. Only the Python 3 standard library is needed.
"""
import argparse
import json
import os
import shlex
import signal
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
REFERENCE = "python3 parser/triel_eval.py {trace}"
TIMEOUT = 60


def lines_of(data: bytes):
    text = data.decode("utf-8", errors="replace").replace("\r\n", "\n")
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines


def select(lines, prefixes):
    out = []
    for line in lines:
        words = line.split()
        if any(words[:len(p)] == p for p in prefixes):
            out.append(line)
    return out


def run(argv, timeout):
    """Standard output of argv, run from the root; raises OSError or TimeoutError."""
    kwargs = {}
    if os.name == "posix":
        kwargs["start_new_session"] = True
    proc = subprocess.Popen(argv, cwd=str(ROOT), stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, **kwargs)
    try:
        out, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        if os.name == "posix":
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except OSError:
                pass
        else:
            proc.kill()
        proc.communicate()
        raise TimeoutError("timed out after %d seconds" % timeout)
    return out


def first_difference(expected, actual):
    for i in range(max(len(expected), len(actual))):
        e = expected[i] if i < len(expected) else None
        a = actual[i] if i < len(actual) else None
        if e != a:
            return i + 1, e, a
    return None


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser(description="Run an implementation on the TRIEL core conformance suite.")
    ap.add_argument("--impl", default=REFERENCE,
                    help="command to run for each case; {spec} and {trace} are replaced "
                         "(default: %(default)s)")
    ap.add_argument("--level", choices=["verdicts", "monitor"], default="verdicts",
                    help="lines compared (default: %(default)s)")
    args = ap.parse_args()

    try:
        template = shlex.split(args.impl)
    except ValueError as e:
        print("error: --impl: %s" % e, file=sys.stderr)
        return 2
    if not template:
        print("error: --impl is empty", file=sys.stderr)
        return 2

    manifest = json.loads((HERE / "manifest.json").read_text(encoding="utf-8"))
    prefixes = [p.split() for p in manifest["levels"][args.level]["lines"]]
    cases = manifest["cases"]

    passed = 0
    for case in cases:
        argv = [t.replace("{spec}", case["spec"]).replace("{trace}", case["trace"]) for t in template]
        expected = select(lines_of((ROOT / case["expected"]).read_bytes()), prefixes)
        try:
            actual = select(lines_of(run(argv, TIMEOUT)), prefixes)
        except (OSError, TimeoutError) as e:
            print("FAIL %s: %s" % (case["id"], e))
            continue
        diff = first_difference(expected, actual)
        if diff is None:
            passed += 1
            print("PASS %s" % case["id"])
        else:
            n, e, a = diff
            print("FAIL %s: line %d of the level" % (case["id"], n))
            print("  expected: %s" % ("(no line)" if e is None else e))
            print("  actual:   %s" % ("(no line)" if a is None else a))
    print("%d/%d passed" % (passed, len(cases)))
    return 0 if passed == len(cases) else 1


if __name__ == "__main__":
    sys.exit(main())
