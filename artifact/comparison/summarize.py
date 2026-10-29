#!/usr/bin/env python3
"""Summary of the outputs of artifact/comparison/run.sh that does not depend on
the order in which cedar lists policies and diagnostics, which varies from run to
run. For every command it keeps the command, the decision or the validation
result, the sorted lists of determining policies, evaluation errors and
validation diagnostics, and the exit code. The outputs of dogwood and of the
TRIEL evaluator do not vary and are kept as they are, except for the path of
the TRIEL evaluator.

Usage: summarize.py RESULTS_DIR SUMMARY_DIR
"""
import re
import sys
from pathlib import Path


def blocks(text):
    """The command blocks of one output file: (command, body lines)."""
    out = []
    for chunk in re.split(r"(?m)^\$ ", text):
        if not chunk.strip():
            continue
        lines = chunk.rstrip("\n").split("\n")
        out.append((lines[0], lines[1:]))
    return out


def summarize_cedar(text):
    res = []
    for cmd, body in blocks(text):
        exit_code = next((l for l in body if re.fullmatch(r"\[exit \d+\]", l)), "[exit ?]")
        res.append("$ " + cmd)
        if cmd.startswith("cedar validate"):
            passed = any("validation passed" in l for l in body)
            res.append("validation " + ("passed" if passed else "failed"))
            # The first diagnostic is printed after "Caused by:", the others after
            # "Error:"; which one comes first varies.
            diags = sorted({m.group(1) for m in
                            (re.match(r"\s*(?:Caused by|Error): (.*)$", l) for l in body)
                            if m and "no errors or warnings" not in m.group(1)})
            res += ["  " + d for d in diags]
        else:
            decision = next((l for l in body if l in ("ALLOW", "DENY")), None)
            if decision is None:
                decision = next((l.strip() for l in body if l.strip()), "(no output)")
            res.append(decision)
            policies, errors, in_policies = [], [], False
            for l in body:
                if l.startswith("note: this decision was due to the following policies"):
                    in_policies = True
                    continue
                if in_policies and l.startswith("  ") and l.strip():
                    policies.append(l.strip())
                    continue
                in_policies = False
                if "error while evaluating policy" in l:
                    errors.append(l.strip())
            if policies:
                res.append("  policies: " + ", ".join(sorted(policies)))
            res += ["  " + e for e in sorted(set(errors))]
        res.append(exit_code)
        res.append("")
    return "\n".join(res)


def main():
    results, summary = Path(sys.argv[1]), Path(sys.argv[2])
    summary.mkdir(parents=True, exist_ok=True)
    for f in sorted(results.glob("*.out")):
        text = f.read_text(encoding="utf-8")
        if f.name.startswith("cedar-"):
            text = summarize_cedar(text)
        elif f.name == "triel-further-traces.out":
            text = re.sub(r"--evaluator \S+", "--evaluator EVAL", text)
        (summary / (f.stem + ".txt")).write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
