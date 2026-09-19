#!/usr/bin/env python3
"""
Ambiguity regression tests for the TRIEL reference grammar.

Each case below is a source fragment that MUST have exactly one parse
derivation under parser/triel.lark. The parser is run with Earley in
ambiguity='explicit' mode, which materialises every competing derivation
as an _ambig node; the test fails if any such node survives.

This guards the fixes recorded as D-19, D-20, D-21, D-32 and the
2026-09 findings F-1, F-2, F-6. Ambiguity is invisible to the
examples/*.triel corpus: an example that parses tells you nothing about
whether it parses in more than one way.

Run:  python3 parser/test_ambiguity.py
"""
import sys
from pathlib import Path

from lark import Lark

GRAMMAR = Path(__file__).parent / "triel.lark"

SKELETON = """SPECIFICATION probe VERSION 1.0.0
SUBJECTS {{ alice: PARTY, bob: PARTY }}
TERMS {{ {term} }}
FACTORS {{ a: Boolean METADATA, b: Boolean METADATA }}
INVARIANTS {{ probe_inv : {inv} }}
"""

DEFAULT_TERM = "alice MUST pay"
DEFAULT_INV = "ALWAYS(a)"

# (label, slot, fragment) — slot is "term" or "inv"
CASES = [
    # F-1: unmatched_condition's body was term_stmt, letting THEN-sequences
    # and a trailing WITHIN/ELSE attach two different ways.
    ("F-1  sequence after IF", "term",
     "IF a THEN alice MUST pay THEN bob MUST ship"),
    ("F-1  WITHIN/ELSE after IF", "term",
     "IF a THEN alice MUST pay WITHIN 5 DAYS ELSE bob MUST ship"),

    # F-2: WHEN with an open IF body must parse, and parse once.
    ("F-2  WHEN with open IF", "term",
     "WHEN a THEN IF b THEN alice MUST pay"),
    ("F-2  WHEN with closed IF", "term",
     "WHEN a THEN IF b THEN alice MUST pay ELSE bob MUST ship"),

    # Dangling else: ELSE binds to the nearest still-open IF, one way only.
    ("D-xx dangling else", "term",
     "IF a THEN IF b THEN alice MUST pay ELSE bob MUST ship"),

    # D-19: permission_stmt no longer carries its own WITHIN.
    ("D-19 MAY + WITHIN", "term",
     "alice MAY act WITHIN 5 DAYS"),

    # D-20: ON..DO body is base_term, so the outer THEN cannot be absorbed.
    ("D-20 ON..DO + THEN", "term",
     "ON e DO alice MUST pay THEN bob MUST ship"),
    ("D-20 ON..DO parenthesised", "term",
     "ON e DO (alice MUST pay THEN bob MUST ship)"),

    # F-6 / D-21 / D-32: CTL operator pairs are single tokens, so EF(a) is
    # not also lexable as a call to a function named EF.
    ("F-6  CTL negation", "inv", "!EF(a)"),
    ("F-6  CTL nested", "inv", "AG(EF(a))"),
    ("F-6  CTL universal", "inv", "AF(a)"),

    # D-22/D-23: LTL until chains and implication chains.
    ("D-22 LTL until chain", "inv", "a U b U a"),
    ("D-22 LTL implication", "inv", "a -> b -> a"),
    ("F-4  IMPLIES chain", "inv", "ALWAYS(a IMPLIES b IMPLIES a)"),

    # UNLESS: precedence against THEN, handler scope, guard expressions.
    ("U-1  THEN..UNLESS", "term",
     "alice MUST pay THEN bob MUST ship UNLESS a DO alice MUST notify"),
    ("U-2  UNLESS handler + THEN", "term",
     "alice MUST pay UNLESS a DO bob MUST ship THEN alice MUST notify"),
    ("U-3  ON..DO under UNLESS", "term",
     "ON e DO alice MUST pay UNLESS a DO bob MUST ship"),
    ("U-4  guard OR/AND", "term",
     "alice MUST pay UNLESS a OR b AND a DO bob MUST ship"),
    ("U-5  nested UNLESS, parenthesised", "term",
     "(alice MUST pay UNLESS a DO bob MUST ship) UNLESS b DO alice MUST notify"),

    # A term reference needs REF; without it, an expression ending a term
    # could swallow a neighbouring term name.
    ("T-1  MAY..WHEN a OR b", "term", "alice MAY pay WHEN a OR b"),
    ("T-2  MAY..WHEN a AND b", "term", "alice MAY pay WHEN a AND b"),
    ("T-3  MUST_NOT..WHEN a OR b", "term", "alice MUST_NOT pay WHEN a OR b"),
    ("T-4  PENALTY a OR b", "term", "alice ON_BREACH PENALTY a OR b"),
    ("T-5  REF in a choice", "term", "alice MAY pay WHEN a OR REF b"),

    # Every CTL operator is one reserved token, AU included.
    ("C-1  AU(a)", "inv", "AU(a)"),
    ("C-2  AG(AU(a))", "inv", "AG(AU(a))"),

    # Controls: must remain unambiguous.
    ("ctl  plain obligation", "term", "alice MUST pay"),
    ("ctl  breach handler", "term",
     "alice ON_BREACH PENALTY 100 CAP 1000, TERMINATE"),
]


# Fragments that MUST be rejected. Each differs from an accepted fragment
# only in the construct under test, so a rejection cannot come from
# somewhere else in the specification.
REJECT_CASES = [
    ("R-1  chained UNLESS", "term",
     "alice MUST pay UNLESS a DO bob MUST ship UNLESS b DO alice MUST notify"),
    ("R-2  MUST..WHEN", "term", "alice MUST pay WHEN a"),
    ("R-3  PRESENT arity", "inv", "ALWAYS(PRESENT(a, b))"),
    ("R-4  bare term reference", "term", "alice MUST pay THEN b"),
    ("R-5  REF is reserved", "term", "REF MUST pay"),
]

# Which parse was chosen, not just that there is one: number of THEN-
# operands at the top of the TERMS block.
SHAPE_CASES = [
    ("S-1  UNLESS binds tighter than THEN",
     "alice MUST pay THEN bob MUST ship UNLESS a DO alice MUST notify", 2),
    ("S-2  UNLESS handler stops before THEN",
     "alice MUST pay UNLESS a DO bob MUST ship THEN alice MUST notify", 2),
]

# Number of OR-operands at the top of the TERMS block: a guard's OR stays
# inside the guard, and only REF introduces a term-level choice.
CHOICE_CASES = [
    ("S-3  guard OR stays in the guard", "alice MAY pay WHEN a OR b", 1),
    ("S-4  REF makes a term choice", "alice MAY pay WHEN a OR REF b", 2),
]


def top_choice_len(tree):
    ch = next(t for t in tree.iter_subtrees_topdown() if t.data == "choice_expr")
    return sum(1 for c in ch.children if getattr(c, "data", None) == "parallel_expr")


def top_sequence_len(tree):
    seq = next(t for t in tree.iter_subtrees_topdown() if t.data == "sequence_expr")
    return sum(1 for c in seq.children if getattr(c, "data", None) == "unless_expr")


def build(slot, fragment):
    return SKELETON.format(
        term=fragment if slot == "term" else DEFAULT_TERM,
        inv=fragment if slot == "inv" else DEFAULT_INV,
    )


def count_ambiguities(tree):
    total = 0
    for subtree in tree.iter_subtrees():
        if subtree.data == "_ambig":
            total += len(subtree.children) - 1
    return total


def main():
    parser = Lark(
        GRAMMAR.read_text(),
        start="start",
        parser="earley",
        ambiguity="explicit",
        lexer="dynamic",
    )

    failures = []
    for label, slot, fragment in CASES:
        source = SKELETON.format(
            term=fragment if slot == "term" else DEFAULT_TERM,
            inv=fragment if slot == "inv" else DEFAULT_INV,
        )
        try:
            tree = parser.parse(source)
        except Exception as exc:
            failures.append(f"{label}: REJECTED ({type(exc).__name__}) -- {fragment}")
            print(f"  FAIL  {label:28s} rejected")
            continue

        extra = count_ambiguities(tree)
        if extra:
            failures.append(f"{label}: {extra + 1} derivations -- {fragment}")
            print(f"  FAIL  {label:28s} {extra + 1} derivations")
        else:
            print(f"  ok    {label:28s}")

    for label, slot, fragment in REJECT_CASES:
        try:
            parser.parse(build(slot, fragment))
        except Exception:
            print(f"  ok    {label:28s} rejected")
            continue
        failures.append(f"{label}: ACCEPTED, must be rejected -- {fragment}")
        print(f"  FAIL  {label:28s} accepted")

    for label, fragment, expected in SHAPE_CASES:
        try:
            got = top_sequence_len(parser.parse(build("term", fragment)))
        except Exception as exc:
            failures.append(f"{label}: did not parse ({type(exc).__name__}) -- {fragment}")
            print(f"  FAIL  {label:28s} did not parse")
            continue
        if got == expected:
            print(f"  ok    {label:28s}")
        else:
            failures.append(f"{label}: {got} THEN-operands, expected {expected} -- {fragment}")
            print(f"  FAIL  {label:28s} shape {got} != {expected}")

    for label, fragment, expected in CHOICE_CASES:
        try:
            got = top_choice_len(parser.parse(build("term", fragment)))
        except Exception as exc:
            failures.append(f"{label}: did not parse ({type(exc).__name__}) -- {fragment}")
            print(f"  FAIL  {label:28s} did not parse")
            continue
        if got == expected:
            print(f"  ok    {label:28s}")
        else:
            failures.append(f"{label}: {got} OR-operands, expected {expected} -- {fragment}")
            print(f"  FAIL  {label:28s} shape {got} != {expected}")

    total = len(CASES) + len(REJECT_CASES) + len(SHAPE_CASES) + len(CHOICE_CASES)
    print()
    if failures:
        print(f"{len(failures)} of {total} checks failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print(f"All {total} checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
