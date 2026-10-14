#!/usr/bin/env python3
"""
Ambiguity regression tests for the TRIEL reference grammar.

Each case below is a source fragment that MUST have exactly one parse
derivation under parser/triel.lark. The parser is run with Earley in
ambiguity='explicit' mode, which materialises every competing derivation
as an _ambig node; the derivations are counted, and the test fails
unless there is exactly one.

This guards the fixes recorded as D-19, D-20, D-21, D-32, D-34 and the
2026-09 findings F-1, F-2, F-6. Ambiguity is invisible to the
examples/*.triel corpus: an example that parses tells you nothing about
whether it parses in more than one way.

Two further checks support the unambiguity statement of
TECHNICAL_REPORT.md §2.12:

  * the LALR(1) table of the grammar has exactly the shift/reduce
    conflicts listed in LALR_CONFLICTS and no reduce/reduce conflict;
  * on every example and every fragment of this file, Earley and LALR(1)
    take the same accept/reject decision and build the same tree, except
    on the inputs that exercise those conflicts.

Run:  python3 parser/test_ambiguity.py
"""
import logging
import sys
from pathlib import Path

from lark import Lark, Token, Tree, logger
from lark.exceptions import GrammarError

REPO = Path(__file__).resolve().parent.parent
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

    # Group A: IF and LET expressions are alternatives of expr, not of
    # primary, so their last branch takes everything to its right.
    ("gA-1 IF..ELSE a OR b", "inv",
     "ALWAYS(IF a THEN b ELSE a OR b)"),
    ("gA-2 IF..ELSE 2 + n == 3", "inv",
     "ALWAYS(IF a THEN 1 ELSE 2 + n == 3)"),
    ("gA-3 LET..IN x + n == 3", "inv",
     "ALWAYS(LET x : Integer = 1 IN x + n == 3)"),
    ("gA-4 IF in a guard", "term",
     "alice MAY pay WHEN IF a THEN b ELSE a OR b"),
    ("gA-5 IF as an LTL state", "inv",
     "IF a THEN b ELSE a OR b"),
    ("gA-6 nested IF with ELIF", "inv",
     "ALWAYS(IF a THEN IF b THEN a ELSE b ELIF b THEN a ELSE a AND b)"),
    ("gA-7 LET in an IF branch", "inv",
     "ALWAYS(IF a THEN LET x : Integer = 1 IN x == n ELSE b IMPLIES a)"),
    # As an operand, an IF or LET expression is parenthesised.
    ("gA-8 (IF) OR b", "inv",
     "ALWAYS((IF a THEN b ELSE a) OR b)"),
    ("gA-9 a OR (IF)", "inv",
     "ALWAYS(a OR (IF a THEN b ELSE a))"),
    ("gA-10 (LET) + n == 3", "inv",
     "ALWAYS((LET x : Integer = 1 IN x) + n == 3)"),

    # Group C: a trigger whose body ends in an open IF is an unmatched
    # term, so ELIF and ELSE bind to the nearest open IF through ON..DO.
    ("gC-1 IF, ON..DO IF..ELSE", "term",
     "IF a THEN ON e DO IF b THEN alice MUST pay ELSE bob MUST ship"),
    ("gC-2 IF, ON..DO IF..ELIF", "term",
     "IF a THEN ON e DO IF b THEN alice MUST pay "
     "ELIF a THEN bob MUST ship ELSE alice MUST notify"),
    ("gC-3 IF, WHEN, ON..DO IF", "term",
     "IF a THEN WHEN b THEN ON e DO IF b THEN alice MUST pay ELSE bob MUST ship"),
    ("gC-4 WHEN, ON..DO IF..ELSE", "term",
     "WHEN a THEN ON e DO IF b THEN alice MUST pay ELSE bob MUST ship"),
    ("gC-5 IF, ON..DO ON..DO IF", "term",
     "IF a THEN ON e DO ON e DO IF b THEN alice MUST pay ELSE bob MUST ship"),
    ("gC-6 ELSE ON..DO open IF", "term",
     "IF a THEN alice MUST pay ELSE ON e DO IF b THEN bob MUST ship"),
    ("gC-7 ON..DO open IF", "term",
     "ON e DO IF b THEN alice MUST pay"),
    ("gC-8 ON..DO open IF + THEN", "term",
     "ON e DO IF b THEN alice MUST pay THEN bob MUST ship"),
    ("gC-9 two ELSE across ON..DO", "term",
     "IF a THEN ON e DO IF b THEN alice MUST pay ELSE bob MUST ship "
     "ELSE alice MUST notify"),
    ("gC-10 ELIF, open IF in ON..", "term",
     "IF a THEN ON e DO IF b THEN alice MUST pay ELIF a THEN IF b THEN bob MUST ship"),
    # D-34: an IF/ELIF chain with no ELSE whose last branch is closed.
    ("gC-11 IF..ELIF, no ELSE", "term",
     "IF a THEN alice MUST pay ELIF b THEN bob MUST ship"),
    ("gC-12 IF..ELIF..ELIF, no ELSE", "term",
     "IF a THEN alice MUST pay ELIF b THEN bob MUST ship ELIF a THEN alice MUST notify"),
    ("gC-13 ELIF, closed IF in last branch", "term",
     "IF a THEN alice MUST pay ELIF b THEN IF a THEN bob MUST ship ELSE alice MUST notify"),

    # Group D: parentheses around a formula with no LTL operator belong to
    # the state expression; ltl_atom parenthesises only LTL formulas.
    ("gD-1 (a)", "inv", "(a)"),
    ("gD-2 ((a))", "inv", "((a))"),
    ("gD-3 (a) U b", "inv", "(a) U b"),
    ("gD-4 (a OR b)", "inv", "(a OR b)"),
    ("gD-5 !(a)", "inv", "!(a)"),
    ("gD-6 (a U b)", "inv", "(a U b)"),
    ("gD-7 ((a U b))", "inv", "((a U b))"),
    ("gD-8 (a -> b) U a", "inv", "(a -> b) U a"),
    ("gD-9 !(a && b)", "inv", "!(a && b)"),
    ("gD-10 G (a || b)", "inv", "G (a || b)"),
    ("gD-11 (!a)", "inv", "(!a)"),
    ("gD-12 (G a) -> (F b)", "inv", "(G a) -> (F b)"),
    ("gD-13 ((a) U (b))", "inv", "((a) U (b))"),
    ("gD-14 (a) && ((b) || a)", "inv", "(a) && ((b) || a)"),
    ("gD-15 (a) == b", "inv", "(a) == b"),
    ("gD-16 (a == b) -> (X (a))", "inv", "(a == b) -> (X (a))"),

    # Group B: OR or AND after an expression that ends a term. One token
    # of lookahead does not tell an operator of the expression from an
    # operator of the term; the input still has one derivation.
    ("gB-1 WHEN a OR term", "term",
     "alice MAY pay WHEN a OR bob MUST ship"),
    ("gB-2 WHEN a AND term", "term",
     "alice MAY pay WHEN a AND bob MUST ship"),
    ("gB-3 PENALTY a OR term", "term",
     "alice ON_BREACH PENALTY a OR bob MUST ship"),
    ("gB-4 WHEN a AND (term)", "term",
     "alice MUST_NOT pay WHEN a AND (bob MUST ship)"),
    ("gB-5 WHEN (a) OR ((term))", "term",
     "alice MAY pay WHEN (a) OR ((bob MUST ship))"),
    ("gB-6 WHEN a OR b AND term", "term",
     "alice MAY pay WHEN a OR b AND bob MUST ship"),

    # Numbers: a decimal literal is one exact token; there is no Float.
    ("N-1  decimal literal", "inv", "ALWAYS(n >= 12.50)"),
    ("N-2  negative decimal", "inv", "ALWAYS(n > -0.5 AND n <= 1.0)"),
    ("N-3  Decimal in LET", "inv", "ALWAYS(LET x : Decimal = 1.5 IN x == n)"),
    ("N-4  decimal PENALTY", "term", "alice ON_BREACH PENALTY 250.50 CAP 1000.00"),

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

    # Group A: an IF or LET expression is not a primary; without
    # parentheses it is not an operand (compare gA-8, gA-9, gA-10).
    ("gA-R1 a OR IF", "inv", "ALWAYS(a OR IF a THEN b ELSE a)"),
    ("gA-R2 NOT IF", "inv", "ALWAYS(NOT IF a THEN b ELSE a)"),
    ("gA-R3 n + LET", "inv", "ALWAYS(n + LET x : Integer = 1 IN x == 3)"),
    ("gA-R4 n == IF", "inv", "ALWAYS(n == IF a THEN 1 ELSE 2)"),
    ("gA-R5 - IF", "inv", "ALWAYS(- IF a THEN 1 ELSE 2 == n)"),

    # Numbers (compare N-1 and N-3): no exponent notation, no Float type.
    ("N-R1 exponent", "inv", "ALWAYS(n >= 1.5e3)"),
    ("N-R2 exponent E-", "inv", "ALWAYS(n >= 2.0E-1)"),
    ("N-R3 Float type", "inv", "ALWAYS(LET x : Float = 1.5 IN x == n)"),
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


def rules(tree):
    return {t.data for t in tree.iter_subtrees()}


def invariant_alternative(tree):
    """The alternative of expr chosen for the argument of the invariant."""
    inv = next(t for t in tree.iter_subtrees_topdown() if t.data == "state_invariant")
    return str(inv.children[0].children[0].data)


def top_base_term(tree):
    """matched_term or unmatched_term: whether the first term is closed."""
    base = next(t for t in tree.iter_subtrees_topdown() if t.data == "base_term")
    return str(base.children[0].data)


# Which parse was chosen for groups A, C and D: (label, slot, fragment,
# a function of the tree, its expected value).
STRUCTURE_CASES = [
    ("S-5  ELSE branch takes OR", "inv",
     "ALWAYS(IF a THEN b ELSE a OR b)", invariant_alternative, "if_expr"),
    ("S-6  IN branch takes ==", "inv",
     "ALWAYS(LET x : Integer = 1 IN x + n == 3)", invariant_alternative, "let_expr"),
    ("S-7  (IF) OR b: disjunction", "inv",
     "ALWAYS((IF a THEN b ELSE a) OR b)", invariant_alternative, "implication_expr"),
    ("S-8  ELSE closes inner IF", "term",
     "IF a THEN ON e DO IF b THEN alice MUST pay ELSE bob MUST ship",
     top_base_term, "unmatched_term"),
    ("S-9  two ELSE close both", "term",
     "IF a THEN ON e DO IF b THEN alice MUST pay ELSE bob MUST ship "
     "ELSE alice MUST notify", top_base_term, "matched_term"),
    ("S-10 open IF under ON..DO", "term",
     "ON e DO IF b THEN alice MUST pay",
     lambda t: "unmatched_trigger" in rules(t), True),
    ("S-11 closed IF under ON..DO", "term",
     "ON e DO IF b THEN alice MUST pay ELSE bob MUST ship",
     lambda t: "unmatched_trigger" in rules(t), False),
    ("S-12 (a) U b: state parens", "inv",
     "(a) U b", lambda t: "ltl_op_expr" in rules(t), False),
    ("S-13 ((a)): state parens", "inv",
     "((a))", lambda t: "ltl_op_expr" in rules(t), False),
    ("S-14 (a U b): LTL parens", "inv",
     "(a U b)", lambda t: "ltl_op_expr" in rules(t), True),
]

# The shift/reduce conflicts of the LALR(1) table, as (terminal, rule that
# would be reduced), and nothing else: no other shift/reduce conflict and
# no reduce/reduce conflict. All four are one decision, OR or AND after an
# expression that ends a term (group B above), met in two states per
# operator: after the first operand of the expression and after a later
# one. They are not ambiguities (TECHNICAL_REPORT.md §2.12).
LALR_CONFLICTS = [
    ("AND", "conjunction_expr"),
    ("AND", "conjunction_expr"),
    ("OR", "disjunction_expr"),
    ("OR", "disjunction_expr"),
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


def count_derivations(tree, memo=None):
    """The number of parse trees packed into a tree built with
    ambiguity='explicit': the alternatives of an _ambig node add up, the
    children of any other node multiply."""
    if not isinstance(tree, Tree):
        return 1
    memo = {} if memo is None else memo
    if id(tree) not in memo:
        counts = [count_derivations(c, memo) for c in tree.children]
        if tree.data == "_ambig":
            memo[id(tree)] = sum(counts)
        else:
            total = 1
            for n in counts:
                total *= n
            memo[id(tree)] = total
    return memo[id(tree)]


def serialise(tree):
    """A tree as text: rule names, and tokens with their terminal names."""
    if tree is None:
        return "_"
    if isinstance(tree, Token):
        return f"{tree.type}:{tree.value!r}"
    return "(" + " ".join([tree.data] + [serialise(c) for c in tree.children]) + ")"


class ConflictLog(logging.Handler):
    """Collects the shift/reduce conflicts lark reports while it builds an
    LALR(1) table: a line naming the terminal, then a line with the rule."""

    def __init__(self):
        super().__init__()
        self.found = []
        self.terminal = None

    def emit(self, record):
        if str(record.msg).startswith("Shift/Reduce conflict"):
            self.terminal = record.args[0]
        elif self.terminal is not None:
            self.found.append((str(self.terminal), str(record.args[0].origin.name)))
            self.terminal = None


def build_lalr(grammar):
    """The LALR(1) parser of the grammar (None if the table has a
    reduce/reduce conflict), its shift/reduce conflicts, and the number of
    reduce/reduce conflicts."""
    log = ConflictLog()
    handlers, level = logger.handlers[:], logger.level
    logger.handlers[:] = [log]
    logger.setLevel(logging.DEBUG)
    try:
        lalr = Lark(grammar, start="start", parser="lalr", propagate_positions=True)
        reduce_reduce = 0
    except GrammarError as exc:
        lalr = None
        reduce_reduce = str(exc).count("Reduce/Reduce collision")
        if not reduce_reduce:
            raise
    finally:
        logger.handlers[:] = handlers
        logger.setLevel(level)
    return lalr, sorted(log.found), reduce_reduce


def exercises_a_conflict(tree):
    """Whether OR or AND joins two terms right after an expression: an
    operand of a term-level OR or AND, other than the last, ends where an
    expression ends. These are the inputs of group B."""
    for node in tree.iter_subtrees():
        if node.data not in ("choice_expr", "parallel_expr"):
            continue
        operands = [c for c in node.children if isinstance(c, Tree)]
        for operand in operands[:-1]:
            if any(e.data == "expr" and e.meta.end_pos == operand.meta.end_pos
                   for e in operand.iter_subtrees()):
                return True
    return False


def corpus():
    """Every example and every fragment of this file, as (name, source)."""
    out = [(p.relative_to(REPO).as_posix(), p.read_text(encoding="utf-8"))
           for p in sorted((REPO / "examples").rglob("*.triel"))]
    out += [(label, build(slot, fragment)) for label, slot, fragment in CASES + REJECT_CASES]
    out += [(label, build("term", fragment))
            for label, fragment, _ in SHAPE_CASES + CHOICE_CASES]
    out += [(case[0], build(case[1], case[2])) for case in STRUCTURE_CASES]
    return out


def main():
    grammar = GRAMMAR.read_text()
    parser = Lark(
        grammar,
        start="start",
        parser="earley",
        ambiguity="explicit",
        lexer="dynamic",
        propagate_positions=True,
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

        derivations = count_derivations(tree)
        if derivations != 1:
            failures.append(f"{label}: {derivations} derivations -- {fragment}")
            print(f"  FAIL  {label:28s} {derivations} derivations")
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

    for label, slot, fragment, measure, expected in STRUCTURE_CASES:
        try:
            got = measure(parser.parse(build(slot, fragment)))
        except Exception as exc:
            failures.append(f"{label}: did not parse ({type(exc).__name__}) -- {fragment}")
            print(f"  FAIL  {label:28s} did not parse")
            continue
        if got == expected:
            print(f"  ok    {label:28s}")
        else:
            failures.append(f"{label}: {got}, expected {expected} -- {fragment}")
            print(f"  FAIL  {label:28s} {got} != {expected}")

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

    # The LALR(1) table: exactly the conflicts of LALR_CONFLICTS.
    lalr, shift_reduce, reduce_reduce = build_lalr(grammar)
    label = "LALR(1) conflicts"
    if shift_reduce == sorted(LALR_CONFLICTS) and reduce_reduce == 0:
        print(f"  ok    {label:28s} {len(shift_reduce)} shift/reduce, 0 reduce/reduce")
    else:
        failures.append(f"{label}: {len(shift_reduce)} shift/reduce {shift_reduce}, "
                        f"{reduce_reduce} reduce/reduce; expected {sorted(LALR_CONFLICTS)} "
                        "and no reduce/reduce")
        print(f"  FAIL  {label:28s} {len(shift_reduce)} shift/reduce, "
              f"{reduce_reduce} reduce/reduce")

    # Earley against LALR(1) on the corpus. An input Earley accepts has one
    # derivation; outside group B, LALR(1) accepts it too and builds the
    # same tree; in group B, LALR(1) shifts the operator and fails. An
    # input Earley rejects, LALR(1) rejects.
    inputs = corpus() if lalr is not None else []
    if lalr is None:
        failures.append("corpus: no LALR(1) parser to compare Earley with")
    compared = conflicting = rejected = 0
    parsed = {}
    for name, source in inputs:
        if source not in parsed:
            try:
                tree = parser.parse(source)
            except Exception:
                tree = None
            try:
                lalr_tree = lalr.parse(source)
            except Exception:
                lalr_tree = None
            parsed[source] = tree, lalr_tree
        tree, lalr_tree = parsed[source]
        if tree is None:
            rejected += lalr_tree is None
            problem = "rejected by Earley, accepted by LALR(1)" if lalr_tree is not None else None
        elif count_derivations(tree) != 1:
            problem = f"{count_derivations(tree)} derivations"
        elif exercises_a_conflict(tree):
            conflicting += 1
            problem = "group B input accepted by LALR(1)" if lalr_tree is not None else None
        elif lalr_tree is None:
            problem = "accepted by Earley, rejected by LALR(1)"
        else:
            compared += 1
            same = serialise(tree).encode() == serialise(lalr_tree).encode()
            problem = None if same else "Earley and LALR(1) trees differ"
        if problem:
            failures.append(f"corpus {name}: {problem}")
            print(f"  FAIL  {name:28s} {problem}")
    label = "Earley against LALR(1)"
    print(f"  ----  {label:28s} {len(inputs)} inputs: {compared} identical trees, "
          f"{conflicting} of group B, {rejected} rejected by both")

    total = (len(CASES) + len(REJECT_CASES) + len(STRUCTURE_CASES) + len(SHAPE_CASES)
             + len(CHOICE_CASES) + 1 + len(inputs))
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
