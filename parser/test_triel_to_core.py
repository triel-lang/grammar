"""Tests of the translator to the formal core and of the scenario driver.

Run from the repository root:  python3 -m pytest parser/test_triel_to_core.py
The scenario tests need the evaluator binary (see parser/triel_eval.py); they
are skipped when it is not built.
"""
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest
from lark import UnexpectedInput

sys.path.insert(0, str(Path(__file__).parent))
from triel_to_core import RULES, classify, sexp, translate  # noqa: E402
from triel_eval import default_evaluator  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
PARSER = REPO / "parser"


def spec(terms="a MUST b", factors="f : Boolean METADATA", invariants="i : ALWAYS(f)",
         decl=""):
    return (f"SPECIFICATION t VERSION 1.0.0 {decl}\n"
            "SUBJECTS { a : PARTY, b2 : PARTY }\n"
            f"TERMS {{ {terms} }}\nFACTORS {{ {factors} }}\nINVARIANTS {{ {invariants} }}\n")


def core(src):
    tr = translate(src)
    assert not tr.rejected, tr.rejected
    return sexp(tr.core)


def rejected(src):
    return sorted(translate(src).rejected)


# --- the rule table -------------------------------------------------------

def test_rule_table_covers_the_grammar():
    text = (PARSER / "triel.lark").read_text()
    rules = set(re.findall(r"^([a-z_][a-z0-9_]*)\s*:", text, flags=re.M))
    assert rules == set(RULES)


# --- classification of the examples --------------------------------------

def test_classification_of_the_examples(monkeypatch):
    monkeypatch.chdir(REPO)
    out, ok = classify(["examples"])
    assert ok
    expected = (REPO / "examples/core/classification.expected").read_text(encoding="utf-8").splitlines()
    assert out == expected


# --- translation rules ----------------------------------------------------

def test_boolean_factor_as_condition_is_visible():
    assert '(always (eq (name (path "f")) (const (bool true))))' in core(spec())


def test_not_equal_is_visible():
    c = core(spec(invariants='i : ALWAYS(g != "x")', factors="g : String METADATA"))
    assert '(not (eq (name (path "g")) (const (str "x"))))' in c


def test_decimal_literal_is_exact():
    c = core(spec(invariants="i : ALWAYS(g >= 12.50)", factors="g : Decimal METADATA"))
    assert '(factor "g" (prim decimal) (none))' in c
    assert '(always (le (const (dec 1250 2)) (name (path "g"))))' in c


@pytest.mark.parametrize("cond, expected", [
    ("g < 1", '(lt (name (path "g")) (const (int 1)))'),
    ("g <= 1", '(le (name (path "g")) (const (int 1)))'),
    ("g > 1", '(lt (const (int 1)) (name (path "g")))'),
    ("g >= 1", '(le (const (int 1)) (name (path "g")))'),
    ("g > -0.5", '(lt (const (dec -5 1)) (name (path "g")))'),
    ("g == 2500.00", '(eq (name (path "g")) (const (dec 250000 2)))'),
])
def test_ordering_comparisons(cond, expected):
    c = core(spec(invariants=f"i : ALWAYS({cond})", factors="g : Decimal METADATA"))
    assert f"(always {expected})" in c


@pytest.mark.parametrize("factors, cond", [
    ('g : String METADATA', 'g < "x"'),
    ('g : Boolean METADATA', 'g <= true'),
    ('g : DateTime METADATA', 'g > DATETIME("2026-01-01T00:00:00Z")'),
])
def test_ordering_comparison_of_a_non_number_is_rejected(factors, cond):
    assert rejected(spec(invariants=f"i : ALWAYS({cond})", factors=factors)) == \
        ["ordering comparison of a non-number"]


def test_integer_and_decimal_factors_compare():
    c = core(spec(invariants="i : ALWAYS(n <= g)", factors="n : Integer METADATA, g : Decimal METADATA"))
    assert '(always (le (name (path "n")) (name (path "g"))))' in c


@pytest.mark.parametrize("src", [
    spec(factors="f : Float METADATA"),
    spec(invariants="i : ALWAYS(g >= 1.5e3)", factors="g : Decimal METADATA"),
])
def test_float_and_exponents_do_not_parse(src):
    with pytest.raises(UnexpectedInput):
        translate(src)


def test_datetime_is_seconds_since_the_epoch():
    c = core(spec(terms='a MUST b BY DATETIME("1970-01-02T00:00:00Z")'))
    assert '(must "a" "b" (at 86400) (none))' in c


@pytest.mark.parametrize("text", ["2026-13-01T00:00:00Z", "2026-01-01T00:00:00+01:00",
                                  "2026-01-01"])
def test_datetime_must_be_iso_utc(text):
    assert rejected(spec(terms=f'a MUST b BY DATETIME("{text}")')) == ["DATETIME not ISO-8601 UTC"]


@pytest.mark.parametrize("unit", ["BUSINESS_DAYS", "MONTHS", "YEARS"])
def test_calendar_units_are_rejected(unit):
    assert rejected(spec(terms=f"a MUST b WITHIN 2 {unit}")) == ["calendar unit"]


def test_durations_are_seconds():
    c = core(spec(terms="a MUST b WITHIN 2 HOURS; a ON_BREACH CURE_BY 30 MINUTES"))
    assert '(after 7200)' in c and '(cure_by 1800)' in c


def test_penalty_literal():
    c = core(spec(terms='a MUST b WITHIN 1 DAYS; a ON_BREACH PENALTY 500, NOTIFY b2'))
    assert '(on_breach "a" (penalty (val (const (int 500))) (none)) (notify "b2"))' in c


CONT = "§2.6 defines continuations only for obligations"


@pytest.mark.parametrize("act", ["TERMINATE", "CURE_BY 1 DAYS", "ESCALATE_TO b2"])
def test_continuation_bound_to_a_prohibition_is_rejected(act):
    assert rejected(spec(terms=f"a MUST_NOT b; a ON_BREACH NOTIFY b2, {act}")) == [CONT]
    assert rejected(spec(terms=f"(a MUST_NOT b); a ON_BREACH {act}")) == [CONT]


def test_decimal_penalty_is_exact():
    c = core(spec(terms="a MUST b WITHIN 1 DAYS; a ON_BREACH PENALTY 250.50"))
    assert '(penalty (val (const (dec 25050 2))) (none))' in c


def test_informational_actions_bound_to_a_prohibition():
    c = core(spec(terms="a MUST_NOT b; a ON_BREACH NOTIFY b2, PENALTY 5"))
    assert '(on_breach "a" (notify "b2") (penalty (val (const (int 5))) (none)))' in c


@pytest.mark.parametrize("terms", [
    "a MUST_NOT b; a MUST c WITHIN 1 DAYS; a ON_BREACH TERMINATE",
    "a MUST c WITHIN 1 DAYS; b2 MUST_NOT b; a ON_BREACH TERMINATE",
    "a MUST c WITHIN 1 DAYS; a MAY d; a ON_BREACH TERMINATE",
    "a MUST c WITHIN 1 DAYS; a MUST_NOT b THEN a MUST d; a ON_BREACH TERMINATE",
])
def test_continuation_binds_to_the_nearest_obligation(terms):
    assert not translate(spec(terms=terms)).rejected


def test_continuation_after_the_nearest_prohibition_is_rejected():
    assert rejected(spec(terms="a MUST c WITHIN 1 DAYS; a MUST_NOT b; a ON_BREACH CURE_BY 1 DAYS"))         == [CONT]


N = "g : Decimal METADATA, h : Optional<Integer> METADATA, f : Boolean METADATA"


@pytest.mark.parametrize("amount, expected", [
    ("g * 0.05 CAP 10000",
     '(penalty (mul (val (name (path "g"))) (val (const (dec 5 2)))) (int 10000))'),
    ("g - 5 + 2 * 3",
     '(penalty (add (sub (val (name (path "g"))) (val (const (int 5)))) '
     '(mul (val (const (int 2))) (val (const (int 3))))) (none))'),
    ("-(g + 1) CAP 2.5",
     '(penalty (neg (add (val (name (path "g"))) (val (const (int 1))))) (dec 25 1))'),
    ("DEFAULT(h, 0) * 2",
     '(penalty (mul (val (default (path "h") (const (int 0)))) (val (const (int 2)))) (none))'),
])
def test_penalty_amount(amount, expected):
    c = core(spec(terms=f"a MUST b WITHIN 1 DAYS; a ON_BREACH PENALTY {amount}", factors=N))
    assert expected in c


@pytest.mark.parametrize("amount, why", [
    ("g / 2", "division in PENALTY"),
    ("g % 2", "division in PENALTY"),
    ('"x"', "PENALTY of a non-number"),
    ("f", "PENALTY of a non-number"),
    ("g > 1", "PENALTY of a non-number"),
    ("PRESENT(g)", "PENALTY of a non-number"),
    ('g CAP "x"', "CAP (not a number)"),
    ("k * 2", "undeclared factor"),
])
def test_penalty_rejections(amount, why):
    assert rejected(spec(terms=f"a MUST b WITHIN 1 DAYS; a ON_BREACH PENALTY {amount}",
                         factors=N)) == [why]


# --- action arguments and FROM ------------------------------------------------

@pytest.mark.parametrize("act, expected", [
    ("pay(b2, 100)", '(action "pay" (path "b2") (int 100))'),
    ("pay(b2, 100.50, -1)", '(action "pay" (path "b2") (dec 10050 2) (int -1))'),
    ('note("x", true)', '(action "note" (str "x") (bool true))'),
    ("submit(g)", '(action "submit" (path "g"))'),
    ("submit(r.x)", '(action "submit" (path "r" "x"))'),
    ("pay()", '(action "pay")'),
])
def test_action_arguments(act, expected):
    c = core(spec(terms=f"a MUST {act}", factors="f : Boolean METADATA, g : Integer METADATA, r : Record { x : Integer } METADATA"))
    assert f'(must "a" {expected} (none) (none))' in c


@pytest.mark.parametrize("act, why", [
    ("pay(c)", "action argument (undeclared name)"),
    ("pay(g + 1)", "action argument (not a name or literal)"),
    ("pay(g > 1)", "action argument (not a name or literal)"),
    ("pay(DEFAULT(g, 1))", "action argument (not a name or literal)"),
    ("pay(r.y)", "undeclared field"),
])
def test_action_argument_rejections(act, why):
    assert rejected(spec(terms=f"a MUST {act}",
                         factors="f : Boolean METADATA, g : Integer METADATA, r : Record { x : Integer } METADATA")) == [why]


def test_arguments_in_permissions_and_prohibitions():
    c = core(spec(terms="a MAY pay(b2) WHEN f; a MUST_NOT pay(b2, 1)"))
    assert '(may "a" (action "pay" (path "b2")) (eq (name (path "f")) (const (bool true))))' in c
    assert '(must_not "a" (action "pay" (path "b2") (int 1)) (true))' in c


@pytest.mark.parametrize("terms, expected", [
    ('a MUST b BY 10 DAYS FROM DATETIME("2026-03-01T00:00:00Z")',
     '(must "a" "b" (after 864000) (at 1772323200))'),
    ('a MUST b FROM DATETIME("2026-03-01T00:00:00Z")', '(must "a" "b" (none) (at 1772323200))'),
    ("a MUST b BY t FROM s", '(must "a" "b" (factor (path "t") 0) (factor (path "s") 0))'),
    ("a MUST b FROM s WITHIN 1 DAYS", '(must "a" "b" (after 86400) (factor (path "s") 0))'),
])
def test_from(terms, expected):
    c = core(spec(terms=terms, factors="f : Boolean METADATA, s : DateTime METADATA, t : DateTime METADATA"))
    assert f"(terms {expected})" in c


@pytest.mark.parametrize("terms, why", [
    ('a MUST b FROM DATETIME("2026-03-01T00:00:00Z") UNTIL DATETIME("2026-04-01T00:00:00Z")',
     "UNTIL"),
    ('a MAY c THEN a MUST b FROM DATETIME("2026-03-01T00:00:00Z")', "FROM in a composite term"),
    ('d := a MUST b FROM DATETIME("2026-03-01T00:00:00Z"); a MAY c THEN REF d',
     "REF to a term with FROM"),
    ("a MUST b FROM u", "undeclared factor"),
])
def test_from_rejections(terms, why):
    assert rejected(spec(terms=terms)) == [why]


def test_only_the_outermost_construct_is_reported():
    assert rejected(spec(terms="a MUST b AND a MUST c(1)")) == ["AND (term)"]


# --- conditional terms, named terms, DEFAULT --------------------------------

G = "g : Integer METADATA, f : Boolean METADATA"


@pytest.mark.parametrize("terms, expected", [
    ("IF g > 1 THEN a MUST b ELSE a MAY c",
     '(if (lt (const (int 1)) (name (path "g"))) (must "a" "b" (none) (none)) (may "a" "c" (true)))'),
    ("IF g > 1 THEN a MUST b",
     '(if (lt (const (int 1)) (name (path "g"))) (must "a" "b" (none) (none)) (skip))'),
    ("IF g > 1 THEN a MUST b ELIF g > 0 THEN a MUST c",
     '(if (lt (const (int 1)) (name (path "g"))) (must "a" "b" (none) (none)) '
     '(if (lt (const (int 0)) (name (path "g"))) (must "a" "c" (none) (none)) (skip)))'),
    ("IF g > 1 THEN a MUST b ELIF g > 0 THEN a MUST c ELSE a MUST d",
     '(if (lt (const (int 1)) (name (path "g"))) (must "a" "b" (none) (none)) '
     '(if (lt (const (int 0)) (name (path "g"))) (must "a" "c" (none) (none)) (must "a" "d" (none) (none))))'),
    ("WHEN g > 1 THEN a MUST b",
     '(if (lt (const (int 1)) (name (path "g"))) (must "a" "b" (none) (none)) (skip))'),
    ("IF g > 1 THEN IF g > 2 THEN a MUST b ELSE a MUST c",
     '(if (lt (const (int 1)) (name (path "g"))) (if (lt (const (int 2)) (name (path "g"))) '
     '(must "a" "b" (none) (none)) (must "a" "c" (none) (none))) (skip))'),
])
def test_conditional_terms(terms, expected):
    assert f"(terms {expected})" in core(spec(terms=terms, factors=G))


def test_conditional_branch_with_a_deadline_is_rejected():
    assert rejected(spec(terms="IF g > 1 THEN (a MUST b WITHIN 1 DAYS)", factors=G)) == \
        ["deadline in a composite term"]


def test_conditional_needs_a_boolean_condition():
    assert rejected(spec(terms="IF g THEN a MUST b", factors=G)) == ["non-Boolean condition"]


def test_named_term_is_an_element_and_ref_is_its_index():
    c = core(spec(terms="d := a MUST b THEN a MUST c; a MAY e; REF d UNLESS f DO REF d"))
    assert ('(terms (then (must "a" "b" (none) (none)) (must "a" "c" (none) (none))) (may "a" "e" (true)) '
            '(unless (ref 0) (eq (name (path "f")) (const (bool true))) (ref 0)))') in c


@pytest.mark.parametrize("terms, why", [
    ("a MUST b THEN REF d", "REF to an undeclared name"),
    ("a MUST b THEN REF d; d := a MUST c", "REF to a name declared later"),
    ("d := a MUST b THEN REF d", "REF to a name declared later"),
    ("d := a MUST b THEN REF e; e := a MUST c THEN REF d", "REF to a name declared later"),
    ("d := a MUST b WITHIN 1 DAYS; a MAY c THEN REF d", "REF to a term with a deadline"),
    ("a MUST b WITHIN 1 DAYS; h := a ON_BREACH NOTIFY b2; REF h", "REF to a breach handler"),
    ("d := a MUST b; d := a MUST c", "duplicate term name"),
])
def test_bad_references_are_rejected(terms, why):
    assert rejected(spec(terms=terms)) == [why]


def test_named_obligation_keeps_its_deadline_and_handler():
    c = core(spec(terms="d := a MUST b WITHIN 1 DAYS; a ON_BREACH NOTIFY b2"))
    assert '(terms (must "a" "b" (after 86400) (none)) (on_breach "a" (notify "b2")))' in c


@pytest.mark.parametrize("factors, cond, expected", [
    ("g : Optional<Integer> METADATA", "DEFAULT(g, 0) >= 0",
     '(le (const (int 0)) (default (path "g") (const (int 0))))'),
    ("g : Optional<Decimal> METADATA", "DEFAULT(g, 1) == 2.5",
     '(eq (default (path "g") (const (int 1))) (const (dec 25 1)))'),
    ("g : Optional<Boolean> METADATA", "DEFAULT(g, false)",
     '(eq (default (path "g") (const (bool false))) (const (bool true)))'),
    ("g : Optional<Integer> METADATA, h : Integer METADATA", "DEFAULT(g, h) < 3",
     '(lt (default (path "g") (name (path "h"))) (const (int 3)))'),
    ("g : Optional<String> METADATA", 'DEFAULT(g, "x") == "y"',
     '(eq (default (path "g") (const (str "x"))) (const (str "y")))'),
])
def test_default(factors, cond, expected):
    assert f"(always {expected})" in core(spec(invariants=f"i : ALWAYS({cond})", factors=factors))


@pytest.mark.parametrize("factors, cond, why", [
    ("r : Record { x : Integer } METADATA", "DEFAULT(r, 0) == 0", "DEFAULT of a record"),
    ("g : Optional<Integer> METADATA", 'DEFAULT(g, "x") == 0', "DEFAULT fallback of another type"),
    ("g : Optional<Integer> METADATA", "DEFAULT(g, 1 + 1) == 0", "arithmetic"),
    ("g : Optional<Integer> METADATA", "DEFAULT(g, g > 1) == 0", "DEFAULT fallback (not a value)"),
    ("g : Optional<String> METADATA", 'DEFAULT(g, "x")', "non-Boolean condition"),
    ("g : Optional<String> METADATA", 'DEFAULT(g, "x") < "y"', "ordering comparison of a non-number"),
])
def test_default_rejections(factors, cond, why):
    assert rejected(spec(invariants=f"i : ALWAYS({cond})", factors=factors)) == [why]


@pytest.mark.parametrize("within,expected", [
    ("2 DAYS", "(after 172800)"),
    ('DATETIME("2026-06-08T00:00:00Z")', "(at 1780876800)"),
    ("d", '(factor (path "d") 0)'),
    ("d + 1 HOURS", '(factor (path "d") 3600)'),
])
def test_eventually_within(within, expected):
    c = core(spec(factors="f : Boolean METADATA, d : DateTime METADATA",
                  invariants=f"i : EVENTUALLY(f) WITHIN {within}"))
    assert f'(invariant "i" (eventually_within (eq (name (path "f")) (const (bool true))) {expected}))' in c


@pytest.mark.parametrize("within,why", [
    ("2 MONTHS", "calendar unit"),
    ("e", "undeclared factor"),
])
def test_eventually_within_rejections(within, why):
    assert rejected(spec(invariants=f"i : EVENTUALLY(f) WITHIN {within}")) == [why]


def test_and_of_terms_is_rejected():
    assert rejected(spec(terms="a MUST b AND a MUST c")) == ["AND (term)"]


def test_deadline_inside_a_composite_term_is_rejected():
    assert rejected(spec(terms="a MUST b WITHIN 1 DAYS THEN a MUST c")) == \
        ["deadline in a composite term"]


def test_present_of_a_record_is_rejected():
    src = spec(factors="r : Record { x : Integer } METADATA", invariants="i : ALWAYS(PRESENT(r))")
    assert rejected(src) == ["PRESENT of a record"]


def test_metadata_lines():
    src = spec(decl='STANDARD "S1", "S2" JURISDICTION "EU" PROVENANCE_REQUIRED: true '
                    'CURRENCY: "USD"',
               factors="f : Boolean METADATA SOURCE a")
    tr = translate(src)
    assert tr.metadata == ['METADATA STANDARD "S1"', 'METADATA STANDARD "S2"',
                           'METADATA JURISDICTION "EU"', "METADATA PROVENANCE_REQUIRED true",
                           'METADATA CURRENCY "USD"', "METADATA SOURCE f a"]


def test_heuristic_layer_is_metadata():
    tr = translate(spec(factors="f : Integer POLARITY -0.5 THRESHOLD 3 SOURCE a SENSITIVITY_BOUND 1.5",
                        invariants="i : ALWAYS(f >= 0)"))
    assert not tr.rejected
    assert tr.metadata == ["METADATA POLARITY f -0.5", "METADATA THRESHOLD f 3",
                           "METADATA SOURCE f a", "METADATA SENSITIVITY_BOUND f 1.5"]
    assert '(factor "f" (prim int) (none))' in sexp(tr.core)


def test_caused_by_is_rejected():
    assert rejected(spec(factors="f : Boolean METADATA, g : Integer POLARITY 1.0 CAUSED_BY { f WEIGHT 0.5 }")) == \
        ["CAUSED_BY"]


def test_stale_block_needs_max_age():
    assert rejected(spec(factors="f : Boolean METADATA ON_STALE BLOCK")) == \
        ["ON_STALE without MAX_AGE"]
    assert rejected(spec(factors="f : Boolean METADATA MAX_AGE 1 DAYS")) == \
        ["MAX_AGE without ON_STALE"]
    assert '(block 86400)' in core(spec(factors="f : Boolean METADATA MAX_AGE 1 DAYS ON_STALE BLOCK"))


# --- command-line behaviour ----------------------------------------------

def run(args, **kw):
    return subprocess.run([sys.executable] + args, capture_output=True, text=True, **kw)


def test_exit_codes(tmp_path):
    ok, bad, broken = tmp_path / "ok.triel", tmp_path / "bad.triel", tmp_path / "broken.triel"
    ok.write_text(spec())
    bad.write_text(spec(terms="a MUST b AND a MUST c"))
    broken.write_text("SPECIFICATION")
    t2c = str(PARSER / "triel_to_core.py")
    assert run([t2c, str(ok)]).returncode == 0
    r = run([t2c, str(bad)])
    assert r.returncode == 2 and "REJECTED: AND (term)" in r.stdout
    assert run([t2c, str(broken)]).returncode == 1


# --- scenarios ------------------------------------------------------------

SCENARIOS = sorted((REPO / "examples/core/scenarios").glob("*.scn"))


@pytest.mark.parametrize("scn", SCENARIOS, ids=[s.stem for s in SCENARIOS])
def test_scenario_input_is_well_formed(scn):
    r = run([str(PARSER / "triel_eval.py"), str(scn), "--input"], cwd=REPO)
    assert r.returncode == 0 and r.stdout.startswith("(input (spec ")


@pytest.mark.skipif(not os.path.exists(default_evaluator()), reason="evaluator not built")
@pytest.mark.parametrize("scn", SCENARIOS, ids=[s.stem for s in SCENARIOS])
def test_scenario_matches_the_expected_output(scn):
    r = run([str(PARSER / "triel_eval.py"), str(scn)], cwd=REPO)
    assert r.returncode == 0, r.stderr
    assert r.stdout.splitlines() == scn.with_suffix(".expected").read_text(encoding="utf-8").splitlines()
