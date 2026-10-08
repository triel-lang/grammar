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
    expected = (REPO / "examples/core/classification.expected").read_text().splitlines()
    assert out == expected


# --- translation rules ----------------------------------------------------

def test_boolean_factor_as_condition_is_visible():
    assert '(always (eq (name (path "f")) (const (bool true))))' in core(spec())


def test_not_equal_is_visible():
    c = core(spec(invariants='i : ALWAYS(g != "x")', factors="g : String METADATA"))
    assert '(not (eq (name (path "g")) (const (str "x"))))' in c


def test_datetime_is_seconds_since_the_epoch():
    c = core(spec(terms='a MUST b BY DATETIME("1970-01-02T00:00:00Z")'))
    assert '(must "a" "b" (at 86400))' in c


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


def test_penalty_literal_is_opaque():
    c = core(spec(terms='a MUST b WITHIN 1 DAYS; a ON_BREACH PENALTY 500, NOTIFY b2'))
    assert '(on_breach "a" (penalty (int 500)) (notify "b2"))' in c


def test_penalty_expression_is_rejected():
    assert rejected(spec(terms="a MUST b WITHIN 1 DAYS; a ON_BREACH PENALTY 5 * 2")) == \
        ["PENALTY expression"]


def test_only_the_outermost_construct_is_reported():
    src = spec(terms="WHEN g > 1 THEN a MUST b(1)", factors="g : Integer METADATA",
               invariants="i : ALWAYS(PRESENT(g))")
    assert rejected(src) == ["WHEN ... THEN (term)"]


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
    assert r.stdout.splitlines() == scn.with_suffix(".expected").read_text().splitlines()
