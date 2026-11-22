"""The corpus of the translator, parser/corpus/cases.jsonl, against the
translator parser/triel_to_core.py (parser/corpus/README.md).

Run from the repository root:  python3 -m pytest -q parser/test_corpus.py

test_case is parametrized by the id of a case: the number of its failed
parameters is the number of cases on which the translator and the corpus
disagree. The other functions check the format of the corpus, that the cases
cover the grammar, that every reason has a pair of cases, and that every reason
the code can give is in the table of classes; and they check the checks
themselves: the format and the comparison on spoilt copies of cases, and the
rule of the README for another implementation on outputs built here.
"""
import difflib
import gc
import json
import re
import sys
from pathlib import Path

import pytest
from lark import UnexpectedInput

PARSER = Path(__file__).resolve().parent
CORPUS = PARSER / "corpus"
sys.path.insert(0, str(PARSER))
sys.path.insert(0, str(CORPUS))
import triel_to_core  # noqa: E402
from triel_to_core import RULES, header, sexp, translate  # noqa: E402
import rejects  # noqa: E402

# False while the accepted cases written before the first run of the translator
# have no term and no header; True once every accepted case has both, and every
# rejected case has its header.
TERMS_RECORDED = True


def read_cases(text):
    """The cases in the text of cases.jsonl, one JSON object per line. A line
    that is not a JSON object is an error that names the line."""
    cases = []
    for n, line in enumerate(text.splitlines(), 1):
        try:
            c = json.loads(line)
        except json.JSONDecodeError as e:
            raise ValueError(f"cases.jsonl, line {n}: not JSON ({e.msg})") from None
        if not isinstance(c, dict):
            raise ValueError(f"cases.jsonl, line {n}: not a JSON object")
        cases.append(c)
    return cases


CASES_TEXT = (CORPUS / "cases.jsonl").read_bytes().decode("utf-8")
CASES = read_cases(CASES_TEXT)
BY_ID = {c["id"]: c for c in CASES}
TABLE = json.loads((CORPUS / "classes.json").read_text(encoding="utf-8"))
CLASSES = TABLE["reasons"]
UNREACHABLE = json.loads((CORPUS / "unreachable.json").read_text(encoding="utf-8"))
SOURCE = (PARSER / "triel_to_core.py").read_text(encoding="utf-8")
GRAMMAR_RULES = re.findall(r"^([a-z_][a-z0-9_]*)\s*:", (PARSER / "triel.lark").read_text(encoding="utf-8"),
                           flags=re.M)

# The arguments of reject that are not string literals, by kind, as counted in
# the translator (parser/corpus/rejects.py); the test fails if they change.
ARGUMENT_KINDS = {"rules": 9, "fstring": 4, "why": 1, "c.value": 1, "PROHIBITION_CONTINUATION": 1,
                  "other": 0}

FIELDS = {"id", "source", "outcome", "term", "header", "classes", "reasons", "single_defect", "pair",
          "rules", "origin", "contains", "disputed", "same_term"}
OUTCOMES = ("accepted", "rejected", "parse_error")


# --- one parse per input -------------------------------------------------------

TREES = {}


class CachedParser:
    """The parser of the translator, with the trees (or the parse errors) cached by text.

    The garbage collector is off while a text is parsed; then the garbage of the
    parse is collected and the trees kept so far are frozen, so that later
    collections do not walk them again. This halves the time of the check and
    changes no result."""

    def __init__(self, parser):
        self.parser = parser

    def parse(self, text):
        if text not in TREES:
            gc.disable()
            try:
                TREES[text] = self.parser.parse(text)
            except UnexpectedInput as e:
                TREES[text] = e
            finally:
                gc.enable()
                gc.collect()
                gc.freeze()
        r = TREES[text]
        if isinstance(r, UnexpectedInput):
            raise r
        return r


@pytest.fixture(scope="module", autouse=True)
def cached_parser():
    cached = CachedParser(triel_to_core.parser())
    with pytest.MonkeyPatch.context() as mp:
        mp.setattr(triel_to_core, "parser", lambda: cached)
        yield
    gc.unfreeze()


def tree(text):
    """The parse tree of text, from the cache, or None for a parse error."""
    try:
        return triel_to_core.parser().parse(text)
    except UnexpectedInput:
        return None


def output(c, ns=None):
    """What the translator gives for the source of case c: (outcome, term, header, reasons).
    ns, if given, is the namespace of another translator module, whose translate,
    header and sexp are used instead."""
    tr_, header_, sexp_ = (translate, header, sexp) if ns is None else (ns["translate"], ns["header"], ns["sexp"])
    try:
        tr = tr_(c["source"])
    except UnexpectedInput:
        return "parse_error", None, None, None
    if tr.rejected:
        return "rejected", None, header_(tr), sorted(tr.rejected)
    return "accepted", sexp_(tr.core), header_(tr), []


def mismatches(c, out):
    """Where the output out of output() differs from the fields of case c, compared
    exactly, as for the reference translator: the failed checks, [] if none."""
    outcome, term, head, reasons = out
    if outcome != c["outcome"]:
        return [f"outcome {outcome!r}, not {c['outcome']!r}"]
    bad = []
    if outcome == "accepted":
        if ("term" in c or TERMS_RECORDED) and term != c.get("term"):
            bad.append(f"term {term!r}, not {c.get('term')!r}")
        if ("header" in c or TERMS_RECORDED) and head != c.get("header"):
            bad.append(f"header {head!r}, not {c.get('header')!r}")
    if outcome == "rejected":
        if ("header" in c or TERMS_RECORDED) and head != c.get("header"):
            bad.append(f"header {head!r}, not {c.get('header')!r}")
        unknown = [r for r in reasons if r not in CLASSES]
        if unknown:
            bad.append(f"reasons not in classes.json: {unknown}")
        elif sorted({CLASSES[r]["class"] for r in reasons}) != c.get("classes"):
            bad.append(f"classes {sorted({CLASSES[r]['class'] for r in reasons})!r}, not {c.get('classes')!r}")
        if reasons != c.get("reasons"):
            bad.append(f"reasons {reasons!r}, not {c.get('reasons')!r}")
        if c.get("single_defect") and len(reasons) != 1:
            bad.append("single_defect with more than one reason")
    for ch in c.get("contains", []):
        if "substring" in ch and not (term is not None and ch["substring"] in term):
            bad.append(f"no substring {ch['substring']!r}")
        if "reasons" in ch and (reasons or []) != ch["reasons"]:
            bad.append(f"reasons {reasons!r}, not {ch['reasons']!r} of contains")
        if "metadata" in ch and not (head is not None and head[1:] == ch["metadata"]):
            bad.append(f"metadata {None if head is None else head[1:]!r}, not {ch['metadata']!r}")
    return bad


# --- A.1: format -----------------------------------------------------------------

def format_errors(cases=None, text=None):
    """The errors of format of a list of cases (default: the corpus, with its
    text); pair and same_term refer to cases of that list."""
    if cases is None:
        cases, text = CASES, CASES_TEXT
    by_id = {c.get("id"): c for c in cases}
    errors = []
    if text is not None and (not text.endswith("\n") or "\r" in text):
        errors.append("cases.jsonl: not LF line ends with a final line end")
    ids = [c.get("id") for c in cases]
    if ids != sorted(ids):
        errors.append("cases.jsonl: the lines are not sorted by id")
    if len(set(ids)) != len(ids):
        errors.append("cases.jsonl: an id is used twice")
    for c in cases:
        i = c.get("id")
        err = lambda m: errors.append(f"{i}: {m}")  # noqa: E731
        if set(c) - FIELDS:
            err(f"unknown fields {sorted(set(c) - FIELDS)}")
        if not isinstance(i, str) or not re.fullmatch(r"[A-Za-z0-9._-]+", i):
            err("id is not of Latin letters, digits, '.', '_' and '-'")
        if not isinstance(c.get("source"), str) or not c["source"].strip():
            err("no source")
        o = c.get("outcome")
        if o not in OUTCOMES:
            err(f"outcome {o!r}")
        if not isinstance(c.get("rules"), list) or not all(r in GRAMMAR_RULES for r in c["rules"]):
            err("rules is not a list of rules of triel.lark")
        origin = c.get("origin")
        if origin != "new" and not (isinstance(origin, list) and origin and origin == sorted(set(origin))
                                    and all(re.fullmatch(r"test_triel_to_core\.py::test_\w+", x) for x in origin)):
            err("origin is neither new nor a sorted list of test_triel_to_core.py::<test>")
        if (origin == "new") != i.startswith("new."):
            err("an id starts with new. exactly when origin is new")
        accepted_only = ("term",)
        rejected_only = ("classes", "reasons", "single_defect")
        for k in accepted_only:
            if o != "accepted" and k in c:
                err(f"{k} on a case that is not accepted")
        if o == "accepted":
            for k in accepted_only:
                if k not in c and TERMS_RECORDED:
                    err(f"accepted without {k}")
            if "term" in c and not isinstance(c["term"], str):
                err("term is not a string")
        if "header" in c and not (isinstance(c["header"], list) and c["header"]
                                  and isinstance(c["header"][0], str) and c["header"][0].startswith("SPEC ")
                                  and all(isinstance(h, str) and h.startswith("METADATA ")
                                          for h in c["header"][1:])):
            err("header is not SPEC and METADATA lines")
        if TERMS_RECORDED and o in ("accepted", "rejected") and "header" not in c:
            err(f"{o} without header")
        if o == "parse_error" and "header" in c:
            err("header on a case that does not parse")
        for k in rejected_only:
            if o != "rejected" and k in c:
                err(f"{k} on a case that is not rejected")
        if o == "rejected":
            rs = c.get("reasons")
            if not (isinstance(rs, list) and rs and rs == sorted(set(rs))):
                err("reasons is not a sorted list without repetitions")
            elif any(r not in CLASSES for r in rs):
                err(f"reasons not in classes.json: {[r for r in rs if r not in CLASSES]}")
            elif c.get("classes") != sorted({CLASSES[r]["class"] for r in rs}):
                err("classes is not the sorted list of the classes of reasons")
            if "single_defect" in c and c["single_defect"] is not True:
                err("single_defect is not true")
            if c.get("single_defect") and isinstance(rs, list) and len(rs) != 1:
                err("single_defect with more than one reason")
        for k in ("pair", "same_term"):
            if k in c:
                j = c[k]
                if j not in by_id or j == i or by_id[j].get(k) != i:
                    err(f"{k} {j!r} does not refer back")
        if "same_term" in c and (o != "accepted" or by_id.get(c["same_term"], {}).get("outcome") != "accepted"):
            err("same_term between cases that are not both accepted")
        if "disputed" in c and not (isinstance(c["disputed"], str) and c["disputed"].strip()):
            err("disputed is not a text")
        checks = c.get("contains")
        if origin != "new" or o == "accepted":
            if not isinstance(checks, list):
                err("no contains")
                checks = []
        for ch in checks or []:
            if not (isinstance(ch, dict) and len(ch) == 1
                    and set(ch) <= {"substring", "reasons", "metadata"}):
                err(f"check {ch!r} is not one of substring, reasons, metadata")
            elif "substring" in ch and not isinstance(ch["substring"], str):
                err("substring is not a string")
            elif "substring" not in ch and not isinstance(next(iter(ch.values())), list):
                err(f"{next(iter(ch))} is not a list")
        if origin == "new" and o == "accepted" and not any("substring" in ch for ch in checks or []):
            err("a new accepted case without a substring")
    return errors


def test_format():
    assert format_errors() == []


# --- A.2: every case against the translator -----------------------------------------

@pytest.mark.parametrize("c", CASES, ids=[c["id"] for c in CASES])
def test_case(c):
    out = output(c)
    assert mismatches(c, out) == []
    if out[0] == "accepted" and "same_term" in c:
        assert out[1] == output(BY_ID[c["same_term"]])[1]


# --- A.3: the grammar ------------------------------------------------------------------

def test_every_rule_of_the_grammar_is_in_a_tree():
    assert len(GRAMMAR_RULES) == len(set(GRAMMAR_RULES)) == len(RULES)
    seen = set()
    wrong = []
    for c in CASES:
        t = tree(c["source"])
        names = set() if t is None else {s.data for s in t.iter_subtrees()}
        seen |= names
        wrong += [(c["id"], r) for r in c["rules"] if r not in names]
    assert wrong == [], "rules of a case not in its tree"
    assert [r for r in GRAMMAR_RULES if r not in seen] == []


# --- A.4: a pair for every reason -------------------------------------------------------

def opcodes(a, b):
    return [op for op in difflib.SequenceMatcher(None, a, b).get_opcodes() if op[0] != "equal"]


def test_pairs_differ_in_at_most_two_places():
    far = [c["id"] for c in CASES if "pair" in c and len(opcodes(c["source"], BY_ID[c["pair"]]["source"])) > 2]
    assert far == []


def test_every_reason_has_a_pair():
    unreachable_calls = {(u["function"], u["index"]) for u in UNREACHABLE if u["kind"] == "unreachable"}
    calls = rejects.calls(SOURCE)
    missing = []
    for reason, row in CLASSES.items():
        pairs = [c for c in CASES if c["outcome"] == "rejected" and c.get("single_defect")
                 and c["reasons"] == [reason] and "pair" in c and BY_ID[c["pair"]]["outcome"] == "accepted"]
        if pairs:
            continue
        if "not_single" in row:
            if any(c["outcome"] == "rejected" and reason in c["reasons"] for c in CASES):
                continue
            missing.append((reason, "no case in which it is among several reasons"))
            continue
        own = [(x["function"], x["index"]) for x in calls if x["kind"] == "str" and x["value"] == reason]
        if row.get("unreachable") and own and all(k in unreachable_calls for k in own):
            continue
        missing.append((reason, "no pair"))
    assert missing == []


# --- A.5: every reason of the code is in the table ------------------------------------------

def test_every_reason_of_the_code_is_in_the_table():
    kinds = rejects.summary(SOURCE)["kinds"]
    assert {k: kinds[k] for k in ARGUMENT_KINDS} == ARGUMENT_KINDS
    found = rejects.reasons(SOURCE)
    assert sorted(set(found) - set(CLASSES)) == []
    assert sorted(set(CLASSES) - set(found)) == []
    for reason, row in CLASSES.items():
        assert row["class"] in TABLE["classes"] and row.get("section")
        srcs = [s for s in found[reason] if s not in ("reject", "RULES")]
        assert (row.get("from") or None) == ("; ".join(srcs) or None), reason


# --- A.6: the checks of the format and the comparison, on spoilt copies of cases -----------

REJECTED = "new.gap.deadline_in_the_branch_of_when"   # rejected, header ["SPEC gaps"], no pair
WITH_METADATA = "moved.caused_by_is_rejected.01"      # rejected, with a METADATA line, no pair
NOT_PARSED = "moved.float_and_exponents_do_not_parse.01"


def spoilt(case_id, **fields):
    """A copy of a case of the corpus with fields replaced; None removes a field."""
    c = dict(BY_ID[case_id])
    for k, v in fields.items():
        if v is None:
            c.pop(k, None)
        else:
            c[k] = v
    return c


SPOILT_FORMAT = {
    "rejected_without_header": (spoilt(REJECTED, header=None), "rejected without header"),
    "header_on_a_parse_error": (spoilt(NOT_PARSED, header=["SPEC t"]), "header on a case that does not parse"),
    "empty_header": (spoilt(REJECTED, header=[]), "header is not SPEC and METADATA lines"),
    "header_line_not_a_string": (spoilt(REJECTED, header=["SPEC gaps", 5]), "header is not SPEC and METADATA lines"),
    "two_spec_lines": (spoilt(REJECTED, header=["SPEC gaps", "SPEC gaps"]), "header is not SPEC and METADATA lines"),
}


@pytest.mark.parametrize("name", SPOILT_FORMAT)
def test_format_of_a_spoilt_case(name):
    c, message = SPOILT_FORMAT[name]
    assert format_errors([BY_ID[c["id"]]]) == []
    assert format_errors([c]) == [f"{c['id']}: {message}"]


def test_header_on_a_parse_error_whatever_terms_recorded(monkeypatch):
    monkeypatch.setattr(sys.modules[__name__], "TERMS_RECORDED", False)
    c, message = SPOILT_FORMAT["header_on_a_parse_error"]
    assert format_errors([c]) == [f"{c['id']}: {message}"]


def test_pair_and_same_term_refer_to_the_cases_given():
    bad, fix = BY_ID["new.field_default.bad"], BY_ID["new.field_default.fix"]
    assert format_errors([bad, fix]) == []
    assert format_errors([bad]) == [f"{bad['id']}: pair {fix['id']!r} does not refer back"]
    copies = [dict(bad, id="new.x.bad", pair="new.x.fix"), dict(fix, id="new.x.fix", pair="new.x.bad")]
    assert format_errors(copies) == []
    raw, escaped = BY_ID["new.string_literal.raw"], BY_ID["new.string_literal.escaped"]
    assert format_errors([escaped, raw]) == []
    assert format_errors([raw]) == [f"{raw['id']}: same_term {escaped['id']!r} does not refer back",
                                    f"{raw['id']}: same_term between cases that are not both accepted"]
    copies = [dict(escaped, id="new.x.escaped", same_term="new.x.raw"),
              dict(raw, id="new.x.raw", same_term="new.x.escaped")]
    assert format_errors(copies) == []


def test_reading_a_spoilt_corpus():
    lines = CASES_TEXT.splitlines(keepends=True)[:3]
    assert read_cases("".join(lines)) == CASES[:3]
    with pytest.raises(ValueError, match=r"^cases\.jsonl, line 2: not JSON "):
        read_cases(lines[0] + lines[1][:60] + "\n" + lines[2])
    with pytest.raises(ValueError, match=r"^cases\.jsonl, line 3: not a JSON object$"):
        read_cases(lines[0] + lines[1] + '["id", "source"]\n')


SPOILT_HEADER = {
    "another_spec_line": (REJECTED, ["SPEC gapsX"]),
    "another_metadata_line": (WITH_METADATA, [BY_ID[WITH_METADATA]["header"][0], "METADATA POLARITY g 2.0"]),
}


@pytest.mark.parametrize("name", SPOILT_HEADER)
def test_another_header_of_a_rejected_case_is_a_mismatch(name):
    case_id, head = SPOILT_HEADER[name]
    c = BY_ID[case_id]
    out = output(c)
    assert mismatches(c, out) == []
    assert mismatches(dict(c, header=head), out) == [f"header {c['header']!r}, not {head!r}"]


# --- A.7: the rule for another implementation (README) ---------------------------------------

def another_implementation(c, outcome, term=None, classes=()):
    """The rule of parser/corpus/README.md for another implementation, given its
    outcome on the source of case c, its term if accepted and the classes of its
    reasons if rejected: "passed", "failed", or "disputed" for a difference on a
    case with disputed."""
    o = c["outcome"]
    if outcome != o:
        differs = True
    elif o == "accepted":
        differs = term != c["term"]
    elif o == "rejected" and c.get("single_defect"):
        differs = set(classes) != set(c["classes"])
    elif o == "rejected":
        differs = not set(classes) & set(c["classes"])
    else:
        differs = False
    if not differs:
        return "passed"
    return "disputed" if "disputed" in c else "failed"


TERM = "(spec (factors) (terms (must \"a\" \"pay\" (none) (none))) (invariants))"
ACCEPTED = {"outcome": "accepted", "term": TERM}
SINGLE = {"outcome": "rejected", "classes": ["types"], "single_defect": True}
SEVERAL = {"outcome": "rejected", "classes": ["names", "types"]}
PARSE_ERROR = {"outcome": "parse_error"}
DISPUTED = {"disputed": "The text does not decide the question."}

# name -> (case, outcome of the implementation, its term, its classes, the verdict)
ANOTHER = {
    "single_defect_with_another_class": (SINGLE, "rejected", None, ["names", "types"], "failed"),
    "single_defect_with_the_classes": (SINGLE, "rejected", None, ["types"], "passed"),
    "several_with_one_class_in_common": (SEVERAL, "rejected", None, ["time", "types"], "passed"),
    "several_without_a_class_in_common": (SEVERAL, "rejected", None, ["time"], "failed"),
    "several_without_a_class_in_common_disputed": (dict(SEVERAL, **DISPUTED), "rejected", None, ["time"], "disputed"),
    "another_outcome": (PARSE_ERROR, "accepted", TERM, [], "failed"),
    "another_outcome_disputed": (dict(PARSE_ERROR, **DISPUTED), "rejected", None, ["types"], "disputed"),
    "accepted_with_another_term": (ACCEPTED, "accepted", TERM.replace("pay", "ship"), [], "failed"),
    "accepted_with_the_term": (ACCEPTED, "accepted", TERM, [], "passed"),
    "parse_error": (PARSE_ERROR, "parse_error", None, [], "passed"),
    "disputed_without_a_difference": (dict(SEVERAL, **DISPUTED), "rejected", None, ["names"], "passed"),
}


@pytest.mark.parametrize("name", ANOTHER)
def test_the_rule_for_another_implementation(name):
    c, outcome, term, classes, verdict = ANOTHER[name]
    assert another_implementation(c, outcome, term, classes) == verdict
