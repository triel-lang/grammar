"""The corpus of the translator, parser/corpus/cases.jsonl, against the
translator parser/triel_to_core.py (parser/corpus/README.md).

Run from the repository root:  python3 -m pytest -q parser/test_corpus.py

test_case is parametrized by the id of a case: the number of its failed
parameters is the number of cases on which the translator and the corpus
disagree. The other functions check the format of the corpus, that the cases
cover the grammar, that every reason has a pair of cases, and that every reason
the code can give is in the table of classes.
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

CASES_TEXT = (CORPUS / "cases.jsonl").read_bytes().decode("utf-8")
CASES = [json.loads(line) for line in CASES_TEXT.splitlines()]
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


def output(c):
    """What the translator gives for the source of case c: (outcome, term, header, reasons)."""
    try:
        tr = translate(c["source"])
    except UnexpectedInput:
        return "parse_error", None, None, None
    if tr.rejected:
        return "rejected", None, header(tr), sorted(tr.rejected)
    return "accepted", sexp(tr.core), header(tr), []


# --- A.1: format -----------------------------------------------------------------

def format_errors():
    errors = []
    if not CASES_TEXT.endswith("\n") or "\r" in CASES_TEXT:
        errors.append("cases.jsonl: not LF line ends with a final line end")
    ids = [c.get("id") for c in CASES]
    if ids != sorted(ids):
        errors.append("cases.jsonl: the lines are not sorted by id")
    if len(set(ids)) != len(ids):
        errors.append("cases.jsonl: an id is used twice")
    for c in CASES:
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
        if TERMS_RECORDED and o == "parse_error" and "header" in c:
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
                if j not in BY_ID or j == i or BY_ID[j].get(k) != i:
                    err(f"{k} {j!r} does not refer back")
        if "same_term" in c and (o != "accepted" or BY_ID.get(c["same_term"], {}).get("outcome") != "accepted"):
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
    outcome, term, head, reasons = output(c)
    assert outcome == c["outcome"]
    if outcome == "accepted":
        if "term" in c or TERMS_RECORDED:
            assert term == c["term"]
        if "header" in c or TERMS_RECORDED:
            assert head == c["header"]
        if "same_term" in c:
            assert term == output(BY_ID[c["same_term"]])[1]
    if outcome == "rejected":
        if "header" in c or TERMS_RECORDED:
            assert head == c["header"]
        unknown = [r for r in reasons if r not in CLASSES]
        assert unknown == [], "reasons not in classes.json"
        assert sorted({CLASSES[r]["class"] for r in reasons}) == c["classes"]
        assert reasons == c["reasons"]
        if c.get("single_defect"):
            assert len(reasons) == 1
    for ch in c.get("contains", []):
        if "substring" in ch:
            assert term is not None and ch["substring"] in term
        if "reasons" in ch:
            assert (reasons or []) == ch["reasons"]
        if "metadata" in ch:
            assert head is not None and head[1:] == ch["metadata"]


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
