#!/usr/bin/env python3
"""
Translator from TRIEL v2.4 to the formal core of formal/core (TRIEL_Exec.thy).

The input is parsed with the reference grammar parser/triel.lark. Every
construct of the specification is either translated into the core, listed as
metadata, or rejected by name. Nothing is dropped silently. Only the outermost
unsupported construct is reported: the translator does not look inside a
construct it rejects.

Usage:
    python3 triel_to_core.py FILE.triel            # header lines and the core AST
    python3 triel_to_core.py --classify PATH ...   # ACCEPTED / REJECTED per file

Exit codes: 0 accepted, 2 rejected, 1 parse or usage error. With --classify the
exit code is 0 whenever every file parses.

Conventions of the translation (formal/core/CORE.md, section on the evaluator):
  * DATETIME("YYYY-MM-DDThh:mm:ssZ") is the number of seconds since
    1970-01-01T00:00:00Z. SECOND, MINUTE, HOUR and DAY durations are converted
    to seconds; calendar units (BUSINESS_DAY, MONTH, YEAR) are rejected.
  * A Boolean factor used as a condition, `x`, is `x == true`; `a != b` is
    `NOT (a == b)`. Both are visible in the printed core AST.
  * Numbers are exact. An integer literal is (int N); a decimal literal is
    (dec M K), the rational M / 10^K, so 12.50 is (dec 1250 2). Integer and
    Decimal factors are both numbers; every Integer is a Decimal.
  * `a < b` and `a <= b` are (lt a b) and (le a b); `a > b` is (lt b a) and
    `a >= b` is (le b a). The operands of an ordering comparison must be
    numbers: an Integer or Decimal factor, or a numeric literal.
  * IF c THEN t ELIF c2 THEN t2 ELSE e is (if c t (if c2 t2 e)); a missing ELSE
    is (skip), which completes Done at once. WHEN c THEN t is (if c t (skip)).
    The branches are composite terms, so a deadline in a branch is rejected.
  * `name := t` is the element t of the block, in force like any other; REF name
    is (ref K), K the index of that element in the block, counted from 0. A
    reference to an undeclared name or to a name declared at or after the
    reference (so also every cycle) is rejected, and so is a reference to a
    breach handler or to a term with a deadline, whose deadline a composite
    term cannot carry.
  * DEFAULT(f, d) is (default PATH V): the value of f if it is present, else d.
    f must not be a record; d must be a value of the type of f (a literal, a
    factor or another DEFAULT). A Boolean DEFAULT used as a condition is
    `DEFAULT(f, d) == true`.
  * An action with arguments, pay(bob, 100), is (action "pay" ARG ...). An
    argument is a literal (a value) or the name of a subject or a factor
    (a path), which is not evaluated; anything else is rejected.
  * FROM s of an obligation is (at T) or (factor PATH 0), the start of its
    window; a duration in BY counts from it. Without FROM it is (none).
    FROM inside a composite term is rejected. (UNTIL is no longer part of an
    obligation: it is a syntax error.)
  * s MUST a WITHIN d ELSE s2 MUST a2 BY d2, at the top level, is
    (must_else S A DL S2 A2 DL2): an obligation with a fallback. The fallback
    must be an obligation without FROM; ELSE in a composite term, FROM with
    ELSE, and a handler bound to such an obligation are rejected. The fallback
    must end after the first deadline: with two DATETIME deadlines this is
    checked here, otherwise by the evaluator at activation.
  * The PENALTY amount is built from numeric literals, Integer and Decimal
    factors and DEFAULT with +, - and * (no division): (penalty P CAP) with
    P ::= (val V) | (add P P) | (sub P P) | (mul P P) | (neg P), and CAP the
    literal of CAP, a number, or (none).
  * A handler binds to the nearest preceding obligation or prohibition of its
    subject at the top level (bound_to in TRIEL_Breach.thy). Section 2.6
    defines continuations only for obligations, so TERMINATE, CURE_BY and
    ESCALATE_TO in a handler bound to a prohibition are rejected.
  * JURISDICTION, STANDARD, CURRENCY, PROVENANCE_REQUIRED, PROOF_SYSTEM, CURVE,
    the DID of a subject, and the POLARITY, THRESHOLD, SOURCE and
    SENSITIVITY_BOUND of each factor are metadata: they are printed and have no
    semantics in the core. CAUSED_BY is rejected. A subject or a factor declared
    twice is rejected, and so is an undeclared subject of a term, a handler,
    NOTIFY, ESCALATE_TO or SOURCE. By the rules of
    TECHNICAL_REPORT.md section 2.9, a factor whose SOURCE is an ORACLE
    requires PROVENANCE_REQUIRED: true, and a PENALTY requires CURRENCY.
  * A ZK<T> factor is a factor of type T; Hash and Address are strings. Without
    WITHOUT REVEALING ALL it is hidden, (hidden_factor NAME TY AGE): the
    evaluator removes it from the data before typing and evaluation. The flow
    rule (TECHNICAL_REPORT.md section 2.7): a hidden factor may be named only as
    an action argument; read anywhere else (a condition, an invariant, PRESENT,
    DEFAULT, PENALTY, a deadline, FROM) it is rejected as "ZK flow rule". Its
    PROVES constraints and BOUND_TO are metadata. Rejected (section 2.8): a ZK
    factor without PROOF_SYSTEM or CURVE, a ZK factor whose SOURCE subject has a
    DID but which has no BOUND_TO, a BOUND_TO subject without a DID, an
    undeclared nonce or salt, PUBLIC_WITNESS, and a ZK type inside another type.
  * The class of an invariant (SAFETY, LIVENESS, FAIRNESS) is a label; the
    verdict depends only on ALWAYS, EVENTUALLY or NEXT.
  * EVENTUALLY(c) WITHIN d is (eventually_within X DL), with the deadline DL
    translated as the deadline of an obligation and resolved at activation.
"""
import argparse
import calendar
import re
import sys
from datetime import datetime
from pathlib import Path

from lark import Lark, Token, Tree, UnexpectedInput

GRAMMAR_PATH = Path(__file__).parent / "triel.lark"

# Every rule of parser/triel.lark, and what the translator does with it.
# "core": translated into the core (possibly with some of its options
# rejected, see the code); "metadata": printed; anything else is the name
# under which the construct is rejected. test_triel_to_core.py checks that
# this table covers exactly the rules of the grammar.
RULES = {
    "start": "core", "specification": "core",
    "declaration_block": "core", "version_literal": "core",
    "standard_ref": "metadata", "jurisdiction_literal": "metadata",
    "import_decl": "IMPORT", "hash_literal": "core",
    "anchor_mode_val": "ANCHOR_MODE", "proof_system_val": "metadata",
    "subject_block": "core", "subject_decl": "core", "role_type": "core",
    "did_literal": "metadata",
    "term_element": "core", "terms_block": "core",
    "named_term_decl": "core", "term_stmt": "core",
    "choice_expr": "core", "parallel_expr": "AND (term)",
    "sequence_expr": "core", "unless_expr": "core", "timeout_expr": "core",
    "base_term": "core", "matched_term": "core", "unmatched_term": "core",
    "term_ref": "core",
    "matched_condition": "core", "unmatched_condition": "core",
    "obligation_stmt": "core", "permission_stmt": "core", "prohibition_stmt": "core",
    "trigger_stmt": "ON ... DO", "unmatched_trigger": "ON ... DO",
    "breach_handler_stmt": "core", "breach_action": "core",
    "contract_ref_stmt": "EXECUTE", "binding": "EXECUTE",
    "factors_block": "core", "factor_decl": "core", "stale_action": "core",
    "polarity_val": "metadata", "factor_source": "metadata",
    "type_expr": "core", "type_base": "core", "primitive_type": "core",
    "composite_type": "core", "field_decl": "core", "enum_ref": "enum type",
    "zk_type": "core", "zk_primitive_type": "core", "zk_constraints": "core",
    "zk_constraint": "metadata", "signed_literal": "metadata", "salt_ref": "core",
    "zk_visibility": "core",
    "cross_modal_block": "CROSS_MODAL", "cross_modal_decl": "CROSS_MODAL",
    "modality_id": "CROSS_MODAL",
    "invariants_block": "core", "invariant_decl": "core", "invariant_type": "metadata",
    "temporal_expr": "core", "causal_expr": "causal invariant",
    "ltl_expr": "LTL formula", "ltl_implication": "LTL formula", "ltl_or": "LTL formula",
    "ltl_until": "LTL formula", "ltl_and": "LTL formula", "ltl_unary": "LTL formula",
    "ltl_atom": "LTL formula", "ltl_op_expr": "LTL formula",
    "ctl_expr": "CTL formula", "ctl_implication": "CTL formula", "ctl_or": "CTL formula",
    "ctl_and": "CTL formula", "ctl_negation": "CTL formula",
    "ctl_path_formula": "CTL formula", "ctl_inner": "CTL formula",
    "state_invariant": "core", "cross_modal_invariant": "CROSS_MODAL_CONSISTENT",
    "event_class": "causal invariant", "param_decl": "causal invariant",
    "modalities_block": "MODALITIES", "modality_conf": "MODALITIES",
    "modality_param": "MODALITIES",
    "expr": "core", "implication_expr": "core", "disjunction_expr": "core",
    "conjunction_expr": "core", "negation_expr": "core", "comparison_expr": "core",
    "arithmetic_expr": "core", "mul_expr": "core", "unary_expr": "core",
    "primary": "core", "presence_expr": "core", "default_expr": "core",
    "if_expr": "IF expression", "let_expr": "LET", "function_call": "function call",
    "comparison_op": "core", "action_expr": "core", "event_expr": "ON ... DO",
    "factor_ref": "core", "deadline_expr": "core", "datetime_expr": "core",
    "state_expr": "LTL formula",
    "literal": "core", "numeric_literal": "core", "signed_numeric_literal": "metadata",
    "boolean_literal": "core", "datetime_literal": "core", "duration_literal": "core",
    "time_unit": "core", "caused_by_entry": "CAUSED_BY", "identifier": "core",
}

UNIT_SECONDS = {"SECOND": 1, "SECONDS": 1, "MINUTE": 60, "MINUTES": 60,
                "HOUR": 3600, "HOURS": 3600, "DAY": 86400, "DAYS": 86400}
CONTINUATIONS = {"TERMINATE", "CURE_BY", "ESCALATE_TO"}
PROHIBITION_CONTINUATION = "§2.6 defines continuations only for obligations"
CALENDAR_UNITS = {"BUSINESS_DAY", "BUSINESS_DAYS", "MONTH", "MONTHS", "YEAR", "YEARS"}
PRIMITIVES = {"Integer": "int", "Decimal": "decimal", "Boolean": "bool", "String": "string",
              "DateTime": "datetime", "Hash": "string", "Address": "string"}
NUMERIC = (["prim", "int"], ["prim", "decimal"])
ISO_UTC = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")


class Str(str):
    """A name or string, printed as a string literal in the core AST."""


def sexp(x) -> str:
    if isinstance(x, Str):
        return '"' + x.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(x, list):
        return "(" + " ".join(sexp(y) for y in x) + ")"
    return str(x)


def pretty(x, indent: int = 0) -> str:
    flat = sexp(x)
    if len(flat) + indent <= 90 or not isinstance(x, list) or not x:
        return flat
    head = sexp(x[0])
    rest = [pretty(y, indent + 2) for y in x[1:]]
    return "(" + head + "".join("\n" + " " * (indent + 2) + r for r in rest) + ")"


def iso_seconds(text: str):
    if not ISO_UTC.match(text):
        return None
    try:
        dt = datetime.strptime(text, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError:
        return None
    return calendar.timegm(dt.timetuple())


def unquote(tok: str) -> str:
    body = tok[1:-1]
    return re.sub(r'\\(u[0-9a-fA-F]{4}|.)',
                  lambda m: (chr(int(m.group(1)[1:], 16)) if m.group(1)[0] == "u"
                             else {"n": "\n", "t": "\t"}.get(m.group(1), m.group(1))),
                  body)


def kids(t: Tree):
    return [c for c in t.children if c is not None]


def subtrees(t: Tree):
    return [c for c in kids(t) if isinstance(c, Tree)]


def tokens(t: Tree):
    return [c.value for c in kids(t) if isinstance(c, Token)]


def leaves(t):
    """Every token below t, in source order."""
    if isinstance(t, Token):
        return [t.value]
    return [v for c in kids(t) for v in leaves(c)]


def literal_text(t: Tree) -> str:
    """A signed_literal as written: 5 DAYS, -10, DATETIME("..."), "EU"."""
    c = kids(t)[0]
    if isinstance(c, Tree) and c.data == "duration_literal":
        return " ".join(leaves(c))
    return "".join(leaves(c))


def constraint_text(t: Tree) -> str:
    """A zk_constraint as written, with normalised spacing."""
    toks = tokens(t)
    sub = subtrees(t)
    lits = [literal_text(x) for x in sub if x.data == "signed_literal"]
    op = [tokens(x)[0] for x in sub if x.data == "comparison_op"]
    if toks[0] == "HASH":
        salt = ident(subtrees([x for x in sub if x.data == "salt_ref"][0])[0])
        return f"HASH(self, {salt}) {op[0]} {lits[0]}"
    if "RANGE" in toks:
        return f"self IN RANGE [{lits[0]}, {lits[1]}]"
    if "SET" in toks:
        return "self IN SET {" + ", ".join(lits) + "}"
    return f"self {op[0]} {lits[0]}"


def ident(t: Tree) -> Str:
    assert t.data == "identifier"
    return Str(kids(t)[0].value)


def only(t: Tree, name: str):
    """The single subtree of t, if it is named name."""
    s = subtrees(t)
    return s[0] if len(s) == 1 and s[0].data == name and not tokens(t) else None


class Translation:
    def __init__(self):
        self.name = None
        self.metadata = []      # header lines after SPEC
        self.rejected = set()
        self.factors = {}       # factor name -> type (None if rejected)
        self.core = None        # the core AST, if accepted
        self.top = None         # the norm or handler at the top level being translated
        self.operand_type = None  # the type of the last operand read by value()
        self.all_names = set()  # every name declared with :=
        self.names = {}         # name declared so far -> (index, why it cannot be referenced)
        self.subject_names = set()
        self.dids = set()       # subjects with a DID
        self.hidden = set()     # hidden factors: ZK<T> without WITHOUT REVEALING ALL
        self.zk = []            # (factor, salts, BOUND_TO (subject, nonce) or None, SOURCE or None)
        self.declared = set()   # PROOF_SYSTEM, CURVE and CURRENCY, if declared
        self.provenance = False # PROVENANCE_REQUIRED: true
        self.oracles = set()    # subjects declared ORACLE
        self.sources = set()    # subjects named in a SOURCE clause
        self.penalties = False  # a PENALTY in a breach handler

    def reject(self, what: str):
        self.rejected.add(what)
        return None

    def subject(self, t: Tree):
        """An identifier that must name a subject declared in SUBJECTS."""
        s = ident(t)
        if s not in self.subject_names:
            self.reject("undeclared subject")
        return s

    # --- declaration, subjects --------------------------------------------

    def declaration(self, t: Tree):
        key = None
        for c in kids(t):
            if isinstance(c, Token):
                if c.value in ("REPLACES", "IMPORT", "ANCHOR_MODE", "QUORUM_THRESHOLD"):
                    self.reject(c.value)
                if c.value in ("PROOF_SYSTEM", "CURVE", "CURRENCY"):
                    self.declared.add(c.value)
                if c.value in ("SPECIFICATION", "VERSION", "REPLACES", "STANDARD",
                               "JURISDICTION", "IMPORT", "PROVENANCE_REQUIRED",
                               "ANCHOR_MODE", "QUORUM_THRESHOLD", "PROOF_SYSTEM",
                               "CURVE", "CURRENCY"):
                    key = c.value
                elif key in ("CURRENCY", "CURVE") and c.type == "STRING_LITERAL":
                    self.metadata.append(f"METADATA {key} {c.value}")
                continue
            if key == "SPECIFICATION" and c.data == "identifier":
                self.name = ident(c)
            elif key == "STANDARD" and c.data == "standard_ref":
                self.metadata.append(f"METADATA STANDARD {kids(c)[0].value}")
            elif key == "JURISDICTION" and c.data == "jurisdiction_literal":
                self.metadata.append(f"METADATA JURISDICTION {kids(c)[0].value}")
            elif key == "PROVENANCE_REQUIRED" and c.data == "boolean_literal":
                self.metadata.append(f"METADATA PROVENANCE_REQUIRED {tokens(c)[0]}")
                self.provenance = tokens(c)[0] == "true"
            elif key == "PROOF_SYSTEM" and c.data == "proof_system_val":
                self.metadata.append(f"METADATA PROOF_SYSTEM {tokens(c)[0]}")

    def subjects(self, t: Tree):
        for d in subtrees(t):
            name = ident(subtrees(d)[0])
            if name in self.subject_names:
                self.reject("duplicate subject")
            self.subject_names.add(name)
            if "ORACLE" in tokens([x for x in subtrees(d) if x.data == "role_type"][0]):
                self.oracles.add(name)
            if "DID" in tokens(d):
                self.dids.add(name)
                did = kids([x for x in subtrees(d) if x.data == "did_literal"][0])[0].value
                self.metadata.append(f"METADATA DID {name} {did}")

    # --- factors and types ------------------------------------------------

    def type_expr(self, t: Tree):
        if "CONSTRAINT" in tokens(t):
            return self.reject("CONSTRAINT")
        return self.type_base(subtrees(t)[0])

    def type_base(self, t: Tree):
        if "Optional" in tokens(t):
            inner = self.type_expr(subtrees(t)[0])
            return None if inner is None else ["optional", inner]
        c = subtrees(t)[0]
        if c.data == "primitive_type":
            p = tokens(c)[0]
            if p in PRIMITIVES:
                return ["prim", PRIMITIVES[p]]
            return self.reject(f"type {p}")
        if c.data == "composite_type":
            kind = tokens(c)[0]
            if kind != "Record":
                return self.reject(f"type {kind}")
            fields = []
            ok = True
            for f in subtrees(c):
                if "DEFAULT" in tokens(f):
                    self.reject("field DEFAULT")
                    ok = False
                    continue
                ft = self.type_expr(subtrees(f)[1])
                ok = ok and ft is not None
                fields.append([ident(subtrees(f)[0]), ft])
            return ["record"] + fields if ok else None
        if c.data == "zk_type":
            return self.reject("nested ZK type")
        return self.reject(RULES[c.data])

    def zk_factor(self, name, z: Tree):
        """The type of a ZK<T> factor, T, and whether it is hidden. PROVES and
        BOUND_TO are metadata (TECHNICAL_REPORT.md sections 2.7 and 2.8)."""
        prim, cons = subtrees(z)
        salts = []
        for c in subtrees(cons):
            if c.data == "zk_constraint":
                self.metadata_sources.append(f"METADATA PROVES {name} {constraint_text(c)}")
                salts += [ident(subtrees(x)[0]) for x in subtrees(c) if x.data == "salt_ref"]
        toks = tokens(cons)
        vis = [tokens(x)[0] for x in subtrees(cons) if x.data == "zk_visibility"]
        if "PUBLIC_WITNESS" in toks:
            self.reject("PUBLIC_WITNESS")
        bound = None
        if "BOUND_TO" in toks:
            ids = [ident(x) for x in subtrees(cons) if x.data == "identifier"]
            bound = (ids[-2], ids[-1])
            self.metadata_sources.append(f"METADATA BOUND_TO {name} {bound[0]} {bound[1]}")
        self.zk.append([name, salts, bound, None])
        return ["prim", PRIMITIVES[tokens(prim)[0]]], vis != ["ALL"]

    def check_zk(self):
        """The semantic rules of TECHNICAL_REPORT.md section 2.8."""
        if self.zk:
            for k in ("PROOF_SYSTEM", "CURVE"):
                if k not in self.declared:
                    self.reject(f"ZK type without {k}")
        for name, salts, bound, source in self.zk:
            if bound is None and source in self.dids:
                self.reject("ZK type without BOUND_TO")
            if bound is not None and bound[0] not in self.dids:
                self.reject("BOUND_TO subject without DID")
            if bound is not None and bound[1] not in self.factors:
                self.reject("undeclared nonce")
            if any(x not in self.factors for x in salts):
                self.reject("undeclared salt")

    def check_rules(self):
        """The semantic rules of TECHNICAL_REPORT.md section 2.9."""
        if self.sources & self.oracles and not self.provenance:
            self.reject("ORACLE source without PROVENANCE_REQUIRED")
        if self.penalties and "CURRENCY" not in self.declared:
            self.reject("PENALTY without CURRENCY")

    def factor(self, t: Tree):
        name = ident(subtrees(t)[0])
        te = subtrees(t)[1]
        base = subtrees(subtrees(te)[0])[0]
        hidden = False
        if base.data == "zk_type" and "CONSTRAINT" not in tokens(te):
            ty, hidden = self.zk_factor(name, base)
        else:
            ty = self.type_expr(te)
        if hidden:
            self.hidden.add(name)
        if name in self.factors:
            self.reject("duplicate factor")
        self.factors[name] = ty
        toks = tokens(t)
        if "CAUSED_BY" in toks:
            self.reject("CAUSED_BY")
        # The heuristic scoring layer has no formal semantics (TECHNICAL_REPORT.md
        # section 4): POLARITY, THRESHOLD and SENSITIVITY_BOUND are metadata,
        # printed in source order together with SOURCE.
        pending = None
        for c in kids(t):
            if isinstance(c, Token) and c.value in ("POLARITY", "THRESHOLD", "SENSITIVITY_BOUND"):
                pending = c.value
            elif isinstance(c, Tree) and c.data in ("polarity_val", "signed_numeric_literal") and pending:
                self.metadata_sources.append(f"METADATA {pending} {name} {''.join(tokens(c))}")
                pending = None
            elif isinstance(c, Tree) and c.data == "factor_source":
                source = self.subject(subtrees(c)[0])
                self.sources.add(source)
                self.metadata_sources.append(f"METADATA SOURCE {name} {source}")
                if self.zk and self.zk[-1][0] == name:
                    self.zk[-1][3] = source
        ages = [s for s in subtrees(t) if s.data == "duration_literal"]
        stale = [s for s in subtrees(t) if s.data == "stale_action"]
        age = ["none"]
        if stale and tokens(stale[0])[0] == "ESCALATE_TO":
            self.reject("ON_STALE ESCALATE_TO")
        elif ages and not stale:
            self.reject("MAX_AGE without ON_STALE")
        elif stale and not ages:
            self.reject("ON_STALE without MAX_AGE")
        elif ages and tokens(stale[0])[0] == "BLOCK":
            m = self.duration(ages[0])
            age = None if m is None else ["block", m]
        tag = "hidden_factor" if hidden else "factor"
        return [[tag, name, ty, age]] if ty is not None and age is not None else []

    def path_type(self, t: Tree):
        """The declared type of a factor_ref, "unknown" if a type on the way was
        rejected, or None (after a rejection) if the name is not declared."""
        names = [ident(c) for c in subtrees(t)]
        if names[0] not in self.factors:
            return self.reject("undeclared factor")
        if names[0] in self.hidden:
            return self.reject("ZK flow rule")
        ty = self.factors[names[0]]
        for f in names[1:]:
            while ty is not None and ty[0] == "optional":
                ty = ty[1]
            if ty is None:
                return "unknown"
            if ty[0] != "record":
                return self.reject("undeclared field")
            fields = dict((fn, ft) for fn, ft in ty[1:])
            if f not in fields:
                return self.reject("undeclared field")
            ty = fields[f]
        while ty is not None and ty[0] == "optional":
            ty = ty[1]
        return "unknown" if ty is None else ty

    def path(self, t: Tree):
        return ["path"] + [ident(c) for c in subtrees(t)]

    # --- literals, durations, deadlines ---------------------------------

    def duration(self, t: Tree):
        n = int(kids(t)[0].value)
        unit = tokens(subtrees(t)[0])[0]
        if unit in CALENDAR_UNITS:
            return self.reject("calendar unit")
        return n * UNIT_SECONDS[unit]

    def datetime(self, t: Tree):
        text = unquote([v for v in kids(t) if isinstance(v, Token) and v.type == "STRING_LITERAL"][0].value)
        s = iso_seconds(text)
        return self.reject("DATETIME not ISO-8601 UTC") if s is None else s

    def literal_value(self, t: Tree):
        c = kids(t)[0]
        if isinstance(c, Token):
            return ["str", Str(unquote(c.value))]
        if c.data == "numeric_literal":
            tok = kids(c)[0]
            if tok.type == "DECIMAL_LITERAL":
                whole, frac = tok.value.split(".")
                return ["dec", int(whole + frac), len(frac)]
            return ["int", int(tok.value)]
        if c.data == "boolean_literal":
            return ["bool", tokens(c)[0]]
        if c.data == "datetime_literal":
            s = self.datetime(c)
            return None if s is None else ["time", s]
        return self.reject("duration value")

    def deadline(self, t: Tree):
        c = subtrees(t)
        if "+" in tokens(t) or "-" in tokens(t):
            sign = 1 if "+" in tokens(t) else -1
            d = self.duration(c[1])
            base = subtrees(c[0])[0]
            if d is None:
                return None
            if base.data == "datetime_literal":
                s = self.datetime(base)
                return None if s is None else ["at", s + sign * d]
            return None if self.path_type(base) is None else ["factor", self.path(base), sign * d]
        c = c[0]
        if c.data == "datetime_literal":
            s = self.datetime(c)
            return None if s is None else ["at", s]
        if c.data == "duration_literal":
            d = self.duration(c)
            return None if d is None else ["after", d]
        return None if self.path_type(c) is None else ["factor", self.path(c), 0]

    # --- expressions --------------------------------------------------------

    def chain(self, t: Tree, rule: str, op: str, tag: str, sub):
        parts = subtrees(t)
        if op not in tokens(t):
            return sub(parts[0])
        xs = [sub(p) for p in parts]
        if any(x is None for x in xs):
            return None
        acc = xs[0]
        for x in xs[1:]:
            acc = [tag, acc, x]
        return acc

    def cond(self, t: Tree):
        """A condition (an expr of the core) from an expr subtree."""
        c = subtrees(t)[0]
        if c.data != "implication_expr":
            return self.reject(RULES[c.data])
        return self.implication(c)

    def implication(self, t: Tree):
        p = subtrees(t)
        if "IMPLIES" not in tokens(t):
            return self.disjunction(p[0])
        a, b = self.disjunction(p[0]), self.implication(p[1])
        return None if a is None or b is None else ["implies", a, b]

    def disjunction(self, t: Tree):
        return self.chain(t, "disjunction_expr", "OR", "or", self.conjunction)

    def conjunction(self, t: Tree):
        return self.chain(t, "conjunction_expr", "AND", "and", self.negation)

    def negation(self, t: Tree):
        if "NOT" in tokens(t):
            x = self.negation(subtrees(t)[0])
            return None if x is None else ["not", x]
        return self.comparison(subtrees(t)[0])

    def comparison(self, t: Tree):
        p = subtrees(t)
        if len(p) == 1:
            return self.bool_operand(p[0])
        op = tokens(p[1])[0]
        a = self.value(p[0])
        ta = self.operand_type
        b = self.value(p[2])
        tb = self.operand_type
        if a is None or b is None:
            return None
        if op in ("==", "!="):
            return ["eq", a, b] if op == "==" else ["not", ["eq", a, b]]
        if any(x != "number" and x not in NUMERIC and x != "unknown" for x in (ta, tb)):
            return self.reject("ordering comparison of a non-number")
        return {"<": ["lt", a, b], "<=": ["le", a, b],
                ">": ["lt", b, a], ">=": ["le", b, a]}[op]

    def primary_of(self, t: Tree):
        """The primary below an arithmetic_expr without operators, or the name of
        the operator that is there."""
        if t.data == "arithmetic_expr" and len(subtrees(t)) > 1:
            return "arithmetic"
        m = subtrees(t)[0]
        if len(subtrees(m)) > 1:
            return "arithmetic"
        u = subtrees(m)[0]
        if "-" in tokens(u):
            return ("minus", subtrees(u)[0])
        return subtrees(u)[0]

    def bool_operand(self, t: Tree):
        p = self.primary_of(t)
        if p == "arithmetic" or isinstance(p, tuple):
            return self.reject("arithmetic")
        c = kids(p)
        inner = [x for x in c if isinstance(x, Tree)]
        if not inner:
            return self.reject("non-Boolean condition")
        x = inner[0]
        if x.data == "expr":
            return self.cond(x)
        if x.data == "literal":
            b = subtrees(x)
            if b and b[0].data == "boolean_literal":
                return ["true"] if tokens(b[0])[0] == "true" else ["false"]
            return self.reject("non-Boolean condition")
        if x.data == "factor_ref":
            ty = self.path_type(x)
            if ty is None:
                return None
            if ty != "unknown" and ty != ["prim", "bool"]:
                return self.reject("non-Boolean condition")
            return ["eq", ["name", self.path(x)], ["const", ["bool", "true"]]]
        if x.data == "presence_expr":
            r = subtrees(x)[0]
            ty = self.path_type(r)
            if ty is None:
                return None
            if ty != "unknown" and ty[0] == "record":
                return self.reject("PRESENT of a record")
            return ["present", self.path(r)]
        if x.data == "default_expr":
            v = self.default(x)
            if v is None:
                return None
            if self.operand_type not in ("unknown", ["prim", "bool"]):
                return self.reject("non-Boolean condition")
            return ["eq", v, ["const", ["bool", "true"]]]
        return self.reject(RULES[x.data])

    def value(self, t: Tree):
        """An operand of a comparison: a factor name or a literal. Its type is left
        in self.operand_type: the declared type of a name, "number" for a numeric
        literal, None otherwise."""
        self.operand_type = None
        p = self.primary_of(t)
        if p == "arithmetic":
            return self.reject("arithmetic")
        if isinstance(p, tuple):
            q = subtrees(p[1])
            lit = q[0] if q and q[0].data == "primary" else None
            if lit is not None:
                l2 = subtrees(lit)
                if l2 and l2[0].data == "literal":
                    v = self.literal_value(l2[0])
                    if v is not None and v[0] in ("int", "dec"):
                        self.operand_type = "number"
                        return ["const", [v[0], -v[1]] + v[2:]]
            return self.reject("arithmetic")
        x = subtrees(p)[0] if subtrees(p) else None
        if x is None:
            return self.reject("non-Boolean condition")
        if x.data == "literal":
            v = self.literal_value(x)
            if v is not None and v[0] in ("int", "dec"):
                self.operand_type = "number"
            return None if v is None else ["const", v]
        if x.data == "factor_ref":
            ty = self.path_type(x)
            if ty is None:
                return None
            if ty != "unknown" and ty[0] == "record":
                return self.reject("== on a record")
            self.operand_type = ty
            return ["name", self.path(x)]
        if x.data == "expr":
            return self.reject("== on a condition")
        if x.data == "presence_expr":
            return self.reject("== on a condition")
        if x.data == "default_expr":
            return self.default(x)
        return self.reject(RULES[x.data])

    def default(self, t: Tree):
        """DEFAULT(f, d) as a value; self.operand_type is left as the type of f."""
        f, d = subtrees(t)
        ty = self.path_type(f)
        if ty is None:
            return None
        if ty != "unknown" and ty[0] == "record":
            return self.reject("DEFAULT of a record")
        x = d
        for rule in ("expr", "implication_expr", "disjunction_expr", "conjunction_expr",
                     "negation_expr", "comparison_expr"):
            if x.data != rule or tokens(x) or len(subtrees(x)) != 1:
                return self.reject("DEFAULT fallback (not a value)")
            x = subtrees(x)[0]
        fb = self.value(x)
        if fb is None:
            return None
        tb = self.operand_type
        if fb[0] == "const" and fb[1][0] in ("bool", "str", "time"):
            tb = ["prim", {"bool": "bool", "str": "string", "time": "datetime"}[fb[1][0]]]
        numeric = lambda y: y == "number" or y in NUMERIC
        if not ("unknown" in (ty, tb) or tb is None or ty == tb
                or (numeric(ty) and numeric(tb))):
            return self.reject("DEFAULT fallback of another type")
        self.operand_type = ty
        return ["default", self.path(f), fb]

    # --- terms ------------------------------------------------------------

    def term_stmt(self, t: Tree, top: bool):
        return self.choice(subtrees(t)[0], top)

    def choice(self, t: Tree, top: bool):
        p = subtrees(t)
        if len(p) == 1:
            return self.parallel(p[0], top)
        return self.chain(t, "choice_expr", "OR", "or", lambda x: self.parallel(x, False))

    def parallel(self, t: Tree, top: bool):
        p = subtrees(t)
        if len(p) > 1:
            return self.reject("AND (term)")
        return self.sequence(p[0], top)

    def sequence(self, t: Tree, top: bool):
        p = subtrees(t)
        if len(p) == 1:
            return self.unless(p[0], top)
        return self.chain(t, "sequence_expr", "THEN", "then", lambda x: self.unless(x, False))

    def unless(self, t: Tree, top: bool):
        p = subtrees(t)
        if len(p) == 1:
            return self.timeout(p[0], top)
        a, c, b = self.timeout(p[0], False), self.cond(p[1]), self.timeout(p[2], False)
        return None if a is None or c is None or b is None else ["unless", a, c, b]

    def timeout(self, t: Tree, top: bool):
        p = subtrees(t)
        if top:
            self.note_top(p[0])
        if "WITHIN" not in tokens(t):
            return self.base(p[0], top, None)
        if "ELSE" in tokens(t):
            return self.fallback(p, top)
        return self.base(p[0], top, p[1])

    def fallback(self, p, top: bool):
        """s MUST a WITHIN d ELSE s2 MUST a2 [BY d2] at the top level: an
        obligation with a fallback (must_else S A DL S2 A2 DL2)."""
        if not top:
            return self.reject("WITHIN ... ELSE in a composite term")
        first = self.base(p[0], True, p[1])
        alt = self.else_obligation(p[2])
        if first is None or alt is None:
            return None
        if first[0] != "must":
            return self.reject("WITHIN (non-obligation)")
        if first[4] != ["none"]:
            return self.reject("FROM with ELSE")
        if first[3][0] == "at" and alt[3][0] == "at" and alt[3][1] <= first[3][1]:
            # Decision 27; with other deadlines the evaluator checks it at activation.
            return self.reject("ELSE deadline not after the first deadline")
        self.top = ("else", first[1])
        return ["must_else", first[1], first[2], first[3], alt[1], alt[2], alt[3]]

    def else_obligation(self, t: Tree):
        """The fallback after ELSE: an obligation without FROM."""
        c = subtrees(t)[0]
        m = subtrees(c)[0] if subtrees(c) else None
        if c.data != "matched_term" or m is None or "(" in tokens(c) or m.data != "obligation_stmt":
            return self.reject("ELSE (non-obligation)")
        if "FROM" in tokens(m):
            return self.reject("FROM in ELSE")
        return self.obligation(m, True, None)

    def base(self, t: Tree, top: bool, within):
        return self.inner(subtrees(t)[0], top, within)

    def inner(self, c: Tree, top: bool, within):
        """A matched_term or an unmatched_term."""
        if c.data == "unmatched_term":
            u = subtrees(c)[0]
            if u.data == "unmatched_trigger":
                return self.reject(RULES[u.data])
            if within is not None:
                return self.reject("WITHIN (non-obligation)")
            return self.conditional(u)
        m = subtrees(c)[0] if subtrees(c) else None
        if "(" in tokens(c):
            if within is not None:
                return self.reject("WITHIN (non-obligation)")
            return self.term_stmt(m, top)
        if m.data == "matched_condition":
            if within is not None:
                return self.reject("WITHIN (non-obligation)")
            return self.conditional(m)
        if m.data == "term_ref":
            if within is not None:
                return self.reject("WITHIN (non-obligation)")
            return self.ref(m)
        if m.data == "obligation_stmt":
            return self.obligation(m, top, within)
        if within is not None:
            return self.reject("WITHIN (non-obligation)")
        if m.data in ("permission_stmt", "prohibition_stmt"):
            s = self.subject(subtrees(m)[0])
            a = self.action(subtrees(m)[1])
            cs = subtrees(m)[2:]
            c = self.cond(cs[0]) if cs else ["true"]
            if a is None or c is None:
                return None
            return ["may" if m.data == "permission_stmt" else "must_not", s, a, c]
        if m.data == "breach_handler_stmt":
            return self.handler(m)
        return self.reject(RULES[m.data])

    def conditional(self, t: Tree):
        """IF/ELIF/ELSE or WHEN: the arms are read from the keywords."""
        ks = kids(t)
        arms, other, i = [], None, 0
        while i < len(ks):
            k = ks[i]
            if isinstance(k, Token) and k.value in ("IF", "ELIF", "WHEN"):
                arms.append((ks[i + 1], ks[i + 3]))
                i += 4
            elif isinstance(k, Token) and k.value == "ELSE":
                other = ks[i + 1]
                i += 2
            else:
                i += 1
        branch = lambda x: (self.base(x, False, None) if x.data == "base_term"
                            else self.inner(x, False, None))
        xs = [(self.cond(c), branch(b)) for c, b in arms]
        acc = ["skip"] if other is None else branch(other)
        if acc is None or any(c is None or b is None for c, b in xs):
            return None
        for c, b in reversed(xs):
            acc = ["if", c, b, acc]
        return acc

    def ref(self, t: Tree):
        name = ident(subtrees(t)[0])
        if name not in self.all_names:
            return self.reject("REF to an undeclared name")
        if name not in self.names:
            return self.reject("REF to a name declared later")
        k, why = self.names[name]
        return self.reject(why) if why else ["ref", k]

    def note_top(self, t: Tree):
        """Record what the top-level element is, for binding handlers: an
        obligation or prohibition with its subject, or a handler with its
        subject and whether it has a continuation-determining action. A
        parenthesised element is recorded again when its inside is reached."""
        c = subtrees(t)[0]
        m = subtrees(c)[0] if subtrees(c) else None
        if m is None or "(" in tokens(c):
            return
        if m.data in ("obligation_stmt", "prohibition_stmt"):
            self.top = (m.data, ident(subtrees(m)[0]))
        elif m.data == "breach_handler_stmt":
            cont = any(tokens(b)[0] in CONTINUATIONS for b in subtrees(m)[1:])
            self.top = (m.data, ident(subtrees(m)[0]), cont)
        else:
            self.top = None

    def check_binding(self, tops):
        """Reject a continuation in a handler bound to a prohibition, and any
        handler bound to an obligation with a fallback (WITHIN ... ELSE)."""
        for i, x in enumerate(tops):
            if x is None or x[0] != "breach_handler_stmt":
                continue
            bound = [y for y in tops[:i] if y is not None and y[0] != "breach_handler_stmt"
                     and y[1] == x[1]]
            if bound and bound[-1][0] == "else":
                self.reject("ON_BREACH bound to WITHIN ... ELSE")
            elif x[2] and bound and bound[-1][0] == "prohibition_stmt":
                self.reject(PROHIBITION_CONTINUATION)

    def action(self, t: Tree):
        """An action: its name, or (action NAME ARG ...) with arguments."""
        name = ident(subtrees(t)[0])
        if "(" not in tokens(t):
            return name
        args = [self.argument(e) for e in subtrees(t)[1:]]
        if any(x is None for x in args):
            return None
        return ["action", name] + args

    def argument(self, t: Tree):
        """An argument of an action: a literal, or the name of a subject or a
        factor, which is not evaluated (TECHNICAL_REPORT.md section 2.6)."""
        x = t
        for rule in ("expr", "implication_expr", "disjunction_expr", "conjunction_expr",
                     "negation_expr", "comparison_expr"):
            if x.data != rule or tokens(x) or len(subtrees(x)) != 1:
                return self.reject("action argument (not a name or literal)")
            x = subtrees(x)[0]
        p = self.primary_of(x)
        if p == "arithmetic":
            return self.reject("action argument (not a name or literal)")
        if isinstance(p, tuple):
            v = self.value(x)
            return None if v is None else v[1]
        c = subtrees(p)[0] if subtrees(p) and not tokens(p) else None
        if c is not None and c.data == "literal":
            return self.literal_value(c)
        if c is not None and c.data == "factor_ref":
            names = [ident(n) for n in subtrees(c)]
            if len(names) == 1 and names[0] in self.subject_names:
                return self.path(c)
            if names[0] not in self.factors:
                return self.reject("action argument (undeclared name)")
            if names[0] in self.hidden:
                # A hidden factor named, not read (decision 24, TECHNICAL_REPORT.md 2.7).
                return self.path(c) if len(names) == 1 else self.reject("undeclared field")
            return None if self.path_type(c) is None else self.path(c)
        return self.reject("action argument (not a name or literal)")

    def start(self, t: Tree):
        """The start of an obligation, FROM: a DATETIME or a factor."""
        c = subtrees(t)[0]
        if c.data == "datetime_literal":
            s = self.datetime(c)
            return None if s is None else ["at", s]
        return None if self.path_type(c) is None else ["factor", self.path(c), 0]

    def obligation(self, t: Tree, top: bool, within):
        s = self.subject(subtrees(t)[0])
        a = self.action(subtrees(t)[1])
        toks = tokens(t)
        dl = ["none"]
        if "BY" in toks:
            if within is not None:
                return self.reject("BY and WITHIN")
            dl = self.deadline([x for x in subtrees(t) if x.data == "deadline_expr"][0])
        elif within is not None:
            dl = self.deadline(within)
        if dl is not None and dl != ["none"] and not top:
            return self.reject("deadline in a composite term")
        st = ["none"]
        if "FROM" in toks:
            if not top:
                return self.reject("FROM in a composite term")
            st = self.start([x for x in subtrees(t) if x.data == "datetime_expr"][0])
        if a is None or dl is None or st is None:
            return None
        return ["must", s, a, dl, st]

    def handler(self, t: Tree):
        s = self.subject(subtrees(t)[0])
        acts = []
        ok = True
        for b in subtrees(t)[1:]:
            kw = tokens(b)[0]
            x = None
            if kw == "PENALTY":
                self.penalties = True
                x = self.penalty(b)
            elif kw == "NOTIFY":
                x = ["notify", self.subject(subtrees(b)[0])]
            elif kw == "TERMINATE":
                x = ["terminate"]
            elif kw == "CURE_BY":
                d = subtrees(subtrees(b)[0])
                if len(d) == 1 and d[0].data == "duration_literal" and len(tokens(subtrees(b)[0])) == 0:
                    k = self.duration(d[0])
                    x = None if k is None else ["cure_by", k]
                else:
                    self.reject("CURE_BY (not a duration)")
            elif kw == "ESCALATE_TO":
                x = ["escalate_to", self.subject(subtrees(b)[0])]
            ok = ok and x is not None
            acts.append(x)
        return ["on_breach", s] + acts if ok else None

    def penalty(self, b: Tree):
        """PENALTY e [CAP c]: (penalty P CAP), the amount and the cap."""
        e = self.amount_expr(subtrees(b)[0])
        cap = ["none"]
        if "CAP" in tokens(b):
            cap = self.literal_value(subtrees(b)[1])
            if cap is not None and cap[0] not in ("int", "dec"):
                cap = self.reject("CAP (not a number)")
        return None if e is None or cap is None else ["penalty", e, cap]

    def amount_expr(self, t: Tree):
        """An amount from an expr subtree: arithmetic on numbers, no condition."""
        x = t
        for rule in ("expr", "implication_expr", "disjunction_expr", "conjunction_expr",
                     "negation_expr", "comparison_expr"):
            if x.data != rule or tokens(x) or len(subtrees(x)) != 1:
                return self.reject("PENALTY of a non-number")
            x = subtrees(x)[0]
        return self.amount(x)

    def amount(self, t: Tree):
        """An amount from arithmetic_expr, mul_expr, unary_expr or primary."""
        if t.data in ("arithmetic_expr", "mul_expr"):
            parts = subtrees(t)
            ops = [k.value for k in kids(t) if isinstance(k, Token)]
            if any(op in ("/", "%") for op in ops):
                return self.reject("division in PENALTY")
            xs = [self.amount(p) for p in parts]
            if any(x is None for x in xs):
                return None
            acc = xs[0]
            for op, x in zip(ops, xs[1:]):
                acc = [{"+": "add", "-": "sub", "*": "mul"}[op], acc, x]
            return acc
        if t.data == "unary_expr":
            if "-" in tokens(t):
                x = self.amount(subtrees(t)[0])
                return None if x is None else ["neg", x]
            return self.amount(subtrees(t)[0])
        c = subtrees(t)[0]
        if "(" in tokens(t):
            return self.amount_expr(c)
        if c.data == "literal":
            v = self.literal_value(c)
            if v is not None and v[0] not in ("int", "dec"):
                return self.reject("PENALTY of a non-number")
            return None if v is None else ["val", ["const", v]]
        if c.data == "factor_ref":
            ty = self.path_type(c)
            if ty is None:
                return None
            if ty != "unknown" and ty not in NUMERIC:
                return self.reject("PENALTY of a non-number")
            return ["val", ["name", self.path(c)]]
        if c.data == "default_expr":
            v = self.default(c)
            if v is None:
                return None
            if self.operand_type not in ("unknown",) and self.operand_type not in NUMERIC:
                return self.reject("PENALTY of a non-number")
            return ["val", v]
        if c.data == "presence_expr":
            return self.reject("PENALTY of a non-number")
        return self.reject(RULES[c.data])

    # --- invariants -------------------------------------------------------

    def invariant(self, t: Tree):
        name = ident(subtrees(t)[0])
        te = [s for s in subtrees(t) if s.data == "temporal_expr"][0]
        c = subtrees(te)[0]
        if c.data != "state_invariant":
            return self.reject(RULES[c.data])
        op = tokens(c)[0]
        e = self.cond(subtrees(c)[0])
        if "WITHIN" in tokens(c):
            dl = self.deadline(subtrees(c)[1])
            return None if e is None or dl is None else ["invariant", name, ["eventually_within", e, dl]]
        return None if e is None else ["invariant", name, [op.lower(), e]]

    # --- specification ----------------------------------------------------

    def specification(self, t: Tree):
        self.metadata_sources = []
        blocks = {b.data: b for b in subtrees(t)}
        self.declaration(blocks["declaration_block"])
        self.subjects(blocks["subject_block"])
        for b in ("cross_modal_block", "modalities_block"):
            if b in blocks:
                self.reject(RULES[b])
        factors = []
        for f in subtrees(blocks["factors_block"]):
            factors += self.factor(f)
        self.check_zk()
        terms = []
        tops = []
        elements = [subtrees(el)[0] for el in subtrees(blocks["terms_block"])]
        self.all_names = {ident(subtrees(x)[0]) for x in elements if x.data == "named_term_decl"}
        for x in elements:
            name = None
            if x.data == "named_term_decl":
                name, x = ident(subtrees(x)[0]), subtrees(x)[1]
                if name in self.names:
                    self.reject("duplicate term name")
            self.top = None
            y = self.term_stmt(x, True)
            if name is not None:
                self.names[name] = (len(terms), referable(y))
            terms.append(y)
            tops.append(self.top)
        self.check_binding(tops)
        invs = [self.invariant(i) for i in subtrees(blocks["invariants_block"])]
        self.check_rules()
        self.metadata += self.metadata_sources
        if not self.rejected:
            self.core = ["spec", ["factors"] + factors, ["terms"] + terms,
                         ["invariants"] + invs]


def referable(x):
    """Why the element x cannot be referenced with REF, or None."""
    def walk(y):
        if not isinstance(y, list) or not y:
            return None
        if y[0] == "on_breach":
            return "REF to a breach handler"
        if (y[0] == "must" and y[3] != ["none"]) or y[0] == "must_else":
            return "REF to a term with a deadline"
        if y[0] == "must" and y[4] != ["none"]:
            return "REF to a term with FROM"
        for z in y[1:]:
            w = walk(z)
            if w:
                return w
        return None
    return walk(x)


_parser = None


def parser() -> Lark:
    global _parser
    if _parser is None:
        _parser = Lark(GRAMMAR_PATH.read_text(), start="start", parser="earley",
                       lexer="dynamic", ambiguity="resolve", keep_all_tokens=True)
    return _parser


def translate(source: str) -> Translation:
    tree = parser().parse(source)
    tr = Translation()
    tr.specification(subtrees(tree)[0])
    return tr


def header(tr: Translation):
    return [f"SPEC {tr.name}"] + tr.metadata


def classify(paths):
    files = []
    for p in paths:
        p = Path(p)
        files += sorted(p.rglob("*.triel")) if p.is_dir() else [p]
    out = []
    ok = True
    for f in sorted(set(files), key=lambda x: x.as_posix()):
        try:
            tr = translate(f.read_text(encoding="utf-8"))
        except UnexpectedInput as e:
            ok = False
            out.append(f"{f.as_posix()}: PARSE ERROR at line {e.line}, column {e.column}")
            continue
        if tr.rejected:
            out.append(f"{f.as_posix()}: REJECTED: " + "; ".join(sorted(tr.rejected)))
        else:
            out.append(f"{f.as_posix()}: ACCEPTED")
    return out, ok


def main() -> int:
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--classify", action="store_true",
                    help="classify every given file (directories are searched for *.triel)")
    ap.add_argument("paths", nargs="+")
    args = ap.parse_args()
    if args.classify:
        out, ok = classify(args.paths)
        print("\n".join(out))
        return 0 if ok else 1
    if len(args.paths) != 1:
        ap.error("give one file, or use --classify")
    path = Path(args.paths[0])
    try:
        tr = translate(path.read_text(encoding="utf-8"))
    except UnexpectedInput as e:
        print(f"{path}: parse error at line {e.line}, column {e.column}", file=sys.stderr)
        return 1
    print("\n".join(header(tr)))
    if tr.rejected:
        print("REJECTED: " + "; ".join(sorted(tr.rejected)))
        return 2
    print(pretty(tr.core))
    return 0


if __name__ == "__main__":
    sys.exit(main())
