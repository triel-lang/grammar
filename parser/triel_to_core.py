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
  * The PENALTY amount must be a literal; it is kept as an opaque value.
  * JURISDICTION, STANDARD, CURRENCY, PROVENANCE_REQUIRED and the SOURCE of
    each factor are metadata: they are printed and have no semantics in the core.
  * The class of an invariant (SAFETY, LIVENESS, FAIRNESS) is a label; the
    verdict depends only on ALWAYS, EVENTUALLY or NEXT.
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
    "anchor_mode_val": "ANCHOR_MODE", "proof_system_val": "PROOF_SYSTEM",
    "subject_block": "core", "subject_decl": "core", "role_type": "core",
    "did_literal": "DID",
    "term_element": "core", "terms_block": "core",
    "named_term_decl": "named term (:=)", "term_stmt": "core",
    "choice_expr": "core", "parallel_expr": "AND (term)",
    "sequence_expr": "core", "unless_expr": "core", "timeout_expr": "core",
    "base_term": "core", "matched_term": "core", "unmatched_term": "core",
    "term_ref": "REF",
    "matched_condition": "IF ... THEN (term)", "unmatched_condition": "IF ... THEN (term)",
    "obligation_stmt": "core", "permission_stmt": "core", "prohibition_stmt": "core",
    "trigger_stmt": "ON ... DO", "breach_handler_stmt": "core", "breach_action": "core",
    "contract_ref_stmt": "EXECUTE", "binding": "EXECUTE",
    "factors_block": "core", "factor_decl": "core", "stale_action": "core",
    "polarity_val": "POLARITY", "factor_source": "metadata",
    "type_expr": "core", "type_base": "core", "primitive_type": "core",
    "composite_type": "core", "field_decl": "core", "enum_ref": "enum type",
    "zk_type": "ZK type", "zk_primitive_type": "ZK type", "zk_constraints": "ZK type",
    "zk_constraint": "ZK type", "signed_literal": "ZK type", "salt_ref": "ZK type",
    "zk_visibility": "ZK type",
    "cross_modal_block": "CROSS_MODAL", "cross_modal_decl": "CROSS_MODAL",
    "modality_id": "CROSS_MODAL",
    "invariants_block": "core", "invariant_decl": "core", "invariant_type": "metadata",
    "temporal_expr": "core", "causal_expr": "causal invariant",
    "ltl_expr": "LTL formula", "ltl_implication": "LTL formula", "ltl_or": "LTL formula",
    "ltl_until": "LTL formula", "ltl_and": "LTL formula", "ltl_unary": "LTL formula",
    "ltl_atom": "LTL formula",
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
    "primary": "core", "presence_expr": "core", "default_expr": "DEFAULT",
    "if_expr": "IF expression", "let_expr": "LET", "function_call": "function call",
    "comparison_op": "core", "action_expr": "core", "event_expr": "ON ... DO",
    "factor_ref": "core", "deadline_expr": "core", "datetime_expr": "core",
    "state_expr": "LTL formula",
    "literal": "core", "numeric_literal": "core", "signed_numeric_literal": "THRESHOLD",
    "boolean_literal": "core", "datetime_literal": "core", "duration_literal": "core",
    "time_unit": "core", "caused_by_entry": "CAUSED_BY", "identifier": "core",
}

UNIT_SECONDS = {"SECOND": 1, "SECONDS": 1, "MINUTE": 60, "MINUTES": 60,
                "HOUR": 3600, "HOURS": 3600, "DAY": 86400, "DAYS": 86400}
CALENDAR_UNITS = {"BUSINESS_DAY", "BUSINESS_DAYS", "MONTH", "MONTHS", "YEAR", "YEARS"}
PRIMITIVES = {"Integer": "int", "Boolean": "bool", "String": "string", "DateTime": "datetime"}
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

    def reject(self, what: str):
        self.rejected.add(what)
        return None

    # --- declaration, subjects --------------------------------------------

    def declaration(self, t: Tree):
        key = None
        for c in kids(t):
            if isinstance(c, Token):
                if c.value in ("REPLACES", "IMPORT", "ANCHOR_MODE", "QUORUM_THRESHOLD",
                               "PROOF_SYSTEM", "CURVE"):
                    self.reject(c.value)
                if c.value in ("SPECIFICATION", "VERSION", "REPLACES", "STANDARD",
                               "JURISDICTION", "IMPORT", "PROVENANCE_REQUIRED",
                               "ANCHOR_MODE", "QUORUM_THRESHOLD", "PROOF_SYSTEM",
                               "CURVE", "CURRENCY"):
                    key = c.value
                elif key == "CURRENCY" and c.type == "STRING_LITERAL":
                    self.metadata.append(f"METADATA CURRENCY {c.value}")
                continue
            if key == "SPECIFICATION" and c.data == "identifier":
                self.name = ident(c)
            elif key == "STANDARD" and c.data == "standard_ref":
                self.metadata.append(f"METADATA STANDARD {kids(c)[0].value}")
            elif key == "JURISDICTION" and c.data == "jurisdiction_literal":
                self.metadata.append(f"METADATA JURISDICTION {kids(c)[0].value}")
            elif key == "PROVENANCE_REQUIRED" and c.data == "boolean_literal":
                self.metadata.append(f"METADATA PROVENANCE_REQUIRED {tokens(c)[0]}")

    def subjects(self, t: Tree):
        for d in subtrees(t):
            if "DID" in tokens(d):
                self.reject("DID")

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
        return self.reject(RULES[c.data])

    def factor(self, t: Tree):
        name = ident(subtrees(t)[0])
        ty = self.type_expr(subtrees(t)[1])
        self.factors[name] = ty
        toks = tokens(t)
        for kw in ("POLARITY", "THRESHOLD", "CAUSED_BY", "SENSITIVITY_BOUND"):
            if kw in toks:
                self.reject(kw)
        src = [s for s in subtrees(t) if s.data == "factor_source"]
        if src:
            self.metadata_sources.append(f"METADATA SOURCE {name} {ident(subtrees(src[0])[0])}")
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
        return [["factor", name, ty, age]] if ty is not None and age is not None else []

    def path_type(self, t: Tree):
        """The declared type of a factor_ref, "unknown" if a type on the way was
        rejected, or None (after a rejection) if the name is not declared."""
        names = [ident(c) for c in subtrees(t)]
        if names[0] not in self.factors:
            return self.reject("undeclared factor")
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
            if tok.type == "FLOAT_LITERAL":
                return self.reject("float literal")
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
        return self.implication(subtrees(t)[0])

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
        if op not in ("==", "!="):
            return self.reject("ordering comparison")
        a, b = self.value(p[0]), self.value(p[2])
        if a is None or b is None:
            return None
        return ["eq", a, b] if op == "==" else ["not", ["eq", a, b]]

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
        return self.reject(RULES[x.data])

    def value(self, t: Tree):
        """An operand of == or !=: a factor name or a literal."""
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
                    if v is not None and v[0] == "int":
                        return ["const", ["int", -v[1]]]
            return self.reject("arithmetic")
        x = subtrees(p)[0] if subtrees(p) else None
        if x is None:
            return self.reject("non-Boolean condition")
        if x.data == "literal":
            v = self.literal_value(x)
            return None if v is None else ["const", v]
        if x.data == "factor_ref":
            ty = self.path_type(x)
            if ty is None:
                return None
            if ty != "unknown" and ty[0] == "record":
                return self.reject("== on a record")
            return ["name", self.path(x)]
        if x.data == "expr":
            return self.reject("== on a condition")
        if x.data == "presence_expr":
            return self.reject("== on a condition")
        return self.reject(RULES[x.data])

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
        if "WITHIN" not in tokens(t):
            return self.base(p[0], top, None)
        if "ELSE" in tokens(t):
            return self.reject("WITHIN ... ELSE")
        return self.base(p[0], top, p[1])

    def base(self, t: Tree, top: bool, within):
        c = subtrees(t)[0]
        if c.data == "unmatched_term":
            return self.reject("WHEN ... THEN (term)" if "WHEN" in tokens(subtrees(c)[0])
                               else "IF ... THEN (term)")
        m = subtrees(c)[0] if subtrees(c) else None
        if "(" in tokens(c):
            if within is not None:
                return self.reject("WITHIN (non-obligation)")
            return self.term_stmt(m, top)
        if m.data == "matched_condition":
            return self.reject("WHEN ... THEN (term)" if tokens(m)[0] == "WHEN"
                               else "IF ... THEN (term)")
        if m.data == "obligation_stmt":
            return self.obligation(m, top, within)
        if within is not None:
            return self.reject("WITHIN (non-obligation)")
        if m.data in ("permission_stmt", "prohibition_stmt"):
            s = ident(subtrees(m)[0])
            a = self.action(subtrees(m)[1])
            cs = subtrees(m)[2:]
            c = self.cond(cs[0]) if cs else ["true"]
            if a is None or c is None:
                return None
            return ["may" if m.data == "permission_stmt" else "must_not", s, a, c]
        if m.data == "breach_handler_stmt":
            return self.handler(m)
        return self.reject(RULES[m.data])

    def action(self, t: Tree):
        if "(" in tokens(t):
            return self.reject("action arguments")
        return ident(subtrees(t)[0])

    def obligation(self, t: Tree, top: bool, within):
        s = ident(subtrees(t)[0])
        a = self.action(subtrees(t)[1])
        toks = tokens(t)
        for kw in ("FROM", "UNTIL"):
            if kw in toks:
                self.reject(kw)
        dl = ["none"]
        if "BY" in toks:
            if within is not None:
                return self.reject("BY and WITHIN")
            dl = self.deadline(subtrees(t)[2])
        elif within is not None:
            dl = self.deadline(within)
        if dl is not None and dl != ["none"] and not top:
            return self.reject("deadline in a composite term")
        if a is None or dl is None or "FROM" in toks or "UNTIL" in toks:
            return None
        return ["must", s, a, dl]

    def handler(self, t: Tree):
        s = ident(subtrees(t)[0])
        acts = []
        ok = True
        for b in subtrees(t)[1:]:
            kw = tokens(b)[0]
            x = None
            if kw == "PENALTY":
                if "CAP" in tokens(b):
                    self.reject("CAP")
                x = self.penalty(subtrees(b)[0])
                if "CAP" in tokens(b):
                    x = None
            elif kw == "NOTIFY":
                x = ["notify", ident(subtrees(b)[0])]
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
                x = ["escalate_to", ident(subtrees(b)[0])]
            ok = ok and x is not None
            acts.append(x)
        return ["on_breach", s] + acts if ok else None

    def penalty(self, t: Tree):
        """The PENALTY amount: a literal, kept as an opaque value."""
        x = t
        for rule in ("expr", "implication_expr", "disjunction_expr", "conjunction_expr",
                     "negation_expr", "comparison_expr", "arithmetic_expr", "mul_expr",
                     "unary_expr", "primary"):
            if x.data != rule or tokens(x) or len(subtrees(x)) != 1:
                return self.reject("PENALTY expression")
            x = subtrees(x)[0]
        if x.data != "literal":
            return self.reject("PENALTY expression")
        v = self.literal_value(x)
        return None if v is None else ["penalty", v]

    # --- invariants -------------------------------------------------------

    def invariant(self, t: Tree):
        name = ident(subtrees(t)[0])
        te = [s for s in subtrees(t) if s.data == "temporal_expr"][0]
        c = subtrees(te)[0]
        if c.data != "state_invariant":
            return self.reject(RULES[c.data])
        op = tokens(c)[0]
        if "WITHIN" in tokens(c):
            return self.reject("EVENTUALLY ... WITHIN")
        e = self.cond(subtrees(c)[0])
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
        terms = []
        for el in subtrees(blocks["terms_block"]):
            x = subtrees(el)[0]
            if x.data == "named_term_decl":
                self.reject("named term (:=)")
                continue
            terms.append(self.term_stmt(x, True))
        invs = [self.invariant(i) for i in subtrees(blocks["invariants_block"])]
        self.metadata += self.metadata_sources
        if not self.rejected:
            self.core = ["spec", ["factors"] + factors, ["terms"] + terms,
                         ["invariants"] + invs]


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
