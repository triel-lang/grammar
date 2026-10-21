#!/usr/bin/env python3
"""
Every TRIEL excerpt in the normative documents conforms to the grammar.

Run from anywhere:  python3 parser/test_documents.py

The excerpts are extracted from the files themselves, so an excerpt that is
added or changed is checked without editing this script:

  * every ```triel block of the documents below is a whole specification and
    must parse, with exactly one derivation;
  * every grammar excerpt of TECHNICAL_REPORT.md (a ``` block with `::=`) must
    be, production by production, the text of the same production in
    TRIEL-grammar-v2_5-core.ebnf (whitespace aside);
  * every "Example N:" of the USAGE EXAMPLES of the EBNF must parse with the
    rule its first keyword names (a declaration header, a FACTORS, INVARIANTS
    or CROSS_MODAL block), and so must the desugaring of Progress<T>;
  * every inline `...` span of the documents that contains PROVES must parse
    as a type.

Exit code 0 iff every excerpt passes; the last line is "All N excerpts
conform to the grammar." This script runs in CI (parse-examples.yml) and in
artifact/run.sh.
"""
import re
import sys
from pathlib import Path

from lark import Lark, UnexpectedInput

REPO = Path(__file__).resolve().parent.parent
GRAMMAR = REPO / "parser" / "triel.lark"
EBNF = REPO / "TRIEL-grammar-v2_5-core.ebnf"
DOCUMENTS = ["TECHNICAL_REPORT.md", "README.md", "FOUNDATIONS.md", "formal/core/CORE.md",
             "examples/core/README.md", "parser/README.md"]
RULE_OF_KEYWORD = {"SPECIFICATION": "declaration_block", "FACTORS": "factors_block",
                   "INVARIANTS": "invariants_block", "CROSS_MODAL": "cross_modal_block"}
STARTS = ["start", "type_expr"] + sorted(set(RULE_OF_KEYWORD.values()))


def parsers():
    text = GRAMMAR.read_text(encoding="utf-8")
    one = Lark(text, start=STARTS, parser="earley", lexer="dynamic", ambiguity="resolve")
    every = Lark(text, start=STARTS, parser="earley", lexer="dynamic", ambiguity="explicit")
    return one, every


def fenced(text: str, lang: str):
    """(line, body) of every fenced block whose info string is lang."""
    out, info, start, body = [], None, 0, []
    for n, line in enumerate(text.splitlines(), 1):
        if info is None and line.startswith("```"):
            info, start, body = line[3:].strip(), n, []
        elif info is not None and line.strip() == "```":
            if info == lang:
                out.append((start, "\n".join(body) + "\n"))
            info = None
        elif info is not None:
            body.append(line)
    return out


def productions(text: str):
    """name -> body of every production "name ::= body" in text, whitespace
    normalised. A body runs to the next production or the end of a comment."""
    text = re.sub(r"\(\*.*?\*\)", "\n", text, flags=re.S)
    out = {}
    parts = re.split(r"^[ \t]*([a-z_][a-z0-9_]*)[ \t]*::=", text, flags=re.M)
    for name, body in zip(parts[1::2], parts[2::2]):
        out[name] = " ".join(body.split())
    return out


def usage_examples(ebnf: str):
    """(title, rule, text) of every "Example N:" of the USAGE EXAMPLES, and the
    desugaring of Progress<T>."""
    start = ebnf.index("USAGE EXAMPLES")
    block = ebnf[start:ebnf.index("====", ebnf.index("Example 1:", start))]
    out = []
    for m in re.finditer(r"^ *(Example \d+:[^\n]*)\n *-+\n(.*?)(?=^ *Example \d+:|\Z)",
                         block, flags=re.M | re.S):
        body = "\n".join(line[3:] if line.startswith("   ") else line
                         for line in m.group(2).splitlines()).strip()
        out.append((m.group(1).strip(), RULE_OF_KEYWORD[body.split()[0]], body))
    m = re.search(r"Progress<T> desugars to:\n(.*?)\n\n", ebnf, flags=re.S)
    out.append(("Progress<T> desugaring", "type_expr", m.group(1).strip()))
    return out


def inline_types(text: str):
    """Inline code spans that are a ZK type with constraints: ZK<...> PROVES(...)."""
    return [s for s in re.findall(r"`([^`\n]+)`", text) if re.match(r"ZK<\w+> *PROVES", s)]


def main() -> int:
    one, every = parsers()
    ebnf = EBNF.read_text(encoding="utf-8")
    grammar_productions = productions(ebnf)
    checks = []    # (where, rule, text)
    failures = []

    for doc in DOCUMENTS:
        text = (REPO / doc).read_text(encoding="utf-8")
        for line, body in fenced(text, "triel"):
            checks.append((f"{doc}:{line}", "start", body))
        for span in inline_types(text):
            checks.append((f"{doc}: `{span}`", "type_expr", span))
        if doc == "TECHNICAL_REPORT.md":
            for line, body in fenced(text, ""):
                if "::=" not in body:
                    continue
                for name, prod in productions(body).items():
                    where = f"{doc}:{line} production {name}"
                    if grammar_productions.get(name) != prod:
                        failures.append(f"{where}: not the production of {EBNF.name}")
                    else:
                        print(f"OK      {where}")
    for title, rule, body in usage_examples(ebnf):
        checks.append((f"{EBNF.name}: {title}", rule, body))

    for where, rule, text in checks:
        try:
            one.parse(text, start=rule)
            n = sum(1 for t in every.parse(text, start=rule).iter_subtrees() if t.data == "_ambig")
        except UnexpectedInput as e:
            failures.append(f"{where}: does not parse as {rule} (line {e.line}, column {e.column})")
            continue
        if n:
            failures.append(f"{where}: {n} ambiguous node(s)")
        else:
            print(f"OK      {where}")

    total = len(checks) + sum(1 for doc in ["TECHNICAL_REPORT.md"]
                              for _, b in fenced((REPO / doc).read_text(encoding="utf-8"), "")
                              if "::=" in b for _ in productions(b))
    for f in failures:
        print(f"FAIL    {f}")
    if failures:
        print(f"{len(failures)} of {total} excerpts do not conform to the grammar.")
        return 1
    print(f"All {total} excerpts conform to the grammar.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
