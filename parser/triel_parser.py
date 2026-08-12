#!/usr/bin/env python3
"""
Reference parser for TRIEL v2.4, built from the published EBNF
(TRIEL-grammar-v2_4-core.ebnf, github.com/triel-lang/grammar).

Usage:
    python3 triel_parser.py FILE.triel [FILE2.triel ...]
    python3 triel_parser.py --check-ambiguity FILE.triel   # diagnostic mode

Exit code is 0 iff every given file parses successfully. This is meant to be
run in CI against examples/*.triel so a grammar change or a new example that
doesn't actually conform can never be merged silently again (see audit
finding A-01).
"""
import sys
import argparse
from pathlib import Path

from lark import Lark, UnexpectedInput
from lark.exceptions import UnexpectedCharacters, UnexpectedToken

GRAMMAR_PATH = Path(__file__).parent / "triel.lark"


def build_parser(ambiguity: str = "resolve") -> Lark:
    grammar_text = GRAMMAR_PATH.read_text()
    return Lark(
        grammar_text,
        start="start",
        parser="earley",
        lexer="dynamic",
        ambiguity=ambiguity,
    )


def count_ambig_nodes(tree) -> int:
    """Count _ambig nodes in a tree parsed with ambiguity='explicit'."""
    count = 0
    for node in tree.iter_subtrees():
        if node.data == "_ambig":
            count += 1
    return count


def check_file(path: Path, check_ambiguity: bool) -> bool:
    source = path.read_text()
    ok = True

    parser = build_parser(ambiguity="resolve")
    try:
        parser.parse(source)
        print(f"OK      {path}")
    except UnexpectedInput as e:
        ok = False
        print(f"FAIL    {path}")
        print(f"        {type(e).__name__} at line {e.line}, column {e.column}")
        context = e.get_context(source, span=60).replace("\n", "\n        ")
        print(f"        {context}")

    if ok and check_ambiguity:
        amb_parser = build_parser(ambiguity="explicit")
        tree = amb_parser.parse(source)
        n = count_ambig_nodes(tree)
        if n:
            print(f"        WARNING: {n} ambiguous parse node(s) in this file "
                  f"— the grammar admits more than one parse tree for this "
                  f"input (see audit findings D-19/D-20/D-21).")

    return ok


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("files", nargs="+", type=Path)
    ap.add_argument("--check-ambiguity", action="store_true",
                     help="Also report whether the input has more than one "
                          "valid parse tree under the current grammar.")
    args = ap.parse_args()

    all_ok = True
    for path in args.files:
        if not check_file(path, args.check_ambiguity):
            all_ok = False

    if not all_ok:
        print("\nOne or more files did not parse against "
              "TRIEL-grammar-v2_4-core.ebnf.")
        return 1
    print(f"\nAll {len(args.files)} file(s) parsed successfully.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
