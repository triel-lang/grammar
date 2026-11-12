"""Probe of the export of parse trees. Parses FILE with parser/triel.lark as
parser/triel_to_core.py does and writes to TREE one line per node in preorder:
N <rule> <number of children>, L <terminal> <decimal codes of the text>, or A
(an absent optional element); writes to EXPECTED the output of the functions
(a) and (b) of formal/surface/Surface_Probe.thy, computed without HOL.
Usage: tree.py FILE TREE EXPECTED"""
import sys
from pathlib import Path
from lark import Lark, Tree

GRAMMAR = Path(__file__).resolve().parents[3] / "parser" / "triel.lark"
CONST = '"delivered"'  # str_const of Surface_Probe.thy, compared in (b)
texts = []  # the texts of the STRING_LITERAL tokens of the lark tree, in preorder


def lines(x):
    if x is None:
        yield "A"
    elif isinstance(x, Tree):
        yield f"N {x.data} {len(x.children)}"
        for c in x.children:
            yield from lines(c)
    else:
        if x.type == "STRING_LITERAL":
            texts.append(str(x))
        yield " ".join(["L", x.type] + [str(ord(c)) for c in x])


src, tree_file, expected_file = sys.argv[1:]
parser = Lark(GRAMMAR.read_text(encoding="utf-8"), start="start", parser="earley",
              lexer="dynamic", ambiguity="resolve", keep_all_tokens=True)
tree_lines = list(lines(parser.parse(Path(src).read_text(encoding="utf-8"))))
Path(tree_file).write_text("\n".join(tree_lines) + "\n", encoding="ascii")
expected = []
for variant in ("lit", "codes"):
    expected += [f"(a) {variant} " + " ".join(str(ord(c)) for c in t) for t in texts]
    expected += [f"(b) {variant} {t == CONST}" for t in texts]
Path(expected_file).write_text("\n".join(expected) + "\n", encoding="ascii")
