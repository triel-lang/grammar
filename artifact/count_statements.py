#!/usr/bin/env python3
"""
Count the proved statements of Isabelle theories: the commands lemma, theorem,
corollary, proposition and schematic_goal. lemmas (a name for facts that are
already proved) is not counted.

Usage:
    python3 count_statements.py FILE.thy...

Comments (* ... *), quoted terms "..." and `...`, and cartouches (the text of
text, section and the other document commands) are blanked out first, so a
keyword inside them is not counted. A command is counted where it starts a line,
as in the theories of formal/core. Prints one line per file and a total line.
"""
import re
import sys

STATEMENT = re.compile(r"^[ \t]*(lemma|theorem|corollary|proposition|schematic_goal)\b(?!s)",
                       re.MULTILINE)
OPEN, CLOSE = ("\\<open>", "‹"), ("\\<close>", "›")


def blank(text: str) -> str:
    return re.sub(r"[^\n]", " ", text)


def outer_syntax(src: str) -> str:
    """The theory source with comments, quotations and cartouches blanked out."""
    out, i, n = [], 0, len(src)
    while i < n:
        start = i
        if src.startswith("(*", i):
            depth, i = 1, i + 2
            while depth:
                if i >= n:
                    raise ValueError("unterminated comment")
                if src.startswith("(*", i):
                    depth, i = depth + 1, i + 2
                elif src.startswith("*)", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        elif src[i] in "\"`":
            quote, i = src[i], i + 1
            while src[i] != quote:
                i += 2 if src[i] == "\\" and src[i + 1] in "\"`\\" else 1
            i += 1
        elif src.startswith(OPEN, i):
            depth = 0
            while True:
                o = next((t for t in OPEN if src.startswith(t, i)), None)
                c = next((t for t in CLOSE if src.startswith(t, i)), None)
                if o:
                    depth, i = depth + 1, i + len(o)
                elif c:
                    depth, i = depth - 1, i + len(c)
                    if not depth:
                        break
                elif i >= n:
                    raise ValueError("unterminated cartouche")
                else:
                    i += 1
        else:
            out.append(src[i])
            i += 1
            continue
        out.append(blank(src[start:i]))
    return "".join(out)


def main(paths):
    total = 0
    for path in paths:
        with open(path, encoding="utf-8") as f:
            n = len(STATEMENT.findall(outer_syntax(f.read())))
        total += n
        print(f"{path}: {n}")
    print(f"total: {total}")


if __name__ == "__main__":
    main(sys.argv[1:])
