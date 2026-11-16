"""The calls of reject in the translator and the reasons it can give, read from
its source text without running it.

    python3 parser/corpus/rejects.py [TRANSLATOR]

prints the counts and every reason with where it comes from. The default
TRANSLATOR is parser/triel_to_core.py. measure.py and test_corpus.py use the
functions below.

A call is self.reject(ARG). It stands as a statement when it is the whole of an
expression statement or of a return statement; otherwise it is inside an
expression. Its ARG is of one of these kinds:

  str       a string literal: the reason itself
  rules     RULES[...]: a value of the table RULES
  fstring   an f-string: a template, expanded by TEMPLATES below
  why       the variable why: a string returned by a function of HELPERS
  c.value   a keyword of the declaration block (COMPUTED below)
  PROHIBITION_CONTINUATION
            the constant of that name, a string of the module

A reason is a text that some call can give. The reasons are the string literal
arguments, the values of RULES other than "core" and "metadata", the string
constants returned by the functions of HELPERS, the expansions of the templates
and the values of the computed arguments.
"""
import ast
import sys
from pathlib import Path

DEFAULT_TRANSLATOR = Path(__file__).resolve().parent.parent / "triel_to_core.py"

# Functions of the module whose string results reach reject through why.
HELPERS = ("referable",)

# Every template of the translator and the texts it gives. The values of the
# placeholders are read from the code around each template:
#   type {p}        p is a token of primitive_type (triel.lark) that is not a key
#                   of PRIMITIVES: only Duration;
#   type {kind}     kind is the first token of composite_type other than Record;
#   ZK type without {k}
#                   k runs over the tuple ("PROOF_SYSTEM", "CURVE") of check_zk;
#   {what} of a non-DateTime factor
#                   what is the second argument of time_factor, "deadline" in
#                   deadline and "FROM" in start.
TEMPLATES = {
    "f'type {p}'": ["type Duration"],
    "f'type {kind}'": ["type List", "type Map", "type Progress"],
    "f'ZK type without {k}'": ["ZK type without PROOF_SYSTEM", "ZK type without CURVE"],
    "f'{what} of a non-DateTime factor'": ["deadline of a non-DateTime factor",
                                          "FROM of a non-DateTime factor"],
}

# The computed arguments other than why and PROHIBITION_CONTINUATION: c.value in
# declaration is one of the keywords of the test just above the call.
COMPUTED = {
    "c.value": ["REPLACES", "IMPORT", "ANCHOR_MODE", "QUORUM_THRESHOLD"],
}

KINDS = ("str", "rules", "fstring", "why", "c.value", "PROHIBITION_CONTINUATION")


def _parents(tree):
    parent = {}
    for node in ast.walk(tree):
        for child in ast.iter_child_nodes(node):
            parent[child] = node
    return parent


def _is_reject(node):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "reject" and isinstance(node.func.value, ast.Name)
            and node.func.value.id == "self")


def arg_kind(arg) -> str:
    """The kind of the argument of a call of reject, or "other"."""
    if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
        return "str"
    if (isinstance(arg, ast.Subscript) and isinstance(arg.value, ast.Name)
            and arg.value.id == "RULES"):
        return "rules"
    if isinstance(arg, ast.JoinedStr):
        return "fstring"
    if isinstance(arg, ast.Name) and arg.id == "why":
        return "why"
    if isinstance(arg, ast.Name) and arg.id == "PROHIBITION_CONTINUATION":
        return "PROHIBITION_CONTINUATION"
    if ast.unparse(arg) == "c.value":
        return "c.value"
    return "other"


def calls(source: str):
    """Every call of self.reject in the order of the text: a dict with the
    function (the name of the method or function that holds it), its number
    among the calls of that function (from 1), the position, whether it is a
    statement, the kind of its argument and the argument as written."""
    tree = ast.parse(source)
    parent = _parents(tree)
    out = []
    for node in ast.walk(tree):
        if not _is_reject(node):
            continue
        p = parent[node]
        f = p
        while not isinstance(f, (ast.FunctionDef, ast.AsyncFunctionDef)):
            f = parent[f]
        statement = isinstance(p, (ast.Expr, ast.Return)) and p.value is node
        arg = node.args[0]
        out.append({"function": f.name, "line": node.lineno, "col": node.col_offset,
                    "end_line": node.end_lineno, "end_col": node.end_col_offset,
                    "statement": statement, "kind": arg_kind(arg), "arg": ast.unparse(arg),
                    "value": arg.value if arg_kind(arg) == "str" else None})
    out.sort(key=lambda c: (c["line"], c["col"]))
    seen = {}
    for c in out:
        seen[c["function"]] = seen.get(c["function"], 0) + 1
        c["index"] = seen[c["function"]]
    return out


def rules_table(source: str) -> dict:
    """The dict RULES of the module, read from its literal."""
    for node in ast.parse(source).body:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name) and node.targets[0].id == "RULES"):
            return ast.literal_eval(node.value)
    raise ValueError("no RULES in the translator")


def module_string(source: str, name: str) -> str:
    for node in ast.parse(source).body:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name) and node.targets[0].id == name):
            return ast.literal_eval(node.value)
    raise ValueError(f"no {name} in the translator")


def helper_strings(source: str) -> dict:
    """The string constants returned by the functions of HELPERS, by function."""
    out = {}
    for node in ast.parse(source).body:
        if isinstance(node, ast.FunctionDef) and node.name in HELPERS:
            out[node.name] = [r.value.value for r in ast.walk(node)
                              if isinstance(r, ast.Return) and isinstance(r.value, ast.Constant)
                              and isinstance(r.value.value, str)]
    return out


def reasons(source: str):
    """Every reason, with where it comes from: a dict reason -> list of sources,
    each "reject", "RULES", "<helper> (why)", "template <template>",
    "computed c.value" or "PROHIBITION_CONTINUATION". Raises ValueError for a
    template or an argument the tables above do not know."""
    out = {}

    def add(text, src):
        srcs = out.setdefault(text, [])
        if src not in srcs:
            srcs.append(src)

    for c in calls(source):
        k = c["kind"]
        if k == "str":
            add(c["value"], "reject")
        elif k == "fstring":
            if c["arg"] not in TEMPLATES:
                raise ValueError(f"unknown template {c['arg']} in {c['function']}")
            for t in TEMPLATES[c["arg"]]:
                add(t, f"template {c['arg']}")
        elif k == "c.value":
            for t in COMPUTED["c.value"]:
                add(t, "computed c.value")
        elif k == "PROHIBITION_CONTINUATION":
            add(module_string(source, "PROHIBITION_CONTINUATION"), "PROHIBITION_CONTINUATION")
        elif k == "other":
            raise ValueError(f"unknown argument {c['arg']} of reject in {c['function']}")
    for v in rules_table(source).values():
        if v not in ("core", "metadata"):
            add(v, "RULES")
    for h, texts in helper_strings(source).items():
        for t in texts:
            add(t, f"{h} (why)")
    return out


def summary(source: str) -> dict:
    cs = calls(source)
    kinds = {k: sum(c["kind"] == k for c in cs) for k in KINDS + ("other",)}
    return {"calls": len(cs), "statements": sum(c["statement"] for c in cs),
            "in_expressions": sum(not c["statement"] for c in cs), "kinds": kinds,
            "reasons": len(reasons(source))}


def main() -> int:
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_TRANSLATOR
    source = path.read_text(encoding="utf-8")
    s = summary(source)
    print(f"calls of reject: {s['calls']} ({s['statements']} statements, "
          f"{s['in_expressions']} inside expressions)")
    print("arguments: " + ", ".join(f"{k} {n}" for k, n in s["kinds"].items()))
    print(f"reasons: {s['reasons']}")
    for text, srcs in sorted(reasons(source).items()):
        print(f"  {text}  [{'; '.join(srcs)}]")
    return 0


if __name__ == "__main__":
    sys.exit(main())
