"""Tests of the skill for AI agents (.agents/skills/triel/SKILL.md) and of AGENTS.md.

Run from the root of the repository, once the evaluator is built
(evaluator/README.md):

    python3 -m pytest -q parser/test_skill.py

The two files may state nothing about the repository that is not checked here:

  1. the frontmatter of SKILL.md (the fields of the Agent Skills format, each
     value on one line in a form that a YAML parser reads as this test does)
     and the size of the file;
  2. every ```triel block of the two files is a whole specification that the
     translator accepts, and every TRIEL fragment inside a line of text is in
     FRAGMENTS, with its result in one minimal specification;
  3. every command of SKILL.md over files of the repository is a template or is
     in COMMANDS, which gives its exit code and lines; and every command of
     AGENTS.md is a command of the CI workflows;
  4. every exit code that SKILL.md names is given by a run;
  5. every path of the repository and every section of a document that the two
     files name exists; SKILL.md has no Markdown link, and every link of
     AGENTS.md resolves;
  6. the trace of SKILL.md whose tick entry has the time of the action is
     blocked, and allowed without that entry; a reading MAX_AGE + 1 seconds old
     is allowed with a tick 1 second before the action and blocked with a tick
     at its time;
  7. every pitfall of SKILL.md, part 4, by a run.

The test does not skip: without the evaluator it fails. Most runs call triel
check in this process; the commands that SKILL.md states a result for run as
programs.
"""
import fnmatch
import functools
import json
import os
import re
import shlex
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest
from lark import UnexpectedInput

sys.path.insert(0, str(Path(__file__).parent))
import triel  # noqa: E402
from triel_eval import default_evaluator, find_spec, read_sexp, scenario_input  # noqa: E402
from triel_to_core import translate  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
SKILL_DIR = REPO / ".agents" / "skills" / "triel"
SKILL = SKILL_DIR / "SKILL.md"
LINK = REPO / ".claude" / "skills" / "triel"
AGENTS = REPO / "AGENTS.md"
TRIEL = str(REPO / "parser" / "triel.py")
SCENARIOS = REPO / "examples" / "core" / "scenarios"
INVOICE = "examples/core/core_invoice_agent.triel"
MANDATE = "examples/core/merchant_mandate.triel"
SENSOR = "examples/core/sensor_overheat.triel"
CONTINUATION = "examples/semantics/prohibition_continuation.triel"
CONT = "§2.6 defines continuations only for obligations"


def read(path) -> str:
    return Path(path).read_text(encoding="utf-8")


@functools.lru_cache(maxsize=None)
def skill() -> str:
    return read(SKILL)


@functools.lru_cache(maxsize=None)
def agents() -> str:
    return read(AGENTS)


@functools.lru_cache(maxsize=None)
def tracked() -> dict:
    """path -> mode of every file in the index."""
    out = subprocess.run(["git", "ls-files", "-s", "-z"], cwd=REPO, capture_output=True,
                         check=True).stdout.decode("utf-8")
    return {e.split("\t", 1)[1]: e.split()[0] for e in out.split("\0") if e}


@pytest.fixture(scope="session", autouse=True)
def evaluator():
    exe = default_evaluator()
    assert os.path.isfile(exe) and os.access(exe, os.X_OK), \
        f"no evaluator at {exe}: build it first (evaluator/README.md); this test does not skip"
    return exe


@functools.lru_cache(maxsize=None)
def _translate(text):
    return translate(text)


@pytest.fixture(autouse=True)
def translate_once(monkeypatch):
    monkeypatch.setattr(triel, "translate", _translate)


def blocks(text: str):
    """(info string, line, body) of every fenced block."""
    out, info, start, body = [], None, 0, []
    for n, line in enumerate(text.splitlines(), 1):
        if info is None and line.startswith("```"):
            info, start, body = line[3:].strip(), n, []
        elif info is not None and line.strip() == "```":
            out.append((info, start, "\n".join(body) + "\n"))
            info = None
        elif info is not None:
            body.append(line)
    assert info is None, "a fenced block is not closed"
    return out


def prose(text: str) -> str:
    """The text without its fenced blocks."""
    return re.sub(r"^ *```.*?^ *```$", "", text, flags=re.S | re.M)


def spans(text: str):
    return re.findall(r"`([^`\n]+)`", prose(text))


# --- Runs ---------------------------------------------------------------------

def check(spec, trace, last=False):
    """triel check in this process: the exit code and the lines of the report."""
    return triel.check(str(REPO / spec), str(trace), last=last)


def program(*args, cwd=REPO):
    """triel check as a program, from the root of the repository."""
    return subprocess.run([sys.executable, TRIEL, "check", *map(str, args)],
                          capture_output=True, text=True, encoding="utf-8", cwd=cwd)


def scenario(name, last=False):
    """A scenario of the repository; without --last the report is its .expected file."""
    scn = SCENARIOS / f"{name}.scn"
    named, _ = scenario_input(read_sexp(read(scn)))
    code, lines = triel.check(str(find_spec(named)), str(scn), last=last)
    if not last:
        assert lines == read(scn.with_suffix(".expected")).splitlines()
    return code, lines


def write_trace(tmp_path, name, spec, entries) -> Path:
    p = tmp_path / f"{name}.json"
    p.write_text(json.dumps({"scenario": name, "spec": str(spec), "entries": entries}), encoding="utf-8")
    return p


def at(base: str, seconds: int) -> str:
    t = datetime.strptime(base, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
    return (t + timedelta(seconds=seconds)).strftime("%Y-%m-%dT%H:%M:%SZ")


def entry(time, event, data):
    return {"time": time, "event": event, "data": data}


TICK = {"kind": "tick"}
ACTIVATE = {"kind": "activate"}


def act(subject, action):
    return {"kind": "act", "subject": subject, "action": action, "polarity": "must_not"}


def arrive(factor):
    return {"kind": "arrive", "factor": factor}


def dec(x):
    return {"dec": x}


def boolean(b):
    return {"bool": b}


PAY = {"name": "pay", "args": [{"name": "supplier"}]}


# --- 1. The frontmatter and the size of SKILL.md ------------------------------

FIELDS = {"name", "description", "license", "compatibility"}
PATHS_LINE = ("All paths in this skill are relative to the root of the repository; "
              "run every command from there.")
LICENSE_LINE = ("This file is licensed under CC BY 4.0 (text only). No patent license, express or "
                "implied, is granted. The code of the repository is under the Apache License 2.0; "
                "see `LICENSE.md`.")
KEYWORDS = ["TRIEL specification", "rules for an agent's actions", "before every action",
            "triel check", "obligations with deadlines", "prohibitions", "permissions", "verdict"]
# A plain scalar of YAML may not start with an indicator, nor contain ": " or " #".
INDICATORS = "`@%!&*[]{},>|'\"#"


def scalar(key: str, value: str) -> str:
    """The value of a frontmatter line: a plain scalar, or a simple string in
    double quotes, each read as a YAML parser reads it."""
    if value.startswith('"'):
        assert re.fullmatch(r'"(?:[^"\\]|\\["\\])*"', value), f"{key}: not a simple string in double quotes"
        return json.loads(value)
    assert value and value == value.strip() and "\t" not in value, f"{key}: empty, or white space at an end"
    assert value[0] not in INDICATORS and not re.match(r"[-?:]( |$)", value), \
        f"{key}: starts with an indicator of YAML"
    assert ": " not in value and " #" not in value and not value.endswith(":"), \
        f"{key}: contains ': ' or ' #', or ends with ':'"
    assert not re.fullmatch(r"(?i)true|false|yes|no|on|off|null|~|[-+.0-9][-+.0-9_eE]*", value), \
        f"{key}: YAML reads this value as something other than a string"
    return value


def frontmatter():
    text = skill()
    assert text.startswith("---\n"), "SKILL.md starts with the line ---"
    end = text.index("\n---\n", 3)
    fields = {}
    for line in text[4:end].split("\n"):
        m = re.fullmatch(r"([a-z][a-z-]*): (.*)", line)
        assert m, f"not a line 'key: value': {line!r}"
        key, value = m.groups()
        assert key not in fields, f"{key} is given twice"
        fields[key] = scalar(key, value)
    return fields, text[end + 5:]


def author() -> str:
    m = re.search(r"^Bound Entity: (.+)$", read(REPO / "LICENSE.md"), re.M)
    return m.group(1).strip()


def test_frontmatter():
    fields, _ = frontmatter()
    assert set(fields) == FIELDS
    name = fields["name"]
    assert 1 <= len(name) <= 64 and re.fullmatch(r"[a-z0-9]+(-[a-z0-9]+)*", name)
    assert name == SKILL_DIR.name
    assert 1 <= len(fields["description"]) <= 1024
    assert 1 <= len(fields["compatibility"]) <= 500
    assert fields["license"] == "CC-BY-4.0"
    for k in KEYWORDS:
        assert k in fields["description"], f"the description lacks {k!r}"
    try:
        import yaml
    except ImportError:
        return
    text = skill()
    assert yaml.safe_load(text[4:text.index("\n---\n", 3)]) == fields


def test_start_of_the_body():
    _, body = frontmatter()
    lines = [line for line in body.splitlines() if line.strip()]
    assert lines[:3] == [PATHS_LINE, LICENSE_LINE, f"© 2026 {author()}"]


def test_size():
    text = skill()
    assert len(text.splitlines()) < 500
    assert len(text.split()) <= 3500


def test_the_folder_of_the_skill_holds_text_only():
    files = {p: m for p, m in tracked().items() if p.startswith(".agents/")}
    assert files == {".agents/skills/triel/SKILL.md": "100644"}
    assert not os.access(SKILL, os.X_OK)


def test_the_skill_is_linked_for_claude_code():
    assert tracked().get(".claude/skills/triel") == "120000", ".claude/skills/triel is a symbolic link in git"
    assert os.readlink(LINK) == "../../.agents/skills/triel"
    assert LINK.resolve() == SKILL_DIR.resolve()
    assert not [p for p in tracked() if p.startswith(".claude/") and p != ".claude/skills/triel"]


# --- 2. TRIEL in the text -----------------------------------------------------

MINIMAL = """SPECIFICATION fragments VERSION 1.0.0
{decl}
SUBJECTS {{
  owner    : PARTY,
  agent    : SYSTEM,
  supplier : PARTY
}}

TERMS {{
  {term}
}}

FACTORS {{
  approved : Boolean METADATA,
  quote    : Decimal METADATA{clause}
}}

INVARIANTS {{
  quote_known : LIVENESS : EVENTUALLY(PRESENT(quote))
}}
"""


def minimal(term, clause="", decl=""):
    return MINIMAL.format(term=term, clause=clause, decl=decl)


def result(source) -> str:
    try:
        tr = translate(source)
    except UnexpectedInput:
        return "does not parse"
    return "rejected: " + "; ".join(sorted(tr.rejected)) if tr.rejected else "accepted"


# Every TRIEL fragment written inside a line of SKILL.md or AGENTS.md, with the
# specification MINIMAL that holds it and the result of the translator on it.
FRAGMENTS = {
    'approved == "yes"': (dict(term='agent MUST_NOT pay(supplier) WHEN approved == "yes"'),
                          "rejected: comparison of different types"),
    "pay(supplier)": (dict(term="agent MUST_NOT pay(supplier)"), "accepted"),
    "MAX_AGE 1 HOURS ON_STALE BLOCK": (dict(term="agent MUST_NOT pay(supplier) WHEN quote > 1000.00",
                                            clause=" MAX_AGE 1 HOURS ON_STALE BLOCK"), "accepted"),
}
REPORT = re.compile(r"(SPEC|METADATA|REJECTED:|TIME ORDER REJECTED|ACTIVATION|BLOCK|TYPES|TERM|INVARIANT"
                    r"|MONITOR|LAST ENTRY|STATUS|BREACHED|NOTIFY|PENALTY|NO DECISION|NO ACTION)( |$)")
WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_]*|--?[a-z][a-z-]*|==|!=|<=|>=|<|>")
EXTENSIONS = r"md|triel|scn|json|py|ebnf|lark|hs|yml|sh|expected|thy|txt"


def kind(span: str):
    """What a span in code font is; None for a span that may be TRIEL."""
    if span in FRAGMENTS:
        return "fragment"
    if "…" in span or "..." in span:
        return "template"
    if span.startswith(("python3 ", "triel ", "|", "-", "git ", "ghc ", "isabelle ", "pip ")):
        return "command"
    if "/" in span or re.fullmatch(rf"[\w.-]+\.(?:{EXTENSIONS})", span):
        return "path"
    if REPORT.match(span):
        return "line of the report"
    if WORD.fullmatch(span) or all(WORD.fullmatch(w) and w.isupper() for w in span.split()):
        return "keyword or name"
    return None


@pytest.mark.parametrize("doc", [SKILL, AGENTS], ids=lambda p: p.name)
def test_triel_is_written_in_triel_blocks(doc):
    for info, line, body in blocks(read(doc)):
        if info == "triel":
            assert result(body) == "accepted", f"{doc.name}:{line}"
        else:
            assert not re.search(r"^\s*SPECIFICATION\s", body, re.M), \
                f"{doc.name}:{line}: a specification outside a ```triel block"


@pytest.mark.parametrize("doc", [SKILL, AGENTS], ids=lambda p: p.name)
def test_every_fragment_in_a_line_is_listed(doc):
    unknown = [s for s in spans(read(doc)) if kind(s) is None]
    assert not unknown, f"TRIEL in a line of {doc.name}, not in FRAGMENTS: {unknown}"


@pytest.mark.parametrize("fragment", sorted(FRAGMENTS))
def test_fragment(fragment):
    where, expected = FRAGMENTS[fragment]
    assert fragment in spans(skill()) + spans(agents())
    assert fragment in where.get("term", "") + where.get("clause", "")
    assert result(minimal(**where)) == expected


# --- 3. Commands --------------------------------------------------------------

# The commands of SKILL.md over files of the repository whose result SKILL.md
# states: the exit code and the lines that the standard output contains. Each
# line is stated in SKILL.md too.
COMMANDS = {
    f"python3 parser/triel_to_core.py {CONTINUATION}": (2, [f"REJECTED: {CONT}"]),
}
PLACEHOLDER = re.compile(r"\b(SPEC|TRACE|FILE|PATH)\b")


def commands(text: str):
    """Every command of the text: a span in code font, or a line of a code
    block, that starts with python3."""
    inline = [s for s in spans(text) if s.startswith("python3 ")]
    lines = [line.strip() for info, _, body in blocks(text) if info in ("bash", "sh")
             for line in body.splitlines() if line.strip().startswith("python3 ")]
    return inline + lines


def test_every_command_of_the_skill_is_a_template_or_is_run():
    for c in commands(skill()):
        assert PLACEHOLDER.search(c) or c in COMMANDS, f"a command of SKILL.md without a test: {c}"
    for c, (_, lines) in COMMANDS.items():
        assert c in commands(skill())
        for line in lines:
            assert f"`{line}`" in skill()


@pytest.mark.parametrize("command", sorted(COMMANDS))
def test_command(command):
    code, lines = COMMANDS[command]
    argv = shlex.split(command)
    assert argv[0] == "python3"
    r = subprocess.run([sys.executable] + argv[1:], capture_output=True, text=True,
                       encoding="utf-8", cwd=REPO)
    assert r.returncode == code
    for line in lines:
        assert line in r.stdout.splitlines()


def workflow_lines():
    """The commands of the workflows, a line continued with \\ joined to the
    next, without the path of the Isabelle distribution."""
    out = []
    for wf in sorted((REPO / ".github" / "workflows").glob("*.yml")):
        text = re.sub(r"\\\n\s*", "", read(wf)).replace("~/isabelle/${ISABELLE_VERSION}/bin/", "")
        out += [" ".join(line.split()) for line in text.splitlines()]
    return out


def test_every_command_of_agents_md_is_a_command_of_ci():
    ci = workflow_lines()
    found = [line.strip() for info, _, body in blocks(agents()) if info == "bash"
             for line in body.splitlines() if line.strip()]
    assert found
    for c in found:
        assert any(" ".join(c.split()) in w for w in ci), f"not a command of the workflows: {c}"
    assert "python3 -m pytest -q parser/test_skill.py" in found


def test_the_workflows_are_named_as_in_agents_md():
    for wf in ("evaluator.yml", "parse-examples.yml", "isabelle.yml"):
        name = re.search(r"^name: (.+)$", read(REPO / ".github" / "workflows" / wf), re.M).group(1)
        assert f"`{wf}` ({name})" in agents()


def test_agents_md_is_short():
    assert len(agents().splitlines()) <= 120


# --- 4. Exit codes ------------------------------------------------------------

def named_codes(text: str):
    """The exit codes that the text names: in its table of codes and after the
    word code."""
    table = re.findall(r"^\s*\| (\d) \|", text, re.M)
    words = re.findall(r"\b[Cc]odes? (\d)\b", text)
    return {int(c) for c in table + words}


def no_args_trace(tmp_path):
    """invoice_over_limit, with the action written without its argument."""
    text = read(SCENARIOS / "invoice_over_limit.scn")
    assert "(act agent (pay (name supplier)) must)" in text
    p = tmp_path / "no_args.scn"
    p.write_text(text.replace("(act agent (pay (name supplier)) must)", "(act agent pay must)"),
                 encoding="utf-8")
    return p


def continuation_trace(tmp_path):
    return write_trace(tmp_path, "continuation", CONTINUATION, [
        entry("2026-01-05T09:00:00Z", ACTIVATE, {"sanctioned": boolean(False)})])


# exit code -> (specification, trace, --last); the trace is a scenario of the
# repository or is made in tmp_path.
CHECK_RUNS = {
    0: (MANDATE, lambda t: SCENARIOS / "mandate_price_approved.scn", True),
    1: (MANDATE, lambda t: SCENARIOS / "invoice_over_limit.scn", True),
    2: (CONTINUATION, continuation_trace, True),
    3: (MANDATE, lambda t: SCENARIOS / "mandate_price_over_limit.scn", True),
    4: ("examples/core/core_deadline_cure.triel", lambda t: SCENARIOS / "deadline_cure_time_order.scn", True),
    5: (INVOICE, no_args_trace, True),
    6: ("examples/core/gdpr_art33_notification.triel", lambda t: SCENARIOS / "gdpr_notified_day_5.scn", False),
}


def test_every_code_named_is_run():
    codes = named_codes(skill())
    assert codes >= {0, 1, 2, 3, 4, 5, 6}
    assert codes <= set(CHECK_RUNS)


@pytest.mark.parametrize("code", sorted(CHECK_RUNS))
def test_exit_code(code, tmp_path):
    spec, trace, last = CHECK_RUNS[code]
    r = program(spec, trace(tmp_path), *(["--last"] if last else []))
    assert r.returncode == code, r.stdout + r.stderr


def test_codes_of_the_translator(tmp_path):
    """Part 2: 0 when the translator accepts, 2 when it rejects, 1 when the file
    does not parse."""
    skeleton = tmp_path / "skeleton.triel"
    skeleton.write_text([b for i, _, b in blocks(skill()) if i == "triel"][0], encoding="utf-8")
    broken = tmp_path / "no_invariants.triel"
    broken.write_text(read(skeleton).split("INVARIANTS")[0], encoding="utf-8")
    for path, code in ((skeleton, 0), (REPO / CONTINUATION, 2), (broken, 1)):
        r = subprocess.run([sys.executable, str(REPO / "parser" / "triel_to_core.py"), str(path)],
                           capture_output=True, text=True, encoding="utf-8", cwd=REPO)
        assert r.returncode == code
    assert "exit code 0; 2 with a line `REJECTED: ...` when it rejects a construct; 1 when the file does not parse" \
        in " ".join(skill().split())


def test_the_code_of_a_pipeline_is_that_of_its_last_command(tmp_path):
    """Part 1, step 2: a BLOCK read through a pipeline turns into 0; saved
    first, the code is kept."""
    base = f"{shlex.quote(sys.executable)} parser/triel.py check {MANDATE} " \
           "examples/core/scenarios/mandate_price_over_limit.scn --last --json"
    piped = subprocess.run(["bash", "-c", base + " | tail -n 1"], cwd=REPO, capture_output=True)
    assert piped.returncode == 0
    report = tmp_path / "report.json"
    saved = subprocess.run(["bash", "-c", f"{base} > {shlex.quote(str(report))}; code=$?; echo $code"],
                           cwd=REPO, capture_output=True, text=True)
    assert saved.stdout.strip() == "3"
    assert json.loads(read(report))[-1] == {"line": "LAST", "entry": 2,
                                           "decisions": [{"term": 1, "decision": "BLOCK"}]}
    assert "> report.json; code=$?" in skill()


NESTED = """SPECIFICATION nested_prohibition VERSION 1.0.0

SUBJECTS {
  agent : SYSTEM
}

TERMS {
  agent MUST_NOT pay WHEN amount > limit;
  agent MUST confirm THEN agent MUST_NOT pay WHEN NOT approved
}

FACTORS {
  amount   : Decimal METADATA,
  limit    : Decimal METADATA,
  approved : Boolean METADATA
}

INVARIANTS {
  limit_positive : SAFETY : ALWAYS(limit > 0)
}
"""


def nested_runs(tmp_path):
    """The same prohibition at the top level and inside a composite term: the
    action allowed by the monitor of the first violates the second, again, or
    not at all for an undefined condition."""
    spec = tmp_path / "nested.triel"
    spec.write_text(NESTED, encoding="utf-8")
    t0 = "2026-01-05T09:00:00Z"
    limit = {"limit": dec("1000.00")}
    unapproved = {"amount": dec("500.00"), **limit, "approved": boolean(False)}
    head = [entry(t0, ACTIVATE, limit), entry(at(t0, 60), {"kind": "act", "subject": "agent",
                                                            "action": "confirm", "polarity": "must"}, limit)]

    def attempt(seconds, data):
        return [entry(at(t0, seconds), TICK, data), entry(at(t0, seconds), act("agent", "pay"), data)]
    runs = {
        "first": head + attempt(120, unapproved),
        "again": head + attempt(120, unapproved) + attempt(180, unapproved),
        "undefined": head + attempt(120, {"amount": dec("500.00"), **limit}),
    }
    out = {}
    for name, entries in runs.items():
        p = write_trace(tmp_path, name, spec, entries)
        code, lines = triel.check(str(spec), str(p), last=True)
        out[name] = (code, lines, len(entries) - 1)
    return out


def test_a_nested_prohibition_is_not_decided_by_code_0(tmp_path):
    runs = nested_runs(tmp_path)
    for name, (code, lines, last) in runs.items():
        assert code == 0, name
        assert lines[-1] == f"LAST ENTRY {last} : MONITOR 1 ALLOW"
        assert not any(line.startswith("MONITOR 2") for line in lines), "a composite term has no monitor"
    composite = {name: [line for line in lines if line.startswith("TERM 2 COMPOSITE")][0]
                 for name, (_, lines, _) in runs.items()}
    assert composite["first"].endswith(f"STATUS VIOLATED ENTRY {runs['first'][2]}")
    assert composite["again"].endswith(f"STATUS VIOLATED ENTRY {runs['first'][2]}")
    assert runs["again"][2] > runs["first"][2]
    assert composite["undefined"].endswith("STATUS OPEN")
    text = " ".join(skill().split())
    for words in ("a second violation gives no new line", "is not violated (`STATUS OPEN`)",
                  "`STATUS VIOLATED ENTRY J` confirms a violation"):
        assert words in text


# --- 5. Paths, sections and links ---------------------------------------------

# Paths that SKILL.md and AGENTS.md name and that are not files of the
# repository, each with the reason.
NOT_TRACKED = {
    "evaluator/triel-eval": "built by GHC; in .gitignore",
    "evaluator/build": "built by GHC; in .gitignore",
    "work/": "the folder of the agent's own files, which SKILL.md tells it to make",
    "report.json": "written by a command of SKILL.md",
    "/tmp/classification.txt": "written by a command of evaluator.yml",
}
PATH = re.compile(rf"(?<![\w/.~$-])(?:[\w.-]+/)+[\w.*-]*|(?<![\w/.~$-])[\w-]+(?:\.[\w-]+)*\.(?:{EXTENSIONS})\b")


def paths(text: str):
    out = set()
    for s in spans(text):
        if kind(s) in ("path", "command"):
            out |= set(PATH.findall(s))
    for info, _, body in blocks(text):
        if info in ("bash", "sh"):
            for token in body.split():
                if token in NOT_TRACKED:
                    out.add(token)
                    continue
                out |= set(PATH.findall(re.sub(r"^-[a-z](?=[\w.-]+/)", "", token)))
    return {p for p in out if not p.startswith(("http", "~"))}


def exists(path: str) -> bool:
    """A file or a folder of the index; a glob that matches one; a bare file
    name, such as run.sh, that names a file of the index."""
    files = tracked()
    p = path.rstrip("/")
    if any(c in p for c in "*?["):
        return any(fnmatch.fnmatch(f, p) for f in files)
    if "/" not in path:
        return p in files or any(f.startswith(p + "/") or f.endswith("/" + p) for f in files)
    return p in files or any(f.startswith(p + "/") for f in files)


@pytest.mark.parametrize("doc", [SKILL, AGENTS], ids=lambda p: p.name)
def test_every_path_exists(doc):
    text = read(doc)
    missing = [p for p in sorted(paths(text)) if p not in NOT_TRACKED and not exists(p)]
    assert not missing, f"{doc.name} names paths that are not in git ls-files: {missing}"


def test_the_build_outputs_are_ignored():
    ignored = read(REPO / ".gitignore").splitlines()
    assert "evaluator/triel-eval" in ignored and "evaluator/build/" in ignored
    for p in ("evaluator/triel-eval", "evaluator/build"):
        assert not exists(p)


SECTION = re.compile(r'`([^`]+)`, sections? ((?:"[^"]+"|\d+[a-z]?)(?:(?:, | and )(?:"[^"]+"|\d+[a-z]?))*)')


def headings(path: str):
    text = read(REPO / path)
    if not path.endswith(".md"):
        return [line.strip() for line in text.splitlines()]
    return [re.sub(r"^#+\s*", "", line).strip() for line in prose(text).splitlines()
            if re.match(r"#+ ", line)]


def has_section(path: str, name: str) -> bool:
    hs = headings(path)
    if re.fullmatch(r"\d+[a-z]?", name):
        return any(h.startswith(name + ". ") for h in hs)
    return name in hs


@pytest.mark.parametrize("doc", [SKILL, AGENTS], ids=lambda p: p.name)
def test_every_section_named_exists(doc):
    text = " ".join(read(doc).split())
    found = SECTION.findall(text)
    for path, names in found:
        assert exists(path), path
        for name in re.findall(r'"([^"]+)"|(\d+[a-z]?)', names):
            name = name[0] or name[1]
            assert has_section(path, name), f"{path} has no section {name!r}"
    # Every section named is named with its document.
    assert len(re.findall(r"\bsections?\b", text)) == len(found)


def test_the_skill_has_no_markdown_link():
    text = skill()
    assert not re.search(r"\]\(|\]\[|<https?:", text)


def slug(heading: str) -> str:
    return re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")


def test_the_links_of_agents_md_resolve():
    for target in re.findall(r"\]\(([^)\s]+)\)", agents()):
        assert not re.match(r"[a-z]+:", target), f"an external link: {target}"
        path, _, anchor = target.partition("#")
        rel = os.path.normpath(os.path.join(os.path.dirname("AGENTS.md"), path))
        assert exists(rel), target
        if anchor:
            assert anchor in {slug(h) for h in headings(rel)}, target


# --- 6. The tick entry --------------------------------------------------------

def tick_example():
    m = re.search(r"<!-- test: tick example -->\n```json\n(.*?)\n```", skill(), re.S)
    assert m, "SKILL.md has the trace of the tick entry, marked <!-- test: tick example -->"
    return json.loads(m.group(1))


def test_the_tick_example(tmp_path):
    t = tick_example()
    tick, action = t["entries"][-2:]
    assert tick["event"] == TICK and action["event"]["kind"] == "act"
    assert tick["time"] == action["time"] and tick["data"] == action["data"]
    as_written = tmp_path / "as_written.json"
    as_written.write_text(json.dumps(t), encoding="utf-8")
    r = program(t["spec"], as_written, "--last")
    assert r.returncode == 3 and r.stdout.splitlines()[-1] == "LAST ENTRY 3 : MONITOR 2 BLOCK"
    without = tmp_path / "without_tick.json"
    without.write_text(json.dumps(dict(t, entries=[e for e in t["entries"] if e["event"] != TICK])),
                       encoding="utf-8")
    r = program(t["spec"], without, "--last")
    assert r.returncode == 0 and r.stdout.splitlines()[-1] == "LAST ENTRY 2 : MONITOR 2 ALLOW"
    text = " ".join(skill().split())
    assert "it ends with `LAST ENTRY 3 : MONITOR 2 BLOCK`, exit code 3" in text
    assert "the answer is `ALLOW`, exit code 0" in text


def test_a_tick_one_second_early_lets_a_stale_reading_through(tmp_path):
    max_age = int(re.search(r"motor_temp\s*:.*MAX_AGE (\d+) SECONDS ON_STALE BLOCK", read(REPO / SENSOR)).group(1))
    t0 = "2026-01-05T08:00:00Z"
    reading = {"motor_temp": dec("80.0"), "limit_c": dec("90.0")}
    move = 30 + max_age + 1
    head = [entry(t0, ACTIVATE, {"limit_c": dec("90.0")}), entry(at(t0, 30), arrive("motor_temp"), reading)]
    last = entry(at(t0, move), act("arm", "move"), reading)
    for name, ticks, code, decision in (("no_tick", [], 0, "ALLOW"),
                                        ("tick_early", [entry(at(t0, move - 1), TICK, reading)], 0, "ALLOW"),
                                        ("tick_at", [entry(at(t0, move), TICK, reading)], 3, "BLOCK")):
        got, lines = check(SENSOR, write_trace(tmp_path, name, SENSOR, head + ticks + [last]), last=True)
        assert (got, lines[-1].split()[-1]) == (code, decision), name


def test_an_approval_without_max_age_goes_stale_too(tmp_path):
    """mandate_price_approval_cleared: the approval is cleared after it was
    given; without the tick entry that records it, the change is allowed."""
    text = read(SCENARIOS / "mandate_price_approval_cleared.scn")
    code, lines = check(MANDATE, SCENARIOS / "mandate_price_approval_cleared.scn", last=True)
    assert (code, lines[-1]) == (3, "LAST ENTRY 3 : MONITOR 1 BLOCK")
    without = re.sub(r'\n  \(entry "[^"]*" \(tick\)\n    \(data[^\n]*\)\)(?=\n  \(entry "[^"]*" \(act)', "", text)
    assert without != text
    p = tmp_path / "without_tick.scn"
    p.write_text(without, encoding="utf-8")
    code, lines = check(MANDATE, p, last=True)
    assert (code, lines[-1]) == (0, "LAST ENTRY 2 : MONITOR 1 ALLOW")
    assert "an approval that the host withdrew after its last entry still counts" in " ".join(skill().split())


def test_the_rule_of_the_tick_entry_in_the_documents():
    for doc in ("README.md", "evaluator/README.md"):
        assert "same time as the action" in " ".join(read(REPO / doc).split()), doc


# --- 7. Pitfalls --------------------------------------------------------------

def pitfalls():
    part = skill().split("\n## 4. Pitfalls\n", 1)[1].split("\n## ", 1)[0]
    return dict(re.findall(r"^- \*\*(.+?)\*\*(.*?)(?=^- \*\*|\Z)", part, re.M | re.S))


def mentions(title, *words):
    text = " ".join((title + pitfalls()[title]).split())
    for w in words:
        assert w in text, f"the pitfall {title!r} does not mention {w!r}"


def pitfall_tick(tmp_path):
    test_the_tick_example(tmp_path)
    test_an_approval_without_max_age_goes_stale_too(tmp_path)


def pitfall_undefined(tmp_path):
    _, lines = scenario("invoice_stale_quote")
    assert "TERM 2 MUST_NOT agent pay(supplier) : PENDING" in lines and "MONITOR 2 : ENTRY 3 BLOCK" in lines
    _, lines = scenario("sensor_stale")
    assert "TERM 3 MUST_NOT arm move : PENDING" in lines and "MONITOR 3 : ENTRY 4 BLOCK" in lines
    mentions(TITLES["undefined"], "invoice_stale_quote", "sensor_stale", "`PENDING`")


def pitfall_data(tmp_path):
    _, lines = scenario("invoice_approval_missing")
    assert "TERM 2 MUST_NOT agent pay(supplier) : PENDING" in lines and "MONITOR 2 : ENTRY 2 BLOCK" in lines
    t0 = "2026-01-05T09:00:00Z"
    given = {"amount_eur": dec("1500.00"), "limit_eur": dec("1000.00"), "owner_approved": boolean(True)}
    left_out = {k: v for k, v in given.items() if k != "owner_approved"}
    for name, data, code in (("listed", given, 0), ("left_out", left_out, 3)):
        entries = [entry(t0, ACTIVATE, {"limit_eur": dec("1000.00"), "owner_approved": boolean(True)}),
                   entry(at(t0, 60), arrive("amount_eur"), given),
                   entry(at(t0, 120), TICK, data), entry(at(t0, 120), act("agent", PAY), data)]
        got, _ = check(INVOICE, write_trace(tmp_path, name, INVOICE, entries), last=True)
        assert got == code, name
    assert "A factor that is not listed is absent." in " ".join(read(REPO / "examples/core/README.md").split())
    mentions(TITLES["data"], "invoice_approval_missing", "absent, not unchanged")


def pitfall_fresh(tmp_path):
    _, lines = scenario("sensor_silent")
    assert "MONITOR 3 : ENTRY 2 BLOCK" in lines
    t0 = "2026-01-05T08:00:00Z"
    reading = {"motor_temp": dec("80.0"), "limit_c": dec("90.0")}
    for name, arrival, code in (("activation_only", [], 3),
                                ("arrival", [entry(at(t0, 1), arrive("motor_temp"), reading)], 0)):
        entries = [entry(t0, ACTIVATE, reading)] + arrival + [
            entry(at(t0, 2), TICK, reading), entry(at(t0, 2), act("arm", "move"), reading)]
        got, _ = check(SENSOR, write_trace(tmp_path, name, SENSOR, entries), last=True)
        assert got == code, name
    assert "3. **Freshness.**" in read(REPO / "examples/core/README.md")
    mentions(TITLES["fresh"], "sensor_silent", "Do not add `arrive` entries")


def pitfall_times(tmp_path):
    code, lines = scenario("deadline_cure_time_order", last=True)
    assert code == 4 and "TIME ORDER REJECTED ENTRY 2" in lines
    mentions(TITLES["times"], "deadline_cure_time_order", "exit code 4")


def pitfall_match(tmp_path):
    p = no_args_trace(tmp_path)
    code, lines = check(INVOICE, p, last=True)
    assert code == 5 and "MONITOR 2 : NO ACTION" in lines and lines[-1] == "LAST ENTRY 2 : NO DECISION"
    code, _ = check(INVOICE, p, last=False)
    assert code == 0, "without --last an action that no monitor decides gives 0"
    assert "(act bob leak must)" in read(SCENARIOS / "sequence_polarity.scn")
    _, lines = scenario("sequence_polarity")
    assert lines[5].startswith("TERM 1 COMPOSITE") and lines[5].endswith("STATUS VIOLATED ENTRY 2")
    mentions(TITLES["match"], "`pay` does not match `pay(supplier)`", "sequence_polarity")


def pitfall_cure(tmp_path):
    code, lines = scenario("gdpr_notified_day_5")
    assert code == 6 and any(line.endswith("CURE FULFILLED") and "BREACHED" in line for line in lines)
    mentions(TITLES["cure"], "gdpr_notified_day_5", "exit code 6")


def pitfall_no_decision(tmp_path):
    code, _ = check(INVOICE, no_args_trace(tmp_path), last=True)
    assert code == 5
    test_a_nested_prohibition_is_not_decided_by_code_0(tmp_path)


def pitfall_types(tmp_path):
    for op in ("==", "!="):
        assert result(minimal(f'agent MUST_NOT pay(supplier) WHEN approved {op} "yes"')) == \
            "rejected: comparison of different types"
    assert result(minimal("agent MUST_NOT pay(supplier) WHEN approved == true")) == "accepted"
    mentions(TITLES["types"], "`REJECTED: comparison of different types`", 'approved == "yes"')


def pitfall_handler(tmp_path):
    assert result(read(REPO / CONTINUATION)) == f"rejected: {CONT}"
    for continuation in ("CURE_BY 1 DAYS", "TERMINATE", "ESCALATE_TO owner"):
        term = f"agent MUST_NOT pay(supplier) WHEN NOT approved; agent ON_BREACH NOTIFY owner, {continuation}"
        assert result(minimal(term)) == f"rejected: {CONT}", continuation
    term = "agent MUST_NOT pay(supplier) WHEN NOT approved; agent ON_BREACH NOTIFY owner, PENALTY 5"
    assert result(minimal(term, decl='    CURRENCY: "EUR"\n')) == "accepted"
    assert f"since {CONT}" in " ".join(read(REPO / "examples/core/README.md").split())
    mentions(TITLES["handler"], CONTINUATION, "`CURE_BY`", "`TERMINATE`", "`ESCALATE_TO`")


def pitfall_penalty(tmp_path):
    term = "agent MUST_NOT pay(supplier) WHEN NOT approved; agent ON_BREACH PENALTY 5"
    assert result(minimal(term)) == "rejected: PENALTY without CURRENCY"
    assert result(minimal(term, decl='    CURRENCY: "EUR"\n')) == "accepted"
    assert 'CURRENCY: "EUR"' in read(REPO / "examples/core/core_payment.triel")
    mentions(TITLES["penalty"], "`REJECTED: PENALTY without CURRENCY`", "examples/core/core_payment.triel")


def pitfall_invariants(tmp_path):
    head = minimal("agent MUST_NOT pay(supplier)").split("INVARIANTS")[0]
    assert result(head) == "does not parse"
    assert result(head + "INVARIANTS {\n}\n") == "does not parse"
    mentions(TITLES["invariants"], "exit code 1")


def pitfall_names(tmp_path):
    for name, expected in (("limit", "accepted"), ("U", "does not parse"), ("EU", "does not parse"),
                           ("BLOCK", "does not parse"), ("größe", "does not parse")):
        source = minimal(f"agent MUST_NOT pay(supplier) WHEN {name} > 10").replace(
            "approved : Boolean METADATA,", f"{name} : Integer METADATA,\n  approved : Boolean METADATA,")
        assert result(source) == expected, name
    ebnf = read(REPO / "TRIEL-grammar-v2_5-core.ebnf")
    for word in ('"U"', '"EU"', '"BLOCK"'):
        assert word in ebnf.split("11a. Reserved Keywords")[1].split("11b.")[0]
    mentions(TITLES["names"], "`U`", "`EU`", "`BLOCK`")


def pitfall_host(tmp_path):
    over = read(SCENARIOS / "mandate_price_over_limit.scn")
    approved = read(SCENARIOS / "mandate_price_approved.scn")

    def entries(t):
        return t[t.index("(entry"):]
    assert entries(over).replace("(price_change_approved (bool false))", "(price_change_approved (bool true))") \
        == entries(approved)
    assert scenario("mandate_price_over_limit", last=True)[0] == 3
    assert scenario("mandate_price_approved", last=True)[0] == 0
    assert "nothing here checks that they are true" in read(REPO / "evaluator/README.md")
    mentions(TITLES["host"], "TRIEL does not check that a trace is true")


TITLES = {
    "tick": "The `tick` entry at the time of the action",
    "undefined": "An undefined condition blocks.",
    "data": "`data` is the complete data at that entry.",
    "fresh": "Freshness needs an arrival.",
    "times": "Times may not decrease.",
    "match": "An event matches a norm by subject, action name and arguments.",
    "cure": "A breach stays on record after a cure.",
    "no_decision": "`NO DECISION` is not a permission, and a prohibition inside a composite term has no monitor",
    "types": "`==` and `!=` compare values of one type.",
    "handler": "The handler of a prohibition",
    "penalty": "`PENALTY` needs a currency",
    "invariants": "`INVARIANTS` is required",
    "names": "Names are ASCII identifiers",
    "host": "The trace is the host's data.",
}
PITFALLS = {TITLES[k]: f for k, f in (
    ("tick", pitfall_tick), ("undefined", pitfall_undefined), ("data", pitfall_data),
    ("fresh", pitfall_fresh), ("times", pitfall_times), ("match", pitfall_match),
    ("cure", pitfall_cure), ("no_decision", pitfall_no_decision), ("types", pitfall_types),
    ("handler", pitfall_handler), ("penalty", pitfall_penalty), ("invariants", pitfall_invariants),
    ("names", pitfall_names), ("host", pitfall_host))}


def test_every_pitfall_has_a_run():
    assert set(pitfalls()) == set(PITFALLS)


@pytest.mark.parametrize("title", sorted(PITFALLS))
def test_pitfall(title, tmp_path):
    PITFALLS[title](tmp_path)


# --- The other statements of SKILL.md -----------------------------------------

def test_statements_of_the_report_part(tmp_path):
    """Part 3: what the lines of the report say."""
    _, lines = scenario("mandate_price_approved")
    assert "INVARIANT budget_limit_set : U" in lines          # ALWAYS is never T on a finite trace
    assert "MONITOR 3 : NO ACTION" in lines                    # the subject never takes the action
    assert "TERM 2 ON_BREACH agent : BOUND 1" in lines
    _, lines = scenario("purpose_consented")
    assert "TERM 1 MAY agent transfer_personal_data : FULFILLED" in lines
    _, lines = scenario("sequence_one_payment")
    assert any(line.endswith("STATUS OPEN") for line in lines)
    assert "always_never_true" in read(REPO / MANDATE)
    for words in ("is never `T` on a finite trace", "`NO ACTION` when the subject never takes the action",
                  "an action under an undefined condition is blocked but not breached"):
        assert words in " ".join(skill().split())


def test_statements_of_the_proof_part():
    """Part 5 says no more than README.md and evaluator/README.md."""
    readme = " ".join(read(REPO / "README.md").split())
    evaluator = " ".join(read(REPO / "evaluator/README.md").split())
    assert "the command only reads the files, runs the translator and the evaluator, and prints" in readme
    assert "The translator, the reading of the trace and the printing are tested, not proved." in readme
    assert "nothing here checks that they are true" in evaluator
    assert "hold the action back on any exit code other than 0" in evaluator
    part = " ".join(skill().split("\n## 5. ", 1)[1].split())
    for words in ("the command only reads the files, runs the translator and the evaluator, and prints",
                  "The translator, the reading of the trace and the printing are tested, not proved.",
                  "holds the action back on any exit code other than 0", "not the interception"):
        assert words in part


def test_the_check_before_an_action_comes_first():
    """Part 1 is the first part, and a standing rule."""
    _, body = frontmatter()
    parts = re.findall(r"^## (.+)$", body, re.M)
    assert parts[0] == "1. Before every action that a TRIEL specification governs"
    first = body.split("\n## 1. ", 1)[1].split("\n## ", 1)[0]
    assert first.split("\n", 2)[2].startswith("Before every action that a TRIEL specification governs")
    assert "--last" in first and "--json" in first
