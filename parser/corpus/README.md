# The corpus of the translator

`cases.jsonl` lists specifications with the result of their translation into the
formal core (`formal/core/CORE.md` §10.6): the outcome; for an accepted
specification, the exact core term; for a rejected one, the classes of the
reasons. The cases are data, not code: any implementation of the translation can
be checked against them as a black box. `parser/test_corpus.py` checks them
against the reference translator `parser/triel_to_core.py`, and `measure.py`
counts what the corpus catches and what it does not.

## What is observed, and how to check another implementation

Run the implementation on the `source` of every case and compare:

- the outcome: `accepted`, `rejected`, or `parse_error` (the text does not parse
  with `parser/triel.lark`), equal to `outcome`;
- for `accepted`: the core term as `sexp` of `parser/triel_to_core.py` prints
  it, equal to `term`, character for character (the grammar of the term is in
  `evaluator/Main.hs`). A string in the term is printed between double quotes,
  with `\` and `"` escaped by `\` and every other character as itself, so a
  newline or a tab in a string is printed as it is. The evaluator also reads
  `\n` and `\t` in a string of the term as a newline and a tab, so a term that
  prints them as `\n` and `\t` has the same value; the corpus compares the form
  that `sexp` prints;
- for `rejected`: the classes of the reasons (`classes.json` gives the class of
  every reason of the reference translator; another implementation maps its own
  reasons to the same seven classes). For a case with `single_defect` the set of
  classes equals `classes`; for any other rejected case it has at least one
  class in common with `classes`.

`reasons` and `header` are for reference: they are the texts of the reference
translator (its reasons, and its lines `SPEC` and `METADATA`), and another
implementation need not reproduce them. `parser/test_corpus.py` compares them
exactly, `header` of a rejected case as well as of an accepted one, since it
checks the reference translator.

A case with `disputed` records what the reference translator does where the
text of the specification does not decide the question or reads otherwise.
Another implementation is not bound by it there: a difference on such a case is
a question about the text, not a failure.

This rule is the function `another_implementation` of `parser/test_corpus.py`.
Given a case and the output of another implementation on its `source` (the
outcome; for `accepted`, the term; for `rejected`, the classes of its reasons),
it gives `passed` if there is no difference, `failed` for a difference, and
`disputed` for a difference on a case with `disputed`. A difference is: another
outcome; for `accepted`, another term; for `rejected` with `single_defect`,
another set of classes; for `rejected` without it, no class in common; for
`parse_error`, only the outcome is compared. Its test checks it on outputs
built in the test.

## Files

| File | What |
|---|---|
| `cases.jsonl` | the cases, one JSON object per line, UTF-8, LF, sorted by `id` |
| `classes.json` | every reason the translator can give: its class, the section of the text the class rests on, and for a reason built by the code, where it comes from |
| `unreachable.json` | the calls of `reject` that no input reaches, or that are redundant, with the argument for each |
| `killed.json` | places of first-order mutants of the translator that the corpus catches by a different output, each with the cases that catch it |
| `survivors.json` | the places of first-order mutants of the translator that the corpus does not catch, each with why: no input tells the mutant apart, or what was tried |
| `rejects.py` | the calls of `reject` and the reasons, read from the source of the translator |
| `measure.py` | the measurements; `--killed` writes `killed.json` and `survivors.json` |
| `../test_corpus.py` | the check of the corpus against the translator |

### A case

| Field | When | What |
|---|---|---|
| `id` | always | unique; Latin letters, digits, `.`, `_`, `-`. `moved.<test>.<n>` for a case taken from `parser/test_triel_to_core.py`, `new.…` for the others |
| `source` | always | the whole text of a specification |
| `outcome` | always | `accepted`, `rejected` or `parse_error` |
| `term` | `accepted` | the core term, `sexp(translate(source).core)` |
| `header` | `accepted`, `rejected` | the lines `SPEC …` and `METADATA …` (for reference) |
| `classes` | `rejected` | the sorted list of the classes of the reasons |
| `reasons` | `rejected` | the sorted list of the reasons of the reference translator (for reference) |
| `single_defect` | `rejected`, optional | `true`: the input has exactly one defect, and one reason |
| `pair` | optional | the `id` of the paired case: a single-defect case and its minimal correction, which is accepted. The two refer to each other, and their sources differ in at most two places (at most two operations other than `equal` of `difflib.SequenceMatcher(None, a, b).get_opcodes()`) |
| `rules` | always | the rules of `parser/triel.lark` the case was written for; each is in its parse tree. May be empty |
| `origin` | always | `new`, or the sorted list of the tests `test_triel_to_core.py::<function>` the input comes from |
| `contains` | moved cases; new accepted cases | checks, each an object with one key: `substring` (a substring of the term), `reasons` (the exact list of reasons) or `metadata` (the exact list of `METADATA` lines). A moved case has every check its test makes on that input; a new accepted case has at least one substring in which its construct is visible, and the corrected case of a pair shows the place of the correction |
| `disputed` | optional | one or two sentences: where the translator and the text of the specification disagree, or where the text is silent. The case records what the translator does |
| `same_term` | optional | the `id` of a case whose term must be the same; the two refer to each other. Used for a string written with a character outside ASCII and the same string written with `\u` escapes |

### The classes

| Class | What |
|---|---|
| `fragment` | a construct outside the fragment of the core: the rejections by the name of a rule of the grammar, `AND (term)`, `CAUSED_BY`, `CONSTRAINT`, `PUBLIC_WITNESS`, field `DEFAULT`, the types outside the core, arithmetic, division in `PENALTY` |
| `names` | names and their scope: undeclared, declared twice, `REF` forward or to an undeclared name |
| `types` | the types of operands and of conditions: conditions, comparisons, `DEFAULT`, `PRESENT`, the amount of `PENALTY` |
| `time` | deadlines and time: `WITHIN`, `BY`, `FROM`, the deadline of `ELSE`, durations, `DATETIME`, calendar units, a deadline in a composite term, staleness (`MAX_AGE`, `ON_STALE`) |
| `structure` | the structure of the block: `ON_BREACH`, continuations, `ELSE`, `REF` to a handler or to a term with a deadline |
| `flow` | the flow rule for hidden factors (`TECHNICAL_REPORT.md` §2.7) |
| `metadata` | the parameters and the binding of ZK proofs (`TECHNICAL_REPORT.md` §2.8), `ORACLE` and `PROVENANCE_REQUIRED`, `CURRENCY` (§2.9) |

Each reason has exactly one class. A reason that names a construct outside the
core is `fragment`; the flow rule is `flow`; the rules of §2.8 and the rules of
§2.9 on `ORACLE` and `CURRENCY` are `metadata`; the rules of §2.9 on staleness
are `time`; the restrictions of `ELSE`, of handlers, of continuations and of
`REF` are `structure`, except a `REF` to an undeclared name or forward
(`names`) and `ELSE deadline not after the first deadline` (`time`). Any other
reason has the class of the section of the text it protects, given in
`section`. A reason built by the code (from an f-string, from a keyword, from
`referable`) is listed with each text it can take, and `from` says where it
comes from. `not_single`, where present, says why the reason cannot be given
alone.

### unreachable.json

A list of objects: `function` and `index` (the call of `reject`, by its number
among the calls of that function in the order of the text, from 1), `reason`,
`kind` (`unreachable` or `redundant`), `argument` (one or two sentences) and
`input` (a specification). For an unreachable call, `input` is written to reach
the call, and `where` is the place where it is rejected earlier, or the rule of
the grammar that makes such an input impossible. For a redundant call, `other`
gives the call (`function`, `index`) that adds the same reason on every input
that reaches this one, and `input`, a case of the corpus, executes both.

### killed.json

A list of objects, one per line, sorted by place. Each is a place of a
first-order mutant of the translator, as `measure.py` makes them (the places of
section 4), that the corpus catches by a difference in output: on at least one
of its cases the mutant gives an output other than an exception that differs
from the case as `test_case` compares them (the function `mismatches`). The
fields: `text`, the line of `parser/triel_to_core.py` as it is written;
`occurrence`, the number of that line among the lines with the same text, from
1; `line`, the number of the line in the file, which follows from the two;
`col`, `op` and `variant`, the rest of the place (`op` is `comparison`,
`and/or`, `not`, `constant` or `statement`); and `ids`, the cases on which the
mutant and the translator differ.

`parser/test_corpus.py` runs the mutant of every place on its cases, with the
parse trees it already has, and fails if the line of a place has changed
("places moved: regenerate with measure.py --killed"), if a case of `ids` is
not in the corpus, if the entries are not sorted by place ("killed.json: not
sorted by place") or list a place twice ("killed.json: a place is listed
twice"), if a place is not a place of mutation ("killed.json: (line, col, op,
variant) is not a place of mutation: regenerate with measure.py --killed"), or
if no case of a place tells its mutant apart: an output that is an exception
does not. It also runs the translator itself the same way on all these cases,
which must agree with the corpus, and fails if the mutants take more than 30
seconds. Four places, the strings `"spec"` and `"factors"` of the term changed
or replaced by `None`, are told apart only by the term: on every case of their
entries the mutant gives the outcome, the header and the reasons of the
translator. After a change of the translator that moves lines,

```bash
python3 parser/corpus/measure.py --killed
```

finds every line again by its text and occurrence, checks that the place is
still a place of mutation and that its mutant is still caught, finds the cases
again and writes the file (into the repository), and does the same for
`survivors.json`, without the cases; if a place is gone or no longer caught,
it writes nothing and says which. The file does not list every mutant that the
corpus catches, and the test does not check that it does.

### survivors.json

The places of first-order mutants of the translator (the places of section 4
of `measure.py`) that the corpus does not catch: on every case the mutant gives
the output of the translator. A list of objects, one per line, sorted by place,
with the fields of `killed.json` but `ids` (`text`, `occurrence`, `line`,
`col`, `op`, `variant`), and two more:

- `kind`: `equivalent`, no input of the grammar gives the mutant an output
  other than the output of the translator; or `open`, no such input has been
  found and the equivalence is not shown;
- `argument`: for `equivalent`, why, by the kind of the mutation, with the
  rules of `parser/triel.lark` and the lines of `parser/triel_to_core.py` it
  rests on: for an index `[0]` changed to `[-1]`, the rule that makes the node
  and why it has exactly one such child there; for a constant changed, where
  its value goes and why it never reaches the output; for a statement deleted,
  why its value is never read or the line never runs; for `and` and `or`
  swapped, why the operands never make the two differ. For `open`, what was
  tried.

A place whose mutant a case of the corpus tells apart only by an exception
(the verdict `caught (exceptions only)` of `measure.py`) is in neither file.
Of its random mutants that no test catches, section 4 of `measure.py` names
`equivalent` those whose places are of kind `equivalent` here
(`equivalent_places`); it reads the file when it runs, not when `measure.py`
is imported.

`parser/test_corpus.py` fails if the file is empty, if it is not in the format
of `killed.json` ("survivors.json: not sorted by place", "survivors.json: a
place is listed twice", "survivors.json: (line, col, op, variant) is not a
place of mutation: regenerate with measure.py --killed"), if an entry has
other fields or no `kind` and `argument`, if a place is also in `killed.json`,
or if the line of a place has changed ("places moved: regenerate with
measure.py --killed"). It also checks `equivalent_places` on a copy of three
entries, one of them `open` and one without `kind`. That the mutants of these
places are still not caught, and that no other place is not caught, the test
does not check: a run of every mutant on the corpus does, as `measure.py`
computes the verdict of a place (`verdict`). `measure.py` has no command for
that run; it is a loop over `places()` that computes
`verdict(mutant_code(p)[0])` for every place `p` and compares the places whose
verdict is `not caught` with the places of this file.

## Running

The check, from the root of the repository (it runs in CI, workflow
`evaluator.yml`):

```bash
python3 -m pytest -q parser/test_corpus.py
```

`test_case` is parametrized by `id`: every failed parameter is a case on which
the translator and the corpus disagree. The other tests check the format, that
every rule of `parser/triel.lark` is in the parse tree of some case, that every
reason has a pair of cases, and that every reason the code of the translator
can give is in `classes.json`. Further tests check these checks: the format
of spoilt copies of cases, of an accepted case as well as of a rejected one,
each copy with the one error it must give (among them a missing, empty or
malformed `header`, `header` on a `parse_error` whatever `TERMS_RECORDED`, and
a field of a case of another outcome); `pair` and `same_term` among the cases
given; the reading of a spoilt `cases.jsonl`, an empty line among them (the
error names the line), and of the file itself with a line cut short: the
collection of `parser/test_corpus.py` fails with an error that names the line,
whichever of `measure.py` and `parser/test_corpus.py` reads the file first;
that the comparison of `test_case` finds each field it compares changed in a
copy of a case (the term and the header of an accepted case, the header, the
classes and the reasons of a rejected case, the checks of `contains`); and that
an output of a mutant that is an exception does not catch it (`caught`). Then
the rule for another implementation, the format of `killed.json` and of
`survivors.json`, and the places of both, also on a copy of each with a line
number changed and a text changed. A test that takes a case of the corpus by
its `id` looks it up when it runs: without that case only the tests that take
it fail.

The measurements, from the root of the repository (not in CI):

```bash
python3 parser/corpus/measure.py
```

They need Python 3.13.18 with the standard library, lark 1.3.1, pytest 9.2.0
and coverage 7.17.3, the versions with which they were made; coverage runs with
`branch = True` and `patch = subprocess`, and the random mutants are first-order
mutants of five kinds: a comparison operator replaced, `and` and `or` swapped,
`not` removed, a constant changed (a number by one, a Boolean negated, a string
changed, a constant replaced by `None`) and a statement deleted. The output is
markdown: the corpus; the deletion of every call of `reject`; the coverage of
the translator by statements and branches, by the corpus and by the corpus with
`parser/test_triel_to_core.py`; 100 random mutants of the translator (seed 7);
and the time of each. `--section N` computes one section alone. The variable
`TRIEL_TRANSLATOR` names another translator to measure (its grammar and its
`test_triel_to_core.py` are those next to it), and `TRIEL_EVALUATOR` the
evaluator for the tests of section 3 and 4. Two runs give the same output except
the lines with times. Every such line ends with `(time)`, so they are set apart
with `grep -v '(time)$'`; `grep -v '(time)'` would also drop the counts
`- caught (time): N` of sections 2 and 4, which are not times.

## What the corpus does not check

- The evaluator, the reports and the scenarios (`examples/core/scenarios`,
  `examples/core/conformance`): the corpus stops at the core term.
- The texts of the reasons and the lines `SPEC` and `METADATA` of another
  implementation, and which reasons it gives besides one of the right class
  when a case has several defects.
- `--actions`, `--classify`, the command line and the indented printing of the
  term.
- Inputs that are not in it: a construct, a combination or a value it does not
  contain may be translated wrongly without a failed case. `measure.py` lists
  the deletions of calls of `reject` that no case catches, and those of its 100
  random mutants that no case catches; the random mutants are a sample of the
  places of mutation, and a mutant outside the sample that no case catches is
  not shown. `killed.json` holds only the places listed in it.
- Inputs nested too deeply for the recursion of the parser or the translator.
- The grammar itself: its ambiguity (`parser/test_ambiguity.py`) and its
  agreement with `TRIEL-grammar-v2_5-core.ebnf`.
