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

## Files

| File | What |
|---|---|
| `cases.jsonl` | the cases, one JSON object per line, UTF-8, LF, sorted by `id` |
| `classes.json` | every reason the translator can give: its class, the section of the text the class rests on, and for a reason built by the code, where it comes from |
| `unreachable.json` | the calls of `reject` that no input reaches, or that are redundant, with the argument for each |
| `rejects.py` | the calls of `reject` and the reasons, read from the source of the translator |
| `measure.py` | the measurements |
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
can give is in `classes.json`.

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
the lines with times.

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
  not shown.
- Inputs nested too deeply for the recursion of the parser or the translator.
- The grammar itself: its ambiguity (`parser/test_ambiguity.py`) and its
  agreement with `TRIEL-grammar-v2_5-core.ebnf`.
