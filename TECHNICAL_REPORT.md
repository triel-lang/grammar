# TRIEL: A Declarative Specification Language with Native Temporal and Zero-Knowledge Constraints

**Technical Report — Draft v0.1**

---

## Abstract

TRIEL is an open, declarative specification language in which a single, human-readable source expresses subjects, obligations, factors, and temporal invariants over a system's behavior. Unlike specifications expressed in natural language, a TRIEL specification's invariants are written in linear and branching-time temporal logic (LTL/CTL), and its data fields may carry zero-knowledge constraints — provable predicates that do not require revealing the underlying value. The grammar as currently defined admits unbounded integer arithmetic and uninterpreted function calls inside temporal formulas, so satisfiability over the full language is not decidable in general; a decidable subset (bounded domains, no free function calls) is achievable but is not yet carved out or enforced by the grammar, and doing so is tracked as future work (Section 4). This report describes the language's syntax and semantics (Section 2), motivates the specification-implementation gap it addresses (Section 3), positions it relative to existing specification and policy languages (Section 4), and states plainly what the language does and does not claim to guarantee (Section 5).

The grammar described here (v2.4) is published under the Open Web Foundation Agreement 1.0 at `github.com/triel-lang/grammar`; every example in this report is drawn from that repository and can be independently checked against the published EBNF.

---

## 1. The Specification–Implementation Gap

### 1.1 The Problem

A specification is typically written once, in natural language or in a semi-formal document, and the system that implements it is built, maintained, and modified separately. Over the life of a project, the two diverge: the implementation accumulates edge-case handling, bug fixes, and expedient decisions that the original specification never mentioned, while the specification itself is rarely revisited once the implementation exists. This divergence is a well-documented source of compliance failures, audit findings, and — in systems with autonomous or semi-autonomous components — behavior that satisfies no one's actual intent.

Three common responses to this gap each fall short in a specific, identifiable way:

- **Natural-language specifications** ("the system shall process refunds within 5 business days") are readable by anyone, but provide no mechanical way to check whether an implementation actually satisfies them, and no way to detect when two clauses of the same specification are in tension with each other.
- **Pointing a capable code-reading tool at the implementation** — increasingly common now that large language models can navigate large codebases — conflates *what the code does* with *what the code was meant to do*. Code captures implementation, including its bugs and shortcuts; a tool reading only the code has no independent signal for which behaviors were intended and which were accidental.
- **Markdown or prose requirements documents** improve on pure natural language by giving structure, but provide no mechanism for surfacing contradictions. Two sections can assert incompatible constraints without the document format doing anything to flag the conflict; catching it is left entirely to the diligence of whoever wrote or last reviewed the document.

### 1.2 Why Temporal Logic and Not Just Assertions

Even specification approaches that do use formal or semi-formal constructs — assertions, unit tests, schema validators — typically check a system's state at a single point in time: "the balance is non-negative right now." Many real specifications are not single-point claims but claims about *sequences of states over time*: "a refund request must eventually be resolved," "a payment must never be split once initiated," "once an account is flagged, it must remain flagged until a reviewer clears it." These are properties of *traces*, not of individual states, and expressing them naturally requires temporal operators — `ALWAYS`, `EVENTUALLY`, `NEXT` — as first-class parts of the specification language, not as a library convention layered on top of an otherwise atemporal assertion mechanism.

### 1.3 Why Zero-Knowledge Constraints, Natively

A related but distinct gap appears whenever a specification must express a compliance condition on a value without disclosing the value itself — "the applicant is over 18," "the account balance exceeds the required threshold," "the vehicle stayed within its permitted zone" — without revealing the birth date, the exact balance, or the route. These conditions are usually implemented by reaching for a separate zero-knowledge proof toolkit, disconnected from whatever specification language governs the rest of the system's behavior: the *business rule* ("an adult may proceed") lives in one artifact, and the *cryptographic circuit* proving the rule's precondition lives in another, with no machine-checked relationship between the two. TRIEL treats a zero-knowledge provability constraint as a type-level annotation on a field — `ZK<Decimal> PROVES (self >= threshold) WITHOUT REVEALING self` — so that the business rule and the disclosure boundary are stated in the same place, by the same author, and checked by the same compiler.

---

## 2. The TRIEL Language (v2.4)

This section summarizes the published grammar's structure; the full EBNF (`TRIEL-grammar-v2_4-core.ebnf`) is authoritative and should be consulted for exact syntax. All examples below are drawn verbatim or near-verbatim from the repository's `examples/` directory.

### 2.1 Top-Level Structure

A TRIEL specification consists of a declaration header, a set of typed subjects, a set of terms (obligations, permissions, prohibitions, and event-triggered rules), a set of factors (typed, optionally zero-knowledge-constrained data fields), and a set of temporal invariants:

```triel
SPECIFICATION age_verification VERSION 1.0.0
    JURISDICTION "EU"

SUBJECTS {
    Applicant : PARTY
}

FACTORS {
    age : ZK<Integer> PROVES (self >= 18) WITHOUT REVEALING self
}

TERMS {
    ON verification_requested(applicant) DO
        Applicant MAY proceed WHEN age >= 18
}

INVARIANTS {
    age_gate_enforced : SAFETY : ALWAYS (proceed_granted IMPLIES age >= 18)
}
```

### 2.2 Deontic Primitives

Obligations, permissions, and prohibitions are the language's three deontic primitives, each binding a subject to an action under an optional condition or deadline:

- `subject MUST action [BY deadline] [FROM start] [UNTIL end]` — an obligation.
- `subject MAY action [WHEN condition] [WITHIN deadline]` — a permission.
- `subject MUST_NOT action [WHEN condition]` — a prohibition.

These compose through `AND` (parallel), `OR` (choice), `THEN` (sequence), and `UNLESS ... DO` (guarded alternative evaluated once at entry), and can be attached to events via `ON event DO term`.

### 2.3 Factors and Zero-Knowledge Constraints

A factor is a typed, named value — a piece of state the specification reasons about. Factors carry a `POLARITY` (whether the factor's increase counts toward or against compliance) or are marked `METADATA` (a value supplied from outside the specification, such as a configurable threshold). A factor's type may additionally be a zero-knowledge type:

```
zk_type ::= "ZK" "<" primitive_type ">" zk_constraints
zk_constraints ::= "PROVES" "(" zk_constraint {"," zk_constraint} ")"
                   ["WITHOUT" "REVEALING" zk_visibility]
```

A `zk_constraint` is restricted, by design, to comparisons against a literal, a range, a set, or a hash — not to an arbitrary expression over other factors. This is a deliberate simplification relative to general-purpose zero-knowledge circuit languages (Section 4.2): TRIEL's zero-knowledge constraints express *what must be provable about a single field*, not the full circuit logic a dedicated ZK-DSL would compile. Where a specification needs to relate a zero-knowledge-constrained factor to another factor (e.g., "assets exceed liabilities," where liabilities are also specification-level state), that relationship is expressed as an ordinary invariant over both factors, keeping the ZK-constraint syntax itself simple and the cross-factor relationship visible in the same `INVARIANTS` block as every other temporal property.

### 2.4 Temporal Invariants

An invariant is either a state invariant (`ALWAYS(expr)`, `EVENTUALLY(expr) [WITHIN deadline]`, `NEXT(expr)`) or a full LTL/CTL formula built from the standard temporal operators (`G`, `F`, `X`, `U`, `R`, `W` for LTL; `A`/`E` path quantifiers combined with `X`/`F`/`G`/`U`/`R` for CTL). Both logics may appear in the same specification's `INVARIANTS` block, each validated according to its own semantics; mixing is permitted because the two logics answer different questions (LTL: does *this* trace satisfy the property; CTL: does *every*/*some* trace from this state satisfy it) that a single specification may need to ask about different parts of its behavior.

### 2.5 Trace Semantics

Write `⟦t⟧` for the set of traces — finite sequences of deontic events `(subject, action, polarity)` — that a `TERMS` block `t` admits. The semantics follows the structure of the grammar directly:

```
⟦subject MUST action⟧                = { ⟨(subject, action, must)⟩ }
⟦subject MAY action WHEN c⟧          = { ⟨(subject, action, may)⟩ }        if eval(c), else ∅
⟦subject MUST_NOT action WHEN c⟧     = { ⟨(subject, action, must_not)⟩ }   if ¬eval(c), else ∅

⟦t1 THEN t2⟧   = { σ1++σ2 | σ1 ∈ ⟦t1⟧, σ2 ∈ ⟦t2⟧ }
⟦t1 AND t2⟧    = { interleave(σ1,σ2) | σ1 ∈ ⟦t1⟧, σ2 ∈ ⟦t2⟧ }
⟦t1 OR t2⟧     = ⟦t1⟧ ∪ ⟦t2⟧

⟦t1 UNLESS c DO t2⟧  = { σ ∈ ⟦t1⟧ | ¬eval(c) } ∪ { σ ∈ ⟦t2⟧ | eval(c) }
```

In every rule above, `eval(c)` is evaluated once, at the point the enclosing term is reached in the trace — the state available at that point in the specification's execution, not at some later or earlier point. This applies uniformly to `WHEN`-guarded permissions and prohibitions and to `UNLESS`'s guard: none of the language's guard constructs re-evaluate their condition mid-term.

A specification's `INVARIANTS` block is satisfied by a trace `σ` in the ordinary sense of LTL/CTL satisfaction over `σ`'s sequence of deontic events, with `ALWAYS`/`EVENTUALLY`/`NEXT` as the abbreviations `G`/`F`/`X` restricted to state-formula arguments (Section 2.4).

*(This semantics governs the surface language as published in the v2.4 grammar. It is stated here at the level of detail needed to support the claims of Section 5; a fully worked compilation-soundness proof is future work, tracked openly in the repository.)*

### 2.6 Breach and Deadline Semantics

Section 2.5 gives every `MUST`/`MAY`/`MUST_NOT` term a *generative* semantics: `⟦t⟧` is the set of traces a `TERMS` block admits, and an obligation simply produces the trace in which its action occurs. That model has no notion of an obligation going unmet — the only trace it knows about is the one where everything happened as specified — which left `ON_BREACH` with nothing to attach to. This section extends the semantics with the distinction that was missing: a *specification trace* (what Section 2.5 already defines) versus an *implementation trace* — the sequence of events a running system actually produces, each carrying a timestamp: `(subject, action, polarity, τ)` with `τ` a point in wall-clock time.

**Satisfaction and breach.** Against an implementation trace `σ`:

- `subject MUST action BY d` is *satisfied* if `σ` contains `(subject, action, must, τ)` for some `τ ≤ eval(d)`, and is *breached* at `eval(d)` if no such event has occurred by then. Deadline satisfaction is therefore only decidable once the deadline is reached, not before — an obligation is neither satisfied nor breached while its window is still open.
- `subject MUST_NOT action WHEN c` is *breached* the instant `σ` contains `(subject, action, must_not, τ)` with `eval(c)` true at `τ`; it carries no deadline, since a prohibition has nothing to wait for.
- `subject MAY action ...` cannot be breached — a permission has no obligation-bearing party to hold to it.

**Binding `ON_BREACH`.** A `breach_handler_stmt` (`subject ON_BREACH ...`) is bound to the nearest preceding obligation or prohibition for the same `subject` within the same `TERMS` block — the reading every example in this repository already uses. This is a deliberately narrow binding rule, stated explicitly rather than left implicit: a subject with two or more obligations and a single trailing `ON_BREACH` is not yet given a defined meaning by this report, and is tracked as open work rather than silently permitted.

**The five breach actions.** They fall into two classes:

- *Informational* — `NOTIFY subject` and `PENALTY expr` — fire once, at the moment of breach, and do not affect how the trace continues. (`PENALTY`'s `expr` still evaluates to a bare number, not a typed monetary amount; that gap is unchanged by this section and remains tracked separately.)
- *Continuation-determining* — `TERMINATE`, `CURE_BY d`, `ESCALATE_TO subject` — each answers the question "what happens to the breached obligation now" in a mutually incompatible way: `TERMINATE` closes it with no further window, `CURE_BY d` reopens a new deadline `d` during which the *original* obligation can still be satisfied without a second breach firing, and `ESCALATE_TO subject'` transfers responsibility for it to `subject'`.

A `breach_action` list containing more than one action from the continuation-determining class — e.g. `PENALTY x, NOTIFY y, TERMINATE, CURE_BY 5 DAYS`, the exact combination flagged elsewhere in review of this grammar — has no single defined continuation and is a semantic error, not a silently accepted specification. This is a semantic-analysis rule in the same sense as the `QUORUM_THRESHOLD` bound already noted in the grammar file's SEMANTIC RULES section: it constrains which grammar-conformant parses are meaningful, and is checked at that level, not by the grammar itself.

**Deadlines are not temporal-logic operators.** Section 2.4 lists `ALWAYS`/`EVENTUALLY`/`NEXT` as the qualitative LTL abbreviations `G`/`F`/`X`. Every deadline-bearing construct — `BY`, `WITHIN`, `MAX_AGE`, `CURE_BY`, `FROM ... UNTIL` — is deliberately kept outside that logic rather than folded into it as a metric extension. Each denotes a plain arithmetic comparison against the `τ` component of a trace event, not a subscripted temporal operator: `EVENTUALLY(expr) WITHIN d`, for instance, is satisfied by `σ` if there exists `τ` with `τ₀ ≤ τ ≤ τ₀ + eval(d)` at which `expr` holds, where `τ₀` is the time the enclosing term became active (Section 2.5's existing rule that guards evaluate once, at entry, fixes what `τ₀` means here). This keeps `WITHIN` from being decorative — it now has a truth condition — without claiming the full temporal logic is metric, which is what made the decidability claim in Section 4 false in the first place.

**What this does not yet cover.** A calendar model — the exact meaning of `BUSINESS_DAY`, month and year arithmetic, timezone handling for `DATETIME` literals — is still undefined; two conformant implementations can compute a deadline differently until that model exists. `PENALTY`'s numeric type remains untyped. Multi-obligation `ON_BREACH` scoping, noted above, is open. All three are tracked as future work rather than assumed solved by this section.

---

### 2.7 Zero-Knowledge Information-Flow Typing

Sections 2.3 and 2.6 treat a `ZK<T>` factor as a type annotation and give its deadline-bearing neighbors a real semantics, but neither says what a specification is and is not allowed to *do* with the hidden value itself once it exists as a factor. Without such a rule, a specification can be entirely grammar-conformant and still leak precisely the value it was written to conceal — for example, an `INVARIANTS` clause that reads `ALWAYS(age >= 18)` directly, where `age` is declared `ZK<Integer> ... WITHOUT REVEALING self`. The type says the value is hidden; nothing enforces it.

**The flow rule.** A factor declared with a `zk_type` and no `WITHOUT REVEALING ALL` override (see below) is *restricted*: its value may appear only inside the `zk_constraint` expressions of its own `PROVES(...)` clause. It is illegal — a semantic-analysis error, in the same sense as the `QUORUM_THRESHOLD` bound and the breach-action rule of Section 2.6 — for a restricted factor's identifier to appear anywhere else a value is evaluated: in an `INVARIANTS` predicate, in a `PENALTY` expression, in a `WHEN`/`IF` guard, or as an operand of comparison or arithmetic outside its own constraint. Using the factor's name as a bare argument to an action that operates on *the proof itself* — `submit_proof(age)` in this repository's own examples — is not a value-evaluation position and remains legal: it names which field a proof is being submitted for without extracting its value into another computation.

**What a specification does instead.** Every `ZK<T>` factor's constraint verification produces a result — whether the proof checked out — and that result, not the value, is what the rest of the specification is entitled to reason about. This report's own Section 2.1 example already follows this pattern (`ALWAYS (proceed_granted IMPLIES age >= 18)` reasons about the outcome, not the raw value in isolation); this section makes the pattern a rule rather than a stylistic choice. The two age-gated examples in this repository (`age_verification.triel`, `eudi_driving_license.triel`) previously read the hidden `age` factor directly in `INVARIANTS` — the exact violation this rule forbids, flagged in independent review of this grammar — and have been corrected to declare a public `age_proof_valid : Boolean` factor and reason about that instead.

**Hidden by default.** The `["WITHOUT" "REVEALING" zk_visibility]` clause in the grammar is optional, but its absence is not treated as "unspecified": a `ZK<T>` factor with no `WITHOUT REVEALING` clause at all defaults to `zk_visibility = self` — fully hidden, and subject to the flow rule above. `WITHOUT REVEALING ALL` is the explicit, visible-in-source opt-out; a specification cannot end up disclosing a value by omission.

**What this does not yet cover.** The flow rule as stated is a semantic-analysis rule, not something the grammar's context-free structure can enforce on its own — checking it requires a pass that knows which factors are ZK-typed, the same category of tool this report has been explicit about not yet having (Section 4). It also does not yet define what happens when a restricted factor is passed through a `LET` binding, a `function_call`, or a `Record`/`List` composite that embeds it — those positions are open questions for the same future analysis pass, not silently assumed safe.

---

### 2.8 Cryptographic Parameterization and Binding

Section 2.7 constrains what a specification may *do* with a hidden value; it says nothing about how the proof around that value is produced, or who is allowed to present it. Left unaddressed, three gaps remain even in a specification that follows the flow rule perfectly: a `HASH(self)` predicate over a low-entropy field is brute-forceable by hashing every candidate value; a proof carries no link to the identity or session it was issued for, so it can be replayed by anyone who observed it once; and nothing in a specification says which proof system or curve it targets, so two conformant compilers can emit mutually unverifiable proofs from the same source. This section closes all three.

**Salting (B-10).** `zk_constraint`'s `HASH` form now requires a second argument — `HASH(self, salt_ref)` — where `salt_ref` names a factor holding a value unique to that specification instance. This is enforced by the grammar itself, not by a semantic-analysis rule layered on top: a `HASH(self)` predicate with no salt argument is no longer syntactically valid at all, so there is no way to omit it. A `salt_ref` pointing at a `METADATA` factor with a fixed, specification-wide literal default is not a salt — a compiler is expected to reject that case at semantic analysis, since a constant defeats the purpose as thoroughly as no salt at all.

**Binding to identity and session (B-11).** `zk_constraints` gains an optional `BOUND_TO(subject, nonce)` clause, where `subject` must be a `SUBJECTS`-declared identifier carrying a `DID`, and `nonce` must be a factor holding a single-use value refreshed per presentation. The clause is optional in the grammar — many specifications have no identity-bearing subject at all, and requiring it unconditionally would be meaningless for those — but a semantic-analysis rule requires it whenever the factor's `SOURCE` subject *does* carry a `DID`: a proof about a DID-bearing identity with no `BOUND_TO` clause is a compile error, on the same footing as the `QUORUM_THRESHOLD` bound already enforced this way. The `eudi_driving_license.triel` example, whose scenario is precisely the identity-wallet case this finding targets, now declares `applicant`'s `DID` and binds the `age` proof to it and to a `presentation_nonce` factor sourced from the verifier.

**Declaring the proof system (B-12).** `declaration_block` gains optional `PROOF_SYSTEM` (`GROTH16` | `PLONK` | `STARK` | `BULLETPROOFS`) and `CURVE` fields. As with `BOUND_TO`, these are grammatically optional but semantically required — whenever a specification's `FACTORS` block contains any `ZK<T>` factor, omitting either is a compile error rather than a default: an implicit choice of proof system is exactly the kind of cross-compiler divergence this grammar exists to rule out, so there is no fallback value to pick silently. Both example specifications with `ZK<T>` factors (`age_verification.triel`, `eudi_driving_license.triel`) now declare `PROOF_SYSTEM: GROTH16` and `CURVE: "BN254"`.

**What this does not yet cover.** These three fixes address how a single proof is salted, bound, and parameterized; they do not specify a key-distribution or verification-key-publication mechanism, which remains open. `BOUND_TO`'s nonce factor is declared but its refresh protocol — who generates it, how often, and how staleness is detected — is left to the compiler implementation, the same category of gap already acknowledged for `MAX_AGE`-governed oracle factors (Section 2.6). A full threat model — who is assumed honest, what constitutes a successful attack, and against which of these three mechanisms — is still absent from this report and remains the most consequential open item for the privacy and identity claims this language makes.

---

### 2.9 Oracle Trust, Monetary Values, and Missing Data

Section 2.6 gave `MAX_AGE` a place in the trace model but stopped short of saying what happens once a factor actually goes stale; nothing in the grammar connected an `ORACLE`-sourced factor to any trust requirement at all; `PENALTY` computed a bare number with no currency, no bound, and no protection against a negative result; and `Optional<T>` (Section 2.3) had no operators, so an invariant reading an absent value was undefined the moment it was empty. This section closes all four.

**Staleness has a defined outcome (C-15, part one).** `factor_decl` gains an optional `ON_STALE` clause — `BLOCK`, `USE_LAST`, or `ESCALATE_TO subject` — using the same escalation vocabulary `breach_action` already established (Section 2.6). It is grammatically optional but semantically required whenever the same factor declares `MAX_AGE`: a value that can expire with no declared behavior for that moment is a compile error now, not a silent "keep using it."

**Oracle data requires provenance (C-15, part two).** `PROVENANCE_REQUIRED` and `ORACLE` both existed in the v2.4 grammar independently, but nothing required them together. A semantic-analysis rule now closes that gap: any specification with a factor sourced from an `ORACLE`-declared subject must set `PROVENANCE_REQUIRED: true`. The concrete attestation mechanism this triggers remains compiler-defined, exactly as `PROVENANCE_REQUIRED`'s semantics were already scoped in the grammar's SEMANTIC RULES section — this rule connects two existing fields rather than inventing new machinery. Multi-source quorum and a dispute mechanism for a contested oracle value are not addressed here and remain open.

**Money has a currency and a ceiling (C-16).** `declaration_block` gains an optional `CURRENCY` field, semantically required whenever any `breach_action` is a `PENALTY` — an amount with no declared currency is a number, not money. `breach_action`'s `PENALTY` form gains an optional `CAP literal`, giving the specification author a hard upper bound where they choose to declare one, and a semantic rule requires the computed amount to be non-negative. This report does not yet introduce a first-class monetary type: `PENALTY`'s `expr` still shares its literal syntax with ordinary `Float`, which is a known precision hazard for currency math. The interim rule is that a literal used in a `Decimal`- or money-denominated context must be read as an exact base-10 decimal by the compiler regardless of that shared lexical form — a semantic requirement standing in for a proper exact-decimal literal syntax, which remains future work. `delivery_agreement.triel` now declares `PROVENANCE_REQUIRED: true` and `CURRENCY: "USD"`, applies `ON_STALE BLOCK` to its `MAX_AGE`-bearing oracle factor, and caps its `PENALTY` at 10000.

**Missing values are reasonable about, not just declarable (D-29).** Two new expression forms make `Optional<T>` usable: `PRESENT(f)` evaluates to a `Boolean` — true if `f` currently holds a value, and false both when `f` is an empty `Optional<T>` and when `f` has gone stale under its own `ON_STALE` rule, since a value the specification no longer trusts is not meaningfully "there" for this purpose. `DEFAULT(f, fallback)` evaluates to `f`'s value when present and to `fallback` otherwise, letting an invariant be written total over both cases without a separate guard every time. Neither form is mandatory by semantic rule — omitting them is only a problem once an invariant goes on to read an `Optional` factor's value directly, which is a type-checking concern left to the same future analysis pass already noted for the information-flow rule of Section 2.7.

---

### 2.10 Content-Pinned References

`IMPORT`, `EXECUTE`, and `REPLACES` are the three ways a TRIEL specification can point at another one — pulling in shared terms, calling out to another specification's logic mid-`TERMS`, or declaring itself a successor to a prior version. None of the three previously said what content they expected to find at the other end: a path, an identifier, and a bare version number are all names, and a name can resolve to different content over time or across deployments without the specification itself changing at all. This section makes all three checkable claims rather than assumptions.

**A shared pinning mechanism.** `import_decl`, `contract_ref_stmt`, and the `REPLACES` field of `declaration_block` each gain an optional `HASH hash_literal` clause, where `hash_literal` is fixed to the format `"sha256:"` followed by 64 lowercase hex digits — a compiler rejecting anything else. The clause is grammatically optional, following the same pattern as `PROOF_SYSTEM`/`CURVE`/`BOUND_TO`/`CURRENCY` before it, but a semantic-analysis rule requires it wherever the surrounding construct is present at all: a specification that imports, executes, or replaces something must say what content it expects there, or the reference is a compile error.

**`REPLACES` now says whose version it replaces.** The field previously took only a version number — `REPLACES 1.0.0` — which never answered "1.0.0 of what," a real ambiguity once a specification imports more than one other file. It now requires the identifier of the specification being superseded: `REPLACES project_task_distribution 1.0.0 HASH "sha256:..."`. This is a breaking syntax change from the grammar published before this finding was addressed; no example in this repository used `REPLACES` prior to this revision, so fixing it required no changes to existing `.triel` files, only to the grammar's own illustrative usage example.

**What this does not yet cover.** Pinning says what content a reference expects; it does not say how that content is fetched, cached, or re-verified at compile time, which remains implementation-defined. It also does not address key rotation for a hash that legitimately needs to change — a specification author updating a pinned import still edits the `HASH` value by hand, the same way a lockfile entry would be updated in other ecosystems; no automated re-pinning workflow is specified here.

---

## 3. Related Work

TRIEL overlaps, in stated purpose, with several existing languages; the comparisons below are drawn at the level of publicly observable syntax and semantics, not implementation internals.

**OPA/Rego.** Rego is a mature declarative policy language evaluating rules against a snapshot of input data — a stateless, single-query evaluation model. TRIEL shares the goal of separating policy from the systems it governs, but adds trace semantics with native LTL/CTL operators and zero-knowledge field constraints, neither of which Rego's evaluation model addresses. This is a difference in scope, not a claim of superiority: Rego's runtime maturity and integration ecosystem for real-time authorization decisions is not something TRIEL, as a specification language without a released runtime, currently offers.

**Wysteria/Wys\*.** Wysteria-family languages express deontic-style obligations over distributed participants and compile toward secure multi-party computation protocols. TRIEL's deontic primitives are similar in spirit, but TRIEL is a specification language without a compilation target into any specific MPC protocol; its zero-knowledge constraints annotate individual fields rather than compiling an entire computation into a provable circuit.

**ZK-SecreC (Cybernetica).** ZK-SecreC is a full programming language for zero-knowledge proofs, with an information-flow type system distinguishing prover-private and shared data. TRIEL is not a programming language in this sense: its zero-knowledge constraints are restricted to predicates over a single field (range, set membership, hash equality against a literal), not general circuit logic. Where a specification needs to relate a ZK-constrained field to other specification state, that relationship is expressed as an ordinary temporal invariant, not as an extension of the zero-knowledge constraint syntax itself (Section 2.3).

**Allium (JUXT).** Allium is a behavioral specification language explicitly designed to be authored and maintained by an LLM on the user's behalf, embedded in a host-language (Clojure) ecosystem. TRIEL specifications are authored directly, independent of any host language, and are defined by a standalone grammar rather than a hosted DSL. The similarity is one of motivation — both aim to give durable, structured form to behavioral intent — rather than of mechanism.

**ZoKrates / Noir.** These are zero-knowledge circuit-writing languages: their job is to compile an entire program into a zkSNARK circuit. TRIEL does not compile programs into circuits; its ZK constraints express a provability predicate on a specification-level field, one order of abstraction above circuit design. A specification requiring genuinely novel circuit logic beyond range/set/hash predicates is better served by ZoKrates, Noir, or ZK-SecreC directly; TRIEL's zero-knowledge constraints are deliberately narrow so that the specification author is not required to reason about circuit design at all.

---

## 4. Scope of Claims

Consistent with the discipline this report holds itself to: TRIEL's grammar and semantics establish what a specification *says* and what traces satisfy it. This report does not claim that a TRIEL specification, once written, is automatically enforced by any particular runtime, nor that translating a natural-language requirement into TRIEL is itself a mechanical or unambiguous process — that translation remains a specification-authoring task requiring human judgment, same as writing any formal specification.

What is mechanically checkable today, and what is not, can be stated precisely rather than left as a general disclaimer. A grammar-conformant parser can check a TRIEL specification's *syntactic well-formedness* — that it conforms to the published EBNF, including type-correctness of its factor declarations. It cannot check *structural non-contradiction* of a specification's deontic terms (Section 1.1): two terms such as `X MUST pay` and `X MUST_NOT pay` are both individually well-formed, and detecting that they conflict requires reasoning about the terms' meaning, not just their shape — this is a satisfiability question that needs a SAT solver or model-checker operating over the semantics of Section 2.5, neither of which exists yet in this project. Whether a given implementation's execution trace satisfies a specification's temporal invariants is *defined* by the semantics of Section 2.5, but no tool — parser, SAT solver, or model-checker — currently verifies either non-contradiction or trace satisfaction; both are stated explicitly as future work, tracked openly in the repository, rather than implied to already exist.

---

*Draft v0.1 — all grammar excerpts verified against `github.com/triel-lang/grammar`, tag v2.4.*
