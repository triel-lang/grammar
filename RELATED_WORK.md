# Related Work

This file compares TRIEL with the closest languages and formalisations, on the basis of their published papers, documentation and specifications. The traditions TRIEL draws on, and the definitions and results each construct uses, are in [`FOUNDATIONS.md`](FOUNDATIONS.md). `TECHNICAL_REPORT.md` §3 compares TRIEL with OPA/Rego, Wysteria and Wys\*, ZK-SecreC, Allium, and ZoKrates and Noir. Statements about TRIEL here are limited to what the Isabelle/HOL core in [`formal/core`](formal/core/CORE.md) proves; names in code font are its definitions and theorems.

## Authorization policies for software and agents

**Cedar** [1] is a language for authorization policies. A request is allowed when some `permit` policy is satisfied and no `forbid` policy is; a satisfied `forbid` overrides, and the default is deny [2]. Reading an attribute that is absent raises an error, and a policy whose evaluation raises an error is skipped [2]. Cedar's validator rejects access to an optional attribute that is not guarded by a `has` test [2]. With the usual guard, `resource has a && …`, a `forbid` policy is not satisfied when `a` is absent. Either way, a prohibition whose condition reads a missing value does not apply, unless the author writes the guard so that absence counts against the request, for example `if context has a then … else true`, or declares the attribute required, so that a request without it is rejected. For validated policies and requests that conform to the schema, the validator is proved sound in Lean: evaluation does not raise such errors [1, §3.5]. The behaviour above is therefore a choice that Cedar leaves to the author, not a defect.

TRIEL makes the opposite choice the default for prohibitions. Its conditions are evaluated in strong Kleene logic, and a monitor blocks a prohibited action unless the condition is known to be false (`blocks`). The core models the two other readings of an undefined condition: skipping it (`skip_allows`) and reading an absent operand as false (`eval_af`). For each, it proves that there is a condition and a state where the reading allows the action although some completion of the data makes the condition true (`skip_reading_unsound`, `absent_false_unsound`). When the fail-closed monitor allows an action, the condition is false in every completion (`monitor_sound_completions`). These theorems are about the readings as defined in the core, not about the implementation of any language. Cedar decides single requests; TRIEL also has obligations with deadlines, breach handlers and invariants over traces.

**Dogwood** [3] extends the `permit`/`forbid` model of Cedar to the history of an AI agent's actions, so that a policy can depend on what the agent has already done. TRIEL has the same aim for agents, and adds obligations with deadlines, breach handlers and three-valued verdicts on finite prefixes. Dogwood's decision pipeline is fail-closed: a failure to evaluate the temporal conditions, to build the context or to build the request denies [28, §6.2 and §7 of the formal specification]. A Cedar policy whose evaluation raises an error is skipped, as in Cedar; the Dogwood test `erroring_forbid_is_skipped_weakening_the_deny` [28] records this as deliberate.

**The running example in Cedar and Dogwood.** `artifact/comparison/` expresses the example `core_invoice_agent` in both languages, runs it with cedar-policy-cli 4.14.0 and dogwood 1.1.0, and records every output. Neither language expresses the obligation with its fallback or the notification, since both decide only when a request arrives. When the owner's approval is an optional request attribute and is absent:

- with the guard that the validator asks for, `context has … && …`, the policy validates, the `forbid` is not satisfied, and both tools allow the payment without an error;
- without a guard, the validator rejects the policy; if it is run anyway, its evaluation raises an error, the policy is skipped, and the payment is allowed with the error reported;
- written as `if context has … then … else true`, the policy validates and the payment is denied, as the TRIEL monitor would block it;
- declared as a required attribute, a request without it is rejected.

When the approval is an event in Dogwood's history instead, its absence denies the payment.

**XACML 3.0** [4] has four decisions: Permit, Deny, NotApplicable and Indeterminate, the last returned when evaluation fails; combining algorithms decide how an Indeterminate result affects the final decision. In TRIEL, an undefined condition is a value of the logic, the rule for prohibitions is fixed (block unless known to be false), and the verdict is kept apart from enforcement: a breach is recorded only when the condition is true (`undefined_guard_blocks_not_breach`).

## Languages for rights, norms and contracts

**ODRL 2.2** [5] describes policies as permissions, prohibitions and duties with constraints, for the use of digital assets. **LegalRuleML 1.0** [6] is an XML vocabulary for legal norms, with deontic specifications and defeasible rules. TRIEL is a textual language whose terms have a trace semantics and machine-checked properties.

**Symboleo** [7] is a specification language for legal contracts with obligations and powers, given a formal semantics. **CL** [8] is a contract language in a dynamic deontic logic: obligations, permissions and prohibitions apply to actions, and violations carry reparations. Logics of violations [9] describe chains of reparations, and defeasible deontic logic, with reasoners such as SPINdle [10], decides what is obligatory when norms conflict or have exceptions. TRIEL shares with these the view of a contract as norms over actions, with deadlines and reparations; it gives verdicts on traces and has no rules of inference between norms, no defeasibility and no priorities between norms.

**Catala** [11] is a programming language for computations prescribed by legislation, such as taxes and benefits, with exceptions structured as in default logic. TRIEL does not compute such amounts; it states norms and decides whether a trace of events satisfies them. In the formal core, arithmetic occurs only in the amount of a `PENALTY`.

**DCR graphs** [12] describe processes declaratively, by relations between events such as conditions and responses. TRIEL states norms over a trace of events rather than the process that produces it.

## Runtime verification and enforcement

LTL3 [13] gives verdicts on finite prefixes that are final once decided; TRIEL uses it for `ALWAYS`, `EVENTUALLY` and `NEXT` (`inv_final`). MonPoly [14, 15] monitors metric first-order temporal logic, with quantification over data values, and a monitor for that logic has been verified in Isabelle/HOL and exported as code [16]; it is the closest counterpart of the TRIEL evaluator, whose code equations are proved equal to the definitions. TRIEL has fixed subjects and no quantification over objects; in return, its verdicts stay the same when data still missing from a state arrives, for conditions whose atoms are equitone, which excludes `PRESENT` and `DEFAULT` (`inv_data_mono`, `verdict_stable`). Schneider's execution monitors [17] and edit automata [18] are the classical models of enforcement; the TRIEL monitor only blocks a prohibited action, and how a blocked action appears in the trace is not modelled.

## Formalisations in the Archive of Formal Proofs

- `LTL3_Semantics` [19] formalises the full logic LTL3 and formula progression. TRIEL has only `ALWAYS`, `EVENTUALLY`, `NEXT` and `EVENTUALLY … WITHIN` over a state formula, evaluated in strong Kleene logic on incomplete data.
- `MFOTL_Monitor` [20] and `MFODL_Monitor_Optimized` [21] verify executable monitors for metric first-order temporal and dynamic logic.
- `CondNormReasHOL` [22] embeds a dyadic deontic logic in HOL for conditional normative reasoning. TRIEL has no deontic inference; it gives verdicts on traces.
- `DCR-ExecutionEquivalence` [23] formalises the syntax and execution of DCR graphs.
- `Featherweight_OCL` [24] gives OCL a semantics with the values null and invalid besides true and false; `UPF` [25] models access-control policies as partial functions.
- `Extended_Finite_State_Machines` [26] contains a three-valued logic in which an invalid value absorbs both conjunction and disjunction (weak Kleene, or Bochvar, logic).

In a search of the AFP topics and keywords in October 2026 we found no entry that formalises strong Kleene logic over partial states.

## Information release in secure multiparty computation

In deployments of secure multiparty computation (MPC), the logic that decides which data may be released is often hand-coded. Skalka and Near [27] formalise noninterference and declassification for low-level MPC code. TRIEL works at the level of the specification: the information-flow rule for hidden zero-knowledge factors (`TECHNICAL_REPORT.md` §2.7) is checked on the specification by the translator to the formal core, and no report of the evaluator depends on the value of a hidden factor (`run_noninterference`). TRIEL does not define how a specification is implemented.

## References

1. J. W. Cutler, C. Disselkoen, A. Eline, S. He, K. Headley, M. Hicks, K. Hietala, E. Ioannidis, J. Kastner, A. Mamat, D. McAdams, M. McCutchen, N. Rungta, E. Torlak, A. M. Wells. Cedar: a new language for expressive, fast, safe, and analyzable authorization. *Proceedings of the ACM on Programming Languages*, 8(OOPSLA1), 2024, article 118, 670–697. https://doi.org/10.1145/3649835
2. Cedar Policy Language Reference Guide: authorization (https://docs.cedarpolicy.com/auth/authorization.html), operators (https://docs.cedarpolicy.com/policies/syntax-operators.html) and validation (https://docs.cedarpolicy.com/policies/validation.html). Accessed October 2026.
3. M. Brooker, J. Tassarotti, J.-B. Tristan. Introducing Dogwood: runtime verification for AI agents. AWS Open Source Blog, 6 August 2026. https://aws.amazon.com/blogs/opensource/introducing-dogwood-runtime-verification-for-ai-agents/
4. OASIS. *eXtensible Access Control Markup Language (XACML) Version 3.0*. OASIS Standard, 22 January 2013. https://docs.oasis-open.org/xacml/3.0/xacml-3.0-core-spec-os-en.html
5. W3C. *ODRL Information Model 2.2*. W3C Recommendation, 15 February 2018. Editors R. Iannella, S. Villata. https://www.w3.org/TR/2018/REC-odrl-model-20180215/
6. OASIS. *LegalRuleML Core Specification Version 1.0*. OASIS Standard, 30 August 2021. https://docs.oasis-open.org/legalruleml/legalruleml-core-spec/v1.0/os/legalruleml-core-spec-v1.0-os.html
7. A. Parvizimosaed, S. Sharifi, D. Amyot, L. Logrippo, M. Roveri, A. Rasti, A. Roudak, J. Mylopoulos. Specification and analysis of legal contracts with Symboleo. *Software and Systems Modeling*, 21(6), 2022, 2395–2427. https://doi.org/10.1007/s10270-022-01053-6
8. C. Prisacariu, G. Schneider. A dynamic deontic logic for complex contracts. *The Journal of Logic and Algebraic Programming*, 81(4), 2012, 458–490. https://doi.org/10.1016/j.jlap.2012.03.003
9. G. Governatori, A. Rotolo. Logic of violations: a Gentzen system for reasoning with contrary-to-duty obligations. *Australasian Journal of Logic*, 4, 2006, 193–215. https://doi.org/10.26686/ajl.v4i0.1780
10. H.-P. Lam, G. Governatori. The making of SPINdle. *RuleML 2009*, LNCS 5858, Springer, 2009, 315–322. https://doi.org/10.1007/978-3-642-04985-9_29
11. D. Merigoux, N. Chataing, J. Protzenko. Catala: a programming language for the law. *Proceedings of the ACM on Programming Languages*, 5(ICFP), 2021. https://doi.org/10.1145/3473582
12. T. T. Hildebrandt, R. R. Mukkamala. Declarative event-based workflow as distributed dynamic condition response graphs. *PLACES 2010*, EPTCS 69, 2011, 59–73. https://doi.org/10.4204/EPTCS.69.5
13. A. Bauer, M. Leucker, C. Schallhart. Runtime verification for LTL and TLTL. *ACM Transactions on Software Engineering and Methodology*, 20(4), 2011, article 14. https://doi.org/10.1145/2000799.2000800
14. D. Basin, F. Klaedtke, S. Müller, E. Zălinescu. Monitoring metric first-order temporal properties. *Journal of the ACM*, 62(2), 2015, 15:1–15:45. https://doi.org/10.1145/2699444
15. D. Basin, F. Klaedtke, E. Zălinescu. The MonPoly monitoring tool. *RV-CuBES 2017*, Kalpa Publications in Computing, vol. 3, 2017, 19–28. https://doi.org/10.29007/89hs
16. J. Schneider, D. Basin, S. Krstić, D. Traytel. A formally verified monitor for metric first-order temporal logic. *Runtime Verification (RV 2019)*, LNCS 11757, Springer, 2019, 310–328. https://doi.org/10.1007/978-3-030-32079-9_18
17. F. B. Schneider. Enforceable security policies. *ACM Transactions on Information and System Security*, 3(1), 2000, 30–50. https://doi.org/10.1145/353323.353382
18. J. Ligatti, L. Bauer, D. Walker. Edit automata: enforcement mechanisms for run-time security policies. *International Journal of Information Security*, 4, 2005, 2–16. https://doi.org/10.1007/s10207-004-0046-8
19. R. Amjad, R. van Glabbeek, L. O'Connor. Definitive set semantics for LTL3. *Archive of Formal Proofs*, August 2024. https://isa-afp.org/entries/LTL3_Semantics.html
20. J. Schneider, D. Traytel. Formalization of a monitoring algorithm for metric first-order temporal logic. *Archive of Formal Proofs*, July 2019. https://isa-afp.org/entries/MFOTL_Monitor.html
21. T. Dardinier, L. Heimes, M. Raszyk, J. Schneider, D. Traytel. Formalization of an optimized monitoring algorithm for metric first-order dynamic logic with aggregations. *Archive of Formal Proofs*, April 2020. https://isa-afp.org/entries/MFODL_Monitor_Optimized.html
22. X. Parent, C. Benzmüller. Conditional normative reasoning as a fragment of HOL (Isabelle/HOL dataset). *Archive of Formal Proofs*, March 2024. https://isa-afp.org/entries/CondNormReasHOL.html
23. A. Christfort, S. Debois. DCR syntax and execution equivalent markings. *Archive of Formal Proofs*, June 2023. https://isa-afp.org/entries/DCR-ExecutionEquivalence.html
24. A. D. Brucker, F. Tuong, B. Wolff. Featherweight OCL: a proposal for a machine-checked formal semantics for OCL 2.5. *Archive of Formal Proofs*, January 2014. https://isa-afp.org/entries/Featherweight_OCL.html
25. A. D. Brucker, L. Brügger, B. Wolff. The Unified Policy Framework (UPF). *Archive of Formal Proofs*, November 2014. https://isa-afp.org/entries/UPF.html
26. M. Foster, A. D. Brucker, R. G. Taylor, J. Derrick. A formal model of extended finite state machines. *Archive of Formal Proofs*, September 2020. https://isa-afp.org/entries/Extended_Finite_State_Machines.html
27. C. Skalka, J. P. Near. Language-based security for low-level MPC. *PPDP 2024*, ACM, 2024. https://doi.org/10.1145/3678232.3678246
28. Dogwood. GitHub repository dogwood-policy/dogwood, version 1.1.0, commit 4ec5e2c of 14 October 2026: `dogwood-docs/guide/08-formal-specification.md` and `dogwood-language/tests/entity_store.rs`. https://github.com/dogwood-policy/dogwood
