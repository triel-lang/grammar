# The bridge from the TRIEL core to MFOTL, part 1: conditions

This directory relates the conditions of the TRIEL core ([`../core`](../core), session `TRIEL_Core`) to the metric first-order temporal logic MFOTL of the AFP entry `MFOTL_Checker` (release afp-2025-2, Isabelle2025-2). It shows that a three-valued condition of the core is a pair of MFOTL formulas, one for "true" and one for "false", with no premise on the completeness of the data, and that "unknown blocks" is the failure of the formula for "false". The core is not changed.

- [`ROOT`](ROOT): the session `TRIEL_MFOTL` (parent `MFOTL_Checker`), with the theories [`TRIEL_MFOTL_Enc.thy`](TRIEL_MFOTL_Enc.thy) (the encoding of a trace) and [`TRIEL_MFOTL_Cond.thy`](TRIEL_MFOTL_Cond.thy) (conditions).
- [`accept/ROOT`](accept/ROOT): the session `TRIEL_MFOTL_Accept`. [`accept/Accept_MFOTL1.thy`](accept/Accept_MFOTL1.thy) restates the theorems below with every type fixed and proves each by its theorem alone; it fails if a restated theorem uses a constant other than those of the core, of the AFP theory `Formula` and of the bridge, or depends on an oracle.
- [`../../.github/workflows/mfotl.yml`](../../.github/workflows/mfotl.yml) builds both sessions against the AFP sessions they need.

## The encoding

The values of MFOTL are `('n, 'v, 's, 'a) mval`: a name `MN x`, a value `MV u`, a subject `MS s` or an action `MA a` of the core. Predicates and variables of MFOTL are strings.

For an implementation trace π (`itrace` of `TRIEL_Breach`) and a set C of values, the database `enc_db C π j` of entry j holds

- `val(MN x, MV u)` for every name x with the value u in the state `st π j`;
- `lt(MV u, MV w)` and `le(MV u, MV w)` for the values u and w of `ran (st π j) ∪ C` with `vless u w` and `vleq u w`;
- `arr(MN x)` if the event of the entry is the arrival of data for x, and `act(MS s, MA a)` if it is an action a of s and j > 0 (entry 0 is the activation entry, whose event is not an action).

An MFOTL trace σ encodes π (`enc_pre C π σ`) if, for every j < |π|, the database of entry j of σ is `enc_db C π j` and its timestamp is `time π j − time π 0`. The entries of σ after the first |π| are not constrained.

A condition c is translated into two formulas: `Pc c` holds when c is true and `Nc c` when c is false. NOT exchanges them; AND, OR and IMPLIES follow the strong Kleene tables (for example `Pc (e₁ AND e₂)` is `Pc e₁ ∧ Pc e₂` and `Nc (e₁ AND e₂)` is `Nc e₁ ∨ Nc e₂`); PRESENT(x) is "some value of x is in the database". A value expression a becomes the formula `V a y`, "the variable y is the value of a": a constant is `y ≈ MV u`, a name x is `val(MN x, y)`, and DEFAULT(x, a) is `val(MN x, y) ∨ (¬ ∃y. val(MN x, y)) ∧ V a y`. A comparison a < b is `∃x1 x2. V a x1 ∧ V b x2 ∧ lt(x1, x2)` for "true" and the same with `¬ lt(x1, x2)` for "false". MFOTL compares a variable only with a constant, so a = b is "one variable is the value of a and of b" for "true", and "a and b have a value, and no variable is the value of both" for "false". Variables: a comparison binds its operands to x1 and x2 and DEFAULT binds again the variable of its operand; `Pc c` and `Nc c` are closed formulas (`fv_Pc_Nc`), so these fixed names are never captured.

## What is proved

The theorems of the session `TRIEL_MFOTL`, as `Accept_MFOTL1.thy` restates them:

- `enc_db_eq`: the database of entry j is exactly the set of facts `val`, `lt`, `le`, `arr` and `act` above.
- `enc_pre_iff`: σ encodes π exactly when its first |π| databases are those of π and its timestamps are the times of π counted from entry 0.
- `enc_pre_exists`: if every state of π has finitely many names and C is finite, an MFOTL trace that encodes π exists.
- `econsts_finite`: the set `econsts c` of the value constants of a condition is finite.
- `enc_time`: the timestamp of entry j of an encoding, as an integer, is `time π j − time π 0`.
- `enc_db_lt`, `enc_db_le`: on values of the state and of C, the fact `lt(MV u, MV w)` (`le(MV u, MV w)`) is in the database exactly when `vless u w` (`vleq u w`).
- `bridge_true`: if `econsts c ⊆ C`, c is true in the state of entry j exactly when `Pc c` holds at j in every encoding, under every valuation.
- `bridge_false`: under the same premise, c is false in the state of entry j exactly when `Nc c` holds at j.
- `bridge_blocks_cond`: a prohibition with the condition c blocks in the state of entry j (`blocks` of the core: c is not known to be false) exactly when `Nc c` does not hold at j.
- `bridge_complete_cond`: if moreover every name that c reads has a value (`names c ⊆ dom (st π j)`, the premise of T4), c is defined and its value is the truth of `Pc c`.

`bridge_true`, `bridge_false` and `bridge_blocks_cond` have no premise on the completeness of the data; only `bridge_complete_cond` has one. The lemmas they rest on are `sat_V` and `sat_V_upd` (the variable y is the value of a), `evalV_ran` (a value of an operand is a value of the state or a constant of the operand), `enc_db_val` (the facts `val` are the state) and `bridge_cond` (`bridge_true` and `bridge_false` at once, by induction on the condition).

## Order of values

What is encoded: the facts `lt(MV u, MV w)` and `le(MV u, MV w)` of entry j, only for pairs of values u and w of `ran (st π j) ∪ C`, the values of the state and the constants given to the encoding.

What is preserved: on these pairs, exactly `vless` and `vleq` (`enc_db_lt`, `enc_db_le`). This is all the comparisons need: the value of an operand of a comparison is a value of the state or a constant of the condition (`evalV_ran`), and `bridge_true` and `bridge_false` assume `econsts c ⊆ C`.

What is not: the class `value_order` of the core fixes `vless` and `vleq` and assumes nothing about them, so the bridge states no law of order (transitivity, irreflexivity, totality, or the relation between `vless` and `vleq`). For MFOTL, `lt` and `le` are facts of the database like any other: its formulas do not know that they are transitive. Comparisons of values outside C and outside the state of the entry are not encoded, so a formula that compares such a value with `lt` or `le` finds no fact.

## What the bridge does not claim

- **Prefix and infinite trace.** An MFOTL trace is infinite, and `enc_pre` fixes only its first |π| entries. The theorems are about one entry j < |π| and its state. They say nothing about the entries after the prefix, nor about a temporal formula whose truth depends on them, and no verdict of the core (prohibitions, obligations, deadlines) is translated here.
- **Enforcement.** `bridge_blocks_cond` relates the condition under which the core blocks to `Nc c` in one state. It does not translate the monitor of the core (`enforce`), and it does not claim that an MFOTL monitor enforces anything.
- **Completions.** The bridge does not relate `Pc` and `Nc` to the completions of the data (`TRIEL_Completions`): that a condition true or false in a state stays so in every completion is a theorem of the core, not of the bridge.
- **`kleene_optimal`.** The bridge does not claim that `Pc` and `Nc` are the most defined sound reading of a condition; it translates the strong Kleene evaluation of the core as it is.
