# The running example in Cedar and Dogwood

This folder expresses the running example `examples/core/core_invoice_agent.triel` in Cedar and in Dogwood, runs it with the reference command-line tools, and records every output.

In the example, an AI agent pays an invoice for its owner:

- the agent must pay within 3 days, or else the owner must pay within 2 more days;
- the agent must not pay when the amount in euros, quoted by an oracle, is over the owner's limit and the owner has not approved the payment;
- the quote counts as absent once it is older than one hour;
- a breach of the agent notifies the owner.

## Tools

| Tool | Version | Installation |
|---|---|---|
| cedar-policy-cli | 4.14.0 | `cargo install cedar-policy-cli --version 4.14.0 --locked` |
| dogwood-cli | 1.1.0, which embeds cedar-policy 4.11.0 | `cargo install dogwood-cli --version 1.1.0 --locked` |

The policies follow the documentation of Cedar (cedar-docs, commit `5d8a02f`, 23 October 2026) and of Dogwood (repository dogwood-policy/dogwood, commit `4ec5e2c`, 14 October 2026). The tools need network access to install, so this comparison is not a step of `artifact/run.sh` and is not part of the offline image.

## Contents

### `dw/`: Dogwood

`schema.cedarschema` declares the actions `Activate`, `Approve`, `Quote` and `Pay`.

`events.dwschema` differs from Dogwood's default event schema (`pinned.dwschema`) in four ways:
- it allows windows of up to 5 days instead of 24 hours;
- it has no `pin callerPrincipal`, so that the events of the owner and of the oracle are visible to a request of the agent;
- it has no `sessionId` field;
- it has no `error` event kind.

The policies:
- `temporal.dw`: the quote, the approval and the activation are events in the history. The owner's window is the permission `owner_may_pay_after_3d`, and staleness is the prohibition `block_without_fresh_quote`.
- `attr_unguarded.dw`: the amount and the approval are attributes of the request, read without `has`.
- `attr_guarded.dw`: the same attributes, guarded with `has … &&`.

  Both attribute variants have no staleness rule, so a stale quote is denied by the limit rule alone. Their `owner_may_pay` is unconditional, so the owner is always allowed.
- `temporal_24h.dw`: `temporal.dw` for the default event schema. It has no owner's window, and the approval window is shortened from 5 days to 24 hours.

### `cedar/`: Cedar alone

The time, the activation time, the limit, and the optional amount, quote time and approval are attributes of the request. The policies:
- `invoice.cedar`: unguarded.
- `invoice_guarded.cedar`: every optional attribute guarded with `has … &&`, as the validator asks.
- `invoice_failclosed.cedar`: the prohibition holds unless its condition `amount_eur > limit_eur AND NOT owner_approved` is known to be false in strong Kleene logic. That is, it holds unless the amount is known and not over the limit, or the approval is known and true. The amount counts as known only while its quote is at most one hour old. This follows `MAX_AGE 1 HOURS ON_STALE BLOCK` with one difference: Cedar measures the age at the time of the request (`now`), whereas TRIEL judges the prohibition in the state of the entry before the action, so it measures the age at that entry. The two agree on every recorded trace; the stale-quote trace has a tick at 10:45 before the payment at 11:00. This is how the fail-closed monitor of the TRIEL core reads the prohibition. The policy validates.

### Other files

- `cedar5/`: one `forbid` over an attribute that may be absent, with three schemas (optional, required, not declared) and three guards (`has … &&`, `!(has …) || …`, `if has … then … else true`).
- `gen/`: `mktraces.py` writes the Dogwood traces and `mkctx.py` writes the Cedar requests; `run.sh` runs both.
- `triel/`: four further traces of the example for the TRIEL evaluator: no quote at all; no quote with the payment approved; no entry after 09:30; and a clock tick between the two deadlines. They are not among the 60 scenarios of `examples/core/scenarios`.
- `run.sh`: runs everything and compares the outputs with `expected/`.
- `summarize.py`: both tools list policies and diagnostics in an order that varies from run to run. For every command, `summarize.py` keeps:
  - for cedar: the decision or validation result, the sorted policies, errors and reasons (also those of a request that cannot be parsed), and the exit code;
  - for dogwood: the output, with each run of `error:` lines sorted.

  Identical diagnostics that repeat are kept once.
- `expected/`: these summaries for the recorded run.
- `recorded/`: the raw outputs of that run.

Both `expected/` and `recorded/` are the outputs of the tools as they ran, not expectations written beforehand.

## Running

```
TRIEL_EVAL=path/to/triel-eval bash artifact/comparison/run.sh [OUTPUT_DIR]
```

Without `TRIEL_EVAL`, the script builds the evaluator from `evaluator/` with `ghc`. The output directory defaults to `artifact/comparison/results/`; an existing directory is replaced only if an earlier run of the script wrote it. The script ends with `All outputs equal the recorded ones.` or lists the files that differ.

## Results

Every trace is activated at 09:00 on Monday 2 November 2026, with a limit of 1000.00. The oracle quotes the invoice at 09:30, and the payment is at 10:00, unless the row says otherwise.

The TRIEL columns are quoted from the report of the evaluator: the verdicts of the obligation to pay (`TERM 1`) and of the prohibition (`TERM 2`), and the `MONITOR 2` line, the decision of the fail-closed monitor of the prohibition at the payment (`examples/core/README.md`, Output; `enforce` and `monitor_decisions` of `formal/core/TRIEL_Breach.thy`). `ENTRY J BLOCK` means that the condition of the prohibition is not known to be false in the state before the payment at entry J, true or undefined, so the monitor blocks the payment; `ALLOW` that it is false; `NO ACTION` that the agent does not pay. A payment is `BLOCK` with the verdict `PENDING` exactly when the condition is undefined before it (`undefined_guard_blocks_not_breach`, `enforce_undefined_blocks`). The scenarios are `examples/core/scenarios/invoice_*.scn` and `triel/x_*.scn`. "—" marks a request that was not run: there is no Dogwood trace for a payment approved while the quote is missing.

| Trace | TRIEL: obligation; prohibition | TRIEL: `MONITOR 2 :` | Cedar unguarded | Cedar guarded | Cedar fail-closed | Dogwood events | Dogwood unguarded | Dogwood guarded |
|---|---|---|---|---|---|---|---|---|
| quote 800.00, agent pays | `FULFILLED`; `PENDING` | `ENTRY 2 ALLOW` | allow | allow | allow | allow | allow | allow |
| quote 1500.00, not approved | `FULFILLED`; `BREACHED 1793613600 NOTIFY owner` | `ENTRY 2 BLOCK` | deny | deny | deny | deny | deny | deny |
| quote 1500.00, approved | `FULFILLED`; `PENDING` | `ENTRY 2 ALLOW` | allow | allow | allow | allow | allow | allow |
| quote 1500.00, approval absent | `FULFILLED`; `PENDING` | `ENTRY 2 BLOCK` | allow, error | allow | deny | deny | allow, error | allow |
| quote stale (payment at 11:00) | `FULFILLED`; `PENDING` | `ENTRY 3 BLOCK` | deny | deny | deny | deny | deny | deny |
| no quote, not approved | `FULFILLED`; `PENDING` | `ENTRY 1 BLOCK` | allow, errors | allow | deny | deny | allow, error | allow |
| no quote, approved | `FULFILLED`; `PENDING` | `ENTRY 1 ALLOW` | allow, errors | allow | allow | — | — | — |
| owner pays on 6 November | `ELSE FULFILLED`; `PENDING` | `NO ACTION` | allow | allow | allow | allow | allow | allow |
| nobody pays, tick on 7 November | `ELSE BREACHED 1794042000`; `PENDING` | `NO ACTION` | no request | no request | no request | no output | no output | no output |

The payment is entry 2 in the traces with a quote (activation, quote, payment), entry 3 in the stale-quote trace (a tick at 10:45 between the quote and the payment) and entry 1 in the traces without a quote.

**Unguarded and guarded policies.** Both validators reject the unguarded policies. `cedar authorize` and `dogwood replay` evaluate them all the same: they skip the erroring `forbid` and report the error. With the guards that the validator asks for, the policies validate, and a `forbid` over an absent attribute is not satisfied, so the payment is allowed without an error.

**Fail-closed Cedar.** `invoice_failclosed.cedar` gives the decisions of the TRIEL monitor on every request: it denies exactly where the `MONITOR 2` line says `BLOCK`, and allows a payment approved while the quote is missing, whose condition is false (`ALLOW`).

**The minimal test in `cedar5/`.** Two more ways make a prohibition hold when the attribute is absent:
- `if context has … then … else true`, which validates and denies;
- declaring the attribute required, so that a request without it fails to parse.

The guard `!(context has …) || …` denies but does not validate.

**Events in Dogwood.** When the approval is an event, the policy reads a missing `Approve` event as no approval. Its denial therefore comes from writing the prohibition over events, not from a third truth value.

Neither language expresses the obligation with its fallback or the notification, since both decide only when a request arrives. In Dogwood, the owner's window can be written as a permission over the history.
