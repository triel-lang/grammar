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

- `dw/`: Dogwood. `schema.cedarschema` declares the actions `Activate`, `Approve`, `Quote` and `Pay`. `events.dwschema` is the default event schema with a window of up to 5 days and without `pin callerPrincipal`, so that the events of the owner and of the oracle are visible to a request of the agent. The policies are:
  - `temporal.dw`: the quote, the approval and the activation are events in the history;
  - `attr_unguarded.dw`: the amount and the approval are attributes of the request, read without `has`;
  - `attr_guarded.dw`: the same attributes, guarded with `has … &&`;
  - `temporal_24h.dw`: `temporal.dw` without the owner's window, for the default event schema.
- `cedar/`: Cedar alone. The time, the activation time, the limit, and the optional amount, quote time and approval are attributes of the request. The policies are:
  - `invoice.cedar`: unguarded;
  - `invoice_guarded.cedar`: every optional attribute guarded with `has … &&`, as the validator asks;
  - `invoice_failclosed.cedar`: every prohibition written as `if context has … then … else true`, so that it holds unless its condition is known to be false.
- `cedar5/`: one `forbid` over an attribute that may be absent, with three schemas (optional, required, not declared) and three guards (`has … &&`, `!(has …) || …`, `if has … then … else true`).
- `gen/`: `mktraces.py` writes the Dogwood traces and `mkctx.py` writes the Cedar requests; `run.sh` runs both.
- `triel/`: three further traces of the example for the TRIEL evaluator: no quote at all, no entry after 09:30, and a clock tick between the two deadlines. They are not among the 59 scenarios of `examples/core/scenarios`.
- `run.sh`: runs everything and compares the outputs with `expected/`.
- `summarize.py`: cedar lists the determining policies and the validation diagnostics in an order that varies from run to run. `summarize.py` keeps, for every command, the decision or validation result, the sorted policies, errors and diagnostics, and the exit code.
- `expected/`: these summaries for the recorded run.
- `recorded/`: the raw outputs of that run.

Both `expected/` and `recorded/` are the outputs of the tools as they ran, not expectations written beforehand.

## Running

```
TRIEL_EVAL=path/to/triel-eval bash artifact/comparison/run.sh
```

Without `TRIEL_EVAL`, the script builds the evaluator from `evaluator/` with `ghc`. It ends with `All outputs equal the recorded ones.` or lists the files that differ.

## Results

Every trace is activated at 09:00 on Monday 2 November 2026, with a limit of 1000.00. The oracle quotes the invoice at 09:30, and the payment is at 10:00 unless the row says otherwise.

For TRIEL, the table gives the verdict of the evaluator. "Blocked" means that the condition of the limit is undefined before the payment, so the fail-closed monitor of the core blocks it (`undefined_guard_blocks_not_breach`). The evaluator does not print this; it reports verdicts only.

| Trace | TRIEL | Cedar unguarded | Cedar guarded | Cedar fail-closed | Dogwood events | Dogwood unguarded | Dogwood guarded |
|---|---|---|---|---|---|---|---|
| quote 800.00, agent pays | fulfilled | allow | allow | allow | allow | allow | allow |
| quote 1500.00, not approved | breached, notify | deny | deny | deny | deny | deny | deny |
| quote 1500.00, approved | fulfilled | allow | allow | allow | allow | allow | allow |
| quote 1500.00, approval absent | pending; blocked | allow, error | allow | deny | deny | allow, error | allow |
| quote stale (payment at 11:00) | pending; blocked | deny | deny | deny | deny | deny | deny |
| no quote, not approved | pending; blocked | allow, errors | allow | deny | deny | allow, error | allow |
| owner pays on 6 November | fallback fulfilled | allow | allow | allow | allow | allow | allow |
| nobody pays, tick on 7 November | fallback breached | no request | no request | no request | no output | no output | no output |

The validators reject the unguarded policies; `cedar authorize` and `dogwood replay` evaluate them all the same, skip the erroring `forbid`, and report the error. With the guards that the validator asks for, the policies validate, and a `forbid` over an absent attribute is not satisfied, so the payment is allowed without an error.

The minimal test in `cedar5/` shows the two ways to make the prohibition hold when the attribute is absent. One is `if context has … then … else true`, which validates and denies. The other is to declare the attribute required, so that a request without it is rejected. The guard `!(context has …) || …` denies but does not validate.

Neither language expresses the obligation with its fallback or the notification, since both decide only when a request arrives. In Dogwood, the owner's window can be written as a permission in the history (`owner_may_pay_after_3d`); with the default event schema, windows are limited to 24 hours.
