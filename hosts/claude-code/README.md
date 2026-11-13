# The TRIEL gate for Claude Code

`gate.py` holds a call of an MCP tool in Claude Code unless `triel check --last` allows the action that the call maps to. It runs as hooks that the operator of the host deploys in managed settings; the agent does not run it, and the configuration of the host keeps the agent from changing it (section "What the agent must not be able to change"). The gate decides only on MCP tools; every other path to an action of the specification is closed by the configuration of the host. It needs Claude Code 2.1.295 or later, for `onFailure`; the input of the hook has `mcp_server` from 2.1.274 ([hooks](https://code.claude.com/docs/en/hooks#pretooluse-input)).

The contract that any host follows is in [`evaluator/README.md`](../../evaluator/README.md#calling-from-a-host), section "Calling from a host"; this folder follows it for Claude Code. The library `parser/triel_host.py` and this adapter are not covered by the proof of `formal/core`; they are checked by tests (`parser/test_host.py`, `test_gate.py`) and by the runs in Claude Code below.

## Files

- `gate.py`: the hooks `pre` (PreToolUse), `post` (PostToolUse), `failure` (PostToolUseFailure) and `denied` (PermissionDenied), and the commands of the operator `activate`, `resolve` and `status`.
- `settings.json`: an example of the managed settings (`/etc/claude-code/managed-settings.json` on Linux).
- `config.example.json`: an example of the configuration of the gate.
- `host_example.py`: an example of a host module.
- `mandate.triel`: the specification of the example.
- `test_gate.py`: the tests, run by CI: `python3 -m pytest -q hosts/claude-code/test_gate.py`.

## How a call is decided

Claude Code runs the hook `pre` for every MCP tool (matcher `mcp__.*`) with the JSON input of PreToolUse on standard input. The gate:

1. reads its configuration, named by `--config`, and refuses one that breaks the rules of section "Tools and servers";
2. finds the server of the call by `mcp_server`, its `name` and its `source`, never by the prefix `mcp__<server>__` of the name of the tool, and the subject and the action that the configuration maps the tool to;
3. takes the lock of the state of the mandate, reads the host clock and holds the call while the outcome of an earlier call is unknown or in conflict, and while another allowed call has not ended ("waits for the outcome of the previous action");
4. asks the host module for the data and builds the trace with `parser/triel_host.py`; reads with `python3 parser/triel_to_core.py --actions SPEC` which monitors decide the action and which composite terms hold a prohibition of it;
5. runs `python3 parser/triel.py check SPEC TRACE --last --json` as a child process, `sys.executable -I` with an environment that the gate sets, not the one it inherits, and with a timeout (`check_timeout_seconds`) shorter than the `timeout` of the hook; it reads the exit code of the process itself, through no pipe.

The call goes on, with exit code 0 and nothing on standard output, only when all of these hold:

- (a) `triel check` exits 0;
- (b) its `LAST` line is for the last entry of the trace;
- (c) the decisions of that line are not empty, and all are `ALLOW`;
- (d) the `TERM` numbers of that line are exactly the `monitors` that `--actions` gives for the subject and the action. A monitor of a prohibition that names the action with arguments, `pay(supplier)`, does not decide on the action the gate writes, `pay`: the call is held with "monitor TERM I did not decide on the action: arguments not matched";
- (e) no prohibition inside a composite term names the action (`composite_prohibitions` of `--actions` is empty): no monitor decides those, so exit 0 says nothing about them.

Anything else exits 2, with the reason on standard error, whose first line is `TRIEL gate: held: REASON`: an exit code of `triel check` other than 0, a timeout, a report that cannot be read, an exception of the gate, an import that fails. All imports of `gate.py` but `sys` are made inside the handler of `main`, so a failed import also exits 2. Of the exit codes of a command hook only 2 blocks the call; any other code, a hook that cannot start and a timeout let the call go on unless the hook sets `"onFailure": "block"` ([hooks](https://code.claude.com/docs/en/hooks#block-the-action-when-a-hook-fails)). `settings.json` sets it and a `timeout` on every hook, so a gate that is missing, exits with another code before it decides, or hangs, holds the call too. The two are independent: the runs below show exit 2 of the gate holding the call without `onFailure`, and `onFailure` holding the call when the hook never runs.

Exit 0 is not a permission. The gate never answers `"allow"`: an `ALLOW` of the monitors is not the consent of the user, and the call goes on to the permission rules of Claude Code as before. The `permissions.allow` of the managed settings, which lets the tools under the gate run without a prompt (section "Permission prompts"), is consent that the operator gives in advance, not the hook.

## The trace

`parser/triel_host.py` builds the trace from the records of the host, never from what the agent says: the agent gives only the tool it is about to call and its input.

- Entry 0 is the activation: the time and the data that `gate.py activate` recorded, the time rounded down to the second.
- Then, in time order, the calls the gate recognised as executed, each with the tick entry of its decision, and an `arrive` entry for every accepted reading of a factor under `MAX_AGE ... ON_STALE BLOCK` not earlier than the activation, at the time its source stamped it, rounded down.
- Last, a tick entry and the action, both at T, the host clock rounded up, with the same data.

Because the trace counts whole seconds and an absent factor allows the action under `DEFAULT(f, d)` and `PRESENT(f) AND ...`, every place where the trace would lose a fresh reading would allow a blocked action. So the gate holds the call when the host gives a value of a factor with `MAX_AGE` without the time of its source, two readings with one time and different values (until a later reading), or a reading later than the host clock (until the clock reaches it), and when a reading that is fresh by the exact times is stale in the trace at T, by the rounding or because it is older than the activation. A reading not later than the last accepted one is not accepted. The value of a factor with `MAX_AGE` is always that of its reading with the greatest time not later than the host clock; under `ON_STALE USE_LAST` whatever its age, with no `arrive` entry, since the translator gives such a factor no age. Every declared factor needs an answer, and a name that is not a factor, or a field that its record type does not declare, at any depth, holds the call: `triel check` accepts unknown names in the data, and a misspelt factor would allow the action.

The price of this rule: a call is held for up to one or two seconds near the boundary of `MAX_AGE`, and after the activation while a reading from before it is still fresh and no newer one has come. Freshness is counted by the clock of the source. If that clock runs ahead, calls are held until the host clock reaches the stamp. If it runs behind, a reading goes stale early, and under `DEFAULT` or `PRESENT` the prohibition lifts although the reading is fresh; the gate cannot see this. Keeping the clocks of the sources in step is the host's job.

The decision is for the moment T. The call runs when the hook has ended, about the time of the check later (about 4 s in the runs below), and later still if a permission prompt waits for the user; the guarantee of freshness and of the time of the action does not hold across such a wait (section "What remains").

## The configuration

`config.example.json`; every path is absolute, and an unknown or missing key is refused.

| Key | Meaning |
|---|---|
| `repo` | the clone of this repository from which `triel check` runs |
| `evaluator` | the evaluator binary, passed to `triel check` with `--evaluator` |
| `spec` | the specification of the mandate |
| `state_dir` | the state of the mandate, its journal `log.jsonl` and the traces |
| `host_module`, `host_options` | the host module and the options it receives |
| `check_timeout_seconds` | the timeout of each child process; shorter than the `timeout` of the hook |
| `pending_timeout_seconds` | how long an allowed call may wait for its Post event before its outcome is unknown |
| `execution_delay_flag_seconds` | a time of execution E later than T by more than this is marked in the journal; it only marks |
| `managed_servers` | the managed MCP servers: `name` and `source` |
| `allowed_tools` | MCP tools of other servers that pass without a check: `server`, `source`, `tool_name` |
| `actions` | each tool of a managed server: `server`, `tool_name`, `subject`, `action`, and `atomic`, true when a failed call of the tool did nothing (below) |

## The host module

The data of the decision come from the host module named in the configuration, by the rules of `parser/triel_host.py`. It has two functions:

- `answers(call, now, factors, options)`: for each declared factor, its value or `None` (no value) for a factor without `MAX_AGE`, and a `Reading` (the value and the unrounded time its source stamped) or `NO_NEW_READING` for a factor with `MAX_AGE`. `call` is `None` at the activation. Derived values, such as the size of a change, are computed here, from the host's own data.
- `executed(fact, options)`: a call was executed. The fact has `tool_use_id`, the time of execution E and the input the call was executed with: the input of PostToolUse; with `resolve --executed`, the input of a PostToolUse that came, else the one recorded at PreToolUse. The gate gives it on every path on which a call is recognised as executed: PostToolUse with the same input, `resolve --executed` and a late PostToolUse.

On each fact, the module updates everything that depends on executed actions: it removes the approval of the call, lowers the remainders and raises the counters; it computes such values from these facts only. This is the duty of every host module: an approval left in place would allow the same call again. If `executed` raises an exception, the gate records a conflict and holds every action. `host_example.py` removes the approval of the call and counts the executed calls of an action, and ignores a fact it has already taken.

## The outcome of a call

An allowed call is pending until its outcome is known: executed, not executed, or unknown. Only executed calls enter the history; a held call never does.

| Event | Outcome |
|---|---|
| PostToolUse with the input recorded at PreToolUse | executed, at E |
| PostToolUse with another input (another hook may have replaced it with `updatedInput`) | unknown, with a line in the journal |
| PostToolUseFailure without `is_interrupt`, for a tool the configuration declares `atomic` | not executed, with a line in the journal |
| PostToolUseFailure with `is_interrupt: true`, or for a tool not declared atomic | unknown |
| PermissionDenied (auto mode only) | not executed, with a line in the journal |
| no Post event within `pending_timeout_seconds` | unknown, never not executed |

E is the time PostToolUse came, minus `duration_ms` (an optional field), rounded up, and never earlier than T; without `duration_ms` it is the time PostToolUse came. The journal has T and E. A failed call of an atomic tool is not executed because the host says so: declaring a tool atomic states that its error result means that nothing was done, and the host answers for that. The text `error` of PostToolUseFailure is not read: its format is not stable ([hooks](https://code.claude.com/docs/en/hooks#posttoolusefailure-input)). Recording a failed call as executed would make an obligation `FULFILLED` by an action that never happened.

A timeout is a failure too. In the runs below, an MCP call that ran past `MCP_TOOL_TIMEOUT` came as PostToolUseFailure with `is_interrupt: false` and the error `MCP server "payments" tool "slow" timed out after 3s`, after the server had received the call and while it was still working on it. So declare a tool atomic only if its server does nothing for a call that Claude Code stopped waiting for, or if no call of the tool can run as long as its timeout.

While the outcome of any call is unknown, every action the specification decides is held, until the operator runs `resolve`. A late PostToolUse of an unknown call puts it into the history at its time of execution; with another input than PreToolUse, and for a call recorded as not executed, it is a conflict: the call enters the history, the host module gets the fact, and every action is held until `resolve`.

**Background MCP calls.** In an interactive session an MCP call that runs longer than two minutes moves to a background task ([mcp](https://code.claude.com/docs/en/mcp#automatic-backgrounding-of-long-tool-calls)); the documentation does not say which hook events come then, and PostToolUse could record as executed a call that is still running. In the runs below it does: with the background mode on in `claude -p` (`CLAUDE_AUTO_BACKGROUND_TASKS=1`, `CLAUDE_CODE_MCP_AUTO_BACKGROUND_MS=2000`), PostToolUse came when the call moved to the background, with `duration_ms` 2005 and a result that says the call is still running, six seconds before the server finished the call, and no other event came for it. `settings.json` turns the mode off with `"env": {"CLAUDE_CODE_MCP_AUTO_BACKGROUND_MS": "0"}`; with it, PostToolUse came after the server finished.

**Permission prompts.** PreToolUse runs before the permission rules and before the prompt. A call that the gate allows and Claude Code then does not execute, refused in a prompt, by a `deny` rule or by another hook, gets no PostToolUse and no PostToolUseFailure ([hooks](https://code.claude.com/docs/en/hooks#posttoolusefailure)); PermissionDenied comes only in auto mode ([hooks](https://code.claude.com/docs/en/hooks#permissiondenied)). In the runs below, for a call that the gate allowed and a missing permission, a `deny` rule or a second hook stopped, the only later event was PostToolBatch, whose `tool_calls` hold the call with the text the model received as `tool_response`, such as `Permission to use mcp__payments__pay with to:mallory has been denied.`; no documented field says that the call did not run, and the gate does not read the text. Such a call stays pending, becomes unknown after `pending_timeout_seconds`, and holds every action until `resolve`. So a refused permission prompt can leave a call unknown until `resolve`, and the managed settings give the tools under the gate permission in `permissions.allow`, so that no prompt is shown.

## Commands of the operator

The operator of the host runs them; the agent has no access to them (section "What the agent must not be able to change"). They take `--config` like the hooks.

- `gate.py activate` records the activation: the host clock and the answers of the host module. It is recorded once per mandate: the state (history, pending, unknown and conflicts) belongs to the mandate, not to a session of Claude Code, and survives sessions; a second activation while a state exists is refused and keeps the history.
- `gate.py resolve ID --executed --at TIME`: the call ID was executed at TIME, not earlier than T and not later than the host clock. `gate.py resolve ID --not-executed`: it was not executed. A conflict is ended with `--executed --at TIME`.
- `gate.py status` prints the activation, the pending, unknown and conflicting calls.

Decisions and updates of the state are made one at a time under a lock (`flock`). The state and the lock are on one machine: `flock` does not work between machines.

## Tools and servers

- The configuration lists the managed servers by `name` and `source`, the `source` of `mcp_server` in the input of the hook. By the documentation `source` names where the definition of the server came from (`plugin`, `sdk`, or a scope of configuration such as `user` or `project`), not the server itself ([hooks](https://code.claude.com/docs/en/hooks#pretooluse-input), [McpServerProvenance](https://code.claude.com/docs/en/agent-sdk/typescript#mcpserverprovenance)). The gate accepts for a managed server only a scope that the agent cannot write: `managed` or `enterprise`. Which of them `managed-mcp.json` gives, the documentation does not say: the operator checks it in the journal of the first call.
- Each tool of a managed server must be mapped to an action, or it does not work: a tool of a managed server without a mapping is held ("tool not mapped to an action"), and so is a call with the name of a managed server but another `source`.
- An MCP tool of any other server is held unless the configuration allows the tool itself, by the name of its server, its `source` and the name of the tool; a server with another name that leads to the same backend does not pass silently. A tool of an allowed server that is not in the list is held ("tool not allowed"), since a server can add tools during a session ([mcp](https://code.claude.com/docs/en/mcp#dynamic-tool-updates)). An allowed server has the same rule for `source` as a managed one and may not have the name of a managed server; the mapping holds only tools of managed servers. A configuration that breaks this is refused when it is read, and everything is held ("configuration: ...").
- An allowed tool is the only exit 0 without the conditions above, with a line in the journal. Allow a tool only if it cannot take an action that the specification decides, also by reaching the backend (a general HTTP client, a browser), and does not write the paths of section "What the agent must not be able to change". The sandbox does not cover MCP servers ([sandboxing](https://code.claude.com/docs/en/sandboxing#what-runs-outside-the-sandbox)).
- The matcher of every hook in `settings.json` is `mcp__.*`, every MCP tool, not the names of the mapping or of one server: the gate decides by `mcp_server`.

## What the agent must not be able to change

Checked against the documentation of Claude Code; do not create managed settings or `managed-mcp.json` where the gate is tried out, since they apply to every session of the machine.

- **The hooks** are in managed settings. Hooks of all levels add up, and `disableAllHooks` outside managed settings does not turn managed hooks off; `allowManagedHooksOnly: true` blocks the hooks of the user, of the project, of local settings and of plugins, except plugins enabled in the managed `enabledPlugins`, while every managed hook runs ([hooks](https://code.claude.com/docs/en/hooks#disable-or-remove-hooks), [settings](https://code.claude.com/docs/en/settings-reference#allowmanagedhooksonly)). The gate compares the input of every call at PostToolUse in any case.
- **The files of the gate.** The hook runs as the same user of the operating system as the agent's Bash. So neither the tools of the agent (Bash, Write, Edit, NotebookEdit, the tools of allowed MCP servers) nor their subprocesses may write the state directory, the configuration, the host module and its data, the specification, the clone from which `triel check` runs, or the evaluator.
  - The sandbox does not cover Write, Edit and NotebookEdit: they need `deny` rules in managed settings; an `Edit(...)` rule covers every built-in tool that edits files, and `//path` is an absolute path ([permissions](https://code.claude.com/docs/en/permissions#what-read-and-edit-rules-cover)).
  - The sandbox protects from Bash only with `sandbox.enabled: true`, `sandbox.failIfUnavailable: true` and `sandbox.allowUnsandboxedCommands: false` in managed settings, and only for paths outside the working directory, the per-user temporary directory and the added directories, which sandboxed commands may write ([sandboxing](https://code.claude.com/docs/en/sandboxing#enforce-sandboxing-with-managed-settings)). Otherwise deny Bash.
- **MCP servers.** The agent can add a server with another name: under `claude -p` the servers of a project's `.mcp.json` are connected without asking ([headless](https://code.claude.com/docs/en/headless)), and `claude mcp add` writes `~/.claude.json`. The gate holds such a server, but only the configuration of the host closes the way around it to the backend: `managed-mcp.json`, with which no other server loads ([managed-mcp](https://code.claude.com/docs/en/managed-mcp#exclusive-control-with-managed-mcp-json)).
- **Built-in tools.** The matcher covers MCP tools only, so the gate does not check Bash, WebFetch or the other built-in tools. An action that the specification decides must be available to the agent only through the tools of managed servers.
  - Credentials are no barrier. Claude Code starts a local MCP server as the same user as the agent's Bash; any user can read `managed-mcp.json`; `${VAR}`, OAuth and `headersHelper` give the credentials to the user ([managed-mcp](https://code.claude.com/docs/en/managed-mcp#authenticate-with-per-user-credentials)).
  - The barrier is the network. Neither Bash nor WebFetch may reach the backend, nor, for a remote managed server, its address: with the user's credentials its tools can be called by an HTTP request past the hooks. Managed settings need a `deny` rule `WebFetch(domain:...)` for these hosts: it closes WebFetch and, by the permissions page, enters the list of denied domains of the sandbox ([permissions](https://code.claude.com/docs/en/permissions#allow-or-deny-every-fetch)). `sandbox.network.allowManagedDomainsOnly: true` closes only the sandbox: WebFetch runs outside it, and the domains of the sandbox do not apply to it ([sandboxing](https://code.claude.com/docs/en/sandboxing#network-isolation)). Without the rule, a host outside the list is reached without a prompt in `bypassPermissions` mode, and after the user agrees in a mode with prompts. Commands in `sandbox.excludedCommands` bypass the proxy of the sandbox; if they cannot be left out, deny Bash.
  - Commands that Claude Code runs from settings (hooks, the status line) run outside the sandbox ([sandboxing](https://code.claude.com/docs/en/sandboxing#what-runs-outside-the-sandbox)). Hence `allowManagedHooksOnly: true` and a managed `deny` of Edit on the settings of Claude Code (`Edit(//**/.claude/**)`). Other keys of the settings run commands too, such as `statusLine`, `fileSuggestion`, `apiKeyHelper`, `awsAuthRefresh`, `awsCredentialExport`, `gcpAuthRefresh` and `otelHeadersHelper` ([settings](https://code.claude.com/docs/en/settings-reference)).
- **The command of the hook** is an absolute path to `python3` with `-I`, the absolute path of `gate.py` and `--config` with an absolute path (exec form, `args`, so no shell reads it); the evaluator is passed with `--evaluator` and an absolute path. The child `triel check` runs as `sys.executable -I` with an environment the gate sets. The clock and the paths are not read from the environment: `test_gate.py` runs the gate with `TRIEL_EVALUATOR`, `PYTHONPATH` and the variables of the earlier prototype set and a `python3` first on `PATH` that prints an `ALLOW`, and gets the same result as without them.

`settings.json` puts these together for the example: the hooks, `allowManagedHooksOnly` and `allowManagedPermissionRulesOnly`, the `env` of background calls, `permissions.allow` for the tools of the configuration, `deny` rules for the paths of the gate, the settings of Claude Code and the hosts of the backend, and the sandbox.

## What remains

- The arguments of actions are not matched: an action whose monitor has arguments is always held (condition (d)).
- A prohibition inside a composite term holds the whole action (condition (e)).
- An action that no top-level prohibition names, for example one named only in an obligation, is always held: `triel check` exits 5.
- The guarantee of freshness and of the time of the action is for the moment T and does not hold if the tool waits for a permission prompt between the hook and its execution. So there must be no prompt: the tools under the gate get permission in managed settings (`permissions.allow`); with it `allowManagedPermissionRulesOnly: true`, because an `ask` rule from another scope prompts in spite of an allow rule (the order is deny, ask, allow), and `allowManagedHooksOnly: true`, because an `ask` of another hook prompts too ([permissions](https://code.claude.com/docs/en/permissions#manage-permissions), [hooks](https://code.claude.com/docs/en/hooks#pretooluse-decision-control)). Managed settings do not remove one prompt: a tool that its server marks with `_meta["anthropic/requiresUserInteraction"]` prompts whatever the permissions ([mcp](https://code.claude.com/docs/en/mcp#require-approval-for-a-specific-tool)), and for it the guarantee does not hold.
- An allowed tool passes with exit 0 without a check: what it does, the gate does not know; allowing it is the operator's decision.
- The ways around the gate, a server with another name that reaches the same backend, a direct request to a remote managed server, the built-in tools such as Bash, commands from the settings of Claude Code, are closed only by the configuration of the host.
- One machine.

## Runs in Claude Code

Claude Code 2.1.323, `claude -p` with the model haiku, run outside the repository: the hooks given with `--settings`, a stdio MCP server `payments` given with `--mcp-config --strict-mcp-config` that writes down every call that reaches it, the tools under the gate allowed with `--allowedTools`, and a hook that writes down every hook event. A server given with `--mcp-config` has the source `dynamic`; since `managed-mcp.json` was not created there, a wrapper of the runs added `dynamic` to the sources the gate accepts, and changed nothing else. "Reached" means that the call reached the server.

| Run | Without `onFailure` | With `"onFailure": "block"` |
|---|---|---|
| the command of the hook is not found (exit 127) | reached | held |
| the hook exits 1 before it decides | reached | held |
| the hook passes its `timeout` (3 s) | reached | held |
| the gate fails with an exception (exit 2) | held | held |
| `triel check` exits 3 (exit 2 of the gate) | held | held |
| `triel check` allows the call | reached; PostToolUse; executed | the same |
| no permission for the tool (`claude -p` shows no prompt) | not reached; events PreToolUse, PermissionRequest, PostToolBatch; the gate keeps the call pending | the same |
| a `deny` rule (`--disallowedTools 'mcp__payments__pay(to:mallory)'`) | not reached; PreToolUse, PostToolBatch; pending | the same |
| a second PreToolUse hook exits 2 | not reached; PreToolUse, PostToolBatch; pending | the same |
| `MCP_TOOL_TIMEOUT` 3000 ms, a call of 10 s | reached; PostToolUseFailure with `is_interrupt: false` after 3 s; unknown (the tool is not atomic) | the same |
| background mode on, threshold 2 s, a call of 8 s | reached; PostToolUse 2 s after the call began, with `duration_ms` 2005, 6 s before the server finished; recorded as executed | the same |
| background mode on, `CLAUDE_CODE_MCP_AUTO_BACKGROUND_MS=0`, a call of 8 s | reached; PostToolUse after the server finished, `duration_ms` 8014; executed | the same |

In every run where the gate held the call, the model reported the reason from the first line of standard error and did not retry. PermissionDenied was not run: it comes only in auto mode ([hooks](https://code.claude.com/docs/en/hooks#permissiondenied)); `test_gate.py` covers what the gate does with it.
