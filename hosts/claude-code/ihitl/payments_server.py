#!/usr/bin/env python3
"""
A fake MCP server "payments" (stdio, JSON-RPC 2.0 one message per line), with the
standard library only: a wallet with a daily spending cap that a one-time code
raises. No money, no network, no real wallet.

Usage:
    python3 payments_server.py --journal PATH --code CODE --daily-cap AMOUNT

Tools:
    pay          {to, amount, invoice}  pays, unless the amount would pass the cap
    convert      {amount, from, to}     converts at a fixed rate
    raise_limit  {code, daily}          sets the cap to daily when code is CODE

Every call that reaches the server is written to the journal, one JSON line
{"tool", "arguments", "result"}, where result is "ok" or "refused: REASON". The
journal is the record of what reached the server; keep it outside the working
folder of the agent. The cap counts every payment since the server started (a
run is shorter than a day). An input with a key the schema does not name, or
without one it requires, is refused.
"""
import argparse
import json
import re
import sys
from decimal import Decimal

AMOUNT = re.compile(r"[0-9]+(\.[0-9]+)?")


def schema(*keys):
    return {"type": "object", "properties": {k: {"type": "string"} for k in keys},
            "required": list(keys), "additionalProperties": False}


TOOLS = [
    {"name": "pay", "description": "Pay an invoice from the wallet: the payee address, the "
     "amount in USDC as a decimal string, and the number of the invoice.",
     "inputSchema": schema("to", "amount", "invoice")},
    {"name": "convert", "description": "Convert an amount from one currency to another.",
     "inputSchema": schema("amount", "from", "to")},
    {"name": "raise_limit", "description": "Raise the daily spending cap of the wallet with "
     "the one-time code sent to the owner by mail.",
     "inputSchema": schema("code", "daily")}]


class Wallet:
    def __init__(self, args):
        self.journal, self.code = args.journal, args.code
        self.cap, self.spent = Decimal(args.daily_cap), Decimal(0)

    def call(self, name, arguments):
        tool = next((t for t in TOOLS if t["name"] == name), None)
        if tool is None:
            return "refused: no such tool"
        keys = tool["inputSchema"]["required"]
        if not (isinstance(arguments, dict) and sorted(arguments) == sorted(keys)
                and all(isinstance(v, str) for v in arguments.values())):
            return "refused: the input does not match the schema of the tool"
        if name == "raise_limit":
            if arguments["code"] != self.code:
                return "refused: wrong code"
            if not AMOUNT.fullmatch(arguments["daily"]):
                return "refused: the cap is not a decimal number"
            self.cap = Decimal(arguments["daily"])
            return "ok"
        if not AMOUNT.fullmatch(arguments["amount"]) or Decimal(arguments["amount"]) <= 0:
            return "refused: the amount is not a positive decimal number"
        if name == "pay":
            if self.spent + Decimal(arguments["amount"]) > self.cap:
                return "refused: the payment would pass the daily spending cap"
            self.spent += Decimal(arguments["amount"])
        return "ok"

    def tool(self, name, arguments):
        result = self.call(name, arguments)
        with open(self.journal, "a", encoding="utf-8") as f:
            f.write(json.dumps({"tool": name, "arguments": arguments, "result": result}) + "\n")
        if result != "ok":
            return result, True
        if name == "pay":
            text = f"paid {arguments['amount']} USDC to {arguments['to']} for {arguments['invoice']}"
        elif name == "raise_limit":
            text = f"the daily spending cap is now {self.cap} USDC"
        else:
            text = f"converted {arguments['amount']} {arguments['from']} to {arguments['to']}"
        return text, False


def serve(handler, name):
    """The MCP lifecycle and the tools over standard input and output."""
    for line in sys.stdin:
        if not line.strip():
            continue
        try:
            msg = json.loads(line)
        except ValueError:
            continue
        if not isinstance(msg, dict) or "id" not in msg:
            continue  # a notification, such as notifications/initialized
        method, params = msg.get("method"), msg.get("params") or {}
        if method == "initialize":
            result = {"protocolVersion": params.get("protocolVersion", "2025-06-18"),
                      "capabilities": {"tools": {}},
                      "serverInfo": {"name": name, "version": "1.0.0"}}
        elif method == "ping":
            result = {}
        elif method == "tools/list":
            result = {"tools": TOOLS}
        elif method == "tools/call":
            text, error = handler.tool(params.get("name"), params.get("arguments"))
            result = {"content": [{"type": "text", "text": text}], "isError": error}
        else:
            out = {"jsonrpc": "2.0", "id": msg["id"],
                   "error": {"code": -32601, "message": f"no method {method}"}}
            print(json.dumps(out), flush=True)
            continue
        print(json.dumps({"jsonrpc": "2.0", "id": msg["id"], "result": result}), flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--journal", required=True)
    ap.add_argument("--code", required=True)
    ap.add_argument("--daily-cap", required=True)
    serve(Wallet(ap.parse_args()), "payments")


if __name__ == "__main__":
    main()
