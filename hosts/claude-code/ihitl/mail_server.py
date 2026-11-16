#!/usr/bin/env python3
"""
A fake MCP server "mail" (stdio, JSON-RPC 2.0 one message per line), with the
standard library only: the inbox of the owner, read only. No mailbox, no
network.

Usage:
    python3 mail_server.py --mailbox PATH

Tools:
    list_messages  {}    the id, the sender and the subject of each message
    read_message   {id}  one message

The mailbox is a JSON file {"messages": [{"id", "from", "subject", "body"}]},
opened for reading on every call; the server has no tool that writes.
"""
import argparse
import json
import sys

TOOLS = [
    {"name": "list_messages", "description": "List the messages of the inbox.",
     "inputSchema": {"type": "object", "properties": {}, "additionalProperties": False}},
    {"name": "read_message", "description": "Read one message of the inbox by its id.",
     "inputSchema": {"type": "object", "properties": {"id": {"type": "string"}},
                     "required": ["id"], "additionalProperties": False}}]


class Inbox:
    def __init__(self, path):
        self.path = path

    def messages(self):
        with open(self.path, "r", encoding="utf-8") as f:
            return json.load(f)["messages"]

    def tool(self, name, arguments):
        if name == "list_messages" and arguments in ({}, None):
            return "\n".join(f"{m['id']} | from {m['from']} | {m['subject']}"
                             for m in self.messages()), False
        if name == "read_message" and isinstance(arguments, dict) and set(arguments) == {"id"}:
            for m in self.messages():
                if m["id"] == arguments["id"]:
                    return f"From: {m['from']}\nSubject: {m['subject']}\n\n{m['body']}", False
            return f"no message {arguments['id']}", True
        return "the input does not match the schema of the tool", True


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
    ap.add_argument("--mailbox", required=True)
    serve(Inbox(ap.parse_args().mailbox), "mail")


if __name__ == "__main__":
    main()
