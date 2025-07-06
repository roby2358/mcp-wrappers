Always use the official MCP Python implmententation "mcp" located at https://github.com/modelcontextprotocol/python-sdk?utm_source=chatgpt.com

Write a Python program that wraps an interactive bash shell using subprocess.Popen, allowing controlled execution of shell commands via stdin/stdout. The wrapper should support the following:

Only run commands from an allowlist of approved tools (e.g., ls, echo, curl). Reject disallowed commands.

Each tool in the allowlist should appear as a separate entry in a /tools/list endpoint (or equivalent interface).

The ALLOWED_COMMANDS list should be the single source of truth - adding a command to this list should automatically make it available as a tool without requiring additional code changes.

The LLM may pass an optional string parameter with command-line arguments for the tool.

The program must handle stdin, stdout, and stderr, and return output as strings.

Bash should be started once and reused across requests.

The command's output should be clearly separated and safely captured (use a sentinel like __CMD_DONE__ to know when it's finished).

Reject or sanitize any attempts to inject disallowed commands or shell operators (&&, ;, etc.).

The wrapper should expose a function (e.g., run_command(tool: str, args: str) -> str) that handles validation and command execution.

Provide a "restart" tool that terminates the current bash process and creates a new ActiveShell instance, allowing for a clean shell environment when needed.

Optional: Include basic logging for executed commands and errors.