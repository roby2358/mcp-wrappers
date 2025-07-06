# CMD Shell MCP Server Requirements

The application MUST be an MCP (Model Context Protocol) server that provides controlled CMD shell execution through the MCP interface.

## MCP Interface Requirements

- The application MUST implement the MCP protocol and expose CMD commands as MCP tools
- The application MUST communicate exclusively via stdio (stdin/stdout) - no network interfaces, HTTP servers, or other communication methods are allowed
- The application MUST provide an intro prompt that describes the available CMD wrapper tools
- The application MUST provide a function to see all available commands (which is redundant with tools/list, but helpful)
- The application MUST run in stdio mode for integration with MCP clients like Claude Desktop

## Core Requirements

### Command Allowlist
- The application MUST only run commands from an allowlist of approved tools (dir, echo, curl, type, find, findstr, cd, where, set, podman)
- Each tool in the allowlist MUST appear as a separate entry in the MCP /tools/list endpoint

### Command Execution
- The shell process MUST be started once and reused across requests
- The MCP client MAY pass an optional string parameter with command-line arguments for the tool
- The program MUST handle stdin, stdout, and stderr, and return output as strings

### Security
- The application MUST reject or sanitize any attempts to inject disallowed commands or shell operators (&&, ||, ;, |, >, >>, <, <<, &, ^, %, $, !, call, start)

### Process Management
- The application MUST provide a "restart" tool that terminates the current shell process and creates a new process, allowing for a clean shell environment when needed
- The application MUST handle process death and automatically restart the CMD process when needed

### Output Handling
- The application MUST clean command output by removing command prompt patterns and command echoes
- The application MUST combine stdout and stderr output when stderr has content

### Logging and Error Handling
- The application SHOULD include basic logging for executed commands and errors
- The application MUST handle timeouts (default 30 seconds) for command execution
- The application MUST provide standardized success and failure responses

### MCP Integration
- The application MUST implement the MCP protocol specification for tool exposure and communication
- The application MUST expose each allowed CMD command as a separate MCP tool

# Technical Specification

## Core Architecture Requirement

**SINGLE PERSISTENT SHELL**: The application MUST maintain exactly ONE persistent CMD shell process throughout its entire lifecycle. This is the fundamental architectural constraint:

- The CMD shell MUST be started ONCE when the application starts
- The same shell process MUST be reused for ALL command executions
- The shell MUST maintain its state (current directory, environment variables, etc.) between commands
- The shell MUST only be restarted when explicitly requested via the restart tool
- The shell MUST automatically restart if it dies unexpectedly

This persistent shell approach is the entire purpose of the application - it provides a controlled, stateful command environment through the MCP interface.

## Technical Constraints
- The application MUST use the official MCP Python implementation "mcp" located at https://github.com/modelcontextprotocol/python-sdk
- The application MUST be a Python program that wraps an interactive CMD shell, allowing controlled execution of shell commands via stdin/stdout.
- The application MUST use mcp.server.fastmcp.FastMCP for MCP server implementation
- The application MUST use subprocess.Popen
- The application MUST use Windows-specific flags (CREATE_NO_WINDOW) to prevent command windows from appearing
- The application MUST use "cmd.exe" as the shell process
- The application MUST handle Windows-specific command line formatting with \r\n line endings
- The allowlist MUST be the single source of truth - adding a command to this list MUST automatically make it available as a tool without requiring additional code changes
- The command's output MUST be clearly separated and safely captured using a unique randomized marker to know when it's finished
- The marker string MUST be "Marker_{uuid4}
