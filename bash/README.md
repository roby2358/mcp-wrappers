# Bash Shell FastMCP App

A FastMCP application that provides a controlled bash shell environment, allowing you to execute a limited set of approved shell commands through the MCP protocol.

## Features

- Secure execution of allowlisted bash commands
- Protection against command injection and shell operators
- Persistent bash process reused across requests
- Built-in intro prompt that instructs the model how to use the Bash shell
- Error handling for common issues
- Command output clearly separated using sentinel markers
- Simple integration with Claude Desktop

### Claude Desktop Configuration

### Config File Location
- **Windows**: `C:\Users\[YourUsername]\AppData\Roaming\Claude\claude_desktop_config.json`
- **macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
- **Linux**: `~/.config/Claude/claude_desktop_config.json`

To use this app with Claude Desktop, add the following to your Claude Desktop configuration:

### Example Configuration
```json
{
  "mcpServers": {
    "bash-shell": {
      "command": "C:/work/mcp-wrappers/bash/venv/Scripts/python.exe",
      "args": ["C:/work/mcp-wrappers/bash/bash.py"]
    }
  }
}
```

Update the paths to match your actual installation directory. The paths should point to:
- Your virtual environment's Python executable
- The `bash.py` file location

## Setup

1. Create and activate a virtual environment (recommended):
```bash
# Create virtual environment
python -m venv venv

# Activate virtual environment
# On Windows:
venv\Scripts\activate
# On macOS/Linux:
source venv/bin/activate
```

2. Install the required dependencies:
```bash
pip install -r requirements.txt
```

## Usage

### Running the App

Start the FastMCP app in stdio mode:

```bash
python bash.py
```

The app communicates via stdin/stdout, making it suitable for integration with MCP clients like Claude Desktop.

### Example MCP Messages

```
{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{"tools":{}},"clientInfo":{"name":"test-client","version":"1.0.0"}}}

{"jsonrpc":"2.0","method":"notifications/initialized"}

{"jsonrpc":"2.0","id":2,"method":"tools/list"}
```

## Implementation Details

The bash.py script:
1. Creates a FastMCP instance named "bash-shell"
2. Initializes a persistent bash process using subprocess.Popen
3. Defines an allowlist of approved commands (ls, echo, curl, etc.)
4. Provides a run_command tool that:
   - Takes a tool name and optional arguments
   - Validates the command against the allowlist
   - Checks for shell operators that could be used for command injection
   - Executes the command in the bash process
   - Returns the command output
5. Provides a list_tools function to see all available commands
6. Uses a sentinel marker to clearly separate command output
7. Includes basic logging for executed commands and errors

## Available Commands

The following commands are allowed:
- ls
- echo
- curl
- cat
- grep
- pwd
- find
- wc

## Example Usage

When using this tool with Claude, you can run commands like:

"Please list the files in the current directory"
The tool will execute: run_command(tool="ls", args="-la")

"Show me the content of the README.md file"
The tool will execute: run_command(tool="cat", args="README.md")

## Security Features

- Only commands in the allowlist can be executed
- Shell operators (&&, ;, |, etc.) are rejected
- Command arguments are validated before execution
- Persistent bash process prevents command history manipulation
