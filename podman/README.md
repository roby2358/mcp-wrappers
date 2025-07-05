# Podman FastMCP Wrapper

A FastMCP wrapper that shells out to podman commands, allowing you to execute podman operations through the MCP protocol.

## Features

- Execute any podman command by passing command line arguments as a string
- Captures stdout, stderr, and return codes
- Error handling for common issues like missing podman installation
- Simple integration with Claude Desktop
- Built-in prompt that instructs the model how to use the podman tool

**Note**: Update the paths to match your actual installation directory. The paths should point to:
- Your virtual environment's Python executable
- The `podman.py` file location

### Claude Desktop Configuration

To use this wrapper with Claude Desktop, add the following to your Claude Desktop configuration:

### Config File Location
- **Windows**: `C:\Users\[YourUsername]\AppData\Roaming\Claude\claude_desktop_config.json`
- **macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
- **Linux**: `~/.config/Claude/claude_desktop_config.json`

### Log File Locations
- **Claude Desktop MCP Log**: `C:\Users\[YourUsername]\AppData\Roaming\Claude\logs\mcp.log`
- **Individual MCP App Log**: `C:\Users\[YourUsername]\AppData\Roaming\Claude\logs\mcp-servers\podman-wrapper.log`

Example paths:
```
C:\Users\roby2\AppData\Roaming\Claude\claude_desktop_config.json
C:\Users\roby2\AppData\Roaming\Claude\logs\mcp.log
C:\Users\roby2\AppData\Roaming\Claude\logs\mcp-servers\podman-wrapper.log
```

### Configuration
```json
{
  "mcpServers": {
    "podman-wrapper": {
      "command": "C:/work/podman-mcp-wrapper/venv/Scripts/python.exe",
      "args": ["C:/work/podman-mcp-wrapper/podman.py"]
    }
  }
}
```

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

1. Install the required dependencies:
```bash
pip install -r requirements.txt
```

2. Make sure podman is installed and available in your PATH.

## Usage

### Running the Wrapper

Start the FastMCP wrapper in stdio mode:

```bash
python podman.py
```

The wrapper communicates via stdin/stdout, making it suitable for integration with MCP clients.

### Using the Wrapper

The wrapper provides a single tool `execute_podman_command` that takes a string parameter containing the podman command line arguments.

## Implementation Details

Create a Python script that implements a FastMCP wrapper for podman commands. The script should:
1. Import the necessary modules: asyncio, sys, typing.Dict, typing.Any, and mcp.server.fastmcp.FastMCP
2. Create a FastMCP instance named "podman-wrapper"
3. Define a prompt function that returns instructions for using the podman tool
4. Define a tool function called execute_podman_command that:
   - Takes a string parameter for the command
   - Validates the command is not empty
   - Splits the command into arguments
   - Executes the command using subprocess.run with podman
   - Returns a dictionary with success, stdout, stderr, return_code, and full_command
5. Use mcp.run() in stdio mode for communication
6. Handle errors gracefully and return appropriate error responses

The implementation should shell out to podman CLI commands and return structured results suitable for MCP protocol communication.

### Example MCP Messages

```
{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{"tools":{}},"clientInfo":{"name":"test-client","version":"1.0.0"}}}

{"jsonrpc":"2.0","method":"notifications/initialized"}

{"jsonrpc":"2.0","id":2,"method":"tools/list"}
```
