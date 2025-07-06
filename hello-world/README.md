# Hello World FastMCP App

A simple FastMCP application that provides an Echo tool, allowing you to send messages and have them echoed back through the MCP protocol.

## Features

- Simple Echo tool that returns any message sent to it
- Built-in intro prompt that instructs the model how to use the Echo tool
- Error handling for common issues
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
    "hello-world": {
      "command": "C:/work/mcp-wrappers/hello-world/.venv/Scripts/python.exe",
      "args": ["C:/work/mcp-wrappers/hello-world/hello-world.py"]
    }
  }
}
```

Update the paths to match your actual installation directory. The paths should point to:
- Your virtual environment's Python executable
- The `hello-world.py` file location

### Configuration

First use the setup below.

```json
{
  "mcpServers": {
    "hello-world": {
      "command": "C:/path/to/.venv/Scripts/python.exe",
      "args": ["C:/path/to/hello-world.py"]
    }
  }
}
```

## Setup

### Using uv (Recommended)

This project uses [uv](https://github.com/astral-sh/uv) for dependency management.

1. Install uv (if not already installed):
```bash
# On Windows:
pip install uv

# On macOS/Linux:
curl -LsSf https://astral.sh/uv/install.sh | sh
```

2. Create virtual environment and install dependencies:
```bash
# This creates .venv and installs all dependencies
uv sync
```

## Usage

### Running the App

Start the FastMCP app in stdio mode:

```bash
python hello-world.py
```

The app communicates via stdin/stdout, making it suitable for integration with MCP clients like Claude Desktop.

## Example Usage

When using this tool with Claude, you can simply ask it to echo a message:

"Please echo 'Hello, world!'"

The Echo tool will return: "Hello, world!"
