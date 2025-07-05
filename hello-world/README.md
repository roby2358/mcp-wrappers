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
      "command": "C:/work/mcp-wrappers/hello-world/venv/Scripts/python.exe",
      "args": ["C:/work/mcp-wrappers/hello-world/hello-world.py"]
    }
  }
}

Update the paths to match your actual installation directory. The paths should point to:
- Your virtual environment's Python executable
- The `hello-world.py` file location

### Configuration

First use the setup below.

```json
{
  "mcpServers": {
    "hello-world": {
      "command": "C:/path/to/venv/Scripts/python.exe",
      "args": ["C:/path/to/hello-world.py"]
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

2. Install the required dependencies:
```bash
pip install -r requirements.txt
```

## Usage

### Running the App

Start the FastMCP app in stdio mode:

```bash
python hello-world.py
```

The app communicates via stdin/stdout, making it suitable for integration with MCP clients like Claude Desktop.

## Implementation Details

The hello-world.py script:
1. Creates a FastMCP instance named "hello-world"
2. Defines an intro prompt function that returns instructions for using the Echo tool
3. Defines a tool function called echo that:
   - Takes a string parameter for the message
   - Returns the message back to the caller
   - Handles errors gracefully
4. Uses mcp.run() in stdio mode for communication

## Example Usage

When using this tool with Claude, you can simply ask it to echo a message:

"Please echo 'Hello, world!'"

The Echo tool will return: "Hello, world!"
