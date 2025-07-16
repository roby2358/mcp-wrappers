"""
CMD Wrapper MCP Server - Allows controlled execution of cmd commands with a single persistent process
"""

# Always use the official MCP Python implmententation "mcp" located at https://github.com/modelcontextprotocol/python-sdk?utm_source=chatgpt.com

import asyncio
import sys
import subprocess
import threading
import logging
import re
import time
from typing import Dict, Any
import uuid

from mcp.server.fastmcp import FastMCP
from background_reader import BackgroundReader
from persistent_cmd_shell import PersistentCmdShell

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(sys.stderr)]
)
logger = logging.getLogger("cmd_shell")

# Create the MCP server instance
mcp = FastMCP("cmd-shell")

# Define the allowlist of approved commands
ALLOWED_COMMANDS = [
    "dir",
    "echo",
    "curl",
    "find",
    "findstr",
    "cd",
    "where",
    "set",
    "podman"
]

def mcp_success(result: str) -> Dict[str, Any]:
    """Create a standardized success response."""
    return {
        "success": True,
        "result": result,
        "error": ""
    }

def mcp_failure(error_message: str) -> Dict[str, Any]:
    """Create a standardized failure response."""
    return {
        "success": False,
        "result": "",
        "error": error_message
    }

# Create global shell instance
shell = PersistentCmdShell()

@mcp.prompt()
def intro() -> str:
    """Return an introductory prompt that describes the CMD wrapper tool."""
    tools_list = ", ".join(ALLOWED_COMMANDS)
    
    return f"""
You have access to a set of CMD commands as individual tools.

Available commands: {tools_list}

To use these tools, call them directly with optional arguments.
For example, to list files in the current directory: dir(arguments="/w")

Shell operators (&&, ;, |, etc.) are not allowed and will be rejected.

You can also use the 'restart' tool to restart the CMD shell if needed.
"""

async def _execute_cmd_command(command: str, arguments: str = "") -> Dict[str, Any]:
    """Helper function to execute a cmd command."""
    # Check for shell operators
    if PersistentCmdShell.contains_shell_operators(arguments):
        return mcp_failure("Error: Shell operators (&&, ;, |, etc.) are not allowed.")
    
    try:
        # Construct the full command
        full_command = f"{command} {arguments}".strip()
        logger.info(f"Executing command: {full_command}")
        
        # Execute the command
        output = await shell.execute_command(full_command)
        
        return mcp_success(output)
    
    except Exception as e:
        logger.error(f"Error running command '{command}': {str(e)}")
        return mcp_failure(f"Error running command: {str(e)}")

# Dynamically create tool functions for each allowed command
def create_command_tool(command_name):
    """Create a tool function for a specific command."""
    @mcp.tool(name=command_name)
    async def command_tool(arguments: str = "") -> Dict[str, Any]:
        """Run the command with optional arguments."""
        return await _execute_cmd_command(command_name, arguments)
    
    # Update the docstring
    command_tool.__doc__ = f"Run the {command_name} command with optional arguments."

# Register all allowed commands as tools
for cmd_name in ALLOWED_COMMANDS:
    create_command_tool(cmd_name)

@mcp.tool()
async def restart() -> Dict[str, Any]:
    """Restart the CMD shell."""
    try:
        result = shell.restart()
        return mcp_success(result)
    except Exception as e:
        logger.error(f"Error restarting CMD shell: {str(e)}")
        return mcp_failure(f"Error restarting CMD shell: {str(e)}")

@mcp.tool()
async def read_into_context(filename: str) -> Dict[str, Any]:
    """Read and display a file's contents without character limits."""
    try:
        # Validate filename to prevent directory traversal
        if ".." in filename or filename.startswith("/") or filename.startswith("\\"):
            return mcp_failure("Error: Invalid filename")
        
        # Read file directly in Python to bypass CMD character limits
        with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        return mcp_success(content)
    except FileNotFoundError:
        return mcp_failure(f"Error: File '{filename}' not found")
    except PermissionError:
        return mcp_failure(f"Error: Permission denied accessing '{filename}'")
    except Exception as e:
        logger.error(f"Error reading file '{filename}': {str(e)}")
        return mcp_failure(f"Error reading file: {str(e)}")

@mcp.tool()
async def list_cmd_shell_tools() -> Dict[str, Any]:
    """List all available tools."""
    try:
        all_tools = ALLOWED_COMMANDS + ["restart", "read_into_context"]
        return mcp_success(all_tools)
    except Exception as e:
        return mcp_failure(f"Error listing tools: {str(e)}")

def main():
    """Entry point for the application."""
    print("Starting CMD Shell MCP Server...", file=sys.stderr)
    mcp.run()

if __name__ == "__main__":
    main()