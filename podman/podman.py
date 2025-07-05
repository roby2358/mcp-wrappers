#!/usr/bin/env python3
"""
Podman MCP Server using the official MCP SDK
"""

import asyncio
import sys
from typing import Dict, Any

from mcp.server.fastmcp import FastMCP

# Create the MCP server instance
mcp = FastMCP("podman-wrapper")

@mcp.prompt()
def get_podman_prompt() -> str:
    """
    Return a prompt that describes the podman tool and asks for a ps -a command.
    """
    return """
You have access to a podman command execution tool. This tool allows you to run podman commands on the host system.

To use this tool, provide the command line arguments as a string to the execute_podman_command function.
For example, to list all containers, you would use: "podman" "ps -a"

Other common podman commands include:
- "images" - List all images
- "run [options] IMAGE [COMMAND]" - Run a command in a new container
- "build -t NAME:TAG PATH" - Build an image from a Dockerfile
- "pull IMAGE" - Pull an image from a registry
- "rm CONTAINER" - Remove one or more containers

Please list all containers by running the "ps -a" command.
"""

@mcp.tool()
async def execute_podman_command(command: str) -> Dict[str, Any]:
    """
    Execute a podman command with the provided arguments.
    This tool shells out to the podman CLI with the given command line arguments.
    """
    if not command:
        return {
            "success": False,
            "stdout": "",
            "stderr": "Error: No command provided.",
            "return_code": 1,
            "full_command": "podman"
        }
    
    # Split the command into arguments
    cmd_parts = command.strip().split()
    full_command = ["podman"] + cmd_parts
    
    try:
        # Execute the command
        process = await asyncio.create_subprocess_exec(
            *full_command,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        
        stdout, stderr = await process.communicate()
        
        # Build the response
        return {
            "success": process.returncode == 0,
            "stdout": stdout.decode('utf-8', errors='replace'),
            "stderr": stderr.decode('utf-8', errors='replace'),
            "return_code": process.returncode,
            "full_command": " ".join(full_command)
        }
            
    except FileNotFoundError:
        return {
            "success": False,
            "stdout": "",
            "stderr": "Error: Podman is not installed or not available in PATH.",
            "return_code": 127,
            "full_command": " ".join(full_command)
        }
    except Exception as e:
        return {
            "success": False,
            "stdout": "",
            "stderr": f"Error executing podman command: {str(e)}",
            "return_code": 1,
            "full_command": " ".join(full_command)
        }

def main():
    """Entry point for the application."""
    print("Starting Podman MCP Server...", file=sys.stderr)
    mcp.run()

if __name__ == "__main__":
    main() 