#!/usr/bin/env python3
"""
Hello World MCP Server using the official MCP SDK
"""

import asyncio
import sys
from pathlib import Path
from typing import Dict, Any

from mcp.server.fastmcp import FastMCP

# Create the MCP server instance
mcp = FastMCP("hello-world")

def mcp_success(result: Any) -> Dict[str, Any]:
    """Return a successful MCP response with the given result."""
    return {
        "success": True,
        "result": result,
        "error": ""
    }

def mcp_failure(error_message: str) -> Dict[str, Any]:
    """Return a failed MCP response with the given error message."""
    return {
        "success": False,
        "result": "",
        "error": error_message
    }

@mcp.prompt()
def intro() -> str:
    """
    Return an introductory prompt that describes the ProjectMCP system.
    """
    try:
        # Read the intro text from resources
        intro_path = Path(__file__).parent.parent / "resources" / "intro.txt"
        with open(intro_path, "r", encoding="utf-8") as f:
            return f.read()
    except FileNotFoundError:
        return """
Welcome to ProjectMCP - Local Project Management Server

ProjectMCP is a lightweight, local-first project management system built on plain .txt files. 
It provides task tracking, prioritization, and project overview capabilities through an MCP interface.

Get started by adding a task to a project or listing existing projects!
"""
    except Exception as e:
        return f"Error loading intro text: {str(e)}"

@mcp.tool()
async def echo(message: str) -> Dict[str, Any]:
    """
    Echo back the provided message.
    This tool simply returns the message that was sent to it.
    """
    if not message:
        return mcp_failure("Error: No message provided.")

    try:
        # Simply return the message
        return mcp_success(message)

    except Exception as e:
        return mcp_failure(f"Error processing message: {str(e)}")

def main():
    """Entry point for the application."""
    print("Starting Hello World MCP Server...", file=sys.stderr)
    mcp.run()

if __name__ == "__main__":
    main()
