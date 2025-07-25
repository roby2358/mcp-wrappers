#!/usr/bin/env python3
"""
Hello World MCP Server using the official MCP SDK
"""

import asyncio
import sys
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
    Return an introductory prompt that describes the Echo tool.
    """
    return """
You have access to an Echo tool that can repeat back any message you send to it.

To use this tool, provide a message as a string to the echo function.
For example, to echo "Hello, world!", you would use: "Hello, world!"

Please use the Echo tool to send a greeting.
"""

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
