#!/usr/bin/env python3
"""
Bash Wrapper MCP Server - Allows controlled execution of bash commands
"""

import asyncio
import sys
import subprocess
import shlex
import re
import logging
from typing import Dict, Any, List, Optional

from mcp.server.fastmcp import FastMCP

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(sys.stderr)]
)
logger = logging.getLogger("bash_shell")

# Create the MCP server instance
mcp = FastMCP("bash-shell")

# Define the allowlist of approved commands
ALLOWED_COMMANDS = [
    "ls",
    "echo",
    "curl",
    "cat",
    "grep",
    "pwd",
    "find",
    "wc",
    "set",
    "podman"
]

class ActiveShell:
    """Class to manage a running bash process."""
    
    # Command completion sentinel
    CMD_SENTINEL = "__CMD_DONE__"
    
    def __init__(self):
        """Initialize the RunningBash instance."""
        self.process = None
        self.initialize()
    
    def initialize(self):
        """Initialize the bash process to be reused across requests."""
        if self.process is None:
            try:
                # Start bash with -i for interactive mode
                self.process = subprocess.Popen(
                    ["bash"],
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    bufsize=0
                )
                logger.info("Bash process initialized")
            except Exception as e:
                logger.error(f"Failed to initialize bash process: {str(e)}")
                raise
    
    @staticmethod
    def contains_shell_operators(command: str) -> bool:
        """Check if the command contains shell operators that could be used for command injection."""
        # List of shell operators and other dangerous patterns
        shell_operators = [
            "&&", "||", ";", "|", ">", ">>", "<", "<<", 
            "`", "$", "$(", "${", "&", "#!", "eval", "exec"
        ]
        
        for operator in shell_operators:
            if operator in command:
                return True
        
        return False
    
    async def execute_command(self, command: str) -> str:
        """Execute a command in the bash process and return its output."""
        if self.process is None:
            self.initialize()
        
        try:
            # Add the sentinel to mark the end of command output
            full_command = f"{command}; echo '{self.CMD_SENTINEL}'\n"
            
            # Send the command to bash
            self.process.stdin.write(full_command)
            self.process.stdin.flush()
            
            # Read output until we see the sentinel
            output = []
            while True:
                line = self.process.stdout.readline()
                if self.CMD_SENTINEL in line:
                    break
                output.append(line)
            
            # Combine output lines
            return "".join(output)
        
        except Exception as e:
            logger.error(f"Error executing command: {str(e)}")
            return f"Error: {str(e)}"

# Create a global instance of ActiveShell
bash = ActiveShell()

@mcp.prompt()
def get_intro_prompt() -> str:
    """Return an introductory prompt that describes the Bash wrapper tool."""
    tools_list = ", ".join(ALLOWED_COMMANDS)
    
    return f"""
You have access to a set of Bash commands as individual tools.

Available commands: {tools_list}

To use these tools, call them directly with optional arguments.
For example, to list files in the current directory: ls(arguments="-la")

Shell operators (&&, ;, |, etc.) are not allowed and will be rejected.
"""

async def _execute_bash_command(command: str, arguments: str = "") -> Dict[str, Any]:
    """
    Helper function to execute a bash command.
    
    Args:
        command: The command to run
        arguments: Optional arguments for the command
    
    Returns:
        Dictionary with success status, result output, and any error messages
    """
    # Check for shell operators
    if ActiveShell.contains_shell_operators(arguments):
        return {
            "success": False,
            "result": "",
            "error": "Error: Shell operators (&&, ;, |, etc.) are not allowed."
        }
    
    try:
        # Construct the full command
        full_command = f"{command} {arguments}".strip()
        logger.info(f"Executing command: {full_command}")
        
        # Execute the command
        output = await bash.execute_command(full_command)
        
        return {
            "success": True,
            "result": output,
            "error": ""
        }
    
    except Exception as e:
        logger.error(f"Error running command '{command}': {str(e)}")
        return {
            "success": False,
            "result": "",
            "error": f"Error running command: {str(e)}"
        }

# Dynamically create tool functions for each allowed command
def create_command_tool(command_name):
    """Create a tool function for a specific command."""
    @mcp.tool(name=command_name)
    async def command_tool(arguments: str = "") -> Dict[str, Any]:
        """Run the command with optional arguments."""
        return await _execute_bash_command(command_name, arguments)
    
    # Update the docstring
    command_tool.__doc__ = f"Run the {command_name} command with optional arguments."

# Register all allowed commands as tools
for cmd in ALLOWED_COMMANDS:
    create_command_tool(cmd)

@mcp.tool()
async def list_bash_shell_tools() -> Dict[str, Any]:
    """
    List all available tools.
    
    Returns:
        Dictionary with the list of allowed commands
    """
    try:
        return {
            "success": True,
            "result": ALLOWED_COMMANDS,
            "error": ""
        }
    except Exception as e:
        return {
            "success": False,
            "result": [],
            "error": f"Error listing tools: {str(e)}"
        }

def main():
    """Entry point for the application."""
    print("Starting Bash Shell MCP Server...", file=sys.stderr)
    mcp.run()

if __name__ == "__main__":
    main()
