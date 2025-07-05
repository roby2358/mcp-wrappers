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

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(sys.stderr)]
)
logger = logging.getLogger("cmd_shell")

# Define Windows-specific flags
try:
    CREATE_NO_WINDOW = subprocess.CREATE_NO_WINDOW
except AttributeError:
    # Fallback if CREATE_NO_WINDOW is not defined
    CREATE_NO_WINDOW = 0x08000000

# Create the MCP server instance
mcp = FastMCP("cmd-shell")

# Define the allowlist of approved commands
ALLOWED_COMMANDS = [
    "dir",
    "echo",
    "curl",
    "type",
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

class BackgroundReader(threading.Thread):
    """Thread to continuously read from the process to prevent buffer issues."""
    
    def __init__(self, stream, name):
        super().__init__(daemon=True)
        self.stream = stream
        self.name = name
        self.buffer = ""
        self.lock = threading.Lock()
        self.running = True
        self.start()
    
    def run(self):
        """Thread run method - continuously reads from the stream."""
        while self.running and not self.stream.closed:
            try:
                # Read character by character to avoid blocking
                char = self.stream.read(1)
                if not char:
                    time.sleep(0.01)  # Small sleep to prevent CPU spinning
                    continue
                
                with self.lock:
                    self.buffer += char
            except Exception as e:
                logger.error(f"{self.name} reader error: {str(e)}")
                time.sleep(0.1)
    
    def get_output(self, clear=True):
        """Get the current buffer contents and optionally clear it."""
        with self.lock:
            output = self.buffer
            if clear:
                self.buffer = ""
        return output
    
    def stop(self):
        """Stop the thread."""
        self.running = False

class PersistentCmdShell:
    """Simple class to manage a persistent cmd process."""
    
    def __init__(self):
        """Initialize the CMD process."""
        self.process = None
        self.stdout_reader = None
        self.stderr_reader = None
        self.initialize()
    
    def initialize(self):
        """Start a new CMD process."""
        if self.process is not None:
            try:
                if self.stdout_reader:
                    self.stdout_reader.stop()
                if self.stderr_reader:
                    self.stderr_reader.stop()
                self.process.terminate()
            except:
                pass
        
        self.process = subprocess.Popen(
            ["cmd.exe"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=0,
            creationflags=CREATE_NO_WINDOW
        )
        
        # Start background readers
        self.stdout_reader = BackgroundReader(self.process.stdout, "stdout")
        self.stderr_reader = BackgroundReader(self.process.stderr, "stderr")
        
        # Initial setup - turn off echo
        self.process.stdin.write("@echo off\r\n")
        self.process.stdin.flush()
        time.sleep(0.5)  # Wait a bit for echo off to take effect
        
        # Clear initial output
        self.stdout_reader.get_output()
        self.stderr_reader.get_output()
        
        logger.info("CMD process initialized")
    
    def restart(self):
        """Restart the CMD process."""
        self.initialize()
        return "CMD shell has been restarted successfully."
    
    @staticmethod
    def contains_shell_operators(command: str) -> bool:
        """Check if the command contains shell operators that could be used for command injection."""
        shell_operators = [
            "&&", "||", ";", "|", ">", ">>", "<", "<<", 
            "&", "^", "%", "$", "!", "call", "start"
        ]
        
        for operator in shell_operators:
            if operator in command:
                return True
        
        return False
    
    def _clean_output(self, output, preserve_paths=False):
        if not preserve_paths:
            # Only clean when we know it's safe
            output = re.sub(r'^[A-Z]:\\[^>]*>', '', output, flags=re.MULTILINE)
        return output.strip()
    
    async def execute_command(self, command, timeout=30):
        """Execute a command in the CMD process with timeout."""
        if self.process.poll() is not None:
            # Process died, restart it
            self.initialize()
        
        try:
            # Create a unique marker for this command
            marker = f"MARKER_{uuid.uuid4().hex}"
            
            # Clear any existing output
            self.stdout_reader.get_output()
            self.stderr_reader.get_output()
            
            # Send the command with an echo marker after it
            full_command = f"{command}\r\necho {marker}\r\n"
            self.process.stdin.write(full_command)
            self.process.stdin.flush()
            
            # Define a coroutine that waits for the marker
            async def wait_for_marker():
                start_time = time.time()
                while time.time() - start_time < timeout:
                    # Check stdout for the marker
                    stdout = self.stdout_reader.get_output(clear=False)
                    if marker in stdout:
                        # Get all output and clear the buffer
                        final_stdout = self.stdout_reader.get_output()
                        stderr = self.stderr_reader.get_output()
                        
                        # Combine stdout and stderr if stderr has content
                        if stderr.strip():
                            combined = f"{final_stdout}\n{stderr}"
                        else:
                            combined = final_stdout
                        
                        # Extract output up to the marker
                        marker_pos = combined.find(marker)
                        if marker_pos >= 0:
                            result = combined[:marker_pos]
                        else:
                            result = combined
                        
                        return self._clean_output(result)
                    
                    # Small sleep to prevent CPU spinning
                    await asyncio.sleep(0.1)
                
                # If we get here, we timed out
                return f"Command execution timed out after {timeout} seconds"
            
            # Wait for the marker with timeout
            return await wait_for_marker()
            
        except Exception as e:
            logger.error(f"Error executing command: {str(e)}")
            # Try to restart on error
            self.restart()
            return f"Error: {str(e)}"

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
async def list_cmd_shell_tools() -> Dict[str, Any]:
    """List all available tools."""
    try:
        all_tools = ALLOWED_COMMANDS + ["restart"]
        return mcp_success(all_tools)
    except Exception as e:
        return mcp_failure(f"Error listing tools: {str(e)}")

def main():
    """Entry point for the application."""
    print("Starting CMD Shell MCP Server...", file=sys.stderr)
    mcp.run()

if __name__ == "__main__":
    main()