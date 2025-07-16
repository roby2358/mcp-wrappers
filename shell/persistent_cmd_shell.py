"""
PersistentCmdShell - A class to manage a persistent cmd process with background output reading
"""

import subprocess
import time
import logging
import re
import uuid
import asyncio
from typing import Dict, Any

from background_reader import BackgroundReader

logger = logging.getLogger("persistent_cmd_shell")

# Define Windows-specific flags
try:
    CREATE_NO_WINDOW = subprocess.CREATE_NO_WINDOW
except AttributeError:
    # Fallback if CREATE_NO_WINDOW is not defined
    CREATE_NO_WINDOW = 0x08000000

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
    
    def _clean_output(self, output, command_sent=None):
        # Remove command prompt patterns
        output = re.sub(r'^[A-Z]:\\[^>]*>', '', output, flags=re.MULTILINE)
        
        # If we know what command was sent, try to remove its echo
        if command_sent:
            # Remove the command echo from the beginning
            lines = output.split('\n')
            cleaned_lines = []
            command_found = False
            
            for line in lines:
                line_stripped = line.strip()
                if not command_found and line_stripped == command_sent.strip():
                    command_found = True
                    continue
                if line_stripped:  # Only add non-empty lines
                    cleaned_lines.append(line.rstrip())
            
            output = '\n'.join(cleaned_lines)
        
        # Final cleanup - remove trailing "echo" if it appears alone
        lines = output.split('\n')
        if lines and lines[-1].strip() == 'echo':
            lines = lines[:-1]
        
        return '\n'.join(lines).strip()
    
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
                        
                        return self._clean_output(result, command_sent=command)
                    
                    # Small sleep to prevent CPU spinning
                    await asyncio.sleep(0.1)
                
                # If we get here, we timed out
                return f"Command execution timed out after {timeout} seconds"
            
            # Wait for the marker with timeout
            return await wait_for_marker()
            
        except Exception as e:
            logger.error(f"Error executing command: {str(e)}")
            return f"Error: {str(e)}"
    
    async def cwd(self, timeout=10):
        """Get the current working directory."""
        return await self.execute_command("cd", timeout) 