"""
BackgroundReader - A thread-based stream reader for handling subprocess output
"""

import threading
import time
import logging

logger = logging.getLogger("background_reader")

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