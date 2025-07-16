"""
BackgroundReader - A thread-based stream reader for handling subprocess output
"""

import threading
import time
import logging
from collections import deque

logger = logging.getLogger("background_reader")

class BackgroundReader(threading.Thread):
    """Thread to continuously read from the process to prevent buffer issues."""
    
    def __init__(self, stream, name, buffer_size=8000):
        super().__init__(daemon=True)
        self.stream = stream
        self.name = name
        # Regular buffer for get_output()
        self.buffer = deque(maxlen=buffer_size)
        # Persistent transcript buffer
        self.transcript_buffer = deque(maxlen=buffer_size)
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
                    # Small sleep to prevent CPU spinning
                    time.sleep(0.01)
                    continue
                
                with self.lock:
                    self.buffer.append(char)
                    self.transcript_buffer.append(char)
            except Exception as e:
                logger.error(f"{self.name} reader error: {str(e)}")
                time.sleep(0.1)
    
    def get_output(self, clear=True):
        """Get the current buffer contents and optionally clear it."""
        with self.lock:
            output = ''.join(self.buffer)
            if clear:
                self.buffer.clear()
        return output
    
    def get_transcript(self):
        """Get the current transcript buffer contents without clearing it."""
        with self.lock:
            return ''.join(self.transcript_buffer)
    
    def stop(self):
        """Stop the thread."""
        self.running = False 