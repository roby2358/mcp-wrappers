"""
Record ID Generation
Provides consistent ID generation for text records across the application.
"""

import random
from typing import ClassVar

# Base32 alphabet: a-z, 2-9 (excluding 1, l, o for visual clarity)
BASE32_CHARS = "abcdefghijkmnpqrstuvwxyz23456789"


class RecordID:
    """Utility class for generating consistent record IDs across the application.
    
    Provides a shared implementation for generating unique 10-character IDs
    in the format XX-XXXX-XX using base32 characters. This ensures all
    record types (ideas, tasks, etc.) share a consistent global namespace.
    """
    
    # Class variable for the character set
    CHARS: ClassVar[str] = BASE32_CHARS
    
    @classmethod
    def generate(cls) -> str:
        """Generate a unique 10-character record ID using base32 characters.
        
        Returns:
            A 10-character record ID in the format XX-XXXX-XX where X are base32 characters.
        """
        chars = [random.choice(cls.CHARS) for _ in range(8)]
        return f"{chars[0]}{chars[1]}-{chars[2]}{chars[3]}{chars[4]}{chars[5]}-{chars[6]}{chars[7]}" 