"""
Record ID Generation
Provides consistent ID generation for text records across the application.
"""

import random
import re
from typing import ClassVar

# Base32 alphabet: a-z, 2-9 (excluding 1, l, o for visual clarity)
BASE32_CHARS = "abcdefghijkmnpqrstuvwxyz23456789"


class RecordID:
    """Utility class for generating consistent record IDs across the application.
    
    Provides a shared implementation for generating unique record IDs using base32 characters.
    Supports both legacy format (XX-XXXX-XX) and new tag-based format (<tag>-XXXX).
    """
    
    @classmethod
    def generate(cls) -> str:
        """Generate a unique 10-character record ID using base32 characters.
        
        Returns:
            A 10-character record ID in the format XX-XXXX-XX where X are base32 characters.
        """
        chars = [random.choice(BASE32_CHARS) for _ in range(8)]
        return f"{chars[0]}{chars[1]}-{chars[2]}{chars[3]}{chars[4]}{chars[5]}-{chars[6]}{chars[7]}"
    
    @classmethod
    def generate_with_tag(cls, tag: str) -> str:
        """Generate a unique tag-based record ID using base32 characters.
        
        Args:
            tag: Tag string (1-12 characters, alphanumeric and hyphens only)
            
        Returns:
            A tag-based record ID in the format <tag>-XXXX where XXXX are base32 characters.
            
        Raises:
            ValueError: If tag format is invalid
        """
        # Validate tag format
        if not re.match(r'^[a-zA-Z0-9-]{1,12}$', tag):
            raise ValueError("Tag must be 1-12 characters long and contain only alphanumeric characters and hyphens")
        
        # Generate 4-character random string using base32
        chars = [BASE32_CHARS[random.randint(0, len(BASE32_CHARS)-1)] for _ in range(4)]
        random_part = ''.join(chars)
        
        return f"{tag}-{random_part}" 