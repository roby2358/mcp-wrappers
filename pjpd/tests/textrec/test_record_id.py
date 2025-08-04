"""
Test record ID generation functionality
"""

import pytest
import re
from src.textrec.record_id import RecordID


class TestRecordIdGeneration:
    """Test the RecordID.generate method"""
    
    def test_record_id_format(self):
        """Test that record IDs are generated in the correct XX-XXXX-XX format"""
        record_id = RecordID.generate()
        
        # Check format: XX-XXXX-XX where X are base32 characters (a-z, 2-9)
        pattern = r'^[a-z2-9]{2}-[a-z2-9]{4}-[a-z2-9]{2}$'
        assert re.match(pattern, record_id), f"Record ID '{record_id}' does not match expected format"
    
    def test_record_id_length(self):
        """Test that record IDs are exactly 10 characters long"""
        record_id = RecordID.generate()
        assert len(record_id) == 10, f"Record ID '{record_id}' is {len(record_id)} characters, expected 10"
    
    def test_record_id_character_set(self):
        """Test that record IDs only contain base32 characters (a-z, 2-9, excluding 1, l, o)"""
        base32_chars = set('abcdefghijkmnpqrstuvwxyz23456789')
        
        for _ in range(100):  # Test multiple generations
            record_id = RecordID.generate()
            for char in record_id:
                if char != '-':  # Skip the dash separators
                    assert char in base32_chars, f"Character '{char}' in record ID '{record_id}' is not base32"
    
    def test_record_id_structure(self):
        """Test that record IDs have the correct structure with hyphens in the right places"""
        record_id = RecordID.generate()
        
        # Should have exactly 2 hyphens
        assert record_id.count('-') == 2, f"Record ID '{record_id}' should have exactly 2 hyphens"
        
        # Should be split into 3 parts by hyphens
        parts = record_id.split('-')
        assert len(parts) == 3, f"Record ID '{record_id}' should be split into 3 parts by hyphens"
        
        # Each part should be exactly 2, 4, and 2 characters respectively
        assert len(parts[0]) == 2, f"Part 1 '{parts[0]}' of record ID '{record_id}' should be exactly 2 characters"
        assert len(parts[1]) == 4, f"Part 2 '{parts[1]}' of record ID '{record_id}' should be exactly 4 characters"
        assert len(parts[2]) == 2, f"Part 3 '{parts[2]}' of record ID '{record_id}' should be exactly 2 characters"
    
    def test_record_id_examples(self):
        """Test that record IDs follow the expected pattern with specific examples"""
        # Generate several IDs and verify they all follow the pattern
        for _ in range(50):
            record_id = RecordID.generate()
            
            # Examples of valid formats: "ab-cdef-gh", "23-4567-89", "a2-b3c4-d5"
            assert len(record_id) == 10
            assert record_id[2] == '-'
            assert record_id[7] == '-'
            
            # All other characters should be base32 (a-z, 2-9, excluding 1, l, o)
            valid_chars = set('abcdefghijkmnpqrstuvwxyz23456789')
            for char in record_id:
                if char != '-':
                    assert char in valid_chars


class TestRecordIdGenerationWithTag:
    """Test the RecordID.generate_with_tag method"""
    
    def test_generate_with_tag_format(self):
        """Test that tag-based record IDs are generated in the correct <tag>-XXXX format"""
        record_id = RecordID.generate_with_tag("bug")
        
        # Check format: <tag>-XXXX where XXXX are base32 characters
        pattern = r'^bug-[a-z2-9]{4}$'
        assert re.match(pattern, record_id), f"Tag-based record ID '{record_id}' does not match expected format"
    
    def test_generate_with_tag_length(self):
        """Test that tag-based record IDs have correct length based on tag"""
        tag = "feature"
        record_id = RecordID.generate_with_tag(tag)
        
        # Length should be tag length + 1 (for hyphen) + 4 (for random part)
        expected_length = len(tag) + 1 + 4
        assert len(record_id) == expected_length, f"Record ID '{record_id}' is {len(record_id)} characters, expected {expected_length}"
    
    def test_generate_with_tag_character_set(self):
        """Test that tag-based record IDs only contain valid characters"""
        base32_chars = set('abcdefghijkmnpqrstuvwxyz23456789')
        
        for _ in range(100):  # Test multiple generations
            record_id = RecordID.generate_with_tag("test")
            parts = record_id.split('-')
            assert len(parts) == 2, f"Record ID '{record_id}' should have exactly 2 parts"
            
            # Random part should only contain base32 characters
            random_part = parts[1]
            for char in random_part:
                assert char in base32_chars, f"Character '{char}' in random part '{random_part}' is not base32"
    
    def test_generate_with_tag_structure(self):
        """Test that tag-based record IDs have the correct structure"""
        record_id = RecordID.generate_with_tag("milestone")
        
        # Should have exactly 1 hyphen
        assert record_id.count('-') == 1, f"Record ID '{record_id}' should have exactly 1 hyphen"
        
        # Should be split into 2 parts by hyphen
        parts = record_id.split('-')
        assert len(parts) == 2, f"Record ID '{record_id}' should be split into 2 parts by hyphen"
        
        # First part should be the tag
        assert parts[0] == "milestone", f"First part '{parts[0]}' should be 'milestone'"
        
        # Second part should be exactly 4 characters
        assert len(parts[1]) == 4, f"Random part '{parts[1]}' should be exactly 4 characters"
    
    def test_generate_with_tag_different_tags(self):
        """Test that different tags produce different ID prefixes"""
        id1 = RecordID.generate_with_tag("bug")
        id2 = RecordID.generate_with_tag("feature")
        
        # Should have different prefixes
        assert id1.startswith("bug-")
        assert id2.startswith("feature-")
        assert not id1.startswith("feature-")
        assert not id2.startswith("bug-")
    
    def test_generate_with_tag_validation_valid_tags(self):
        """Test that valid tags are accepted"""
        valid_tags = ["bug", "feature", "milestone", "task-123", "a-b-c", "a", "123", "a1b2c3"]
        
        for tag in valid_tags:
            try:
                record_id = RecordID.generate_with_tag(tag)
                assert record_id.startswith(f"{tag}-"), f"Record ID '{record_id}' should start with '{tag}-'"
            except ValueError as e:
                pytest.fail(f"Valid tag '{tag}' was rejected: {e}")
    
    def test_generate_with_tag_validation_invalid_tags(self):
        """Test that invalid tags are rejected with ValueError"""
        invalid_tags = [
            "",  # Empty tag
            "toolongtag123",  # Too long (>12 chars)
            "invalid@tag",  # Invalid character
            "space tag",  # Contains space
            "tag with spaces",  # Contains spaces
            "tag\nwith\nnewlines",  # Contains newlines
            "tag\twith\ttabs",  # Contains tabs
        ]
        
        for tag in invalid_tags:
            try:
                result = RecordID.generate_with_tag(tag)
                pytest.fail(f"Invalid tag '{tag}' (length: {len(tag)}) was accepted, generated: {result}")
            except ValueError:
                # Expected - this is what we want
                pass
    
    def test_generate_with_tag_validation_edge_cases(self):
        """Test edge cases for tag validation"""
        # Test exactly 12 characters (should be valid)
        long_tag = "a" * 12
        record_id = RecordID.generate_with_tag(long_tag)
        assert record_id.startswith(f"{long_tag}-")
        
        # Test 13 characters (should be invalid)
        too_long_tag = "a" * 13
        with pytest.raises(ValueError):
            RecordID.generate_with_tag(too_long_tag)
        
        # Test single character (should be valid)
        single_char_tag = "a"
        record_id = RecordID.generate_with_tag(single_char_tag)
        assert record_id.startswith(f"{single_char_tag}-")
    
    def test_generate_with_tag_examples(self):
        """Test that tag-based record IDs follow the expected pattern with specific examples"""
        # Test various tag types
        test_cases = [
            ("bug", r"^bug-[a-z2-9]{4}$"),
            ("feature", r"^feature-[a-z2-9]{4}$"),
            ("milestone", r"^milestone-[a-z2-9]{4}$"),
            ("task-123", r"^task-123-[a-z2-9]{4}$"),
            ("a-b-c", r"^a-b-c-[a-z2-9]{4}$"),
        ]
        
        for tag, pattern in test_cases:
            record_id = RecordID.generate_with_tag(tag)
            assert re.match(pattern, record_id), f"Record ID '{record_id}' does not match pattern '{pattern}'"
            
            # Verify structure
            parts = record_id.split('-')
            assert len(parts) >= 2, f"Record ID '{record_id}' should have at least 2 parts"
            assert parts[0] == tag.split('-')[0], f"First part should match tag prefix"
            assert len(parts[-1]) == 4, f"Random part should be exactly 4 characters" 