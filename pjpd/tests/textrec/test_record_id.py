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
    
    def test_record_id_uniqueness(self):
        """Test that generated record IDs are reasonably unique"""
        generated_ids = set()
        
        # Generate 1000 IDs and check for uniqueness
        for _ in range(1000):
            record_id = RecordID.generate()
            assert record_id not in generated_ids, f"Duplicate record ID generated: {record_id}"
            generated_ids.add(record_id)
    
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
    
    def test_record_id_randomness(self):
        """Test that record IDs show reasonable randomness (not all the same)"""
        ids = [RecordID.generate() for _ in range(100)]
        
        # Should have some variation (not all identical)
        unique_ids = set(ids)
        assert len(unique_ids) > 1, "All generated record IDs are identical, suggesting lack of randomness"
        
        # Should have reasonable uniqueness (at least 50% unique in 100 samples)
        uniqueness_ratio = len(unique_ids) / len(ids)
        assert uniqueness_ratio > 0.5, f"Record ID uniqueness ratio {uniqueness_ratio} is too low"
    
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