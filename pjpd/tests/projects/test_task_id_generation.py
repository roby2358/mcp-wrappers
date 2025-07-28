"""
Test task ID generation functionality
"""

import pytest
import re
from src.projects.task import Task


class TestTaskIdGeneration:
    """Test the generate_task_id method"""
    
    def test_task_id_format(self):
        """Test that task IDs are generated in the correct XX-XXXX-XX format"""
        task_id = Task.generate_task_id()
        
        # Check format: XX-XXXX-XX where X are URL-safe base64 characters
        pattern = r'^[A-Za-z0-9\-_]{2}-[A-Za-z0-9\-_]{4}-[A-Za-z0-9\-_]{2}$'
        assert re.match(pattern, task_id), f"Task ID '{task_id}' does not match expected format"
    
    def test_task_id_length(self):
        """Test that task IDs are exactly 10 characters long"""
        task_id = Task.generate_task_id()
        assert len(task_id) == 10, f"Task ID '{task_id}' is {len(task_id)} characters, expected 10"
    
    def test_task_id_character_set(self):
        """Test that task IDs only contain URL-safe base64 characters"""
        url_safe_chars = set('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_')
        
        for _ in range(100):  # Test multiple generations
            task_id = Task.generate_task_id()
            for char in task_id:
                assert char in url_safe_chars, f"Character '{char}' in task ID '{task_id}' is not URL-safe base64"
    
    def test_task_id_uniqueness(self):
        """Test that generated task IDs are reasonably unique"""
        generated_ids = set()
        
        # Generate 1000 IDs and check for uniqueness
        for _ in range(1000):
            task_id = Task.generate_task_id()
            assert task_id not in generated_ids, f"Duplicate task ID generated: {task_id}"
            generated_ids.add(task_id)
    
    def test_task_id_structure(self):
        """Test that task IDs have the correct structure with hyphens in the right places"""
        task_id = Task.generate_task_id()
        
        # Should have exactly 2 hyphens
        assert task_id.count('-') == 2, f"Task ID '{task_id}' should have exactly 2 hyphens"
        
        # Should be split into 3 parts by hyphens
        parts = task_id.split('-')
        assert len(parts) == 3, f"Task ID '{task_id}' should be split into 3 parts by hyphens"
        
        # Each part should be exactly 2, 4, and 2 characters respectively
        assert len(parts[0]) == 2, f"Part 1 '{parts[0]}' of task ID '{task_id}' should be exactly 2 characters"
        assert len(parts[1]) == 4, f"Part 2 '{parts[1]}' of task ID '{task_id}' should be exactly 4 characters"
        assert len(parts[2]) == 2, f"Part 3 '{parts[2]}' of task ID '{task_id}' should be exactly 2 characters"
    
    def test_task_id_randomness(self):
        """Test that task IDs show reasonable randomness (not all the same)"""
        ids = [Task.generate_task_id() for _ in range(100)]
        
        # Should have some variation (not all identical)
        unique_ids = set(ids)
        assert len(unique_ids) > 1, "All generated task IDs are identical, suggesting lack of randomness"
        
        # Should have reasonable uniqueness (at least 50% unique in 100 samples)
        uniqueness_ratio = len(unique_ids) / len(ids)
        assert uniqueness_ratio > 0.5, f"Task ID uniqueness ratio {uniqueness_ratio} is too low"
    
    def test_task_id_examples(self):
        """Test that task IDs follow the expected pattern with specific examples"""
        # Generate several IDs and verify they all follow the pattern
        for _ in range(50):
            task_id = Task.generate_task_id()
            
            # Examples of valid formats: "AB-CDEF-GH", "12-3456-78", "aB-cDeF-gH", "A1-B2C3-D4"
            assert len(task_id) == 10
            assert task_id[2] == '-'
            assert task_id[7] == '-'
            
            # All other characters should be URL-safe base64
            valid_chars = set('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_')
            for char in task_id:
                if char != '-':
                    assert char in valid_chars 