"""Unit tests for NoIgnoreList class."""

import pytest
from pathlib import Path
from src.projects.ignore_list import NoIgnoreList


class TestNoIgnoreList:
    """Test the NoIgnoreList class behavior."""
    
    def test_no_ignore_list_initialization(self):
        """Test that NoIgnoreList can be instantiated without parameters."""
        no_ignore = NoIgnoreList()
        assert no_ignore is not None
    
    def test_filter_files_returns_all_files(self):
        """Test that filter_files returns all files unfiltered."""
        no_ignore = NoIgnoreList()
        
        # Create some test file paths
        test_files = [
            Path("project1.txt"),
            Path("project2.txt"),
            Path("ignored_project.txt"),
            Path("special@project.txt")
        ]
        
        # filter_files should return all files unchanged
        filtered = no_ignore.filter_files(test_files)
        
        assert filtered == test_files
        assert len(filtered) == 4
        assert all(f in filtered for f in test_files)
    
    def test_should_ignore_always_returns_false(self):
        """Test that should_ignore always returns False for any filename."""
        no_ignore = NoIgnoreList()
        
        # Test various filename patterns that might normally be ignored
        test_filenames = [
            "ignored.txt",
            "*.tmp",
            "backup~",
            ".#lock",
            "project.txt",
            "special@project.txt",
            "project with spaces.txt"
        ]
        
        for filename in test_filenames:
            assert not no_ignore.should_ignore(filename), f"should_ignore returned True for '{filename}'"
    
    def test_filter_files_with_empty_list(self):
        """Test that filter_files handles empty file lists correctly."""
        no_ignore = NoIgnoreList()
        
        empty_files = []
        filtered = no_ignore.filter_files(empty_files)
        
        assert filtered == []
        assert len(filtered) == 0
    
    def test_filter_files_with_none_files(self):
        """Test that filter_files handles None gracefully."""
        no_ignore = NoIgnoreList()
        
        # This should raise an AttributeError since None doesn't have a .name attribute
        with pytest.raises(AttributeError):
            no_ignore.filter_files([None])
    
    def test_should_ignore_with_empty_string(self):
        """Test that should_ignore handles empty strings correctly."""
        no_ignore = NoIgnoreList()
        
        assert not no_ignore.should_ignore("")
        assert not no_ignore.should_ignore("   ")  # Just whitespace
    
    def test_should_ignore_with_special_characters(self):
        """Test that should_ignore handles special characters correctly."""
        no_ignore = NoIgnoreList()
        
        special_filenames = [
            "file with spaces.txt",
            "file@domain.com.txt",
            "file#hash.txt",
            "file$dollar.txt",
            "file%percent.txt",
            "file&ampersand.txt",
            "file*asterisk.txt",
            "file?question.txt",
            "file|pipe.txt",
            "file\\backslash.txt",
            "file/forward_slash.txt",
            "file:colon.txt",
            "file;semicolon.txt",
            "file<less.txt",
            "file>greater.txt",
            "file=equals.txt",
            "file+plus.txt",
            "file`backtick.txt",
            "file~tilde.txt"
        ]
        
        for filename in special_filenames:
            assert not no_ignore.should_ignore(filename), f"should_ignore returned True for '{filename}'"
    
    def test_filter_files_preserves_path_objects(self):
        """Test that filter_files preserves Path objects exactly as passed."""
        no_ignore = NoIgnoreList()
        
        # Create Path objects with different attributes
        test_files = [
            Path("project1.txt").resolve(),
            Path("project2.txt").absolute(),
            Path("project3.txt")
        ]
        
        filtered = no_ignore.filter_files(test_files)
        
        # Should preserve exact Path objects
        assert filtered == test_files
        for i, file in enumerate(test_files):
            assert filtered[i] is file  # Same object reference
            assert filtered[i].resolve() == file.resolve()  # Same resolved path
    
    def test_should_ignore_with_unicode_filenames(self):
        """Test that should_ignore handles unicode filenames correctly."""
        no_ignore = NoIgnoreList()
        
        unicode_filenames = [
            "café.txt",
            "naïve.txt",
            "résumé.txt",
            "über.txt",
            "café_naïve_résumé.txt",
            "测试.txt",
            "тест.txt",
            "テスト.txt"
        ]
        
        for filename in unicode_filenames:
            assert not no_ignore.should_ignore(filename), f"should_ignore returned True for '{filename}'"
    
    def test_should_ignore_with_numeric_filenames(self):
        """Test that should_ignore handles numeric filenames correctly."""
        no_ignore = NoIgnoreList()
        
        numeric_filenames = [
            "123.txt",
            "0.txt",
            "999999.txt",
            "1.0.txt",
            "v2.1.txt",
            "2023-12-25.txt"
        ]
        
        for filename in numeric_filenames:
            assert not no_ignore.should_ignore(filename), f"should_ignore returned True for '{filename}'"
