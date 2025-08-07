"""
Tests for ignore list functionality
"""

import pytest
from pathlib import Path
from src.projects.ignore_list import IgnoreList


class TestIgnoreList:
    """Test the IgnoreList class functionality"""
    
    def test_no_ignore_file(self, tmp_path):
        """Test behavior when no pjpdignore file exists"""
        ignore_list = IgnoreList(tmp_path)
        ignore_list.load_patterns()
        
        # Should not ignore any files when no pjpdignore file exists
        assert not ignore_list.should_ignore("project.txt")
        assert not ignore_list.should_ignore("test.txt")
        assert not ignore_list.should_ignore("*.txt")
    
    def test_empty_ignore_file(self, tmp_path):
        """Test behavior with empty pjpdignore file"""
        # Create pjpd directory and ignore file
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        ignore_file = pjpd_dir / "pjpdignore"
        ignore_file.write_text("")
        
        ignore_list = IgnoreList(tmp_path)
        ignore_list.load_patterns()
        
        # Should not ignore any files when pjpdignore file is empty
        assert not ignore_list.should_ignore("project.txt")
        assert not ignore_list.should_ignore("test.txt")
    
    def test_comment_lines(self, tmp_path):
        """Test that comment lines are ignored"""
        # Create pjpd directory and ignore file
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        ignore_file = pjpd_dir / "pjpdignore"
        ignore_file.write_text("# This is a comment\n*.tmp\n# Another comment")
        
        ignore_list = IgnoreList(pjpd_dir)
        ignore_list.load_patterns()
        
        # Should ignore .tmp files but not .txt files
        assert ignore_list.should_ignore("test.tmp")
        assert not ignore_list.should_ignore("test.txt")
    
    def test_wildcard_patterns(self, tmp_path):
        """Test wildcard pattern matching"""
        # Create pjpd directory and ignore file
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        ignore_file = pjpd_dir / "pjpdignore"
        ignore_file.write_text("*.tmp\nbackup_*\n*_old.txt")
        
        ignore_list = IgnoreList(pjpd_dir)
        ignore_list.load_patterns()
        
        # Test various patterns
        assert ignore_list.should_ignore("test.tmp")
        assert ignore_list.should_ignore("backup_project.txt")
        assert ignore_list.should_ignore("project_old.txt")
        assert not ignore_list.should_ignore("project.txt")
        assert not ignore_list.should_ignore("new_project.txt")
    
    def test_whitespace_handling(self, tmp_path):
        """Test that leading/trailing whitespace is stripped"""
        # Create pjpd directory and ignore file
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        ignore_file = pjpd_dir / "pjpdignore"
        ignore_file.write_text("  *.tmp  \n  backup_*  ")
        
        ignore_list = IgnoreList(pjpd_dir)
        ignore_list.load_patterns()
        
        # Patterns should work despite whitespace
        assert ignore_list.should_ignore("test.tmp")
        assert ignore_list.should_ignore("backup_project.txt")
        assert not ignore_list.should_ignore("project.txt")
    
    def test_filter_files(self, tmp_path):
        """Test the filter_files method"""
        # Create pjpd directory and ignore file
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        ignore_file = pjpd_dir / "pjpdignore"
        ignore_file.write_text("*.tmp\nbackup_*")
        
        # Create some test files
        files = [
            tmp_path / "project1.txt",
            tmp_path / "project2.txt", 
            tmp_path / "backup_project.txt",
            tmp_path / "temp.tmp"
        ]
        
        ignore_list = IgnoreList(pjpd_dir)
        filtered_files = ignore_list.filter_files(files)
        
        # Should only return the non-ignored files
        expected_files = [tmp_path / "project1.txt", tmp_path / "project2.txt"]
        assert set(filtered_files) == set(expected_files)
    
    def test_case_sensitive_patterns(self, tmp_path):
        """Test that patterns are case-sensitive"""
        # Create pjpd directory and ignore file
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        ignore_file = pjpd_dir / "pjpdignore"
        ignore_file.write_text("*.TMP\nBACKUP_*")
        
        ignore_list = IgnoreList(pjpd_dir)
        ignore_list.load_patterns()
        
        # Case-sensitive matching
        assert ignore_list.should_ignore("test.TMP")
        assert not ignore_list.should_ignore("test.tmp")
        assert ignore_list.should_ignore("BACKUP_project.txt")
        assert not ignore_list.should_ignore("backup_project.txt")
    
    def test_reload_functionality(self, tmp_path):
        """Test that reload() works correctly"""
        # Create pjpd directory and ignore file
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        ignore_file = pjpd_dir / "pjpdignore"
        ignore_file.write_text("*.tmp")
        
        ignore_list = IgnoreList(pjpd_dir)
        ignore_list.load_patterns()
        
        # Should ignore .tmp files
        assert ignore_list.should_ignore("test.tmp")
        
        # Update the ignore file
        ignore_file.write_text("*.log")
        
        # Reload and test
        ignore_list.reload()
        assert not ignore_list.should_ignore("test.tmp")
        assert ignore_list.should_ignore("test.log") 