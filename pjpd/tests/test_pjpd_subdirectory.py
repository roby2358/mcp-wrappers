"""
Tests for pjpd subdirectory functionality
"""

import pytest
from pathlib import Path
from src.mcp_wrapper import _normalize_projects_directory
from src.ideas.ideas import Ideas
from src.epics.epics import Epics


class TestPjpdSubdirectory:
    """Test the pjpd subdirectory functionality"""
    
    def test_normalize_projects_directory_no_suffix(self):
        """Test that paths without pjpd suffix are unchanged"""
        path = Path("/home/user/projects")
        normalized = _normalize_projects_directory(path)
        assert normalized == path
        
        path = Path("C:\\work\\projects")
        normalized = _normalize_projects_directory(path)
        assert normalized == path
    
    def test_normalize_projects_directory_with_suffix(self):
        """Paths ending with a pjpd segment should be preserved"""
        path = Path("/home/user/projects/pjpd")
        normalized = _normalize_projects_directory(path)
        assert normalized == path
        
        path = Path("C:\\work\\projects\\pjpd")
        normalized = _normalize_projects_directory(path)
        assert normalized == path
    
    def test_normalize_projects_directory_with_trailing_slash(self):
        """Paths with trailing slash are normalised but preserved"""
        path = Path("/home/user/projects/pjpd/")
        normalized = _normalize_projects_directory(path)
        assert normalized == Path("/home/user/projects/pjpd")
        
        path = Path("C:\\work\\projects\\pjpd\\")
        normalized = _normalize_projects_directory(path)
        assert normalized == Path("C:\\work\\projects\\pjpd")
    
    def test_normalize_projects_directory_partial_match(self):
        """Test that partial matches don't trigger removal"""
        path = Path("/home/user/projects/my_pjpd_project")
        normalized = _normalize_projects_directory(path)
        assert normalized == path
        
        path = Path("C:\\work\\projects\\pjpd_backup")
        normalized = _normalize_projects_directory(path)
        assert normalized == path
    
    def test_ideas_manager_pjpd_subdirectory(self, tmp_path):
        """Test that Ideas manager looks in pjpd subdirectory"""
        # Create pjpd directory and ideas file
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        ideas_file = pjpd_dir / "ideas.txt"
        ideas_file.write_text("Score:   80\nID: test-abcd\nTest idea\n---")
        
        # Create Ideas manager
        ideas = Ideas(tmp_path)
        
        # Should load ideas from pjpd/ideas.txt
        assert len(ideas.ideas) == 1
        assert ideas.ideas[0].id == "test-abcd"
        assert ideas.ideas[0].score == 80
    
    def test_epics_manager_pjpd_subdirectory(self, tmp_path):
        """Test that Epics manager looks in pjpd subdirectory"""
        # Create pjpd directory and epics file
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        epics_file = pjpd_dir / "epics.txt"
        epics_file.write_text("Score:   75\nID: test-efgh\nTest epic\n---")
        
        # Create Epics manager
        epics = Epics(tmp_path)
        
        # Should load epics from pjpd/epics.txt
        assert len(epics.epics) == 1
        assert epics.epics[0].id == "test-efgh"
        assert epics.epics[0].score == 75
