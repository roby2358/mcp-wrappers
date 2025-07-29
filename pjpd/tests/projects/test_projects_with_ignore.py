"""
Tests for Projects class with ignore list integration
"""

import pytest
from pathlib import Path
from src.projects.projects import Projects


class TestProjectsWithIgnore:
    """Test Projects class integration with ignore list"""
    
    def test_projects_load_with_ignore_file(self, tmp_path):
        """Test that projects are filtered when .ignore file exists"""
        # Create some project files
        (tmp_path / "project1.txt").write_text("")
        (tmp_path / "project2.txt").write_text("")
        (tmp_path / "backup_project.txt").write_text("")
        (tmp_path / "temp.tmp").write_text("")
        
        # Create .ignore file
        ignore_file = tmp_path / ".ignore"
        ignore_file.write_text("backup_*\n*.tmp")
        
        # Load projects
        projects = Projects(tmp_path)
        projects._load_projects()
        
        # Should only load non-ignored projects
        assert "project1" in projects.projects
        assert "project2" in projects.projects
        assert "backup_project" not in projects.projects
        assert len(projects.projects) == 2
    
    def test_projects_load_without_ignore_file(self, tmp_path):
        """Test that all projects are loaded when no .ignore file exists"""
        # Create some project files
        (tmp_path / "project1.txt").write_text("")
        (tmp_path / "project2.txt").write_text("")
        (tmp_path / "backup_project.txt").write_text("")
        
        # Load projects (no .ignore file)
        projects = Projects(tmp_path)
        projects._load_projects()
        
        # Should load all .txt files
        assert "project1" in projects.projects
        assert "project2" in projects.projects
        assert "backup_project" in projects.projects
        assert len(projects.projects) == 3
    
    def test_projects_load_with_comments_in_ignore(self, tmp_path):
        """Test that comments in .ignore file are handled correctly"""
        # Create some project files
        (tmp_path / "project1.txt").write_text("")
        (tmp_path / "project2.txt").write_text("")
        (tmp_path / "ignored_project.txt").write_text("")
        
        # Create .ignore file with comments
        ignore_file = tmp_path / ".ignore"
        ignore_file.write_text("# Ignore backup files\nignored_*\n# End of file")
        
        # Load projects
        projects = Projects(tmp_path)
        projects._load_projects()
        
        # Should ignore files matching patterns but not comments
        assert "project1" in projects.projects
        assert "project2" in projects.projects
        assert "ignored_project" not in projects.projects
        assert len(projects.projects) == 2
    
    def test_projects_load_with_whitespace_in_ignore(self, tmp_path):
        """Test that whitespace in .ignore file is handled correctly"""
        # Create some project files
        (tmp_path / "project1.txt").write_text("")
        (tmp_path / "ignored_project.txt").write_text("")
        
        # Create .ignore file with whitespace
        ignore_file = tmp_path / ".ignore"
        ignore_file.write_text("  ignored_*  \n  *.tmp  ")
        
        # Load projects
        projects = Projects(tmp_path)
        projects._load_projects()
        
        # Should ignore files despite whitespace in patterns
        assert "project1" in projects.projects
        assert "ignored_project" not in projects.projects
        assert len(projects.projects) == 1 