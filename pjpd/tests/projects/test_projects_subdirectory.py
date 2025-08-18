"""
Tests for Projects class subdirectory functionality
Tests that projects are properly managed in the pjpd subdirectory
"""

import pytest
from pathlib import Path
from src.projects.projects import Projects


class TestProjectsSubdirectory:
    """Test cases for Projects class subdirectory functionality"""
    
    def test_projects_subdirectory_creation(self, tmp_path):
        """Test that pjpd subdirectory is created when needed"""
        # Create a projects directory without pjpd subdirectory
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        
        # Create Projects instance - should NOT create pjpd subdirectory yet
        projects = Projects(projects_dir)
        
        # Verify pjpd subdirectory was NOT created yet (lazy initialization)
        pjpd_dir = projects_dir / "pjpd"
        assert not pjpd_dir.exists()
        
        # Verify projects_subdir property is set correctly
        assert projects.projects_subdir == pjpd_dir
        
        # Now create a project to trigger directory creation
        projects.create_project("test-project")
        
        # Verify pjpd subdirectory was created
        assert pjpd_dir.exists()
        assert pjpd_dir.is_dir()
    
    def test_projects_subdirectory_exists(self, tmp_path):
        """Test that existing pjpd subdirectory is used correctly"""
        # Create both parent and pjpd directories
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        pjpd_dir = projects_dir / "pjpd"
        pjpd_dir.mkdir()
        
        # Create Projects instance
        projects = Projects(projects_dir)
        
        # Verify pjpd subdirectory is used
        assert projects.projects_subdir == pjpd_dir
        assert pjpd_dir.exists()
    
    def test_projects_subdirectory_file_operations(self, tmp_path):
        """Test that project files are created in the pjpd subdirectory"""
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        
        projects = Projects(projects_dir)
        
        # Create a project
        project = projects.create_project("test-project")
        
        # Verify project file is in pjpd subdirectory
        expected_file = projects.projects_subdir / "test-project.txt"
        assert expected_file.exists()
        assert project.file_path == expected_file
        
        # Verify project is not in parent directory
        parent_file = projects_dir / "test-project.txt"
        assert not parent_file.exists()
    
    def test_projects_subdirectory_listing(self, tmp_path):
        """Test that project listing shows correct subdirectory paths"""
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        
        projects = Projects(projects_dir)
        
        # Create some projects
        projects.create_project("project1")
        projects.create_project("project2")
        
        # List projects
        projects_list = projects.list_projects()
        
        # Verify all projects have correct relative paths
        for project_info in projects_list:
            assert project_info["file_path"] in ["project1.txt", "project2.txt"]
            # Verify the file actually exists in the subdirectory
            file_path = projects.projects_subdir / project_info["file_path"]
            assert file_path.exists()
    
    def test_projects_subdirectory_ignore_list(self, tmp_path):
        """Test that ignore list works correctly with subdirectory"""
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        
        projects = Projects(projects_dir)
        
        # First create a project to ensure the subdirectory exists
        projects.create_project("dummy-project")
        
        # Create some project files in the subdirectory
        (projects.projects_subdir / "project1.txt").write_text("")
        (projects.projects_subdir / "project2.txt").write_text("")
        (projects.projects_subdir / "backup_project.txt").write_text("")
        
        # Create ignore file in the subdirectory
        ignore_file = projects.projects_subdir / "pjpdignore"
        ignore_file.write_text("backup_*")
        
        # Refresh projects
        projects.refresh_projects()
        
        # Should only load non-ignored projects (plus our dummy project)
        assert "project1" in projects.projects
        assert "project2" in projects.projects
        assert "backup_project" not in projects.projects
        assert "dummy-project" in projects.projects
        assert len(projects.projects) == 3
    
    def test_projects_subdirectory_parent_directory_validation(self, tmp_path):
        """Test that Projects handles non-existent directory gracefully"""
        # Try to create Projects with non-existent directory
        non_existent_dir = tmp_path / "nonexistent"
        
        # Should not raise an error, just not be present
        projects = Projects(non_existent_dir)
        assert not projects.present
    
    def test_projects_subdirectory_parent_not_directory(self, tmp_path):
        """Test that Projects handles file path gracefully"""
        # Create a file instead of directory
        file_path = tmp_path / "not_a_directory"
        file_path.write_text("this is a file")
        
        # Should not raise an error, just not be present
        projects = Projects(file_path)
        assert not projects.present
    
    def test_projects_subdirectory_set_projects_dir(self, tmp_path):
        """Test that set_projects_dir updates subdirectory correctly"""
        # Create initial projects directory
        projects_dir1 = tmp_path / "projects1"
        projects_dir1.mkdir()
        
        projects = Projects(projects_dir1)
        original_subdir = projects.projects_subdir
        
        # Create second projects directory
        projects_dir2 = tmp_path / "projects2"
        projects_dir2.mkdir()
        
        # Change projects directory
        projects.set_projects_dir(projects_dir2)
        
        # Verify subdirectory was updated
        new_subdir = projects_dir2 / "pjpd"
        assert projects.projects_subdir == new_subdir
        
        # The new subdirectory should not exist yet (lazy initialization)
        assert not new_subdir.exists()
        
        # Create a project to trigger directory creation
        projects.create_project("test-project")
        
        # Now the subdirectory should exist
        assert new_subdir.exists()
        assert new_subdir.is_dir()
        
        # Verify original subdirectory is unchanged (it was never created due to lazy initialization)
        assert not original_subdir.exists()
    
    def test_projects_subdirectory_refresh_clears_cache(self, tmp_path):
        """Test that refresh_projects clears and reloads from subdirectory"""
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        
        projects = Projects(projects_dir)
        
        # Create a project
        projects.create_project("test-project")
        assert "test-project" in projects.projects
        
        # Manually add a file to the subdirectory
        new_project_file = projects.projects_subdir / "new-project.txt"
        new_project_file.write_text("")
        
        # Refresh should pick up the new project
        projects.refresh_projects()
        assert "new-project" in projects.projects
        assert len(projects.projects) == 2
    
    def test_projects_subdirectory_relative_paths(self, tmp_path):
        """Test that relative paths in list_projects are correct"""
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        
        projects = Projects(projects_dir)
        
        # Create a project
        projects.create_project("test-project")
        
        # List projects
        projects_list = projects.list_projects()
        
        # Verify relative path is correct
        assert len(projects_list) == 1
        project_info = projects_list[0]
        assert project_info["file_path"] == "test-project.txt"
        
        # Verify the relative path is relative to the subdirectory
        full_path = projects.projects_subdir / project_info["file_path"]
        assert full_path.exists()
    
    def test_projects_subdirectory_get_project_sanitization(self, tmp_path):
        """Test that get_project works with sanitized names in subdirectory"""
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        
        projects = Projects(projects_dir)
        
        # Create a project with special characters
        project = projects.create_project("My Project!")
        
        # Should be able to get the project using original name
        retrieved_project = projects.get_project("My Project!")
        assert retrieved_project.name == project.name
        assert retrieved_project.file_path == project.file_path
        
        # Should also work with sanitized name
        sanitized_name = projects._sanitize_name("My Project!")
        retrieved_project2 = projects.get_project(sanitized_name)
        assert retrieved_project2.name == project.name
        assert retrieved_project2.file_path == project.file_path
        
        # Verify file exists in subdirectory with sanitized name
        expected_file = projects.projects_subdir / f"{sanitized_name}.txt"
        assert expected_file.exists()
        
        # Verify the sanitized name is correct (spaces become underscores, lowercase)
        assert sanitized_name == "my_project!"
