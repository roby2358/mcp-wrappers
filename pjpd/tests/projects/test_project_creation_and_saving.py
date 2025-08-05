"""
Unit tests for project creation and task saving
Tests that projects are properly created and tasks are saved to files
"""

import pytest
from pathlib import Path
import tempfile
import shutil

from src.projects.projects import Projects
from src.projects.project import Project


class TestProjectCreationAndSaving:
    """Test cases for project creation and task saving functionality"""
    
    @pytest.fixture
    def temp_projects_dir(self, tmp_path):
        """Create a temporary projects directory for testing"""
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        return projects_dir
    
    def test_create_project_creates_file(self, temp_projects_dir):
        """Test that creating a project creates the actual file on disk"""
        projects = Projects(temp_projects_dir)
        
        # Create a new project
        project = projects.create_project("test-project")
        
        # Verify the file was created
        expected_file = temp_projects_dir / "test-project.txt"
        assert expected_file.exists()
        assert project.file_path == expected_file
        
        # Verify the project is in the projects cache
        assert "test-project" in projects.projects
        # The project retrieved from cache should have the same file path and name
        cached_project = projects.projects["test-project"]
        assert cached_project.file_path == project.file_path
        assert cached_project.name == project.name
    
    def test_add_task_to_new_project_creates_file(self, temp_projects_dir):
        """Test that adding a task to a new project creates the project file"""
        projects = Projects(temp_projects_dir)
        
        # Create the project first
        projects.create_project("test-project")
        # Add a task to the existing project
        task = projects.add_task("test-project", "Test task", 5)
        
        # Verify the project file was created
        expected_file = temp_projects_dir / "test-project.txt"
        assert expected_file.exists()
        
        # Verify the task was added
        assert task is not None
        assert task.description == "Test task"
        assert task.priority == 5
        assert task.status == "ToDo"
        
        # Verify the project is in the cache
        assert "test-project" in projects.projects
    
    def test_add_task_saves_to_file(self, temp_projects_dir):
        """Test that adding a task saves it to the project file"""
        projects = Projects(temp_projects_dir)
        
        # Create the project and then add a task
        projects.create_project("test-project")
        task = projects.add_task("test-project", "Test task", 10)
        
        # Verify the file contains the task
        project_file = temp_projects_dir / "test-project.txt"
        content = project_file.read_text(encoding="utf-8")
        
        # Check that the task format is correct
        assert "ID: " in content
        assert "Priority:   10" in content
        assert "Status: ToDo" in content
        assert "Test task" in content
    
    def test_task_format_is_correct(self, temp_projects_dir):
        """Test that tasks are saved in the correct format (Priority first, Status second, ID third, Description last)"""
        projects = Projects(temp_projects_dir)
        
        projects.create_project("test-project")
        task = projects.add_task("test-project", "Test task", 100)
        
        # Read the file content
        project_file = temp_projects_dir / "test-project.txt"
        content = project_file.read_text(encoding="utf-8")
        
        # Split into lines and check the order
        lines = content.strip().split('\n')
        
        # Should have at least 4 lines: Priority, Status, ID, Description
        assert len(lines) >= 4
        
        # Check the order: Priority first, then Status, then Tag, then ID, then Description last
        assert lines[0].startswith("Priority: ")
        assert lines[1].startswith("Status: ")
        assert lines[2].startswith("ID: ")
        
        # The description should be on the last line
        description = lines[3]
        assert "Test task" in description
    
    def test_multiple_tasks_are_saved(self, temp_projects_dir):
        """Test that multiple tasks are saved correctly"""
        projects = Projects(temp_projects_dir)
        
        projects.create_project("test-project")
        task1 = projects.add_task("test-project", "First task", 5)
        task2 = projects.add_task("test-project", "Second task", 10)
        
        # Read the file content
        project_file = temp_projects_dir / "test-project.txt"
        content = project_file.read_text(encoding="utf-8")
        
        # Should contain both tasks separated by ---
        assert "First task" in content
        assert "Second task" in content
        assert "---" in content
        
        # Verify both tasks are in the project
        project = projects.get_project("test-project")
        assert len(project.tasks) == 2
    
    def test_empty_project_file_is_created(self, temp_projects_dir):
        """Test that creating an empty project creates an empty file"""
        projects = Projects(temp_projects_dir)
        
        # Create an empty project
        project = projects.create_project("empty-project")
        
        # Verify the file exists but is empty
        project_file = temp_projects_dir / "empty-project.txt"
        assert project_file.exists()
        
        # The file should be empty (no tasks)
        content = project_file.read_text(encoding="utf-8")
        assert content == ""
    
    def test_project_with_special_characters(self, temp_projects_dir):
        """Test that project names with special characters are handled correctly"""
        projects = Projects(temp_projects_dir)
        
        # Create a project with special characters
        project = projects.create_project("My Project! @#$%")
        
        # Verify the file was created with sanitized name
        expected_file = temp_projects_dir / "my_project!_@#$%.txt"
        assert expected_file.exists()
        assert project.file_path == expected_file 