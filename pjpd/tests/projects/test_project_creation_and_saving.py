"""
Unit tests for task creation and saving in the single-project model.
"""

import pytest
from pathlib import Path

from src.projects.projects import Projects


class TestProjectCreationAndSaving:
    """Test cases for task creation and saving functionality"""

    @pytest.fixture
    def projects_manager(self, tmp_path):
        return Projects(tmp_path)

    def test_add_task_creates_pjpd_directory(self, projects_manager):
        """Adding a task auto-creates the pjpd directory and tasks.txt"""
        task = projects_manager.add_task("Test task", 5, "task")

        assert projects_manager.tasks_file.exists()
        assert task is not None
        assert task.description == "Test task"
        assert task.priority == 5
        assert task.status == "ToDo"

    def test_add_task_saves_to_file(self, projects_manager):
        projects_manager.add_task("Test task", 10, "task")

        content = projects_manager.tasks_file.read_text(encoding="utf-8")
        assert "ID: " in content
        assert "Priority:   10" in content
        assert "Status: ToDo" in content
        assert "Test task" in content

    def test_task_format_is_correct(self, projects_manager):
        """Tasks are saved as Priority, Status, ID, Created, Updated, Description"""
        projects_manager.add_task("Test task", 100, "task")

        content = projects_manager.tasks_file.read_text(encoding="utf-8")
        lines = content.strip().split('\n')

        assert len(lines) >= 6
        assert lines[0].startswith("Priority: ")
        assert lines[1].startswith("Status: ")
        assert lines[2].startswith("ID: ")
        assert lines[3].startswith("Created: ")
        assert lines[4].startswith("Updated: ")
        assert "Test task" in lines[5]

    def test_multiple_tasks_are_saved(self, projects_manager):
        projects_manager.add_task("First task", 5, "task")
        projects_manager.add_task("Second task", 10, "task")

        content = projects_manager.tasks_file.read_text(encoding="utf-8")
        assert "First task" in content
        assert "Second task" in content
        assert "----" in content

        assert len(projects_manager.project.tasks) == 2

    def test_project_file_path(self, projects_manager):
        """project_file returns the full path to tasks.txt"""
        expected = projects_manager.project_dir / "pjpd" / "tasks.txt"
        assert projects_manager.project_file == expected
