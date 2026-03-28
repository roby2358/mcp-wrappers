"""
Test the update_task functionality
"""

import pytest
from pathlib import Path

from src.projects.projects import Projects


class TestUpdateTaskTool:
    """Test the update_task functionality"""

    @pytest.fixture
    def projects_manager(self, tmp_path):
        """Create a projects manager with a temporary directory"""
        return Projects(tmp_path)

    def test_update_task_description(self, projects_manager):
        task = projects_manager.add_task("Original description", 2, "task")
        updated_task = projects_manager.update_task(task.id, "Updated description", None, None)

        assert updated_task is not None
        assert updated_task.description == "Updated description"
        assert updated_task.priority == 2
        assert updated_task.status == "ToDo"

    def test_update_task_priority(self, projects_manager):
        task = projects_manager.add_task("Test task", 2, "task")
        updated_task = projects_manager.update_task(task.id, None, 5, None)

        assert updated_task is not None
        assert updated_task.priority == 5
        assert updated_task.description == "Test task"
        assert updated_task.status == "ToDo"

    def test_update_task_status(self, projects_manager):
        task = projects_manager.add_task("Test task", 2, "task")
        updated_task = projects_manager.update_task(task.id, None, None, "Done")

        assert updated_task is not None
        assert updated_task.status == "Done"
        assert updated_task.description == "Test task"
        assert updated_task.priority == 2

    def test_update_task_multiple_fields(self, projects_manager):
        task = projects_manager.add_task("Original task", 2, "task")
        updated_task = projects_manager.update_task(task.id, "Updated task", 4, "Done")

        assert updated_task is not None
        assert updated_task.description == "Updated task"
        assert updated_task.priority == 4
        assert updated_task.status == "Done"

    def test_update_nonexistent_task(self, projects_manager):
        projects_manager.add_task("A task", 2, "task")
        updated_task = projects_manager.update_task("task-9999", "New description", None, None)
        assert updated_task is None

    def test_update_task_persistence(self, projects_manager):
        task = projects_manager.add_task("Original task", 2, "task")
        projects_manager.update_task(task.id, "Updated task", 5, "Done")

        # Reload from disk
        new_manager = Projects(projects_manager.project_dir)
        updated_task = new_manager.get_task(task.id)

        assert updated_task is not None
        assert updated_task.description == "Updated task"
        assert updated_task.priority == 5
        assert updated_task.status == "Done"

    def test_update_task_partial_updates(self, projects_manager):
        task = projects_manager.add_task("Test task", 3, "task")

        updated_task = projects_manager.update_task(task.id, "New description", None, None)
        assert updated_task is not None
        assert updated_task.description == "New description"
        assert updated_task.priority == 3
        assert updated_task.status == "ToDo"

        updated_task = projects_manager.update_task(task.id, None, 1, None)
        assert updated_task is not None
        assert updated_task.description == "New description"
        assert updated_task.priority == 1
        assert updated_task.status == "ToDo"
