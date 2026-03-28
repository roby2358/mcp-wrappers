"""
Tests for task Created/Updated timestamps.
"""

import pytest
from pathlib import Path

from src.projects.projects import Projects
from src.projects.task import Task


class TestTaskTimestamps:
    """Verify Created and Updated timestamps on tasks."""

    @pytest.fixture
    def projects_manager(self, tmp_path):
        return Projects(tmp_path)

    def test_new_task_has_timestamps(self, projects_manager):
        """A newly created task has both created and updated set."""
        task = projects_manager.add_task("Test task", 50, "test")

        assert task.created is not None
        assert task.updated is not None
        assert task.created == task.updated

    def test_updated_task_refreshes_updated(self, projects_manager):
        """Updating a task refreshes updated but preserves created."""
        task = projects_manager.add_task("Test task", 50, "test")
        original_created = task.created

        updated = projects_manager.update_task(task.id, "Changed", None, None)

        assert updated.created == original_created
        assert updated.updated is not None
        assert updated.updated >= original_created

    def test_timestamps_persist_to_file(self, projects_manager):
        """Timestamps are written to the file and can be read back."""
        task = projects_manager.add_task("Test task", 50, "test")

        content = projects_manager.tasks_file.read_text(encoding="utf-8")
        assert f"Created: {task.created}" in content
        assert f"Updated: {task.updated}" in content

    def test_timestamps_roundtrip(self, projects_manager):
        """Timestamps survive a write-then-read cycle."""
        task = projects_manager.add_task("Test task", 50, "test")
        original_created = task.created

        reloaded = projects_manager.project.get_task(task.id)

        assert reloaded.created == original_created
        assert reloaded.updated == task.updated

    def test_legacy_task_without_timestamps_parses(self):
        """A task record without timestamps parses cleanly (backward compat)."""
        text = "Priority:   50\nStatus: ToDo\nID: test-abcd\nDo the thing"
        task = Task.from_text(text)

        assert task is not None
        assert task.id == "test-abcd"
        assert task.description == "Do the thing"
        assert task.created is None
        assert task.updated is None

    def test_legacy_task_gets_timestamps_on_update(self, projects_manager):
        """A legacy task without timestamps gets both set on first update."""
        # Write a legacy record directly (no timestamps)
        projects_manager._ensure_project()
        projects_manager.tasks_file.write_text(
            "Priority:   50\nStatus: ToDo\nID: old-abcd\nLegacy task",
            encoding="utf-8",
        )

        updated = projects_manager.update_task("old-abcd", "Updated legacy", None, None)

        assert updated.created is not None
        assert updated.updated is not None
        assert updated.created == updated.updated

    def test_timestamps_in_to_dict(self, projects_manager):
        """Timestamps appear in the API dict representation."""
        task = projects_manager.add_task("Test task", 50, "test")
        d = task.to_dict()

        assert "created" in d
        assert "updated" in d
        assert d["created"] == task.created

    def test_legacy_task_to_dict_omits_timestamps(self):
        """A legacy task without timestamps omits them from to_dict."""
        text = "Priority:   50\nStatus: ToDo\nID: test-abcd\nDo the thing"
        task = Task.from_text(text)
        d = task.to_dict()

        assert "created" not in d
        assert "updated" not in d
