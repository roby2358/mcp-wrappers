"""
Tests that marking tasks done preserves priority and sorts correctly.
"""

import pytest
from pathlib import Path

from src.projects.projects import Projects


class TestMarkDonePreservesPriority:
    """Verify mark_done preserves priority and sort order is ToDo-first."""

    @pytest.fixture
    def projects_manager(self, tmp_path):
        return Projects(tmp_path)

    def test_mark_done_preserves_priority(self, projects_manager):
        """Marking a task done should not change its priority."""
        task = projects_manager.add_task("Important thing", 80, "bug")
        projects_manager.mark_task_done(task.id)

        reloaded = projects_manager.project.get_task(task.id)
        assert reloaded.status == "Done"
        assert reloaded.priority == 80

    def test_todo_tasks_sort_before_done(self, projects_manager):
        """ToDo tasks appear before Done tasks in the file."""
        low_todo = projects_manager.add_task("Low todo", 10, "lo")
        high_done = projects_manager.add_task("High done", 90, "hi")
        projects_manager.mark_task_done(high_done.id)

        tasks = projects_manager.project.tasks
        assert tasks[0].status == "ToDo"
        assert tasks[0].id == low_todo.id
        assert tasks[1].status == "Done"
        assert tasks[1].id == high_done.id

    def test_sort_within_same_status(self, projects_manager):
        """Within the same status group, higher priority comes first."""
        low = projects_manager.add_task("Low", 10, "lo")
        high = projects_manager.add_task("High", 90, "hi")

        tasks = projects_manager.project.tasks
        assert tasks[0].priority == 90
        assert tasks[1].priority == 10

    def test_done_tasks_retain_relative_priority_order(self, projects_manager):
        """Done tasks are sorted by priority among themselves."""
        t1 = projects_manager.add_task("Medium done", 50, "med")
        t2 = projects_manager.add_task("High done", 90, "hi")
        projects_manager.mark_task_done(t1.id)
        projects_manager.mark_task_done(t2.id)

        tasks = projects_manager.project.tasks
        assert tasks[0].priority == 90
        assert tasks[1].priority == 50
