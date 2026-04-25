"""
Tests for the pjpd_reprioritize_task MCP tool.
"""

import pytest

from src.mcp_wrapper import pjpd_reprioritize_task
from src.projects.projects import Projects


class TestReprioritizeTaskTool:
    @pytest.fixture
    def projects_manager(self, tmp_path, monkeypatch):
        """Create a Projects manager rooted at tmp_path and patch the wrapper to use it."""
        manager = Projects(tmp_path)
        monkeypatch.setattr("src.mcp_wrapper.projects_manager", manager)
        return manager

    @pytest.mark.asyncio
    async def test_reprioritize_single_task(self, projects_manager):
        task = projects_manager.add_task("Do the thing", 10, "task")

        response = await pjpd_reprioritize_task(priority=80, task_ids=[task.id])

        assert response["success"] is True
        assert response["result"]["tasks"][0]["priority"] == 80
        assert response["result"]["tasks"][0]["description"] == "Do the thing"

        reloaded = projects_manager.project.get_task(task.id)
        assert reloaded.priority == 80
        assert reloaded.description == "Do the thing"

    @pytest.mark.asyncio
    async def test_reprioritize_multiple_tasks(self, projects_manager):
        t1 = projects_manager.add_task("First", 10, "a")
        t2 = projects_manager.add_task("Second", 20, "b")

        response = await pjpd_reprioritize_task(priority=55, task_ids=[t1.id, t2.id])

        assert response["success"] is True
        assert {t["id"] for t in response["result"]["tasks"]} == {t1.id, t2.id}
        assert all(t["priority"] == 55 for t in response["result"]["tasks"])

        assert projects_manager.project.get_task(t1.id).priority == 55
        assert projects_manager.project.get_task(t2.id).priority == 55

    @pytest.mark.asyncio
    async def test_missing_id_makes_no_changes(self, projects_manager):
        task = projects_manager.add_task("Real task", 10, "task")

        response = await pjpd_reprioritize_task(
            priority=99, task_ids=[task.id, "task-zzzz"]
        )

        assert response["success"] is False
        assert "task-zzzz" in response["error"]
        assert projects_manager.project.get_task(task.id).priority == 10

    @pytest.mark.asyncio
    async def test_invalid_id_format_rejected(self, projects_manager):
        projects_manager.add_task("Real task", 10, "task")

        response = await pjpd_reprioritize_task(priority=5, task_ids=["not-a-valid-id!"])

        assert response["success"] is False
        assert "Task ID" in response["error"]

    @pytest.mark.asyncio
    async def test_preserves_status_and_description(self, projects_manager):
        task = projects_manager.add_task("Important", 10, "task")
        projects_manager.mark_task_done(task.id)

        response = await pjpd_reprioritize_task(priority=1, task_ids=[task.id])

        assert response["success"] is True
        reloaded = projects_manager.project.get_task(task.id)
        assert reloaded.status == "Done"
        assert reloaded.description == "Important"
        assert reloaded.priority == 1
