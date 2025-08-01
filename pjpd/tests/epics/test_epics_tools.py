"""Unit tests for the epics MCP tools."""

import pytest
from pathlib import Path
from unittest.mock import patch
import tempfile
import shutil

from src.mcp_wrapper import (
    pjpd_list_epics,
    pjpd_add_epic,
    pjpd_update_epic,
    pjpd_mark_epic_done,
    mcp_success,
    mcp_failure,
)
from src.epics.epic import Epic


class TestEpicsTools:
    """Test the epics MCP tools."""

    @pytest.fixture
    def temp_projects_dir(self):
        """Create a temporary projects directory for testing."""
        temp_dir = tempfile.mkdtemp()
        yield Path(temp_dir)
        shutil.rmtree(temp_dir)

    @pytest.fixture
    def mock_epics_manager(self, temp_projects_dir):
        """Create a mock epics manager for testing."""
        with patch("src.mcp_wrapper.epics_manager") as mock_manager:
            yield mock_manager

    # ------------------------------------------------------------------
    # list_epics
    # ------------------------------------------------------------------
    @pytest.mark.asyncio
    async def test_list_epics_success(self, mock_epics_manager):
        """Test successful listing of epics."""
        mock_epics = [
            {
                "id": "AAA111BBB2",
                "score": 100,
                "ideas": ["IDEA1"],
                "projects": ["proj"],
                "description": "High level feature",
            },
            {
                "id": "CCC333DDD4",
                "score": 50,
                "ideas": [],
                "projects": [],
                "description": "Medium feature",
            },
        ]
        mock_epics_manager.list_epics.return_value = mock_epics

        result = await pjpd_list_epics(max_results=10)

        assert result["success"] is True
        assert result["result"]["total_epics"] == 2
        assert result["result"]["epics"] == mock_epics
        mock_epics_manager.list_epics.assert_called_once_with(max_results=10)

    # ------------------------------------------------------------------
    # add_epic
    # ------------------------------------------------------------------
    @pytest.mark.asyncio
    async def test_add_epic_success(self, mock_epics_manager):
        """Test successful addition of an epic."""
        mock_epic = Epic(
            id="AAA111BBB2",
            score=75,
            ideas=["IDEA1"],
            projects=["proj1"],
            description="Epic description",
        )
        mock_epics_manager.add_epic.return_value = mock_epic

        result = await pjpd_add_epic(score=75, description="Epic description", ideas="IDEA1", projects="proj1")

        assert result["success"] is True
        assert result["result"]["id"] == "AAA111BBB2"
        assert result["result"]["score"] == 75
        assert "Epic added successfully" in result["result"]["message"]
        mock_epics_manager.add_epic.assert_called_once()

    # ------------------------------------------------------------------
    # update_epic
    # ------------------------------------------------------------------
    @pytest.mark.asyncio
    async def test_update_epic_success(self, mock_epics_manager):
        """Test successful update of an epic."""
        mock_epic = Epic(
            id="AAA111BBB2",
            score=100,
            ideas=[],
            projects=[],
            description="Updated epic",
        )
        mock_epics_manager.update_epic.return_value = True
        mock_epics_manager.epics = [mock_epic]

        result = await pjpd_update_epic(epic_id="AAA111BBB2", score=100, description="Updated epic")

        assert result["success"] is True
        assert result["result"]["id"] == "AAA111BBB2"
        assert result["result"]["score"] == 100
        assert "updated successfully" in result["result"]["message"]
        mock_epics_manager.update_epic.assert_called_once()

    @pytest.mark.asyncio
    async def test_update_epic_not_found(self, mock_epics_manager):
        """Test updating an epic that doesn't exist."""
        mock_epics_manager.update_epic.return_value = False

        result = await pjpd_update_epic(epic_id="NONEXIST", score=50)

        assert result["success"] is False
        assert "not found" in result["error"]

    # ------------------------------------------------------------------
    # mark_epic_done
    # ------------------------------------------------------------------
    @pytest.mark.asyncio
    async def test_mark_epic_done_success(self, mock_epics_manager):
        """Test successful marking of an epic as done."""
        mock_epics_manager.mark_epic_done.return_value = True

        result = await pjpd_mark_epic_done(epic_id="AAA111BBB2")

        assert result["success"] is True
        assert result["result"]["epic_id"] == "AAA111BBB2"
        assert "marked as done" in result["result"]["message"]
        mock_epics_manager.mark_epic_done.assert_called_once_with("AAA111BBB2")

    @pytest.mark.asyncio
    async def test_mark_epic_done_not_found(self, mock_epics_manager):
        """Test marking an epic as done that doesn't exist."""
        mock_epics_manager.mark_epic_done.return_value = False

        result = await pjpd_mark_epic_done(epic_id="NONEXIST")

        assert result["success"] is False
        assert "not found" in result["error"]
