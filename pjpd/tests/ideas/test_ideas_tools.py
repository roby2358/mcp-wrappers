"""
Unit tests for the ideas MCP tools.
"""

import pytest
from pathlib import Path
from unittest.mock import Mock, patch
import tempfile
import shutil

from src.mcp_wrapper import (
    pjpd_list_ideas,
    pjpd_put_idea,
    pjpd_mark_idea_done,
    mcp_success,
    mcp_failure
)
from src.ideas.idea import Idea


class TestIdeasTools:
    """Test the ideas MCP tools."""

    @pytest.fixture
    def temp_projects_dir(self):
        """Create a temporary projects directory for testing."""
        temp_dir = tempfile.mkdtemp()
        yield Path(temp_dir)
        shutil.rmtree(temp_dir)

    @pytest.fixture
    def mock_ideas_manager(self, temp_projects_dir):
        """Create a mock ideas manager for testing."""
        with patch('src.mcp_wrapper.ideas_manager') as mock_manager:
            yield mock_manager

    async def test_list_ideas_success(self, mock_ideas_manager):
        """Test successful listing of ideas."""
        mock_ideas = [
            {"id": "idea-1234", "score": 100, "description": "High priority idea"},
            {"id": "idea-5678", "score": 50, "description": "Medium priority idea"},
        ]
        mock_ideas_manager.list_ideas.return_value = mock_ideas

        result = await pjpd_list_ideas(count=10)

        assert result["success"] is True
        assert result["result"]["total_ideas"] == 2
        assert result["result"]["ideas"] == mock_ideas
        assert "Retrieved 2 ideas" in result["result"]["message"]
        mock_ideas_manager.list_ideas.assert_called_once_with(count=10)

    async def test_list_ideas_default_count(self, mock_ideas_manager):
        """Test listing ideas with default count parameter."""
        mock_ideas = [{"id": "idea-1234", "score": 100, "description": "Test idea"}]
        mock_ideas_manager.list_ideas.return_value = mock_ideas

        result = await pjpd_list_ideas()

        assert result["success"] is True
        assert result["result"]["total_ideas"] == 1
        mock_ideas_manager.list_ideas.assert_called_once_with(count=20)

    async def test_list_ideas_error(self, mock_ideas_manager):
        """Test error handling in list_ideas."""
        mock_ideas_manager.list_ideas.side_effect = Exception("Test error")

        result = await pjpd_list_ideas()

        assert result["success"] is False
        assert "Error listing ideas" in result["error"]

    async def test_put_idea_create(self, mock_ideas_manager):
        """Test creating a new idea via put_idea with tag."""
        mock_idea = Idea(id="idea-1234", tag="idea", score=75, description="Test idea")
        mock_ideas_manager.add_idea.return_value = mock_idea

        result = await pjpd_put_idea(score=75, description="Test idea", tag="idea")

        assert result["success"] is True
        assert result["result"]["id"] == "idea-1234"
        assert result["result"]["score"] == 75
        assert "created successfully" in result["result"]["message"]
        mock_ideas_manager.add_idea.assert_called_once_with("Test idea", 75, "idea")

    async def test_put_idea_update(self, mock_ideas_manager):
        """Test updating an existing idea via put_idea with id."""
        mock_idea = Idea(id="idea-a2c4", tag="idea", score=100, description="Updated idea")
        mock_ideas_manager.update_idea.return_value = True
        mock_ideas_manager.ideas = [mock_idea]

        result = await pjpd_put_idea(
            score=100, description="Updated idea", id="idea-a2c4"
        )

        assert result["success"] is True
        assert result["result"]["id"] == "idea-a2c4"
        assert result["result"]["score"] == 100
        assert "updated successfully" in result["result"]["message"]
        mock_ideas_manager.update_idea.assert_called_once_with(
            "idea-a2c4", "Updated idea", 100
        )

    async def test_put_idea_update_not_found(self, mock_ideas_manager):
        """Test updating an idea that doesn't exist."""
        mock_ideas_manager.update_idea.return_value = False

        result = await pjpd_put_idea(score=50, description="X", id="idea-9999")

        assert result["success"] is False
        assert "not found" in result["error"]

    async def test_put_idea_error(self, mock_ideas_manager):
        """Test error handling in put_idea."""
        mock_ideas_manager.add_idea.side_effect = Exception("Test error")

        result = await pjpd_put_idea(score=50, description="Test idea", tag="idea")

        assert result["success"] is False
        assert "Error putting idea" in result["error"]

    async def test_mark_idea_done_success(self, mock_ideas_manager):
        """Test successfully marking an idea as done."""
        mock_idea = Idea(id="idea-a2c4", tag="idea", score=50, description="Some idea")
        mock_ideas_manager.ideas = [mock_idea]
        mock_ideas_manager.mark_idea_done.return_value = True

        result = await pjpd_mark_idea_done(idea_ids=["idea-a2c4"])

        assert result["success"] is True
        assert result["result"]["idea_ids"] == ["idea-a2c4"]
        assert "marked" in result["result"]["message"].lower()
        mock_ideas_manager.mark_idea_done.assert_called_once_with("idea-a2c4")

    async def test_mark_idea_done_not_found(self, mock_ideas_manager):
        """Test marking an idea as done that doesn't exist."""
        mock_ideas_manager.ideas = []

        result = await pjpd_mark_idea_done(idea_ids=["idea-9999"])

        assert result["success"] is False
        assert "not found" in result["error"].lower()

    async def test_mark_idea_done_error(self, mock_ideas_manager):
        """Test error handling in mark_idea_done."""
        mock_idea = Idea(id="idea-1234", tag="idea", score=50, description="Some idea")
        mock_ideas_manager.ideas = [mock_idea]
        mock_ideas_manager.mark_idea_done.side_effect = Exception("Test error")

        result = await pjpd_mark_idea_done(idea_ids=["idea-1234"])

        assert result["success"] is False
        assert "Error marking ideas as done" in result["error"]


class TestMCPResponseHelpers:
    """Test the MCP response helper functions."""

    def test_mcp_success(self):
        result = {"test": "data"}
        response = mcp_success(result)

        assert response["success"] is True
        assert response["result"] == result
        assert response["error"] == ""

    def test_mcp_failure(self):
        error_msg = "Test error message"
        response = mcp_failure(error_msg)

        assert response["success"] is False
        assert response["result"] == ""
        assert response["error"] == error_msg
