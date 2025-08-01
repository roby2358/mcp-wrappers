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
    pjpd_add_idea,
    pjpd_update_idea,
    pjpd_remove_idea,
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
        # Mock ideas data
        mock_ideas = [
            {"id": "ABC123DEF4", "score": 100, "description": "High priority idea"},
            {"id": "XYZ789GHI0", "score": 50, "description": "Medium priority idea"},
        ]
        mock_ideas_manager.list_ideas.return_value = mock_ideas

        result = await pjpd_list_ideas(max_results=10)

        assert result["success"] is True
        assert result["result"]["total_ideas"] == 2
        assert result["result"]["ideas"] == mock_ideas
        assert "Retrieved 2 ideas" in result["result"]["message"]
        mock_ideas_manager.list_ideas.assert_called_once_with(max_results=10)

    async def test_list_ideas_no_max_results(self, mock_ideas_manager):
        """Test listing ideas without max_results parameter."""
        mock_ideas = [{"id": "ABC123DEF4", "score": 100, "description": "Test idea"}]
        mock_ideas_manager.list_ideas.return_value = mock_ideas

        result = await pjpd_list_ideas()

        assert result["success"] is True
        assert result["result"]["total_ideas"] == 1
        mock_ideas_manager.list_ideas.assert_called_once_with(max_results=None)

    async def test_list_ideas_error(self, mock_ideas_manager):
        """Test error handling in list_ideas."""
        mock_ideas_manager.list_ideas.side_effect = Exception("Test error")

        result = await pjpd_list_ideas()

        assert result["success"] is False
        assert "Error listing ideas" in result["error"]

    async def test_add_idea_success(self, mock_ideas_manager):
        """Test successful addition of an idea."""
        mock_idea = Idea(id="ABC123DEF4", score=75, description="Test idea")
        mock_ideas_manager.add_idea.return_value = mock_idea

        result = await pjpd_add_idea(score=75, description="Test idea")

        assert result["success"] is True
        assert result["result"]["id"] == "ABC123DEF4"
        assert result["result"]["score"] == 75
        assert result["result"]["description"] == "Test idea"
        assert "Idea added successfully" in result["result"]["message"]
        mock_ideas_manager.add_idea.assert_called_once_with("Test idea", 75)

    async def test_add_idea_error(self, mock_ideas_manager):
        """Test error handling in add_idea."""
        mock_ideas_manager.add_idea.side_effect = Exception("Test error")

        result = await pjpd_add_idea(score=50, description="Test idea")

        assert result["success"] is False
        assert "Error adding idea" in result["error"]

    async def test_update_idea_success(self, mock_ideas_manager):
        """Test successful update of an idea."""
        mock_idea = Idea(id="ABC123DEF4", score=100, description="Updated idea")
        mock_ideas_manager.update_idea.return_value = True
        mock_ideas_manager.ideas = [mock_idea]

        result = await pjpd_update_idea(
            idea_id="ABC123DEF4", 
            score=100, 
            description="Updated idea"
        )

        assert result["success"] is True
        assert result["result"]["id"] == "ABC123DEF4"
        assert result["result"]["score"] == 100
        assert result["result"]["description"] == "Updated idea"
        assert "updated successfully" in result["result"]["message"]
        mock_ideas_manager.update_idea.assert_called_once_with(
            "ABC123DEF4", "Updated idea", 100
        )

    async def test_update_idea_not_found(self, mock_ideas_manager):
        """Test updating an idea that doesn't exist."""
        mock_ideas_manager.update_idea.return_value = False

        result = await pjpd_update_idea(idea_id="NONEXIST", score=50)

        assert result["success"] is False
        assert "not found" in result["error"]

    async def test_update_idea_error(self, mock_ideas_manager):
        """Test error handling in update_idea."""
        mock_ideas_manager.update_idea.side_effect = Exception("Test error")

        result = await pjpd_update_idea(idea_id="ABC123DEF4", score=50)

        assert result["success"] is False
        assert "Error updating idea" in result["error"]

    async def test_remove_idea_success(self, mock_ideas_manager):
        """Test successful removal of an idea."""
        mock_ideas_manager.remove_idea.return_value = True

        result = await pjpd_remove_idea(idea_id="ABC123DEF4")

        assert result["success"] is True
        assert result["result"]["idea_id"] == "ABC123DEF4"
        assert "removed successfully" in result["result"]["message"]
        mock_ideas_manager.remove_idea.assert_called_once_with("ABC123DEF4")

    async def test_remove_idea_not_found(self, mock_ideas_manager):
        """Test removing an idea that doesn't exist."""
        mock_ideas_manager.remove_idea.return_value = False

        result = await pjpd_remove_idea(idea_id="NONEXIST")

        assert result["success"] is False
        assert "not found" in result["error"]

    async def test_remove_idea_error(self, mock_ideas_manager):
        """Test error handling in remove_idea."""
        mock_ideas_manager.remove_idea.side_effect = Exception("Test error")

        result = await pjpd_remove_idea(idea_id="ABC123DEF4")

        assert result["success"] is False
        assert "Error removing idea" in result["error"]


class TestMCPResponseHelpers:
    """Test the MCP response helper functions."""

    def test_mcp_success(self):
        """Test successful MCP response creation."""
        result = {"test": "data"}
        response = mcp_success(result)
        
        assert response["success"] is True
        assert response["result"] == result
        assert response["error"] == ""

    def test_mcp_failure(self):
        """Test failed MCP response creation."""
        error_msg = "Test error message"
        response = mcp_failure(error_msg)
        
        assert response["success"] is False
        assert response["result"] == ""
        assert response["error"] == error_msg 