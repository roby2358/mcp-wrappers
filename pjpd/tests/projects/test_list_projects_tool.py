"""
Unit tests for list_projects MCP tool
Tests the functionality of listing projects and verifying project directory is returned
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
import sys
import os

# Import the MCP wrapper module
from mcp_wrapper import list_projects, mcp_success, mcp_failure


class TestListProjectsTool:
    """Test cases for list_projects MCP tool"""
    
    @pytest.fixture
    def temp_projects_dir(self, tmp_path):
        """Create a temporary projects directory for testing"""
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        return projects_dir
    
    @pytest.fixture
    def mock_projects_manager(self):
        """Mock the projects manager"""
        with patch('mcp_wrapper.projects_manager') as mock_manager:
            mock_manager.projects_dir = Path("/tmp/test-projects")
            yield mock_manager
    
    @pytest.fixture
    def mock_config(self):
        """Mock the config module"""
        with patch('mcp_wrapper.config') as mock_config:
            mock_config.return_value = "~/projects"
            yield mock_config
    
    async def test_list_projects_with_projects(self, temp_projects_dir, mock_projects_manager, mock_config):
        """Test listing projects when projects exist"""
        # Setup mock overview with projects
        mock_overview = {
            "total_projects": 2,
            "total_tasks": 5,
            "total_todo": 3,
            "total_done": 2,
            "projects": [
                {
                    "name": "project-1",
                    "total_tasks": 3,
                    "todo_tasks": 2,
                    "done_tasks": 1,
                    "high_priority_todo": 1,
                    "medium_priority_todo": 1,
                    "low_priority_todo": 0
                },
                {
                    "name": "project-2", 
                    "total_tasks": 2,
                    "todo_tasks": 1,
                    "done_tasks": 1,
                    "high_priority_todo": 0,
                    "medium_priority_todo": 1,
                    "low_priority_todo": 0
                }
            ]
        }
        
        # Setup projects manager mock
        mock_projects_manager.get_overview.return_value = mock_overview
        mock_projects_manager.projects_dir = temp_projects_dir
        
        # Call the tool
        result = await list_projects()
        
        # Verify the result
        assert result["success"] is True
        assert result["result"]["total_projects"] == 2
        assert result["result"]["total_tasks"] == 5
        assert result["result"]["total_todo"] == 3
        assert result["result"]["total_done"] == 2
        # The project_directory should equal the manager's current directory when no path is provided
        assert result["result"]["project_directory"] == str(mock_projects_manager.projects_dir)
        assert len(result["result"]["projects"]) == 2
        
        # Verify projects manager was called correctly
        mock_projects_manager.get_overview.assert_called_once()
    
    async def test_list_projects_no_projects(self, temp_projects_dir, mock_projects_manager, mock_config):
        """Test listing projects when no projects exist"""
        # Setup mock overview with no projects
        mock_overview = {
            "total_projects": 0,
            "total_tasks": 0,
            "total_todo": 0,
            "total_done": 0,
            "projects": []
        }
        
        # Setup projects manager mock
        mock_projects_manager.get_overview.return_value = mock_overview
        mock_projects_manager.projects_dir = temp_projects_dir
        
        # Call the tool
        result = await list_projects()
        
        # Verify the result
        assert result["success"] is True
        assert result["result"]["total_projects"] == 0
        assert result["result"]["total_tasks"] == 0
        assert result["result"]["total_todo"] == 0
        assert result["result"]["total_done"] == 0
        # The project_directory should equal the manager's current directory when no path is provided
        assert result["result"]["project_directory"] == str(mock_projects_manager.projects_dir)
        assert result["result"]["projects"] == []
        
        # Verify projects manager was called correctly
        mock_projects_manager.get_overview.assert_called_once()
    
    async def test_list_projects_with_custom_path(self, temp_projects_dir, mock_projects_manager, mock_config):
        """Test listing projects with a custom path parameter"""
        # Setup mock overview
        mock_overview = {
            "total_projects": 1,
            "total_tasks": 2,
            "total_todo": 1,
            "total_done": 1,
            "projects": [
                {
                    "name": "test-project",
                    "total_tasks": 2,
                    "todo_tasks": 1,
                    "done_tasks": 1,
                    "high_priority_todo": 0,
                    "medium_priority_todo": 1,
                    "low_priority_todo": 0
                }
            ]
        }
        
        # Setup projects manager mock
        mock_projects_manager.get_overview.return_value = mock_overview
        mock_projects_manager.projects_dir = temp_projects_dir
        
        # Call the tool with custom path
        custom_path = "/custom/projects/path"
        result = await list_projects(path=custom_path)
        
        # Verify the result
        assert result["success"] is True
        # The project_directory should be the normalized path (without pjpd suffix)
        # Normalize path separators for cross-platform compatibility
        expected_path = str(Path("/custom/projects/path")).replace('\\', '/')
        actual_path = str(Path(result["result"]["project_directory"])).replace('\\', '/')
        assert actual_path == expected_path
        
        # Verify projects manager was called with the custom path
        mock_projects_manager.set_projects_dir.assert_called_once()
        # Check that the path was set (the actual path object will be different due to Path conversion)
        call_args = mock_projects_manager.set_projects_dir.call_args[0][0]
        # Normalize path separators for cross-platform compatibility
        assert str(call_args).replace('\\', '/') == custom_path.replace('\\', '/')
    
    async def test_list_projects_error_handling(self, mock_projects_manager, mock_config):
        """Test error handling in list_projects"""
        # Setup projects manager to raise an exception
        mock_projects_manager.get_overview.side_effect = Exception("Test error")
        
        # Call the tool
        result = await list_projects()
        
        # Verify the result
        assert result["success"] is False
        assert "Error listing projects" in result["error"]
        assert "Test error" in result["error"]
    
    async def test_list_projects_missing_directory(self, mock_projects_manager, mock_config):
        """Test list_projects when the specified projects directory doesn't exist"""
        # Setup projects manager to raise FileNotFoundError for missing directory
        mock_projects_manager.set_projects_dir.side_effect = FileNotFoundError("Projects directory does not exist: /nonexistent/path")
        
        # Call the tool with a non-existent path
        result = await list_projects(path="/nonexistent/path")
        
        # Verify the result
        assert result["success"] is False
        assert "Error listing projects" in result["error"]
        assert "Projects directory does not exist" in result["error"] 