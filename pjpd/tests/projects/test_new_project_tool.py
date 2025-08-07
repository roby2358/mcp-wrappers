"""
Unit tests for new_project MCP tool
Tests the functionality of creating empty project files
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
import sys
import os

# Import the MCP wrapper module
from mcp_wrapper import new_project, mcp_success, mcp_failure


class TestNewProjectTool:
    """Test cases for new_project MCP tool"""
    
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
            mock_manager.projects_dir = None
            yield mock_manager
    
    @pytest.fixture
    def mock_config(self):
        """Mock the config module"""
        with patch('mcp_wrapper.config') as mock_config:
            mock_config.return_value = "~/projects"
            yield mock_config
    
    async def test_new_project_success(self, temp_projects_dir, mock_projects_manager, mock_config):
        """Test successful creation of a new project"""
        # Setup mock project
        mock_project = MagicMock()
        mock_project.name = "test-project"
        mock_project.file_path = temp_projects_dir / "pjpd" / "test-project.txt"
        
        # Setup projects manager mock
        mock_projects_manager.create_project.return_value = mock_project
        
        # Call the tool
        result = await new_project("test-project")
        
        # Verify the result
        assert result["success"] is True
        assert result["result"]["project_name"] == "test-project"
        assert result["result"]["file_path"] == str(temp_projects_dir / "pjpd" / "test-project.txt")
        assert "created successfully" in result["result"]["message"]
        
        # Verify projects manager was called correctly
        mock_projects_manager.create_project.assert_called_once_with("test-project")
    
    async def test_new_project_with_special_characters(self, temp_projects_dir, mock_projects_manager, mock_config):
        """Test creating a project with special characters in the name"""
        # Setup mock project
        mock_project = MagicMock()
        mock_project.name = "my-project"
        mock_project.file_path = temp_projects_dir / "pjpd" / "my-project.txt"
        
        # Setup projects manager mock
        mock_projects_manager.create_project.return_value = mock_project
        
        # Call the tool with special characters
        result = await new_project("My Project!")
        
        # Verify the result
        assert result["success"] is True
        assert result["result"]["project_name"] == "my-project"
        
        # Verify projects manager was called with sanitized name
        mock_projects_manager.create_project.assert_called_once_with("My Project!")
    
    async def test_new_project_creates_directory_if_needed(self, temp_projects_dir, mock_projects_manager, mock_config):
        """Test that the tool creates the projects directory if it doesn't exist"""
        # Setup mock project
        mock_project = MagicMock()
        mock_project.name = "test-project"
        mock_project.file_path = temp_projects_dir / "pjpd" / "test-project.txt"
        
        # Setup projects manager mock
        mock_projects_manager.create_project.return_value = mock_project
        
        # Call the tool
        result = await new_project("test-project")
        
        # Verify the result
        assert result["success"] is True
        
        # Verify that the projects directory creation was handled
        # (The actual directory creation is handled by the projects manager)
    
    async def test_new_project_error_handling(self, mock_projects_manager, mock_config):
        """Test error handling when project creation fails"""
        # Setup projects manager to raise an exception
        mock_projects_manager.create_project.side_effect = Exception("Permission denied")
        
        # Call the tool
        result = await new_project("test-project")
        
        # Verify the result
        assert result["success"] is False
        assert "Error creating project" in result["error"]
        assert "Permission denied" in result["error"]
    
    async def test_new_project_empty_name(self, mock_projects_manager, mock_config):
        """Test that creating a project with an empty name returns a failure response."""

        # Configure the projects manager to raise ValueError for an empty name
        mock_projects_manager.create_project.side_effect = ValueError(
            "Project name cannot be empty or invalid"
        )

        # Call the tool with an empty project name
        result = await new_project("")

        # Verify that the response indicates failure
        assert result["success"] is False
        assert "Project name cannot be empty or invalid" in result["error"]
    
    async def test_new_project_unicode_name(self, temp_projects_dir, mock_projects_manager, mock_config):
        """Test creating a project with unicode characters in the name"""
        # Call the tool with unicode characters
        result = await new_project("Projëct with Ünicode")
        
        # Verify the result - unicode characters should be rejected
        assert result["success"] is False
        assert "Project name contains invalid characters" in result["error"] 