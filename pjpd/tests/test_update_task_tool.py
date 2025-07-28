"""
Test the update_task MCP tool
"""

import pytest
from pathlib import Path
import tempfile
import shutil

from src.projects.projects import Projects
from src.projects.task import Task


class TestUpdateTaskTool:
    """Test the update_task tool functionality"""
    
    @pytest.fixture
    def temp_projects_dir(self):
        """Create a temporary directory for testing"""
        temp_dir = tempfile.mkdtemp()
        yield Path(temp_dir)
        shutil.rmtree(temp_dir)
    
    @pytest.fixture
    def projects_manager(self, temp_projects_dir):
        """Create a projects manager with a temporary directory"""
        return Projects(temp_projects_dir)
    
    def test_update_task_description(self, projects_manager):
        """Test updating a task's description"""
        # Create a project and add a task
        project = projects_manager.create_project("test-project")
        task = projects_manager.add_task("test-project", "Original description", 2)
        
        # Update the task description
        updated_task = projects_manager.update_task(
            "test-project", task.id, description="Updated description"
        )
        
        assert updated_task is not None
        assert updated_task.description == "Updated description"
        assert updated_task.priority == 2  # Should remain unchanged
        assert updated_task.status == "ToDo"  # Should remain unchanged
    
    def test_update_task_priority(self, projects_manager):
        """Test updating a task's priority"""
        # Create a project and add a task
        project = projects_manager.create_project("test-project")
        task = projects_manager.add_task("test-project", "Test task", 2)
        
        # Update the task priority
        updated_task = projects_manager.update_task(
            "test-project", task.id, priority=5
        )
        
        assert updated_task is not None
        assert updated_task.priority == 5
        assert updated_task.description == "Test task"  # Should remain unchanged
        assert updated_task.status == "ToDo"  # Should remain unchanged
    
    def test_update_task_status(self, projects_manager):
        """Test updating a task's status"""
        # Create a project and add a task
        project = projects_manager.create_project("test-project")
        task = projects_manager.add_task("test-project", "Test task", 2)
        
        # Update the task status
        updated_task = projects_manager.update_task(
            "test-project", task.id, status="Done"
        )
        
        assert updated_task is not None
        assert updated_task.status == "Done"
        assert updated_task.description == "Test task"  # Should remain unchanged
        assert updated_task.priority == 2  # Should remain unchanged
    
    def test_update_task_multiple_fields(self, projects_manager):
        """Test updating multiple fields of a task"""
        # Create a project and add a task
        project = projects_manager.create_project("test-project")
        task = projects_manager.add_task("test-project", "Original task", 2)
        
        # Update multiple fields
        updated_task = projects_manager.update_task(
            "test-project", task.id, 
            description="Updated task", 
            priority=4, 
            status="Done"
        )
        
        assert updated_task is not None
        assert updated_task.description == "Updated task"
        assert updated_task.priority == 4
        assert updated_task.status == "Done"
    
    def test_update_nonexistent_task(self, projects_manager):
        """Test updating a task that doesn't exist"""
        # Create a project but don't add any tasks
        project = projects_manager.create_project("test-project")
        
        # Try to update a non-existent task
        updated_task = projects_manager.update_task(
            "test-project", "nonexistent-id", description="New description"
        )
        
        assert updated_task is None
    
    def test_update_task_in_nonexistent_project(self, projects_manager):
        """Test updating a task in a project that doesn't exist"""
        # Try to update a task in a non-existent project
        updated_task = projects_manager.update_task(
            "nonexistent-project", "some-task-id", description="New description"
        )
        
        assert updated_task is None
    
    def test_update_task_persistence(self, projects_manager):
        """Test that task updates are persisted to disk"""
        # Create a project and add a task
        project = projects_manager.create_project("test-project")
        task = projects_manager.add_task("test-project", "Original task", 2)
        
        # Update the task
        projects_manager.update_task(
            "test-project", task.id, 
            description="Updated task", 
            priority=5, 
            status="Done"
        )
        
        # Create a new projects manager to reload from disk
        new_projects_manager = Projects(projects_manager.projects_dir)
        
        # Get the updated task
        updated_task = new_projects_manager.get_task("test-project", task.id)
        
        assert updated_task is not None
        assert updated_task.description == "Updated task"
        assert updated_task.priority == 5
        assert updated_task.status == "Done"
    
    def test_update_task_partial_updates(self, projects_manager):
        """Test that partial updates only change specified fields"""
        # Create a project and add a task
        project = projects_manager.create_project("test-project")
        task = projects_manager.add_task("test-project", "Test task", 3)
        
        # Update only description
        updated_task = projects_manager.update_task(
            "test-project", task.id, description="New description"
        )
        
        assert updated_task is not None
        assert updated_task.description == "New description"
        assert updated_task.priority == 3  # Unchanged
        assert updated_task.status == "ToDo"  # Unchanged
        
        # Update only priority
        updated_task = projects_manager.update_task(
            "test-project", task.id, priority=1
        )
        
        assert updated_task is not None
        assert updated_task.description == "New description"  # Unchanged
        assert updated_task.priority == 1
        assert updated_task.status == "ToDo"  # Unchanged 