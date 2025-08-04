"""
Tests for Pydantic validation models.
"""

import pytest
from pydantic import ValidationError
from src.validation import (
    NewProjectRequest, AddTaskRequest, UpdateTaskRequest, ListTasksRequest,
    MarkDoneRequest, NextStepsRequest, AddIdeaRequest, UpdateIdeaRequest,
    RemoveIdeaRequest, AddEpicRequest, UpdateEpicRequest, MarkEpicDoneRequest
)


class TestNewProjectRequest:
    """Test NewProjectRequest validation."""
    
    def test_valid_project_name(self):
        """Test that valid project names are accepted."""
        request = NewProjectRequest(project="my-project")
        assert request.project == "my-project"
    
    def test_valid_project_name_with_spaces(self):
        """Test that project names with spaces are accepted."""
        request = NewProjectRequest(project="My Project")
        assert request.project == "My Project"
    
    def test_valid_project_name_with_underscores(self):
        """Test that project names with underscores are accepted."""
        request = NewProjectRequest(project="my_project")
        assert request.project == "my_project"
    
    def test_empty_project_name(self):
        """Test that empty project names are rejected."""
        with pytest.raises(ValidationError):
            NewProjectRequest(project="")
    
    def test_whitespace_only_project_name(self):
        """Test that whitespace-only project names are rejected."""
        with pytest.raises(ValidationError):
            NewProjectRequest(project="   ")
    
    def test_invalid_project_name_with_special_chars(self):
        """Test that project names with special characters are rejected."""
        with pytest.raises(ValidationError):
            NewProjectRequest(project="my*project")
        
        with pytest.raises(ValidationError):
            NewProjectRequest(project="my|project")


class TestAddTaskRequest:
    """Test AddTaskRequest validation."""
    
    def test_valid_task_request(self):
        """Test that valid task requests are accepted."""
        request = AddTaskRequest(
            project="my-project",
            description="Do something important",
            priority=5,
            tag="task"
        )
        assert request.project == "my-project"
        assert request.description == "Do something important"
        assert request.priority == 5
        assert request.tag == "task"
    
    def test_default_values(self):
        """Test that default values work correctly."""
        request = AddTaskRequest(
            project="my-project",
            description="Do something",
            tag="task"
        )
        assert request.priority == 2
        assert request.tag == "task"
    
    def test_invalid_priority(self):
        """Test that invalid priorities are rejected."""
        with pytest.raises(ValidationError):
            AddTaskRequest(
                project="my-project",
                description="Do something",
                priority=10000  # Should be 0-9999
            )
        
        with pytest.raises(ValidationError):
            AddTaskRequest(
                project="my-project",
                description="Do something",
                priority=-1  # Should be 0-9999
            )
    
    def test_invalid_tag(self):
        """Test that invalid tags are rejected."""
        with pytest.raises(ValidationError):
            AddTaskRequest(
                project="my-project",
                description="Do something",
                tag="invalid@tag"  # Contains special character
            )
    
    def test_empty_description(self):
        """Test that empty descriptions are rejected."""
        with pytest.raises(ValidationError):
            AddTaskRequest(
                project="my-project",
                description=""
            )


class TestUpdateTaskRequest:
    """Test UpdateTaskRequest validation."""
    
    def test_valid_update_request(self):
        """Test that valid update requests are accepted."""
        request = UpdateTaskRequest(
            project="my-project",
            task_id="task-a2c4",
            description="Updated description",
            priority=7,
            status="Done"
        )
        assert request.project == "my-project"
        assert request.task_id == "task-a2c4"
        assert request.description == "Updated description"
        assert request.priority == 7
        assert request.status == "Done"
    
    def test_invalid_task_id_format(self):
        """Test that invalid task ID formats are rejected."""
        with pytest.raises(ValidationError):
            UpdateTaskRequest(
                project="my-project",
                task_id="invalid-id"  # Missing base32 part
            )
        
        with pytest.raises(ValidationError):
            UpdateTaskRequest(
                project="my-project",
                task_id="task@a2c4"  # Contains special character
            )
    
    def test_invalid_status(self):
        """Test that invalid status values are rejected."""
        with pytest.raises(ValidationError):
            UpdateTaskRequest(
                project="my-project",
                task_id="task-a2c4",
                status="Invalid"
            )


class TestMarkDoneRequest:
    """Test MarkDoneRequest validation."""
    
    def test_valid_mark_done_request(self):
        """Test that valid mark done requests are accepted."""
        request = MarkDoneRequest(
            project="my-project",
            task_id="task-a2c4"
        )
        assert request.project == "my-project"
        assert request.task_id == "task-a2c4"
    
    def test_invalid_task_id_format(self):
        """Test that invalid task ID formats are rejected."""
        with pytest.raises(ValidationError):
            MarkDoneRequest(
                project="my-project",
                task_id="invalid-id"
            )


class TestNextStepsRequest:
    """Test NextStepsRequest validation."""
    
    def test_valid_next_steps_request(self):
        """Test that valid next steps requests are accepted."""
        request = NextStepsRequest(max_results=10)
        assert request.max_results == 10
    
    def test_default_max_results(self):
        """Test that default max_results works."""
        request = NextStepsRequest()
        assert request.max_results == 5
    
    def test_invalid_max_results(self):
        """Test that invalid max_results are rejected."""
        with pytest.raises(ValidationError):
            NextStepsRequest(max_results=0)  # Should be > 0
        
        with pytest.raises(ValidationError):
            NextStepsRequest(max_results=101)  # Should be <= 100


class TestAddIdeaRequest:
    """Test AddIdeaRequest validation."""
    
    def test_valid_idea_request(self):
        """Test that valid idea requests are accepted."""
        request = AddIdeaRequest(
            score=75,
            description="A great idea",
            tag="idea"
        )
        assert request.score == 75
        assert request.description == "A great idea"
        assert request.tag == "idea"
    
    def test_invalid_score(self):
        """Test that invalid scores are rejected."""
        with pytest.raises(ValidationError):
            AddIdeaRequest(
                score=10000,  # Should be 0-9999
                description="A great idea"
            )
        
        with pytest.raises(ValidationError):
            AddIdeaRequest(
                score=-1,  # Should be 0-9999
                description="A great idea"
            )


class TestUpdateIdeaRequest:
    """Test UpdateIdeaRequest validation."""
    
    def test_valid_update_idea_request(self):
        """Test that valid update idea requests are accepted."""
        request = UpdateIdeaRequest(
            idea_id="idea-5f6g",
            score=80,
            description="Updated idea"
        )
        assert request.idea_id == "idea-5f6g"
        assert request.score == 80
        assert request.description == "Updated idea"
    
    def test_invalid_idea_id_format(self):
        """Test that invalid idea ID formats are rejected."""
        with pytest.raises(ValidationError):
            UpdateIdeaRequest(
                idea_id="invalid-id"
            )


class TestRemoveIdeaRequest:
    """Test RemoveIdeaRequest validation."""
    
    def test_valid_remove_idea_request(self):
        """Test that valid remove idea requests are accepted."""
        request = RemoveIdeaRequest(idea_id="idea-5f6g")
        assert request.idea_id == "idea-5f6g"
    
    def test_invalid_idea_id_format(self):
        """Test that invalid idea ID formats are rejected."""
        with pytest.raises(ValidationError):
            RemoveIdeaRequest(idea_id="invalid-id")


class TestAddEpicRequest:
    """Test AddEpicRequest validation."""
    
    def test_valid_epic_request(self):
        """Test that valid epic requests are accepted."""
        request = AddEpicRequest(
            score=85,
            description="A great epic",
            tag="epic",
            ideas="idea-a2c4 idea-5f6g",
            projects="project1 project2"
        )
        assert request.score == 85
        assert request.description == "A great epic"
        assert request.tag == "epic"
        assert request.ideas == "idea-a2c4 idea-5f6g"
        assert request.projects == "project1 project2"
    
    def test_invalid_score(self):
        """Test that invalid scores are rejected."""
        with pytest.raises(ValidationError):
            AddEpicRequest(
                score=10000,  # Should be 0-9999
                description="A great epic"
            )


class TestUpdateEpicRequest:
    """Test UpdateEpicRequest validation."""
    
    def test_valid_update_epic_request(self):
        """Test that valid update epic requests are accepted."""
        request = UpdateEpicRequest(
            epic_id="epic-a2c4",
            score=90,
            description="Updated epic",
            ideas="idea-5f6g",
            projects="project1"
        )
        assert request.epic_id == "epic-a2c4"
        assert request.score == 90
        assert request.description == "Updated epic"
        assert request.ideas == "idea-5f6g"
        assert request.projects == "project1"
    
    def test_invalid_epic_id_format(self):
        """Test that invalid epic ID formats are rejected."""
        with pytest.raises(ValidationError):
            UpdateEpicRequest(epic_id="invalid-id")


class TestMarkEpicDoneRequest:
    """Test MarkEpicDoneRequest validation."""
    
    def test_valid_mark_epic_done_request(self):
        """Test that valid mark epic done requests are accepted."""
        request = MarkEpicDoneRequest(epic_id="epic-a2c4")
        assert request.epic_id == "epic-a2c4"
    
    def test_invalid_epic_id_format(self):
        """Test that invalid epic ID formats are rejected."""
        with pytest.raises(ValidationError):
            MarkEpicDoneRequest(epic_id="invalid-id") 