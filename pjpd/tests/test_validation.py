"""
Tests for Pydantic validation models.
"""

import pytest
from pydantic import ValidationError
from src.validation import (
    AddTaskRequest, UpdateTaskRequest, ListTasksRequest,
    MarkDoneRequest, AddIdeaRequest, UpdateIdeaRequest,
    MarkIdeaDoneRequest, AddEpicRequest, UpdateEpicRequest, MarkEpicDoneRequest
)


class TestAddTaskRequest:
    """Test AddTaskRequest validation."""

    def test_valid_task_request(self):
        request = AddTaskRequest(
            description="Do something important",
            priority=5,
            tag="task"
        )
        assert request.description == "Do something important"
        assert request.priority == 5
        assert request.tag == "task"

    def test_default_values(self):
        request = AddTaskRequest(description="Do something", tag="task")
        assert request.priority == 2
        assert request.tag == "task"

    def test_invalid_priority(self):
        with pytest.raises(ValidationError):
            AddTaskRequest(description="Do something", priority=10000, tag="task")

        with pytest.raises(ValidationError):
            AddTaskRequest(description="Do something", priority=-1, tag="task")

    def test_invalid_tag(self):
        with pytest.raises(ValidationError):
            AddTaskRequest(description="Do something", tag="invalid@tag")

    def test_empty_description(self):
        with pytest.raises(ValidationError):
            AddTaskRequest(description="", tag="task")


class TestUpdateTaskRequest:
    """Test UpdateTaskRequest validation."""

    def test_valid_update_request(self):
        request = UpdateTaskRequest(
            task_id="task-a2c4",
            description="Updated description",
            priority=7,
            status="Done"
        )
        assert request.task_id == "task-a2c4"
        assert request.description == "Updated description"
        assert request.priority == 7
        assert request.status == "Done"

    def test_invalid_task_id_format(self):
        with pytest.raises(ValidationError):
            UpdateTaskRequest(task_id="invalid-id")

        with pytest.raises(ValidationError):
            UpdateTaskRequest(task_id="task@a2c4")

    def test_invalid_status(self):
        with pytest.raises(ValidationError):
            UpdateTaskRequest(task_id="task-a2c4", status="Invalid")


class TestMarkDoneRequest:
    """Test MarkDoneRequest validation."""

    def test_valid_mark_done_request(self):
        request = MarkDoneRequest(task_id="task-a2c4")
        assert request.task_id == "task-a2c4"

    def test_invalid_task_id_format(self):
        with pytest.raises(ValidationError):
            MarkDoneRequest(task_id="invalid-id")


class TestAddIdeaRequest:
    """Test AddIdeaRequest validation."""

    def test_valid_idea_request(self):
        request = AddIdeaRequest(score=75, description="A great idea", tag="idea")
        assert request.score == 75
        assert request.description == "A great idea"
        assert request.tag == "idea"

    def test_invalid_score(self):
        with pytest.raises(ValidationError):
            AddIdeaRequest(score=10000, description="A great idea", tag="idea")

        with pytest.raises(ValidationError):
            AddIdeaRequest(score=-1, description="A great idea", tag="idea")


class TestUpdateIdeaRequest:
    """Test UpdateIdeaRequest validation."""

    def test_valid_update_idea_request(self):
        request = UpdateIdeaRequest(idea_id="idea-5f6g", score=80, description="Updated idea")
        assert request.idea_id == "idea-5f6g"
        assert request.score == 80
        assert request.description == "Updated idea"

    def test_invalid_idea_id_format(self):
        with pytest.raises(ValidationError):
            UpdateIdeaRequest(idea_id="invalid-id")


class TestMarkIdeaDoneRequest:
    """Test MarkIdeaDoneRequest validation."""

    def test_valid_mark_idea_done_request(self):
        request = MarkIdeaDoneRequest(idea_id="idea-5f6g")
        assert request.idea_id == "idea-5f6g"

    def test_invalid_idea_id_format(self):
        with pytest.raises(ValidationError):
            MarkIdeaDoneRequest(idea_id="invalid-id")


class TestAddEpicRequest:
    """Test AddEpicRequest validation."""

    def test_valid_epic_request(self):
        request = AddEpicRequest(
            score=85, description="A great epic", tag="epic",
            ideas="idea-a2c4 idea-5f6g", projects="project1 project2"
        )
        assert request.score == 85
        assert request.description == "A great epic"
        assert request.tag == "epic"
        assert request.ideas == "idea-a2c4 idea-5f6g"
        assert request.projects == "project1 project2"

    def test_invalid_score(self):
        with pytest.raises(ValidationError):
            AddEpicRequest(score=10000, description="A great epic", tag="epic")


class TestUpdateEpicRequest:
    """Test UpdateEpicRequest validation."""

    def test_valid_update_epic_request(self):
        request = UpdateEpicRequest(
            epic_id="epic-a2c4", score=90, description="Updated epic",
            ideas="idea-5f6g", projects="project1"
        )
        assert request.epic_id == "epic-a2c4"
        assert request.score == 90
        assert request.description == "Updated epic"

    def test_invalid_epic_id_format(self):
        with pytest.raises(ValidationError):
            UpdateEpicRequest(epic_id="invalid-id")


class TestMarkEpicDoneRequest:
    """Test MarkEpicDoneRequest validation."""

    def test_valid_mark_epic_done_request(self):
        request = MarkEpicDoneRequest(epic_id="epic-a2c4")
        assert request.epic_id == "epic-a2c4"

    def test_invalid_epic_id_format(self):
        with pytest.raises(ValidationError):
            MarkEpicDoneRequest(epic_id="invalid-id")
