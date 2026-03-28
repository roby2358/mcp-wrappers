"""
Tests for Pydantic validation models.
"""

import pytest
from pydantic import ValidationError
from src.validation import (
    PutTaskRequest, ListTasksRequest, MarkDoneRequest,
    PutIdeaRequest, MarkIdeaDoneRequest,
)


class TestPutTaskRequest:
    """Test PutTaskRequest validation."""

    def test_create_with_tag(self):
        request = PutTaskRequest(description="Do something", priority=5, tag="task")
        assert request.tag == "task"
        assert request.id is None
        assert request.description == "Do something"
        assert request.priority == 5

    def test_update_with_id(self):
        request = PutTaskRequest(description="Updated", priority=3, id="task-a2c4")
        assert request.id == "task-a2c4"
        assert request.tag is None

    def test_default_priority(self):
        request = PutTaskRequest(description="Do something", tag="task")
        assert request.priority == 50

    def test_both_tag_and_id_rejected(self):
        with pytest.raises(ValidationError, match="not both"):
            PutTaskRequest(description="X", tag="task", id="task-a2c4")

    def test_neither_tag_nor_id_rejected(self):
        with pytest.raises(ValidationError, match="Provide either"):
            PutTaskRequest(description="X")

    def test_invalid_tag(self):
        with pytest.raises(ValidationError):
            PutTaskRequest(description="X", tag="invalid@tag")

    def test_invalid_id_format(self):
        with pytest.raises(ValidationError):
            PutTaskRequest(description="X", id="bad-id")

    def test_empty_description(self):
        with pytest.raises(ValidationError):
            PutTaskRequest(description="", tag="task")

    def test_invalid_priority(self):
        with pytest.raises(ValidationError):
            PutTaskRequest(description="X", tag="task", priority=10000)

        with pytest.raises(ValidationError):
            PutTaskRequest(description="X", tag="task", priority=-1)


class TestMarkDoneRequest:
    """Test MarkDoneRequest validation."""

    def test_valid_mark_done_request(self):
        request = MarkDoneRequest(task_ids=["task-a2c4"])
        assert request.task_ids == ["task-a2c4"]

    def test_valid_mark_done_multiple(self):
        request = MarkDoneRequest(task_ids=["task-a2c4", "bug-x3y5"])
        assert len(request.task_ids) == 2

    def test_invalid_task_id_format(self):
        with pytest.raises(ValidationError):
            MarkDoneRequest(task_ids=["invalid-id"])

    def test_empty_list_rejected(self):
        with pytest.raises(ValidationError):
            MarkDoneRequest(task_ids=[])


class TestPutIdeaRequest:
    """Test PutIdeaRequest validation."""

    def test_create_with_tag(self):
        request = PutIdeaRequest(score=75, description="A great idea", tag="idea")
        assert request.tag == "idea"
        assert request.id is None
        assert request.score == 75

    def test_update_with_id(self):
        request = PutIdeaRequest(score=80, description="Updated idea", id="idea-5f6g")
        assert request.id == "idea-5f6g"
        assert request.tag is None

    def test_both_tag_and_id_rejected(self):
        with pytest.raises(ValidationError, match="not both"):
            PutIdeaRequest(score=50, description="X", tag="idea", id="idea-5f6g")

    def test_neither_tag_nor_id_rejected(self):
        with pytest.raises(ValidationError, match="Provide either"):
            PutIdeaRequest(score=50, description="X")

    def test_invalid_tag(self):
        with pytest.raises(ValidationError):
            PutIdeaRequest(score=50, description="X", tag="bad@tag")

    def test_invalid_id_format(self):
        with pytest.raises(ValidationError):
            PutIdeaRequest(score=50, description="X", id="bad-id")

    def test_invalid_score(self):
        with pytest.raises(ValidationError):
            PutIdeaRequest(score=10000, description="X", tag="idea")

        with pytest.raises(ValidationError):
            PutIdeaRequest(score=-1, description="X", tag="idea")


class TestMarkIdeaDoneRequest:
    """Test MarkIdeaDoneRequest validation."""

    def test_valid_mark_idea_done_request(self):
        request = MarkIdeaDoneRequest(idea_ids=["idea-5f6g"])
        assert request.idea_ids == ["idea-5f6g"]

    def test_valid_mark_idea_done_multiple(self):
        request = MarkIdeaDoneRequest(idea_ids=["idea-5f6g", "feat-a2b3"])
        assert len(request.idea_ids) == 2

    def test_invalid_idea_id_format(self):
        with pytest.raises(ValidationError):
            MarkIdeaDoneRequest(idea_ids=["invalid-id"])

    def test_empty_list_rejected(self):
        with pytest.raises(ValidationError):
            MarkIdeaDoneRequest(idea_ids=[])
