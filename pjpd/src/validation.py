"""
Pydantic models for MCP tool validation.
"""

import re
from typing import Any, Dict, List, Literal, Optional, Union

from pydantic import BaseModel, Field, field_validator

# Regex patterns for validation
TAG_PATTERN = r'^[a-zA-Z0-9\-]+$'
ID_PATTERN = r'^[a-zA-Z0-9\-]+-[a-z2-9]{4}$'


def validate_tag_format(value: str) -> str:
    """Validate that a tag contains only alphanumeric characters and hyphens."""
    if not re.match(TAG_PATTERN, value):
        raise ValueError("Tag can only contain alphanumeric characters and hyphens")
    return value


def validate_id_format(value: str, id_type: str = "ID") -> str:
    """Validate that an ID follows the format <tag>-XXXX where XXXX is alphanumeric."""
    if not re.match(ID_PATTERN, value):
        raise ValueError(f"{id_type} must be in format <tag>-XXXX where XXXX is alphanumeric")
    return value


class TaskDict(BaseModel):
    """Dictionary representation of a task returned by the API."""
    id: str
    priority: int = Field(..., description="Plain integer priority (higher numbers = higher priority)")
    status: str = Field(..., description="Task status (ToDo or Done)")
    description: str


class MCPResponseSuccess(BaseModel):
    """Successful MCP response schema."""
    success: Literal[True] = True
    result: Any
    error: str = ""


class MCPResponseFailure(BaseModel):
    """Failed MCP response schema."""
    success: Literal[False] = False
    result: str = ""
    error: str


MCPResponse = Union[MCPResponseSuccess, MCPResponseFailure]


class AddTaskRequest(BaseModel):
    """Request model for adding a task."""
    description: str = Field(..., min_length=1, description="The description of the task")
    priority: int = Field(default=2, ge=0, le=9999, description="Priority level (0-9999, higher numbers = higher priority)")
    tag: str = Field(..., min_length=1, max_length=12, description="Tag string (1-12 characters, alphanumeric and hyphens only)")

    @field_validator('tag')
    @classmethod
    def validate_tag(cls, v):
        return validate_tag_format(v)


class UpdateTaskRequest(BaseModel):
    """Request model for updating a task."""
    task_id: str = Field(..., description="The unique tag-based task ID (format: <tag>-XXXX where XXXX is alphanumeric)")
    description: Optional[str] = Field(None, description="Optional new description for the task")
    priority: Optional[int] = Field(None, ge=0, le=9999, description="Optional new priority level (0-9999)")
    status: str = Field(default="ToDo", description="Optional new status (ToDo or Done)")

    @field_validator('status')
    @classmethod
    def validate_status(cls, v):
        if v not in ["ToDo", "Done"]:
            raise ValueError("Status must be either 'ToDo' or 'Done'")
        return v

    @field_validator('task_id')
    @classmethod
    def validate_task_id(cls, v):
        return validate_id_format(v, "Task ID")


class ListTasksRequest(BaseModel):
    """Request model for listing tasks."""
    priority: Optional[int] = Field(None, ge=0, le=9999, description="Filter tasks by priority level (returns all tasks >= this priority)")
    status: Optional[str] = Field(None, description="Filter tasks by status (ToDo or Done)")
    max_results: Optional[int] = Field(None, gt=1, le=1000, description="Maximum number of tasks to return")

    @field_validator('status')
    @classmethod
    def validate_status(cls, v):
        if v is not None and v not in ["ToDo", "Done"]:
            raise ValueError("Status must be either 'ToDo' or 'Done'")
        return v


class MarkDoneRequest(BaseModel):
    """Request model for marking a task as done."""
    task_id: str = Field(..., description="The unique tag-based task ID (format: <tag>-XXXX where XXXX is alphanumeric)")

    @field_validator('task_id')
    @classmethod
    def validate_task_id(cls, v):
        return validate_id_format(v, "Task ID")


class NextStepsRequest(BaseModel):
    """Request model for getting next steps."""
    max_results: int = Field(default=5, gt=1, le=100, description="Maximum number of suggestions to return")


class ListIdeasRequest(BaseModel):
    """Request model for listing ideas."""
    max_results: Optional[int] = Field(None, gt=1, le=1000, description="Maximum number of results to return")


class AddIdeaRequest(BaseModel):
    """Request model for adding an idea."""
    score: int = Field(..., ge=0, le=9999, description="Score value (0-9999, higher numbers = higher relevance)")
    description: str = Field(..., min_length=1, description="Idea description")
    tag: str = Field(..., min_length=1, max_length=12, description="Tag string (1-12 characters, alphanumeric and hyphens only)")

    @field_validator('tag')
    @classmethod
    def validate_tag(cls, v):
        return validate_tag_format(v)


class UpdateIdeaRequest(BaseModel):
    """Request model for updating an idea."""
    idea_id: str = Field(..., description="Tag-based idea ID (format: <tag>-XXXX where XXXX is alphanumeric)")
    score: Optional[int] = Field(None, ge=0, le=9999, description="Optional new score value (0-9999)")
    description: Optional[str] = Field(None, min_length=1, description="Optional new idea description")

    @field_validator('idea_id')
    @classmethod
    def validate_idea_id(cls, v):
        return validate_id_format(v, "Idea ID")


class MarkIdeaDoneRequest(BaseModel):
    """Request model for marking an idea as done."""
    idea_id: str = Field(..., description="Tag-based idea ID (format: <tag>-XXXX where XXXX is alphanumeric)")

    @field_validator('idea_id')
    @classmethod
    def validate_idea_id(cls, v):
        return validate_id_format(v, "Idea ID")


class ListEpicsRequest(BaseModel):
    """Request model for listing epics."""
    max_results: Optional[int] = Field(None, gt=1, le=1000, description="Maximum number of results to return")


class AddEpicRequest(BaseModel):
    """Request model for adding an epic."""
    score: int = Field(..., ge=0, le=9999, description="Score value (0-9999, higher numbers = higher relevance)")
    description: str = Field(..., min_length=1, description="Epic description")
    tag: str = Field(..., min_length=1, max_length=12, description="Tag string (1-12 characters, alphanumeric and hyphens only)")
    ideas: str = Field(default="", description="Space-delimited list of idea IDs (optional)")
    projects: str = Field(default="", description="Space-delimited list of project names (optional)")

    @field_validator('tag')
    @classmethod
    def validate_tag(cls, v):
        return validate_tag_format(v)


class UpdateEpicRequest(BaseModel):
    """Request model for updating an epic."""
    epic_id: str = Field(..., description="Tag-based epic ID (format: <tag>-XXXX where XXXX is alphanumeric)")
    score: Optional[int] = Field(None, ge=0, le=9999, description="Optional new score (0-9999)")
    description: Optional[str] = Field(None, min_length=1, description="Optional new description")
    ideas: Optional[str] = Field(None, description="Optional space-delimited list of idea IDs")
    projects: Optional[str] = Field(None, description="Optional space-delimited list of project names")

    @field_validator('epic_id')
    @classmethod
    def validate_epic_id(cls, v):
        return validate_id_format(v, "Epic ID")


class MarkEpicDoneRequest(BaseModel):
    """Request model for marking an epic as done."""
    epic_id: str = Field(..., description="Tag-based epic ID (format: <tag>-XXXX where XXXX is alphanumeric)")

    @field_validator('epic_id')
    @classmethod
    def validate_epic_id(cls, v):
        return validate_id_format(v, "Epic ID")
