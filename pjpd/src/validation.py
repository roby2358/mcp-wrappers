"""
Pydantic models for MCP tool validation.
"""

import re
from typing import Any, Dict, List, Literal, Optional, Union

from pydantic import BaseModel, Field, field_validator, model_validator

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


class PutTaskRequest(BaseModel):
    """Request model for creating or updating a task.

    Exactly one of ``tag`` or ``id`` must be provided:
    - ``tag`` (without ``id``): create a new task, generating an ID from the tag.
    - ``id`` (without ``tag``): update an existing task by ID.
    """
    description: str = Field(..., min_length=1, description="The description of the task")
    priority: int = Field(default=50, ge=0, le=9999, description="Priority from 0 (negligible) to 100 (urgent). Values outside this range are allowed for exceptional cases.")
    tag: Optional[str] = Field(None, min_length=1, max_length=12, description="Tag for new task (1-12 chars, alphanumeric and hyphens). Provide to create.")
    id: Optional[str] = Field(None, description="Existing task ID (format: <tag>-XXXX). Provide to update.")

    @field_validator('tag')
    @classmethod
    def validate_tag(cls, v):
        if v is not None:
            return validate_tag_format(v)
        return v

    @field_validator('id')
    @classmethod
    def validate_id(cls, v):
        if v is not None:
            return validate_id_format(v, "Task ID")
        return v

    @model_validator(mode='after')
    def exactly_one_of_tag_or_id(self):
        if self.tag and self.id:
            raise ValueError("Provide either 'tag' (to create) or 'id' (to update), not both")
        if not self.tag and not self.id:
            raise ValueError("Provide either 'tag' (to create) or 'id' (to update)")
        return self


class ListTasksRequest(BaseModel):
    """Request model for listing tasks."""
    count: int = Field(default=20, ge=1, le=1000, description="Maximum number of tasks to return")
    show_done: bool = Field(default=False, description="Whether to include completed tasks")


class MarkDoneRequest(BaseModel):
    """Request model for marking tasks as done."""
    task_ids: List[str] = Field(..., min_length=1, description="List of tag-based task IDs (format: <tag>-XXXX)")

    @field_validator('task_ids')
    @classmethod
    def validate_task_ids(cls, v):
        for tid in v:
            validate_id_format(tid, "Task ID")
        return v


class ListIdeasRequest(BaseModel):
    """Request model for listing ideas."""
    count: int = Field(default=20, ge=1, le=1000, description="Maximum number of ideas to return")


class PutIdeaRequest(BaseModel):
    """Request model for creating or updating an idea.

    Exactly one of ``tag`` or ``id`` must be provided:
    - ``tag`` (without ``id``): create a new idea, generating an ID from the tag.
    - ``id`` (without ``tag``): update an existing idea by ID.
    """
    score: int = Field(..., ge=0, le=9999, description="Score value (0-9999, higher numbers = higher relevance)")
    description: str = Field(..., min_length=1, description="Idea description")
    tag: Optional[str] = Field(None, min_length=1, max_length=12, description="Tag for new idea (1-12 chars, alphanumeric and hyphens). Provide to create.")
    id: Optional[str] = Field(None, description="Existing idea ID (format: <tag>-XXXX). Provide to update.")

    @field_validator('tag')
    @classmethod
    def validate_tag(cls, v):
        if v is not None:
            return validate_tag_format(v)
        return v

    @field_validator('id')
    @classmethod
    def validate_id(cls, v):
        if v is not None:
            return validate_id_format(v, "Idea ID")
        return v

    @model_validator(mode='after')
    def exactly_one_of_tag_or_id(self):
        if self.tag and self.id:
            raise ValueError("Provide either 'tag' (to create) or 'id' (to update), not both")
        if not self.tag and not self.id:
            raise ValueError("Provide either 'tag' (to create) or 'id' (to update)")
        return self


class MarkIdeaDoneRequest(BaseModel):
    """Request model for marking ideas as done."""
    idea_ids: List[str] = Field(..., min_length=1, description="List of tag-based idea IDs (format: <tag>-XXXX)")

    @field_validator('idea_ids')
    @classmethod
    def validate_idea_ids(cls, v):
        for iid in v:
            validate_id_format(iid, "Idea ID")
        return v
