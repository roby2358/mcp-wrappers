#!/usr/bin/env python3
"""
pjpd MCP Server — single-project task, idea, and epic management.

The current working directory is the project root. All data lives under
``<cwd>/pjpd/`` (tasks.txt, ideas.txt, epics.txt).
"""

import logging
import sys
from pathlib import Path
from typing import Any, Dict, List

from mcp.server.fastmcp import FastMCP

from config import Config
from epics import Epics
from ideas import Ideas
from projects import Projects
from validation import (
    AddEpicRequest,
    AddIdeaRequest,
    AddTaskRequest,
    ListEpicsRequest,
    ListIdeasRequest,
    ListTasksRequest,
    MarkDoneRequest,
    MarkEpicDoneRequest,
    MarkIdeaDoneRequest,
    NextStepsRequest,
    UpdateEpicRequest,
    UpdateIdeaRequest,
    UpdateTaskRequest,
)

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------


def setup_logging():
    """Configure logging for the entire application."""
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
        stream=sys.stderr,
    )


setup_logging()
logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# MCP server & managers
# ---------------------------------------------------------------------------

mcp = FastMCP("projectmcp")
config = Config()

# The project root is always the current working directory.
project_dir = Path.cwd()

projects_manager = Projects(project_dir)
ideas_manager = Ideas(project_dir)
epics_manager = Epics(project_dir)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _add_legacy_warning(result: Dict[str, Any]) -> Dict[str, Any]:
    """Add a legacy project file warning to a result dict if applicable."""
    warning = projects_manager.legacy_project_file_warning()
    if warning:
        result["warning"] = warning
    return result


def mcp_success(result: Any) -> Dict[str, Any]:
    return {"success": True, "result": result, "error": ""}


def mcp_failure(error_message: str) -> Dict[str, Any]:
    return {"success": False, "result": "", "error": error_message}


# ---------------------------------------------------------------------------
# Prompts
# ---------------------------------------------------------------------------


@mcp.prompt()
def pjpd_intro() -> str:
    """Return an introductory prompt that describes the ProjectMCP system."""
    try:
        intro_path = Path(__file__).parent.parent / "resources" / "intro.txt"
        with open(intro_path, "r", encoding="utf-8") as f:
            return f.read()
    except Exception as e:
        return f"Error loading intro text: {str(e)}"


# ---------------------------------------------------------------------------
# Task tools
# ---------------------------------------------------------------------------


@mcp.tool()
async def pjpd_add_task(
    description: str, tag: str, priority: int = 2
) -> Dict[str, Any]:
    """Add a new task to the project.

    Args:
        description: The description of the task.
        tag: Tag string (1-12 characters, alphanumeric and hyphens only). Required.
        priority: The priority level of the task (higher numbers = higher priority). Defaults to 2.

    Returns:
        Standard MCP response with task details or error message.
    """
    try:
        request = AddTaskRequest(description=description, priority=priority, tag=tag)
        task = projects_manager.add_task(
            request.description, request.priority, request.tag
        )

        if not task:
            return mcp_failure("Failed to add task")

        return mcp_success(
            _add_legacy_warning({
                **task.to_dict(),
                "project_file": str(projects_manager.project_file),
                "message": "Task added successfully",
            })
        )
    except Exception as e:
        return mcp_failure(f"Error adding task: {str(e)}")


@mcp.tool()
async def pjpd_update_task(
    task_id: str,
    description: str = None,
    priority: int = None,
    status: str = "ToDo",
) -> Dict[str, Any]:
    """Update an existing task in the project.

    Args:
        task_id: The unique tag-based task ID (format: `<tag>-XXXX`) to update.
        description: Optional new description for the task.
        priority: Optional new priority level (higher numbers = higher priority).
        status: Optional new status ("ToDo" or "Done"). Defaults to "ToDo".

    Returns:
        Standard MCP response with updated task details or error message.
    """
    try:
        request = UpdateTaskRequest(
            task_id=task_id, description=description, priority=priority, status=status
        )
        updated_task = projects_manager.update_task(
            request.task_id, request.description, request.priority, request.status
        )

        if not updated_task:
            return mcp_failure(f"Task '{request.task_id}' not found")

        return mcp_success(
            _add_legacy_warning({
                **updated_task.to_dict(),
                "project_file": str(projects_manager.project_file),
                "message": f"Task '{request.task_id}' updated successfully",
            })
        )
    except Exception as e:
        return mcp_failure(f"Error updating task: {str(e)}")


@mcp.tool()
async def pjpd_list_tasks(
    priority: int | None = None,
    status: str | None = None,
    max_results: int | None = None,
) -> Dict[str, Any]:
    """List tasks with optional filtering.

    Args:
        priority: Filter tasks by priority level (returns all tasks >= this priority).
        status: Filter tasks by status ("ToDo" or "Done").
        max_results: Maximum number of tasks to return.

    Returns:
        Standard MCP response containing a list of matching tasks or an error.
    """
    try:
        request = ListTasksRequest(
            priority=priority, status=status, max_results=max_results
        )

        status_str: str | None = None
        if request.status is not None:
            status_str = request.status.strip().lower()

        filtered = projects_manager.project.filter_tasks(
            priority=request.priority, status=status_str
        )

        # Sort by priority desc, then description for deterministic output
        filtered.sort(key=lambda t: (-t["priority"], t["description"].lower()))

        # Apply max_results
        if request.max_results is not None and request.max_results > 0:
            filtered = filtered[: request.max_results]
        else:
            max_from_config = config(Config.MAX_RESULTS, 50)
            if max_from_config > 0:
                filtered = filtered[:max_from_config]

        return mcp_success(
            _add_legacy_warning({
                "total_tasks": len(filtered),
                "tasks": filtered,
                "project_file": str(projects_manager.project_file),
            })
        )
    except Exception as e:
        return mcp_failure(f"Error listing tasks: {str(e)}")


@mcp.tool()
async def pjpd_mark_done(task_id: str) -> Dict[str, Any]:
    """Mark a task as completed.

    Args:
        task_id: The unique tag-based task ID (format: `<tag>-XXXX`) to mark as done.

    Returns:
        Standard MCP response with updated task details or error message.
    """
    try:
        request = MarkDoneRequest(task_id=task_id)
        updated_task = projects_manager.update_task(
            request.task_id, description=None, priority=0, status="Done"
        )

        if not updated_task:
            return mcp_failure(f"Task '{request.task_id}' not found")

        return mcp_success(
            _add_legacy_warning({
                **updated_task.to_dict(),
                "project_file": str(projects_manager.project_file),
                "message": f"Task '{request.task_id}' marked as done",
            })
        )
    except Exception as e:
        return mcp_failure(f"Error marking task as done: {str(e)}")


@mcp.tool()
async def pjpd_next_steps(max_results: int = 5) -> Dict[str, Any]:
    """Determine high-priority tasks to work on next.

    Args:
        max_results: Maximum number of suggestions to return. Defaults to 5.

    Returns:
        Standard MCP response with list of high-priority tasks to work on next.
    """
    try:
        request = NextStepsRequest(max_results=max_results)
        next_tasks = projects_manager.get_next_steps(request.max_results)

        if not next_tasks:
            return mcp_success(
                _add_legacy_warning({
                    "tasks": [],
                    "total_tasks": 0,
                    "project_file": str(projects_manager.project_file),
                    "message": "No high-priority tasks found. All tasks are completed or no tasks exist.",
                })
            )

        task_list = [task.to_dict() for task in next_tasks]

        return mcp_success(
            _add_legacy_warning({
                "tasks": task_list,
                "total_tasks": len(task_list),
                "project_file": str(projects_manager.project_file),
                "message": f"Found {len(task_list)} high-priority tasks to work on next",
            })
        )
    except Exception as e:
        return mcp_failure(f"Error getting next steps: {str(e)}")


@mcp.tool()
async def pjpd_get_statistics() -> Dict[str, Any]:
    """Get comprehensive statistics about the project.

    Returns:
        Standard MCP response with detailed statistics including total counts,
        breakdowns by priority and status.
    """
    try:
        stats = projects_manager.get_statistics()

        return mcp_success(
            _add_legacy_warning({
                **stats,
                "message": f"Retrieved statistics: {stats['total_tasks']} total tasks",
            })
        )
    except Exception as e:
        return mcp_failure(f"Error getting statistics: {str(e)}")


# ---------------------------------------------------------------------------
# Idea tools
# ---------------------------------------------------------------------------


@mcp.tool()
async def pjpd_list_ideas(max_results: int = None) -> Dict[str, Any]:
    """List ideas with optional filtering.

    Args:
        max_results: Maximum number of results to return.

    Returns:
        Standard MCP response with list of ideas sorted by score (highest first).
    """
    try:
        request = ListIdeasRequest(max_results=max_results)
        ideas = ideas_manager.list_ideas(max_results=request.max_results)

        return mcp_success(
            {
                "total_ideas": len(ideas),
                "ideas": ideas,
                "project_file": str(ideas_manager.ideas_file),
                "message": f"Retrieved {len(ideas)} ideas",
            }
        )
    except Exception as e:
        return mcp_failure(f"Error listing ideas: {str(e)}")


@mcp.tool()
async def pjpd_add_idea(score: int, description: str, tag: str) -> Dict[str, Any]:
    """Create a new idea in ideas.txt with parameters.

    Args:
        score: Score value (higher numbers = higher relevance).
        description: Idea description.
        tag: Tag string (1-12 characters, alphanumeric and hyphens only). Required.

    Returns:
        Standard MCP response with created idea details or error message.
    """
    try:
        request = AddIdeaRequest(score=score, description=description, tag=tag)
        idea = ideas_manager.add_idea(request.description, request.score, request.tag)

        return mcp_success(
            {
                **idea.to_dict(),
                "project_file": str(ideas_manager.ideas_file),
                "message": f"Idea added successfully with ID '{idea.id}'",
            }
        )
    except Exception as e:
        return mcp_failure(f"Error adding idea: {str(e)}")


@mcp.tool()
async def pjpd_update_idea(
    idea_id: str, score: int = None, description: str = None
) -> Dict[str, Any]:
    """Update an existing idea.

    Args:
        idea_id: Tag-based idea ID (format: `<tag>-XXXX`).
        score: Optional new score value.
        description: Optional new idea description.

    Returns:
        Standard MCP response with updated idea details or error message.
    """
    try:
        request = UpdateIdeaRequest(
            idea_id=idea_id, score=score, description=description
        )
        updated = ideas_manager.update_idea(
            request.idea_id, request.description, request.score
        )

        if not updated:
            return mcp_failure(f"Idea '{request.idea_id}' not found")

        for idea in ideas_manager.ideas:
            if idea.id == request.idea_id:
                return mcp_success(
                    {
                        **idea.to_dict(),
                        "project_file": str(ideas_manager.ideas_file),
                        "message": f"Idea '{request.idea_id}' updated successfully",
                    }
                )

        return mcp_failure(f"Error retrieving updated idea '{request.idea_id}'")
    except Exception as e:
        return mcp_failure(f"Error updating idea: {str(e)}")


@mcp.tool()
async def pjpd_mark_idea_done(idea_id: str) -> Dict[str, Any]:
    """Mark an idea as done by setting score to 0 and prefixing description with '(Done)'.

    Args:
        idea_id: Tag-based idea ID (format: `<tag>-XXXX`).

    Returns:
        Standard MCP response indicating success or failure.
    """
    try:
        request = MarkIdeaDoneRequest(idea_id=idea_id)
        updated = ideas_manager.mark_idea_done(request.idea_id)

        if not updated:
            return mcp_failure(f"Idea '{request.idea_id}' not found")

        return mcp_success(
            {
                "idea_id": request.idea_id,
                "project_file": str(ideas_manager.ideas_file),
                "message": f"Idea '{request.idea_id}' marked as done (score set to 0, description prefixed)",
            }
        )
    except Exception as e:
        return mcp_failure(f"Error marking idea as done: {str(e)}")


# ---------------------------------------------------------------------------
# Epic tools
# ---------------------------------------------------------------------------


@mcp.tool()
async def pjpd_list_epics(max_results: int = None) -> Dict[str, Any]:
    """List epics with optional filtering.

    Args:
        max_results: Maximum number of results to return.

    Returns:
        Standard MCP response with list of epics sorted by score (highest first).
    """
    try:
        request = ListEpicsRequest(max_results=max_results)
        epics = epics_manager.list_epics(max_results=request.max_results)

        return mcp_success(
            {
                "total_epics": len(epics),
                "epics": epics,
                "project_file": str(epics_manager.epics_file),
                "message": f"Retrieved {len(epics)} epics",
            }
        )
    except Exception as e:
        return mcp_failure(f"Error listing epics: {str(e)}")


@mcp.tool()
async def pjpd_add_epic(
    score: int, description: str, tag: str, ideas: str = "", projects: str = ""
) -> Dict[str, Any]:
    """Create a new epic in epics.txt.

    Args:
        score: Score value (higher numbers = higher relevance).
        description: Epic description.
        tag: Tag string (1-12 characters, alphanumeric and hyphens only). Required.
        ideas: Space-delimited list of idea IDs (optional).
        projects: Space-delimited list of project names (optional).

    Returns:
        Standard MCP response with created epic details or error message.
    """
    try:
        request = AddEpicRequest(
            score=score, description=description, tag=tag, ideas=ideas, projects=projects
        )
        epic = epics_manager.add_epic(
            description=request.description,
            score=request.score,
            tag=request.tag,
            ideas=request.ideas.split() if request.ideas else [],
            projects=request.projects.split() if request.projects else [],
        )

        return mcp_success(
            {
                **epic.to_dict(),
                "project_file": str(epics_manager.epics_file),
                "message": f"Epic added successfully with ID '{epic.id}'",
            }
        )
    except Exception as e:
        return mcp_failure(f"Error adding epic: {str(e)}")


@mcp.tool()
async def pjpd_update_epic(
    epic_id: str,
    score: int = None,
    description: str = None,
    ideas: str = None,
    projects: str = None,
) -> Dict[str, Any]:
    """Update an existing epic.

    Args:
        epic_id: Tag-based epic ID (format: `<tag>-XXXX`).
        score: Optional new score.
        description: Optional new description.
        ideas: Optional space-delimited list of idea IDs.
        projects: Optional space-delimited list of project names.

    Returns:
        Standard MCP response with updated epic details or error message.
    """
    try:
        request = UpdateEpicRequest(
            epic_id=epic_id,
            score=score,
            description=description,
            ideas=ideas,
            projects=projects,
        )
        updated = epics_manager.update_epic(
            request.epic_id,
            description=request.description,
            score=request.score,
            ideas=request.ideas.split() if request.ideas is not None else None,
            projects=request.projects.split() if request.projects is not None else None,
        )

        if not updated:
            return mcp_failure(f"Epic '{request.epic_id}' not found")

        for epic in epics_manager.epics:
            if epic.id == request.epic_id:
                return mcp_success(
                    {
                        **epic.to_dict(),
                        "project_file": str(epics_manager.epics_file),
                        "message": f"Epic '{request.epic_id}' updated successfully",
                    }
                )

        return mcp_failure(f"Error retrieving updated epic '{request.epic_id}'")
    except Exception as e:
        return mcp_failure(f"Error updating epic: {str(e)}")


@mcp.tool()
async def pjpd_mark_epic_done(epic_id: str) -> Dict[str, Any]:
    """Mark an epic as done by setting its score to 0.

    Args:
        epic_id: Tag-based epic ID (format: `<tag>-XXXX`).

    Returns:
        Standard MCP response indicating success or failure.
    """
    try:
        request = MarkEpicDoneRequest(epic_id=epic_id)
        marked_done = epics_manager.mark_epic_done(request.epic_id)

        if marked_done:
            return mcp_success(
                {
                    "epic_id": request.epic_id,
                    "project_file": str(epics_manager.epics_file),
                    "message": f"Epic '{request.epic_id}' marked as done (score set to 0)",
                }
            )
        else:
            return mcp_failure(f"Epic '{request.epic_id}' not found")
    except Exception as e:
        return mcp_failure(f"Error marking epic as done: {str(e)}")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main():
    """Entry point for the application."""
    logger.info("Starting Pjpd MCP Server...")
    mcp.run()


if __name__ == "__main__":
    main()
