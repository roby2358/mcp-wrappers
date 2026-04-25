#!/usr/bin/env python3
"""
pjpd MCP Server — single-project task and idea management.

The current working directory is the project root. All data lives under
``<cwd>/pjpd/`` (tasks.txt, ideas.txt).
"""

import logging
import sys
from pathlib import Path
from typing import Any, Dict, List

from mcp.server.fastmcp import FastMCP

from config import Config
from ideas import Ideas
from projects import Projects
from validation import (
    ListIdeasRequest,
    ListTasksRequest,
    MarkIdeaDoneRequest,
    MarkTaskDoneRequest,
    PutIdeaRequest,
    PutTaskRequest,
    ReprioritizeTaskRequest,
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


def _bulk_update_tasks(
    task_ids: List[str],
    description: str | None,
    priority: int | None,
    status: str | None,
    message: str,
) -> Dict[str, Any]:
    """All-or-nothing bulk task update. Returns an MCP response dict.

    If any ID is missing, no tasks are modified and a failure response is returned
    naming the missing IDs.
    """
    missing = [tid for tid in task_ids if not projects_manager.get_task(tid)]
    if missing:
        return mcp_failure(
            f"Tasks not found: {missing}. No tasks were modified. "
            f"Use pjpd_list_tasks(show_done=True) to see all task IDs."
        )

    updated = [
        projects_manager.update_task(tid, description, priority, status).to_dict()
        for tid in task_ids
    ]

    return mcp_success(
        _add_legacy_warning({
            "tasks": updated,
            "project_file": str(projects_manager.project_file),
            "message": message,
        })
    )


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
async def pjpd_put_task(
    description: str,
    tag: str = None,
    id: str = None,
    priority: int = 50,
) -> Dict[str, Any]:
    """Create or update a task. Provide `tag` to create a new task, or `id` to update an existing one.

    Args:
        description: What needs to be done, in enough detail to act on without additional context.
        tag: Tag string (1-12 characters, alphanumeric and hyphens only). Provide to create a new task.
        id: Existing task ID (format: `<tag>-XXXX`). Provide to update an existing task.
        priority: Priority from 0 (negligible) to 100 (urgent). Values outside this range are allowed for exceptional cases. Defaults to 50.

    Returns:
        Standard MCP response with task details or error message.
    """
    try:
        request = PutTaskRequest(description=description, tag=tag, id=id, priority=priority)

        if request.tag:
            task = projects_manager.add_task(
                request.description, request.priority, request.tag
            )
            if not task:
                return mcp_failure(
                    "Failed to add task. Verify the pjpd/ directory exists and tasks.txt is writable."
                )
            return mcp_success(
                _add_legacy_warning({
                    **task.to_dict(),
                    "project_file": str(projects_manager.project_file),
                    "message": "Task created successfully",
                })
            )
        else:
            updated_task = projects_manager.update_task(
                request.id, request.description, request.priority, None
            )
            if not updated_task:
                return mcp_failure(
                    f"Task '{request.id}' not found. Use pjpd_list_tasks() to see existing task IDs."
                )
            return mcp_success(
                _add_legacy_warning({
                    **updated_task.to_dict(),
                    "project_file": str(projects_manager.project_file),
                    "message": f"Task '{request.id}' updated successfully",
                })
            )
    except Exception as e:
        return mcp_failure(f"Error putting task: {str(e)}")


@mcp.tool()
async def pjpd_list_tasks(
    count: int = 20,
    show_done: bool = False,
) -> Dict[str, Any]:
    """List tasks with optional filtering.

    Args:
        count: Maximum number of tasks to return. Defaults to 20.
        show_done: Whether to include completed tasks. Defaults to False.

    Returns:
        Standard MCP response containing a list of matching tasks or an error.
    """
    try:
        request = ListTasksRequest(count=count, show_done=show_done)

        status_str: str | None = None if request.show_done else "todo"

        filtered = projects_manager.project.filter_tasks(status=status_str)

        # Sort: ToDo before Done, then priority desc, then description
        status_rank = {"ToDo": 0, "Done": 1}
        filtered.sort(key=lambda t: (status_rank.get(t["status"], 2), -t["priority"], t["description"].lower()))

        total = len(filtered)
        filtered = filtered[: request.count]

        result = _add_legacy_warning({
            "total_tasks": len(filtered),
            "tasks": filtered,
            "project_file": str(projects_manager.project_file),
        })

        if total > request.count:
            result["info"] = f"Returned {len(filtered)} of {total} total tasks"

        return mcp_success(result)
    except Exception as e:
        return mcp_failure(f"Error listing tasks: {str(e)}")


@mcp.tool()
async def pjpd_mark_task_done(task_ids: List[str]) -> Dict[str, Any]:
    """Mark one or more tasks as completed. All IDs must exist or nothing is changed.

    Args:
        task_ids: List of tag-based task IDs (format: `<tag>-XXXX`) to mark as done.

    Returns:
        Standard MCP response with updated task details or error message.
    """
    try:
        request = MarkTaskDoneRequest(task_ids=task_ids)
        return _bulk_update_tasks(
            request.task_ids,
            None,
            None,
            "Done",
            f"Marked {len(request.task_ids)} task(s) as done",
        )
    except Exception as e:
        return mcp_failure(f"Error marking tasks as done: {str(e)}")


@mcp.tool()
async def pjpd_reprioritize_task(priority: int, task_ids: List[str]) -> Dict[str, Any]:
    """Set the priority of one or more tasks. All IDs must exist or nothing is changed.

    Use this to shuffle priorities without resending the description text.

    Args:
        priority: New priority to apply to every listed task. 0 (negligible) to 100 (urgent); values outside this range are allowed for exceptional cases.
        task_ids: List of tag-based task IDs (format: `<tag>-XXXX`) to reprioritize.

    Returns:
        Standard MCP response with updated task details or error message.
    """
    try:
        request = ReprioritizeTaskRequest(priority=priority, task_ids=task_ids)
        return _bulk_update_tasks(
            request.task_ids,
            None,
            request.priority,
            None,
            f"Reprioritized {len(request.task_ids)} task(s) to priority {request.priority}",
        )
    except Exception as e:
        return mcp_failure(
            f"Error reprioritizing tasks: {str(e)}. "
            f"Possible fixes: 1) Ensure each task_id matches <tag>-XXXX format (e.g. 'task-ab12'), "
            f"2) Pass priority as an integer (0-100 typical, higher allowed), "
            f"3) Use pjpd_list_tasks(show_done=True) to confirm the task IDs exist."
        )


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
async def pjpd_list_ideas(count: int = 20) -> Dict[str, Any]:
    """List ideas sorted by score (highest first).

    Args:
        count: Maximum number of ideas to return. Defaults to 20.

    Returns:
        Standard MCP response with list of ideas sorted by score (highest first).
    """
    try:
        request = ListIdeasRequest(count=count)
        ideas = ideas_manager.list_ideas(count=request.count)

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
async def pjpd_put_idea(
    score: int,
    description: str,
    tag: str = None,
    id: str = None,
) -> Dict[str, Any]:
    """Create or update an idea. Provide `tag` to create a new idea, or `id` to update an existing one.

    Args:
        score: Relevance score from 0 (trivial) to 100 (critical). Values outside this range are allowed for exceptional cases.
        description: What the idea entails, in enough detail for a human or model to understand its purpose and scope.
        tag: Tag string (1-12 characters, alphanumeric and hyphens only). Provide to create a new idea.
        id: Existing idea ID (format: `<tag>-XXXX`). Provide to update an existing idea.

    Returns:
        Standard MCP response with idea details or error message.
    """
    try:
        request = PutIdeaRequest(score=score, description=description, tag=tag, id=id)

        if request.tag:
            idea = ideas_manager.add_idea(request.description, request.score, request.tag)
            return mcp_success(
                {
                    **idea.to_dict(),
                    "project_file": str(ideas_manager.ideas_file),
                    "message": f"Idea created successfully with ID '{idea.id}'",
                }
            )
        else:
            updated = ideas_manager.update_idea(
                request.id, request.description, request.score
            )
            if not updated:
                return mcp_failure(
                    f"Idea '{request.id}' not found. Use pjpd_list_ideas() to see existing idea IDs."
                )

            for idea in ideas_manager.ideas:
                if idea.id == request.id:
                    return mcp_success(
                        {
                            **idea.to_dict(),
                            "project_file": str(ideas_manager.ideas_file),
                            "message": f"Idea '{request.id}' updated successfully",
                        }
                    )

            return mcp_failure(
                f"Idea '{request.id}' was updated on disk but could not be re-read. Use pjpd_list_ideas() to verify the current state."
            )
    except Exception as e:
        return mcp_failure(f"Error putting idea: {str(e)}")


@mcp.tool()
async def pjpd_mark_idea_done(idea_ids: List[str]) -> Dict[str, Any]:
    """Mark one or more ideas as done (score set to 0, description prefixed with '(Done)').
    All IDs must exist or nothing is changed.

    Args:
        idea_ids: List of tag-based idea IDs (format: `<tag>-XXXX`) to mark as done.

    Returns:
        Standard MCP response indicating success or failure.
    """
    try:
        request = MarkIdeaDoneRequest(idea_ids=idea_ids)

        known_ids = {idea.id for idea in ideas_manager.ideas}
        missing = [iid for iid in request.idea_ids if iid not in known_ids]
        if missing:
            return mcp_failure(
                f"Ideas not found: {missing}. No ideas were modified. "
                f"Use pjpd_list_ideas() to see existing idea IDs."
            )

        for iid in request.idea_ids:
            ideas_manager.mark_idea_done(iid)

        return mcp_success(
            {
                "idea_ids": request.idea_ids,
                "project_file": str(ideas_manager.ideas_file),
                "message": f"Marked {len(request.idea_ids)} idea(s) as done",
            }
        )
    except Exception as e:
        return mcp_failure(f"Error marking ideas as done: {str(e)}")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main():
    """Entry point for the application."""
    logger.info("Starting Pjpd MCP Server...")
    mcp.run()


if __name__ == "__main__":
    main()
