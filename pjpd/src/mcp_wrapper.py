#!/usr/bin/env python3
"""
Hello World MCP Server using the official MCP SDK
"""

import logging
import sys
from pathlib import Path
from typing import Dict, Any, List, TypedDict, Literal, Union

from enum import Enum

from mcp.server.fastmcp import FastMCP
from projects import Projects
from ideas import Ideas
from epics import Epics
from config import Config
from validation import (
    TaskDict,
    ListProjectsRequest, NewProjectRequest, AddTaskRequest, UpdateTaskRequest,
    ListTasksRequest, MarkDoneRequest, NextStepsRequest,
    ListIdeasRequest, AddIdeaRequest, UpdateIdeaRequest, MarkIdeaDoneRequest,
    ListEpicsRequest, AddEpicRequest, UpdateEpicRequest, MarkEpicDoneRequest
)

# Utility ----------------------------------------------------------------------


def _normalize_projects_directory(path: Path) -> Path:
    """
    Normalize a directory path while preserving all its components.

    1. Expands user shortcuts (``~``) via ``Path.expanduser``.
    2. Collapses redundant separators/trailing slashes using ``pathlib.Path``.
    """
    return Path(path).expanduser()


# Constants
NO_PROJECTS_RESPONSE = {
    "projects": [],
    "total_projects": 0,
    "total_tasks": 0,
    "total_todo": 0,
    "total_done": 0,
    "message": "No projects found. Create your first project by adding a task!"
}

# Centralized logging configuration
def setup_logging():
    """Configure logging for the entire application."""
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        stream=sys.stderr
    )

# Initialize logging
setup_logging()

logger = logging.getLogger(__name__)

# Create the MCP server instance
mcp = FastMCP("projectmcp")

# Create configuration and projects manager instances
config = Config()

# Initialise with the configured default projects directory ("~/projects")
# This path is normalised via _normalize_projects_directory so that "~" is
# expanded but the trailing segment, if any, is preserved.
_default_dir = config(Config.PROJECTS_DIRECTORY, "~/projects")
project_dir = _normalize_projects_directory(Path(_default_dir))

# All managers will handle the /pjpd sub-directory internally
projects_manager = Projects(project_dir)
ideas_manager = Ideas(project_dir)
# Epics manager parallels ideas_manager but operates on epics.txt
epics_manager = Epics(project_dir)

# Strict typing helpers -----------------------------------------------------

# Note: TypedDict definitions moved to validation.py as Pydantic models

# MCP Tools and prompts -----------------------------------------------------

def mcp_success(result: Any) -> Dict[str, Any]:
    """Return a successful MCP response with the given result."""
    return {
        "success": True,
        "result": result,
        "error": "",
    }

def mcp_failure(error_message: str) -> Dict[str, Any]:
    """Return a failed MCP response with the given error message."""
    return {
        "success": False,
        "result": "",
        "error": error_message,
    }

@mcp.prompt()
def pjpd_intro() -> str:
    """
    Return an introductory prompt that describes the ProjectMCP system.
    """
    try:
        intro_path = Path(__file__).parent.parent / "resources" / "intro.txt"
        with open(intro_path, "r", encoding="utf-8") as f:
            return f.read()
    except Exception as e:
        return f"Error loading intro text: {str(e)}"

@mcp.tool()
async def pjpd_list_projects(path: str = None) -> Dict[str, Any]:
    """
    List all projects with their task counts and overview.
    
    Args:
        path: Optional path to the projects directory. If not provided, uses the configured path or defaults to ~/projects.
    
    Returns a comprehensive overview of all projects including task counts, 
    todo/done status, project details, and the current project directory.
    """
    try:
        request = ListProjectsRequest(path=path)
        
        # Decide whether we need to change the current projects directory.
        if request.path is not None:
            # A new directory was supplied – switch managers to this location.
            project_dir = Path(request.path).expanduser()
            projects_manager.set_projects_dir(project_dir)
            ideas_manager.set_directory(project_dir)
            epics_manager.set_directory(project_dir)
        else:
            # No directory supplied – keep whatever directory the managers are
            # already using.
            project_dir = projects_manager.projects_dir
        
        overview = projects_manager.get_overview()
        
        # Add the **parent** project directory (not the pjpd subdirectory) to the response
        overview["project_directory"] = str(project_dir)
        
        return mcp_success(overview)
        
    except Exception as e:
        return mcp_failure(f"Error listing projects: {str(e)}")

@mcp.tool()
async def pjpd_new_project(project: str) -> Dict[str, Any]:
    """Create a new empty project file.
    
    Args:
        project: The name of the project to create.
    
    Returns:
        Standard MCP response indicating success or failure.
    """
    try:
        request = NewProjectRequest(project=project)
        
        created_project = projects_manager.create_project(request.project)
        
        return mcp_success({
            "project_name": created_project.name,
            "file_path": str(created_project.file_path),
            "message": f"Project '{created_project.name}' created successfully"
        })
        
    except Exception as e:
        return mcp_failure(f"Error creating project: {str(e)}")


@mcp.tool()
async def pjpd_add_task(project: str, description: str, tag: str, priority: int = 2) -> Dict[str, Any]:
    """Add a new task to a project.
    
    Args:
        project: The name of the project to add the task to. If the project doesn't exist, it will be created.
        description: The description of the task.
        tag: Tag string (1-12 characters, alphanumeric and hyphens only). Required.
        priority: The priority level of the task (higher numbers = higher priority). Defaults to 2.
    
    Returns:
        Standard MCP response with task details or error message.
    """
    try:
        request = AddTaskRequest(project=project, description=description, priority=priority, tag=tag)
        
        task = projects_manager.add_task(request.project, request.description, request.priority, request.tag)
        
        if not task:
            return mcp_failure(f"Failed to add task to project '{request.project}'")
        
        return mcp_success({
            **task.to_dict(),
            "project": request.project,
            "message": f"Task added to project '{request.project}' successfully"
        })
            
        
    except Exception as e:
        return mcp_failure(f"Error adding task: {str(e)}")


@mcp.tool()
async def pjpd_update_task(project: str, task_id: str, description: str = None, 
                     priority: int = None, status: str = "ToDo") -> Dict[str, Any]:
    """Update an existing task in a project.
    
    Args:
        project: The name of the project containing the task.
        task_id: The unique tag-based task ID (format: `<tag>-XXXX`) to update.
        description: Optional new description for the task.
        priority: Optional new priority level (higher numbers = higher priority).
        status: Optional new status ("ToDo" or "Done"). Defaults to "ToDo".
    
    Returns:
        Standard MCP response with updated task details or error message.
    """
    try:
        request = UpdateTaskRequest(project=project, task_id=task_id, description=description, priority=priority, status=status)
        
        updated_task = projects_manager.update_task(
            request.project, request.task_id, request.description, request.priority, request.status
        )
        
        if not updated_task:
            return mcp_failure(f"Task '{request.task_id}' not found in project '{request.project}'")
        
        return mcp_success({
            **updated_task.to_dict(),
            "project": request.project,
            "message": f"Task '{request.task_id}' updated successfully in project '{request.project}'"
        })
        
    except Exception as e:
        return mcp_failure(f"Error updating task: {str(e)}")


@mcp.tool()
async def pjpd_list_tasks(
    project: str | None = None,
    priority: int | None = None,
    status: str | None = None,
    max_results: int | None = None,
) -> Dict[str, Any]:
    """List tasks with optional filtering.

    Args:
        project: Filter tasks by a specific project name.
        priority: Filter tasks by priority level (returns all tasks >= this priority).
        status: Filter tasks by status ("ToDo" or "Done").
        max_results: Maximum number of tasks to return.

    Returns:
        Standard MCP response containing a list of matching tasks or an error.
    """

    try:
        request = ListTasksRequest(project=project, priority=priority, status=status, max_results=max_results)
        
        status_str: str | None
        if request.status is None:
            status_str = None
        else:
            status_str = request.status.strip().lower()

        tasks: List[TaskDict] = []

        # If a specific project is requested, validate it exists first
        if request.project:
            target_project = projects_manager.get_project(request.project)
            if not target_project:
                return mcp_failure(f"Project '{request.project}' not found")
            
            # Only process the specified project
            filtered_tasks = target_project.filter_tasks(priority=request.priority, status=status_str)
            tasks.extend(filtered_tasks)  # type: ignore[arg-type]
        else:
            # Iterate over all projects and gather tasks that match filters
            for proj in projects_manager.projects.values():
                filtered_tasks = proj.filter_tasks(priority=request.priority, status=status_str)
                # filter_tasks returns plain Dicts; cast for stricter typing purposes
                tasks.extend(filtered_tasks)  # type: ignore[arg-type]

        # Sort tasks by priority (higher numbers first) then description for deterministic output
        tasks.sort(key=lambda item: (-item["priority"], item["description"].lower()))

        # Apply max_results limit if provided, otherwise use config default
        if request.max_results is not None and request.max_results > 0:
            tasks = tasks[:request.max_results]
        else:
            max_results_from_config = config(Config.MAX_RESULTS, 50)
            if max_results_from_config > 0:
                tasks = tasks[:max_results_from_config]

        return mcp_success(
            {
                "total_tasks": len(tasks),
                "tasks": tasks,
            }
        )

    except Exception as e:
        return mcp_failure(f"Error listing tasks: {str(e)}")


@mcp.tool()
async def pjpd_mark_done(project: str, task_id: str) -> Dict[str, Any]:
    """Mark a task as completed.
    
    Args:
        project: The name of the project containing the task.
        task_id: The unique tag-based task ID (format: `<tag>-XXXX`) to mark as done.
    
    Returns:
        Standard MCP response with updated task details or error message.
    """
    try:
        request = MarkDoneRequest(project=project, task_id=task_id)
        
        updated_task = projects_manager.update_task(
            request.project, request.task_id, description=None, priority=0, status="Done"
        )
        
        if not updated_task:
            return mcp_failure(f"Task '{request.task_id}' not found in project '{request.project}'")
        
        return mcp_success({
            **updated_task.to_dict(),
            "project": request.project,
            "message": f"Task '{request.task_id}' marked as done in project '{request.project}'"
        })
        
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
            return mcp_success({
                "tasks": [],
                "total_tasks": 0,
                "message": "No high-priority tasks found. All tasks are completed or no tasks exist."
            })
        
        # Convert tasks to the expected format with project information
        task_list = []
        for task in next_tasks:
            # Find which project this task belongs to
            project_name = None
            for proj_name, project in projects_manager.projects.items():
                if project.get_task(task.id):
                    project_name = proj_name
                    break
            
            task_dict = {
                **task.to_dict(),
                "project": project_name
            }
            task_list.append(task_dict)
        
        return mcp_success({
            "tasks": task_list,
            "total_tasks": len(task_list),
            "message": f"Found {len(task_list)} high-priority tasks to work on next"
        })
        
    except Exception as e:
        return mcp_failure(f"Error getting next steps: {str(e)}")


@mcp.tool()
async def pjpd_get_statistics() -> Dict[str, Any]:
    """Get comprehensive statistics about all projects.
    
    Returns:
        Standard MCP response with detailed statistics including total counts,
        breakdowns by priority, status, and project.
    """
    try:
        stats = projects_manager.get_statistics()
        
        return mcp_success({
            **stats,
            "message": f"Retrieved statistics for {stats['total_projects']} projects with {stats['total_tasks']} total tasks"
        })
        
    except Exception as e:
        return mcp_failure(f"Error getting statistics: {str(e)}")


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
        
        return mcp_success({
            "total_ideas": len(ideas),
            "ideas": ideas,
            "message": f"Retrieved {len(ideas)} ideas"
        })
        
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
        
        return mcp_success({
            **idea.to_dict(),
            "message": f"Idea added successfully with ID '{idea.id}'"
        })
        
    except Exception as e:
        return mcp_failure(f"Error adding idea: {str(e)}")


@mcp.tool()
async def pjpd_update_idea(idea_id: str, score: int = None, description: str = None) -> Dict[str, Any]:
    """Update an existing idea.
    
    Args:
        idea_id: Tag-based idea ID (format: `<tag>-XXXX`).
        score: Optional new score value.
        description: Optional new idea description.
    
    Returns:
        Standard MCP response with updated idea details or error message.
    """
    try:
        request = UpdateIdeaRequest(idea_id=idea_id, score=score, description=description)
        
        updated = ideas_manager.update_idea(request.idea_id, request.description, request.score)
        
        if not updated:
            return mcp_failure(f"Idea '{request.idea_id}' not found")
        
        # Find the updated idea to return its details
        for idea in ideas_manager.ideas:
            if idea.id == request.idea_id:
                return mcp_success({
                    **idea.to_dict(),
                    "message": f"Idea '{request.idea_id}' updated successfully"
                })
        
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

        return mcp_success({
            "idea_id": request.idea_id,
            "message": f"Idea '{request.idea_id}' marked as done (score set to 0, description prefixed)"
        })
    except Exception as e:
        return mcp_failure(f"Error marking idea as done: {str(e)}")


# --------------------------------------------------------------------------
# Epics tools
# --------------------------------------------------------------------------


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

        return mcp_success({
            "total_epics": len(epics),
            "epics": epics,
            "message": f"Retrieved {len(epics)} epics"
        })

    except Exception as e:
        return mcp_failure(f"Error listing epics: {str(e)}")


@mcp.tool()
async def pjpd_add_epic(score: int, description: str, tag: str, ideas: str = "", projects: str = "") -> Dict[str, Any]:
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
        request = AddEpicRequest(score=score, description=description, tag=tag, ideas=ideas, projects=projects)
        
        epic = epics_manager.add_epic(
            description=request.description,
            score=request.score,
            tag=request.tag,
            ideas=request.ideas.split() if request.ideas else [],
            projects=request.projects.split() if request.projects else [],
        )

        return mcp_success({
            **epic.to_dict(),
            "message": f"Epic added successfully with ID '{epic.id}'"
        })

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
        request = UpdateEpicRequest(epic_id=epic_id, score=score, description=description, ideas=ideas, projects=projects)
        
        updated = epics_manager.update_epic(
            request.epic_id,
            description=request.description,
            score=request.score,
            ideas=request.ideas.split() if request.ideas is not None else None,
            projects=request.projects.split() if request.projects is not None else None,
        )

        if not updated:
            return mcp_failure(f"Epic '{request.epic_id}' not found")

        # Find the updated epic to return its details
        for epic in epics_manager.epics:
            if epic.id == request.epic_id:
                return mcp_success({
                    **epic.to_dict(),
                    "message": f"Epic '{request.epic_id}' updated successfully"
                })

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
            return mcp_success({
                "epic_id": request.epic_id,
                "message": f"Epic '{request.epic_id}' marked as done (score set to 0)"
            })
        else:
            return mcp_failure(f"Epic '{request.epic_id}' not found")

    except Exception as e:
        return mcp_failure(f"Error marking epic as done: {str(e)}")


# --- Compatibility aliases (for unit tests and backward compatibility) ---

async def list_projects(path: str | None = None):
    """Alias for pjpd_list_projects to maintain backwards compatibility."""
    return await pjpd_list_projects(path=path)


async def new_project(project: str):
    """Alias for pjpd_new_project to maintain backwards compatibility."""
    return await pjpd_new_project(project=project)


def main():
    """Entry point for the application."""
    logger.info("Starting Pjpd MCP Server...")
    mcp.run()

if __name__ == "__main__":
    main()
