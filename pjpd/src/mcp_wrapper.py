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
from config import Config

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

# Create the MCP server instance
mcp = FastMCP("projectmcp")

# Create configuration and projects manager instances
config = Config()
projects_manager = Projects(Path(config(Config.PROJECTS_DIRECTORY, "~/projects")))

# Strict typing helpers -----------------------------------------------------


class TaskDict(TypedDict):
    """Dictionary representation of a task returned by the API."""

    id: str
    project: str
    priority: int  # Plain integer priority (higher numbers = higher priority)
    status: str  # Keep string to avoid Enum/JSON serialisation issues
    description: str


class MCPResponseSuccess(TypedDict):
    """Successful MCP response schema."""

    success: Literal[True]
    result: Any
    error: str


class MCPResponseFailure(TypedDict):
    """Failed MCP response schema."""

    success: Literal[False]
    result: str
    error: str


MCPResponse = Union[MCPResponseSuccess, MCPResponseFailure]

# MCP Tools and prompts -----------------------------------------------------


def mcp_success(result: Any) -> MCPResponse:
    """Return a successful MCP response with the given result."""
    return MCPResponseSuccess(
        success=True,
        result=result,
        error="",
    )

def mcp_failure(error_message: str) -> MCPResponse:
    """Return a failed MCP response with the given error message."""
    return MCPResponseFailure(
        success=False,
        result="",
        error=error_message,
    )

@mcp.prompt()
def intro() -> str:
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
async def list_projects(path: str = None) -> Dict[str, Any]:
    """
    List all projects with their task counts and overview.
    
    Args:
        path: Optional path to the projects directory. If not provided, uses the configured path or defaults to ~/projects.
    
    Returns a comprehensive overview of all projects including task counts, 
    todo/done status, and project details.
    """
    try:
        # Set the projects directory if a path is provided, otherwise use config
        if path:
            projects_manager.set_projects_dir(Path(path))
        
        overview = projects_manager.get_overview()
        
        if overview["total_projects"] == 0:
            return mcp_success(NO_PROJECTS_RESPONSE)
        
        return mcp_success(overview)
        
    except Exception as e:
        return mcp_failure(f"Error listing projects: {str(e)}")

@mcp.tool()
async def new_project(project: str) -> Dict[str, Any]:
    """Create a new empty project file.
    
    Args:
        project: The name of the project to create.
    
    Returns:
        Standard MCP response indicating success or failure.
    """
    try:
        created_project = projects_manager.create_project(project)
        
        return mcp_success({
            "project_name": created_project.name,
            "file_path": str(created_project.file_path),
            "message": f"Project '{created_project.name}' created successfully"
        })
        
    except Exception as e:
        return mcp_failure(f"Error creating project: {str(e)}")


@mcp.tool()
async def add_task(project: str, description: str, priority: int = 2) -> Dict[str, Any]:
    """Add a new task to a project.
    
    Args:
        project: The name of the project to add the task to. If the project doesn't exist, it will be created.
        description: The description of the task.
        priority: The priority level of the task (higher numbers = higher priority). Defaults to 2.
    
    Returns:
        Standard MCP response with task details or error message.
    """
    try:
        task = projects_manager.add_task(project, description, priority)
        
        if task:
            return mcp_success({
                **task.to_dict(),
                "project": project,
                "message": f"Task added to project '{project}' successfully"
            })
        else:
            return mcp_failure(f"Failed to add task to project '{project}'")
        
    except Exception as e:
        return mcp_failure(f"Error adding task: {str(e)}")


@mcp.tool()
async def update_task(project: str, task_id: str, description: str = None, 
                     priority: int = None, status: str = "ToDo") -> Dict[str, Any]:
    """Update an existing task in a project.
    
    Args:
        project: The name of the project containing the task.
        task_id: The unique ID of the task to update.
        description: Optional new description for the task.
        priority: Optional new priority level (higher numbers = higher priority).
        status: Optional new status ("ToDo" or "Done"). Defaults to "ToDo".
    
    Returns:
        Standard MCP response with updated task details or error message.
    """
    try:
        updated_task = projects_manager.update_task(
            project, task_id, description, priority, status
        )
        
        if updated_task:
            return mcp_success({
                **updated_task.to_dict(),
                "project": project,
                "message": f"Task '{task_id}' updated successfully in project '{project}'"
            })
        else:
            return mcp_failure(f"Task '{task_id}' not found in project '{project}'")
        
    except Exception as e:
        return mcp_failure(f"Error updating task: {str(e)}")


@mcp.tool()
async def list_tasks(
    project: str | None = None,
    priority: int | None = None,
    status: str | None = None,
    max_results: int | None = None,
) -> MCPResponse:
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
        status_str: str | None
        if status is None:
            status_str = None
        else:
            status_str = status.strip().lower()

        tasks: List[TaskDict] = []

        # Iterate over projects and gather tasks that match filters
        for proj in projects_manager.projects.values():
            if project and proj.name.lower() != project.lower():
                continue

            filtered_tasks = proj.filter_tasks(priority=priority, status=status_str)
            # filter_tasks returns plain Dicts; cast for stricter typing purposes
            tasks.extend(filtered_tasks)  # type: ignore[arg-type]

        # Sort tasks by priority (higher numbers first) then description for deterministic output
        tasks.sort(key=lambda item: (-item["priority"], item["description"].lower()))

        # Apply max_results limit if provided, otherwise use config default
        if max_results is not None and max_results > 0:
            tasks = tasks[:max_results]
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
async def mark_done(project: str, task_id: str) -> Dict[str, Any]:
    """Mark a task as completed.
    
    Args:
        project: The name of the project containing the task.
        task_id: The unique 10-character task ID to mark as done.
    
    Returns:
        Standard MCP response with updated task details or error message.
    """
    try:
        updated_task = projects_manager.update_task(
            project, task_id, description=None, priority=0, status="Done"
        )
        
        if not updated_task:
            return mcp_failure(f"Task '{task_id}' not found in project '{project}'")
        
        return mcp_success({
            **updated_task.to_dict(),
            "project": project,
            "message": f"Task '{task_id}' marked as done in project '{project}'"
        })
        
    except Exception as e:
        return mcp_failure(f"Error marking task as done: {str(e)}")


@mcp.tool()
async def next_steps(max_results: int = 5) -> Dict[str, Any]:
    """Determine high-priority tasks to work on next.
    
    Args:
        max_results: Maximum number of suggestions to return. Defaults to 5.
    
    Returns:
        Standard MCP response with list of high-priority tasks to work on next.
    """
    try:
        next_tasks = projects_manager.get_next_steps(max_results)
        
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


def main():
    """Entry point for the application."""
    print("Starting Hello World MCP Server...", file=sys.stderr)
    mcp.run()

if __name__ == "__main__":
    main()
