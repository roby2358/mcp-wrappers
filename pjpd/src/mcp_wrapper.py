#!/usr/bin/env python3
"""
Hello World MCP Server using the official MCP SDK
"""

import asyncio
import logging
import sys
from pathlib import Path
from typing import Dict, Any, List

from mcp.server.fastmcp import FastMCP
from projects import Projects

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
mcp = FastMCP("hello-world")

# Create a single Projects instance to track the path
projects_manager = Projects()

def mcp_success(result: Any) -> Dict[str, Any]:
    """Return a successful MCP response with the given result."""
    return {
        "success": True,
        "result": result,
        "error": ""
    }

def mcp_failure(error_message: str) -> Dict[str, Any]:
    """Return a failed MCP response with the given error message."""
    return {
        "success": False,
        "result": "",
        "error": error_message
    }

@mcp.prompt()
def intro() -> str:
    """
    Return an introductory prompt that describes the ProjectMCP system.
    """
    try:
        intro_path = Path(__file__).parent.parent / "resources" / "intro.txt"
        with open(intro_path, "r", encoding="utf-8") as f:
            return f.read()
    except FileNotFoundError:
        return "ProjectMCP Intro text missing: FileNotFoundError"
    except Exception as e:
        return f"Error loading intro text: {str(e)}"

@mcp.tool()
async def list_projects(path: str = None) -> Dict[str, Any]:
    """
    List all projects with their task counts and overview.
    
    Args:
        path: Optional path to the projects directory. If not provided, uses the previously set path or defaults to ~/projects.
    
    Returns a comprehensive overview of all projects including task counts, 
    todo/done status, and project details.
    """
    try:
        # Set the projects directory if a path is provided
        if path:
            projects_dir = Path(path)
            projects_manager.set_projects_dir(projects_dir)
        elif projects_manager.projects_dir is None:
            # Use default if no path has been set yet
            projects_dir = Path.home() / "projects"
            projects_manager.set_projects_dir(projects_dir)
        
        # Get comprehensive project overview
        overview = projects_manager.get_overview()
        
        if overview["total_projects"] == 0:
            return mcp_success({
                "projects": [],
                "total_projects": 0,
                "total_tasks": 0,
                "total_todo": 0,
                "total_done": 0,
                "message": "No projects found. Create your first project by adding a task!"
            })
        
        return mcp_success(overview)
        
    except Exception as e:
        return mcp_failure(f"Error listing projects: {str(e)}")


# ---------------------------------------------------------------------------
# list_tasks tool
# ---------------------------------------------------------------------------


@mcp.tool()
async def list_tasks(
    project: str | None = None,
    priority: int | None = None,
    status: str | None = None,
    max_results: int | None = None,
) -> Dict[str, Any]:
    """List tasks with optional filtering.

    Args:
        project: Filter tasks by a specific project name.
        priority: Filter tasks by priority level (1=High, 2=Medium, 3=Note).
        status: Filter tasks by status ("ToDo" or "Done").
        max_results: Maximum number of tasks to return.

    Returns:
        Standard MCP response containing a list of matching tasks or an error.
    """

    try:
        # Ensure the projects directory is set (use default if not already defined)
        if projects_manager.projects_dir is None:
            default_dir = Path.home() / "projects"
            projects_manager.set_projects_dir(default_dir)

        # Helper to normalise status input (keep None or exact value)
        if status is not None:
            status = status.strip()

        tasks: List[Dict[str, Any]] = []

        # Iterate over projects and gather tasks that match filters
        for proj in projects_manager.projects.values():
            if project and proj.name != project:
                continue

            for t in proj.tasks:
                if priority is not None and t.priority != priority:
                    continue
                if status is not None and t.status != status:
                    continue

                tasks.append({
                    "id": t.id,
                    "project": proj.name,
                    "priority": t.priority,
                    "status": t.status,
                    "description": t.description,
                })

        # Sort tasks by priority then description for deterministic output
        tasks.sort(key=lambda item: (item["priority"], item["description"].lower()))

        # Apply max_results limit if provided
        if max_results is not None and max_results > 0:
            tasks = tasks[:max_results]

        return mcp_success({
            "total_tasks": len(tasks),
            "tasks": tasks,
        })

    except Exception as e:
        return mcp_failure(f"Error listing tasks: {str(e)}")

@mcp.tool()
async def echo(message: str) -> Dict[str, Any]:
    """
    Echo back the provided message.
    This tool simply returns the message that was sent to it.
    """
    if not message:
        return mcp_failure("Error: No message provided.")

    try:
        # Simply return the message
        return mcp_success(message)

    except Exception as e:
        return mcp_failure(f"Error processing message: {str(e)}")

def main():
    """Entry point for the application."""
    print("Starting Hello World MCP Server...", file=sys.stderr)
    mcp.run()

if __name__ == "__main__":
    main()
