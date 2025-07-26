#!/usr/bin/env python3
"""
Hello World MCP Server using the official MCP SDK
"""

import asyncio
import sys
from pathlib import Path
from typing import Dict, Any, List

from mcp.server.fastmcp import FastMCP
from projects import Projects

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
    List all projects with their task counts.
    
    Args:
        path: Optional path to the projects directory. If not provided, uses the previously set path or defaults to ~/projects.
    
    Returns a list of all projects found in the projects directory, 
    including the number of tasks in each project.
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
        
        # Get project list
        projects_list = projects_manager.list_projects()
        
        if not projects_list:
            return mcp_success({
                "projects": [],
                "message": "No projects found. Create your first project by adding a task!"
            })
        
        # Calculate totals
        total_tasks = sum(project["task_count"] for project in projects_list)
        
        return mcp_success({
            "projects": projects_list,
            "total_projects": len(projects_list),
            "total_tasks": total_tasks
        })
        
    except Exception as e:
        return mcp_failure(f"Error listing projects: {str(e)}")

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
