"""
Projects Management
Manages multiple projects and provides collection-level operations
"""

# Built-ins
import logging
import re
from pathlib import Path
from typing import Dict, List, Any, Optional
from collections import defaultdict

from .project import Project, Task
from .ignore_list import IgnoreList

logger = logging.getLogger(__name__)

# Characters permitted in project names (for validation)
# Keep this at module level so it is computed once and easily discovered by
# readers and other modules.
ALLOWED_NAME_CHARS: set[str] = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_@#$%! ")

# Characters permitted in sanitized filenames (spaces are replaced with underscores)
FILENAME_SAFE_CHARS: set[str] = set("abcdefghijklmnopqrstuvwxyz0123456789-_@#$%!")

class Projects:

    """Manages multiple projects and provides collection-level operations.
    
    This class handles the creation, loading, and management of multiple project
    files stored as .txt files in a designated directory. It provides methods
    for project-level operations like listing, filtering, and statistics.
    """
    
    def __init__(self, projects_dir: Path | str):
        """Create a Projects manager.

        Args:
            projects_dir: Path to the directory containing project *.txt files. If
                the directory does not yet exist it will be created automatically.
        """
        self.set_projects_dir(projects_dir)
 

    def set_projects_dir(self, projects_dir: Path | str) -> None:
        """Update the projects directory.

        The directory must exist or an exception will be raised.
        The in-memory cache will be cleared to ensure a fresh reload the next time
        projects are accessed.

        Args:
            projects_dir: Path to the directory containing project files.
            
        Raises:
            FileNotFoundError: If the specified projects directory doesn't exist.
        """
        self.projects_dir = Path(projects_dir).expanduser()

        # Check if directory exists and raise exception if it doesn't
        if not self.projects_dir.exists():
            raise FileNotFoundError(f"Projects directory does not exist: {self.projects_dir}")
        
        if not self.projects_dir.is_dir():
            raise FileNotFoundError(f"Path exists but is not a directory: {self.projects_dir}")

        self.refresh_projects()
        
    def refresh_projects(self) -> None:
        """Refresh the projects list from disk.
        
        This method reloads all project files from the projects directory,
        applying any ignore list filters, and updates the in-memory cache.
        """
        self._ignore_list = IgnoreList(self.projects_dir)
        
        self._projects = {}
            
        try:
            # Find all .txt files in the projects directory
            project_files = list(self.projects_dir.glob("*.txt"))
            
            # Apply ignore list filtering
            filtered_files = self._ignore_list.filter_files(project_files)
            
            for project_file in filtered_files:
                project_name = project_file.stem  # filename without extension
                project = Project(project_name, project_file)
                self._projects[project_name] = project
                
            logger.info(f"Loaded {len(self._projects)} projects (filtered from {len(project_files)} .txt files)")
            
        except Exception as e:
            logger.error(f"Error loading projects: {e}")
            self._projects = {}
    
    @property
    def projects(self) -> Dict[str, Project]:
        """Get all projects.
        
        Returns:
            Dictionary mapping project names to Project instances.
        """
        self.refresh_projects()
        return self._projects
    
    def get_project(self, name: str) -> Project:
        """Retrieve a project by its sanitised name.

        The provided name is sanitized to match how project files are stored on disk.
        This allows consumers to pass either the original name (which could contain 
        spaces or other characters) or the sanitized filename-friendly version.

        Args:
            name: The project name to look up. Will be sanitized for filename matching.

        Returns:
            The Project instance.

        Raises:
            ValueError: If the project doesn't exist or if the project file is ignored.
        """
        self.refresh_projects()

        # Look up the sanitized name (since that's how files are stored)
        safe_name = self._sanitize_name(name)
        
        # Check if the sanitized name + .txt would be ignored
        if self._ignore_list.should_ignore(f"{safe_name}.txt"):
            raise ValueError(f"Project '{name}' is ignored")
        
        project = self.projects.get(safe_name)
        if project is not None:
            return project
            
        raise ValueError(f"Project '{name}' does not exist")
    
    def create_project(self, name: str) -> Project:
        """Create a new project.
        
        Args:
            name: The name for the new project. Will be sanitized for filename use.
            
        Returns:
            The newly created Project instance.
        """
        # Sanitize the project name for filename
        safe_name = self._sanitize_name(name)
        if self._ignore_list.should_ignore(f"{safe_name}.txt"):
            raise ValueError(f"Project name {name} is ignored")
        
        file_path = self.projects_dir / f"{safe_name}.txt"
        
        if not file_path.exists():
            file_path.touch()
        
        project = Project(safe_name, file_path)
        self.projects[safe_name] = project
        
        return project
    
    def _sanitize_name(self, name: str) -> str:
        """Sanitize a project name for use as a filename.
        
        Converts the name to lowercase, replaces disallowed characters with
        underscores, reduces runs of underscores to a single underscore, and
        ensures the result is a valid filename.
        
        Args:
            name: The original project name to sanitize.
            
        Returns:
            A sanitized filename-safe version of the name.
        """
        # Normalise to lower-case for consistency and easier look-ups
        name = name.lower()

        # Replace all disallowed characters with underscores
        transformed = [ch if ch in FILENAME_SAFE_CHARS else "_" for ch in name]
        name = re.sub(r"_+", "_", "".join(transformed))

        # Strip leading / trailing underscores or dots to avoid hidden / invalid
        # filenames on some filesystems.
        name = name.strip("._")

        if not name:
            raise ValueError(f"Project name cannot be empty or invalid: {name}")
        
        return name
    
    def list_projects(self) -> List[Dict[str, Any]]:
        """List all projects with their task counts.
        
        Returns:
            List of dictionaries containing project information including name,
            file path, and task count.
        """
        self.refresh_projects()
        
        projects_info = []
        
        for project in self.projects.values():
            projects_info.append({
                "name": project.name,
                "file_path": str(project.file_path.relative_to(self.projects_dir)),
                "task_count": project.get_task_count()
            })
        
        return projects_info
    
    def get_all_tasks(self, project_filter: Optional[str] = None, 
                      priority_filter: Optional[int] = None,
                      status_filter: Optional[str] = None) -> List[Task]:
        """Get all tasks across all projects with optional filtering.
        
        Args:
            project_filter: Optional project name to filter tasks by. If specified,
                only tasks from this project will be returned.
            priority_filter: Optional minimum priority level. Only tasks with
                priority >= this value will be returned.
            status_filter: Optional status filter. Only tasks with this exact
                status will be returned.
                
        Returns:
            List of Task instances matching the specified filters.
        """
        self.refresh_projects()
        
        # If a project filter is specified, validate that the project exists
        if project_filter:
            try:
                target_project = self.get_project(project_filter)
                # Only process the specified project
                tasks = target_project.tasks
                
                if priority_filter is not None:
                    tasks = [t for t in tasks if t.priority >= priority_filter]
                    
                if status_filter is not None:
                    tasks = [t for t in tasks if t.status == status_filter]
                    
                return tasks
            except ValueError:
                # Project doesn't exist, return empty list
                return []
        
        all_tasks = []
        
        for project in self.projects.values():
            tasks = project.tasks
            
            if priority_filter is not None:
                tasks = [t for t in tasks if t.priority >= priority_filter]
                
            if status_filter is not None:
                tasks = [t for t in tasks if t.status == status_filter]
                
            all_tasks.extend(tasks)
        
        return all_tasks
    
    def add_task(self, project_name: str, description: str, priority: int = 2, tag: str = "task") -> Optional[Task]:
        """Add a task to a project.
        
        Args:
            project_name: Name of the project to add the task to.
            description: Description of the task.
            priority: Priority level for the task (default: 2).
            tag: Tag string for the task (default: "task").
            
        Returns:
            The created Task instance, or None if the operation failed.
            
        Raises:
            ValueError: If the project does not exist.
        """
        self.refresh_projects()
        
        project = self.get_project(project_name)
        return project.add_task(description, priority, tag)
    
    def get_task(self, project_name: str, task_id: str) -> Optional[Task]:
        """Get a specific task from a project.
        
        Args:
            project_name: Name of the project containing the task.
            task_id: Unique identifier of the task to retrieve.
            
        Returns:
            The Task instance if found, None otherwise.
            
        Raises:
            ValueError: If the project does not exist.
        """
        self.refresh_projects()

        project = self.get_project(project_name)
        return project.get_task(task_id)
    
    def update_task(self, project_name: str, task_id: str, 
                   description: Optional[str] = None,
                   priority: Optional[int] = None,
                   status: Optional[str] = None) -> Optional[Task]:
        """Update a task in a project.
        
        Args:
            project_name: Name of the project containing the task.
            task_id: Unique identifier of the task to update.
            description: New description for the task (optional).
            priority: New priority level for the task (optional).
            status: New status for the task (optional).
            
        Returns:
            The updated Task instance if found, None otherwise.
            
        Raises:
            ValueError: If the project does not exist.
        """
        project = self.get_project(project_name)
        return project.update_task(task_id, description, priority, status)
    
    def mark_task_done(self, project_name: str, task_id: str) -> Optional[Task]:
        """Mark a task as completed.
        
        Args:
            project_name: Name of the project containing the task.
            task_id: Unique identifier of the task to mark as done.
            
        Returns:
            The updated Task instance if found, None otherwise.
            
        Raises:
            ValueError: If the project does not exist.
        """
        project = self.get_project(project_name)
        return project.mark_done(task_id)
    
    def get_overview(self) -> Dict[str, Any]:
        """Get an overview of all projects.
        
        Returns:
            Dictionary containing summary statistics including total projects,
            total tasks, todo tasks, done tasks, and individual project overviews.
        """
        self.refresh_projects()
        
        total_projects = len(self.projects)
        total_tasks = 0
        total_todo = 0
        total_done = 0
        
        project_overviews = []
        
        for project in self.projects.values():
            overview = project.get_overview()
            project_overviews.append(overview)
            
            total_tasks += overview["total_tasks"]
            total_todo += overview["todo_tasks"]
            total_done += overview["done_tasks"]
        
        return {
            "total_projects": total_projects,
            "total_tasks": total_tasks,
            "total_todo": total_todo,
            "total_done": total_done,
            "projects": project_overviews
        }
    
    def get_next_steps(self, limit: int = 5) -> List[Task]:
        """Get high-priority tasks to work on next.
        
        Returns the highest priority todo tasks across all projects,
        sorted by priority (highest first).
        
        Args:
            limit: Maximum number of tasks to return (default: 5).
            
        Returns:
            List of Task instances sorted by priority (highest first).
        """
        self.refresh_projects()
        
        # Get all todo tasks
        todo_tasks = self.get_all_tasks(status_filter="ToDo")
        
        # Sort by priority (plain integer, higher numbers = higher priority)
        todo_tasks.sort(key=lambda t: t.priority, reverse=True)
        
        # Return the top tasks up to the limit
        return todo_tasks[:limit]
    
    def sort_project(self, project_name: str) -> bool:
        """Re-sort tasks within a project by priority.
        
        Sorts all tasks in the specified project by priority (highest first)
        and saves the sorted order to disk.
        
        Args:
            project_name: Name of the project to sort.
            
        Returns:
            True if the project was sorted successfully.
            
        Raises:
            ValueError: If the project does not exist.
        """
        project = self.get_project(project_name)
        
        # Get all tasks and sort by priority (higher numbers first)
        tasks = project.tasks
        tasks.sort(key=lambda t: t.priority, reverse=True)
        
        # Save the sorted tasks
        project._save_tasks()
        return True
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get detailed statistics about all projects.
        
        Returns:
            Dictionary containing comprehensive statistics including total counts,
            breakdowns by priority, status, and project.
        """
        self.refresh_projects()
        
        stats = {
            "total_projects": len(self.projects),
            "total_tasks": 0,
            "tasks_by_priority": defaultdict(int),
            "tasks_by_status": defaultdict(int),
            "tasks_by_project": defaultdict(int)
        }
        
        for project in self.projects.values():
            project_task_count = len(project.tasks)
            stats["total_tasks"] += project_task_count
            stats["tasks_by_project"][project.name] = project_task_count
            
            for task in project.tasks:
                stats["tasks_by_priority"][task.priority] += 1
                stats["tasks_by_status"][task.status] += 1
        
        return dict(stats) 