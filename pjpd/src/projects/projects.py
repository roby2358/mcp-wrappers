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

logger = logging.getLogger(__name__)

# Characters permitted to survive in a sanitised project filename.
# Keep this at module level so it is computed once and easily discovered by
# readers and other modules.
ALLOWED_NAME_CHARS: set[str] = set("abcdefghijklmnopqrstuvwxyz0123456789-_@#$%!")

class Projects:

    """Manages multiple projects and provides collection-level operations"""
    
    def __init__(self, projects_dir: Path | str | None = None):
        """Create a Projects manager.

        Args:
            projects_dir: Path to the directory containing project *.txt files. If
                the directory does not yet exist it will be created automatically.
                When *None*, the directory must be provided later via
                `set_projects_dir` before attempting to access projects.
        """

        # Normalise to a ``Path`` (and expand ~ for user convenience)
        self.projects_dir = Path(projects_dir).expanduser() if projects_dir else None

        # Create the directory up-front so subsequent file operations succeed
        if self.projects_dir is not None:
            self.projects_dir.mkdir(parents=True, exist_ok=True)

        self._projects: Optional[Dict[str, Project]] = None
        
    def set_projects_dir(self, projects_dir: Path | str) -> None:
        """Update the projects directory.

        The directory will be created if it does not already exist and the
        in-memory cache will be cleared to ensure a fresh reload the next time
        projects are accessed.
        """

        self.projects_dir = Path(projects_dir).expanduser()

        # Guarantee directory existence so downstream operations are safe
        self.projects_dir.mkdir(parents=True, exist_ok=True)

        # Clear cache to force reload on next access
        self._projects = None
        
    @property
    def projects(self) -> Dict[str, Project]:
        """Get all projects, loading from disk if needed"""
        if self._projects is None:
            self._load_projects()

        # _load_projects() guarantees ``self._projects`` is at least an empty
        # dictionary.  We must return the *same* object so that callers can
        # freely mutate it (e.g. ``self.projects[<name>] = project``) and the
        # changes remain visible to the manager.  Returning a new empty dict
        # (as the previous implementation did when the cache was empty) breaks
        # this contract and causes newly-created projects to disappear from
        # the in-memory cache.
        return self._projects
    
    def _load_projects(self) -> None:
        """Load all projects from the projects directory"""
        self._projects = {}
        
        if not self.projects_dir or not self.projects_dir.exists():
            return
            
        try:
            # Find all .txt files in the projects directory
            project_files = list(self.projects_dir.glob("*.txt"))
            
            for project_file in project_files:
                project_name = project_file.stem  # filename without extension
                project = Project(project_name, project_file)
                self._projects[project_name] = project
                
            logger.info(f"Loaded {len(self._projects)} projects")
            
        except Exception as e:
            logger.error(f"Error loading projects: {e}")
            self._projects = {}
    
    def get_project(self, name: str) -> Optional[Project]:
        """Retrieve a project by its *original* or sanitised name.

        Consumers may pass either the exact name they initially provided when
        the project was created (which could contain spaces or other
        characters) *or* the sanitised filename-friendly version.  We therefore
        attempt both look-ups to provide the most ergonomic API.
        """

        # Direct look-up first (handles already-sanitised names)
        project = self.projects.get(name)
        if project is not None:
            return project

        # Fall back to the sanitised variant
        safe_name = self._sanitize_name(name)
        return self.projects.get(safe_name)
    
    def create_project(self, name: str) -> Project:
        """Create a new project"""
        # Sanitize the project name for filename
        safe_name = self._sanitize_name(name)
        file_path = self.projects_dir / f"{safe_name}.txt"
        
        # Ensure the projects directory exists
        self.projects_dir.mkdir(parents=True, exist_ok=True)
        
        # Create an empty project file if it doesn't exist
        if not file_path.exists():
            file_path.touch()
        
        project = Project(safe_name, file_path)
        self.projects[safe_name] = project
        
        return project
    
    def _sanitize_name(self, name: str) -> str:
        """Sanitize a project name for use as a filename"""
        # Normalise to lower-case for consistency and easier look-ups
        name = name.lower()

        # Replace all disallowed characters with underscores
        transformed = [ch if ch in ALLOWED_NAME_CHARS else "_" for ch in name]
        name = re.sub(r"_+", "_", "".join(transformed))

        # Strip leading / trailing underscores or dots to avoid hidden / invalid
        # filenames on some filesystems.
        name = name.strip("._")

        return name or "project"
    
    def list_projects(self) -> List[Dict[str, Any]]:
        """List all projects with their task counts"""
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
        """Get all tasks across all projects with optional filtering"""
        all_tasks = []
        
        for project in self.projects.values():
            if project_filter and project.name != project_filter:
                continue
                
            tasks = project.tasks
            
            if priority_filter is not None:
                tasks = [t for t in tasks if t.priority >= priority_filter]
                
            if status_filter is not None:
                tasks = [t for t in tasks if t.status == status_filter]
                
            all_tasks.extend(tasks)
        
        return all_tasks
    
    def add_task(self, project_name: str, description: str, priority: int = 2) -> Optional[Task]:
        """Add a task to a project, creating the project if it doesn't exist"""
        project = self.get_project(project_name)
        if not project:
            project = self.create_project(project_name)
        
        return project.add_task(description, priority)
    
    def get_task(self, project_name: str, task_id: str) -> Optional[Task]:
        """Get a specific task from a project"""
        project = self.get_project(project_name)
        if not project:
            return None
        return project.get_task(task_id)
    
    def update_task(self, project_name: str, task_id: str, 
                   description: Optional[str] = None,
                   priority: Optional[int] = None,
                   status: Optional[str] = None) -> Optional[Task]:
        """Update a task in a project"""
        project = self.get_project(project_name)
        if not project:
            return None
        return project.update_task(task_id, description, priority, status)
    
    def mark_task_done(self, project_name: str, task_id: str) -> Optional[Task]:
        """Mark a task as completed"""
        project = self.get_project(project_name)
        if not project:
            return None
        return project.mark_done(task_id)
    
    def get_overview(self) -> Dict[str, Any]:
        """Get an overview of all projects"""
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
        """Get high-priority tasks to work on next"""
        # Get all todo tasks
        todo_tasks = self.get_all_tasks(status_filter="ToDo")
        
        # Sort by priority (plain integer, higher numbers = higher priority)
        todo_tasks.sort(key=lambda t: t.priority, reverse=True)
        
        # Return the top tasks up to the limit
        return todo_tasks[:limit]
    
    def sort_project(self, project_name: str) -> bool:
        """Re-sort tasks within a project by priority"""
        project = self.get_project(project_name)
        if not project:
            return False
        
        # Get all tasks and sort by priority (higher numbers first)
        tasks = project.tasks
        tasks.sort(key=lambda t: t.priority, reverse=True)
        
        # Save the sorted tasks
        project._save_tasks()
        return True
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get detailed statistics about all projects"""
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