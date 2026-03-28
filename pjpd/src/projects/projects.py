"""
Projects Management
Manages a single project backed by pjpd/tasks.txt in the working directory.
"""

import logging
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional

from .project import Project, Task

logger = logging.getLogger(__name__)


class Projects:
    """Manages a single project backed by ``pjpd/tasks.txt``.

    The *project_dir* is expected to be the current working directory.
    All task data lives in ``<project_dir>/pjpd/tasks.txt``.
    """

    def __init__(self, project_dir: Path | str):
        self.project_dir = Path(project_dir).expanduser()
        self.tasks_file = self.project_dir / "pjpd" / "tasks.txt"
        self._project: Optional[Project] = None

    @property
    def project_file(self) -> Path:
        """Full path to the project tasks file."""
        return self.tasks_file

    def legacy_project_file_warning(self) -> Optional[str]:
        """Return a warning string if a legacy project file exists.

        A legacy file is ``pjpd/<dir_name>.txt`` where *<dir_name>* is the
        last component of *project_dir*.  Returns ``None`` when no such file
        is found.
        """
        dir_name = self.project_dir.name
        legacy_file = self.project_dir / "pjpd" / f"{dir_name}.txt"
        if legacy_file.exists() and legacy_file != self.tasks_file:
            return (
                f"Legacy project file '{legacy_file.name}' found in pjpd/. "
                f"This is from an older multi-project layout. Tasks are now stored in pjpd/tasks.txt. "
                f"Migrate any tasks from '{legacy_file.name}' into tasks.txt, then delete the legacy file."
            )
        return None

    @property
    def present(self) -> bool:
        """Check if the pjpd directory exists on disk."""
        return self.tasks_file.parent.exists() and self.tasks_file.parent.is_dir()

    def _ensure_project(self) -> None:
        """Create the pjpd directory and tasks file if they don't exist."""
        self.tasks_file.parent.mkdir(parents=True, exist_ok=True)
        if not self.tasks_file.exists():
            self.tasks_file.touch()

    def _load_project(self) -> Project:
        """Load (or reload) the project from disk."""
        self._project = Project(name="tasks", file_path=self.tasks_file)
        return self._project

    @property
    def project(self) -> Project:
        """The single project instance, reloaded from disk each access."""
        return self._load_project()

    # ------------------------------------------------------------------
    # Task operations
    # ------------------------------------------------------------------

    def add_task(self, description: str, priority: int, tag: str) -> Task:
        """Add a task to the project.

        Creates the pjpd directory and tasks file if they don't exist yet.
        """
        self._ensure_project()
        return self.project.add_task(description, priority, tag)

    def get_task(self, task_id: str) -> Optional[Task]:
        """Get a specific task by ID."""
        return self.project.get_task(task_id)

    def update_task(
        self,
        task_id: str,
        description: Optional[str],
        priority: Optional[int],
        status: Optional[str],
    ) -> Optional[Task]:
        """Update a task by ID."""
        return self.project.update_task(task_id, description, priority, status)

    def mark_task_done(self, task_id: str) -> Optional[Task]:
        """Mark a task as completed."""
        return self.project.mark_done(task_id)

    # ------------------------------------------------------------------
    # Aggregate helpers
    # ------------------------------------------------------------------

    def get_overview(self) -> Dict[str, Any]:
        """Get an overview of the project."""
        overview = self.project.get_overview()
        overview["project_file"] = str(self.tasks_file)
        return overview

    def get_statistics(self) -> Dict[str, Any]:
        """Get detailed statistics about the project."""
        tasks = self.project.tasks
        stats: Dict[str, Any] = {
            "total_tasks": len(tasks),
            "tasks_by_priority": defaultdict(int),
            "tasks_by_status": defaultdict(int),
            "project_file": str(self.tasks_file),
        }

        for task in tasks:
            stats["tasks_by_priority"][task.priority] += 1
            stats["tasks_by_status"][task.status] += 1

        return dict(stats)
