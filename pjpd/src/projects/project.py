"""
Project Management
Represents a single project with its tasks stored in a text file
"""

import logging
from pathlib import Path
import uuid
from typing import Dict, List, Any, Optional

from textrec.text_records import TextRecords
from .task import Task

logger = logging.getLogger(__name__)

class Project:
    """Represents a single project with its tasks"""
    
    def __init__(self, name: str, file_path: Path):
        self.name = name
        self.file_path = Path(file_path)
        self.text_records = TextRecords(self.file_path.parent)
        self._tasks: Optional[List[Task]] = None
        
    @property
    def tasks(self) -> List[Task]:
        """Get all tasks in this project, loading from file if needed"""
        if self._tasks is None:
            self._load_tasks()
        return self._tasks
    
    def _load_tasks(self) -> None:
        """Load tasks from the project file"""
        if not self.file_path.exists():
            self._tasks = []
            return
            
        try:
            records = self.text_records.parse_file(self.file_path)
            self._tasks = []
            
            for record in records:
                task = Task.from_text(record["text"])
                if task:
                    self._tasks.append(task)
                    
        except Exception as e:
            logger.error(f"Error loading tasks for project {self.name}: {e}")
            self._tasks = []
    
    def add_task(self, description: str, priority: int = 2, tag: str = "task") -> Task:
        """Add a new task to this project"""
        # Generate a unique task ID using the provided tag
        task = Task(
            id=Task.generate_task_id(tag),
            tag=tag,
            priority=priority,
            status="ToDo",
            description=description
        )
        
        self.tasks.append(task)
        self._save_tasks()
        return task
    
    def get_task(self, task_id: str) -> Optional[Task]:
        """Get a task by its ID"""
        for task in self.tasks:
            if task.id == task_id:
                return task
        return None
    
    def update_task(self, task_id: str, description: Optional[str] = None, 
                   priority: Optional[int] = None, status: Optional[str] = None) -> Optional[Task]:
        """Update an existing task"""
        task = self.get_task(task_id)
        if not task:
            return None
            
        if description is not None:
            task.description = description
        if priority is not None:
            task.priority = priority
        if status is not None:
            task.status = status
        
        self._save_tasks()
        return task
    
    def mark_done(self, task_id: str) -> Optional[Task]:
        """Mark a task as completed"""
        return self.update_task(task_id, status="Done")
    
    def _save_tasks(self) -> None:
        """Save tasks to the project file"""
        try:
            # Sort tasks by priority (descending) before saving
            sorted_tasks = sorted(self.tasks, key=lambda task: task.priority, reverse=True)
            
            # Convert tasks to text format
            task_texts = [task.to_text() for task in sorted_tasks]
            
            # Join with --- separators
            content = '\n---\n'.join(task_texts)
            
            # Always write the content, even if empty (for empty projects)
            self.text_records.write_atomic(self.file_path, content)
                
        except Exception as e:
            logger.error(f"Error saving tasks for project {self.name}: {e}")
            raise
    
    def get_task_count(self) -> int:
        """Get the total number of tasks"""
        return len(self.tasks)
    
    def get_tasks_by_priority(self, priority: int) -> List[Task]:
        """Get all tasks with priority >= the specified value"""
        return [task for task in self.tasks if task.priority >= priority]
    
    def get_tasks_by_status(self, status: str) -> List[Task]:
        """Get all tasks with a specific status"""
        return [task for task in self.tasks if task.status == status]
    
    def get_overview(self) -> Dict[str, Any]:
        """Get an overview of this project"""
        todo_tasks = self.get_tasks_by_status("ToDo")
        done_tasks = self.get_tasks_by_status("Done")
        
        high_priority_todo = [t for t in todo_tasks if t.priority >= 100]
        medium_priority_todo = [t for t in todo_tasks if 10 <= t.priority < 100]
        low_priority_todo = [t for t in todo_tasks if t.priority < 10]
        
        return {
            "name": self.name,
            "total_tasks": len(self.tasks),
            "todo_tasks": len(todo_tasks),
            "done_tasks": len(done_tasks),
            "high_priority_todo": len(high_priority_todo),
            "medium_priority_todo": len(medium_priority_todo),
            "low_priority_todo": len(low_priority_todo)
        }
    
    def filter_tasks(self, priority: Optional[int] = None, status: Optional[str] = None) -> List[Dict[str, Any]]:
        """Filter tasks by priority and status, returning them as dictionaries.
        
        Args:
            priority: Filter tasks by priority level (plain integer). Returns all tasks >= this priority.
            status: Filter tasks by status ("ToDo" or "Done").
            
        Returns:
            List of task dictionaries with id, priority, status, and description.
        """
        filtered_tasks = []
        
        for task in self.tasks:
            # Filter by priority if specified (>= priority)
            if priority is not None and task.priority < priority:
                continue
                
            # Filter by status if specified (case-insensitive comparison)
            if status is not None and task.status.lower() != status.lower():
                continue
                
            filtered_tasks.append({
                "id": task.id,
                "project": self.name,
                "priority": task.priority,
                "status": task.status,
                "description": task.description,
            })
            
        return filtered_tasks 