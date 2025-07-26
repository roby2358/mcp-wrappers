"""
Project Management
Represents a single project with its tasks stored in a text file
"""

import logging
import sys
from pathlib import Path
from typing import Dict, List, Any, Optional
from dataclasses import dataclass
from datetime import datetime

from textrec.text_records import TextRecords

# Initialize logging to stderr
logging.basicConfig(level=logging.INFO, stream=sys.stderr)
logger = logging.getLogger(__name__)

@dataclass
class Task:
    """Represents a single task in a project"""
    id: str
    priority: int  # 1=High, 2=Medium, 3=Note
    status: str    # "ToDo" or "Done"
    description: str
    created_at: datetime
    completed_at: Optional[datetime] = None
    
    @classmethod
    def from_text(cls, text: str) -> Optional['Task']:
        """Parse a task from text format"""
        try:
            lines = text.strip().split('\n')
            if len(lines) < 3:
                return None
                
            # Parse the header line: ID [Priority] Status
            header = lines[0].strip()
            if not header:
                return None
                
            # Extract ID, priority, and status
            parts = header.split()
            if len(parts) < 3:
                return None
                
            task_id = parts[0]
            
            # Find priority and status
            priority = 2  # Default to Medium
            status = "ToDo"  # Default to ToDo
            
            for part in parts[1:]:
                if part in ["High", "Medium", "Note"]:
                    priority = {"High": 1, "Medium": 2, "Note": 3}[part]
                elif part in ["ToDo", "Done"]:
                    status = part
            
            # Description is everything after the header
            description = '\n'.join(lines[1:]).strip()
            
            return cls(
                id=task_id,
                priority=priority,
                status=status,
                description=description,
                created_at=datetime.now()  # We don't store creation time in text format
            )
            
        except Exception as e:
            logger.error(f"Error parsing task from text: {e}")
            return None
    
    def to_text(self) -> str:
        """Convert task to text format for storage"""
        priority_text = {1: "High", 2: "Medium", 3: "Note"}[self.priority]
        header = f"{self.id} {priority_text} {self.status}"
        return f"{header}\n{self.description}"

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
        return self._tasks or []
    
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
    
    def add_task(self, description: str, priority: int = 2) -> Task:
        """Add a new task to this project"""
        import uuid
        
        # Generate a unique 12-character ID
        task_id = str(uuid.uuid4())[:12]
        
        task = Task(
            id=task_id,
            priority=priority,
            status="ToDo",
            description=description,
            created_at=datetime.now()
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
            if status == "Done" and task.completed_at is None:
                task.completed_at = datetime.now()
            elif status == "ToDo":
                task.completed_at = None
        
        self._save_tasks()
        return task
    
    def mark_done(self, task_id: str) -> Optional[Task]:
        """Mark a task as completed"""
        return self.update_task(task_id, status="Done")
    
    def _save_tasks(self) -> None:
        """Save tasks to the project file"""
        try:
            # Ensure directory exists
            self.file_path.parent.mkdir(parents=True, exist_ok=True)
            
            # Convert tasks to text format
            task_texts = [task.to_text() for task in self.tasks]
            
            # Join with --- separators
            content = '\n---\n'.join(task_texts)
            
            # Write to file
            with open(self.file_path, 'w', encoding='utf-8') as f:
                f.write(content)
                
        except Exception as e:
            logger.error(f"Error saving tasks for project {self.name}: {e}")
    
    def get_task_count(self) -> int:
        """Get the total number of tasks"""
        return len(self.tasks)
    
    def get_tasks_by_priority(self, priority: int) -> List[Task]:
        """Get all tasks with a specific priority"""
        return [task for task in self.tasks if task.priority == priority]
    
    def get_tasks_by_status(self, status: str) -> List[Task]:
        """Get all tasks with a specific status"""
        return [task for task in self.tasks if task.status == status]
    
    def get_overview(self) -> Dict[str, Any]:
        """Get an overview of this project"""
        todo_tasks = self.get_tasks_by_status("ToDo")
        done_tasks = self.get_tasks_by_status("Done")
        
        high_priority_todo = [t for t in todo_tasks if t.priority == 1]
        medium_priority_todo = [t for t in todo_tasks if t.priority == 2]
        note_todo = [t for t in todo_tasks if t.priority == 3]
        
        return {
            "name": self.name,
            "total_tasks": len(self.tasks),
            "todo_tasks": len(todo_tasks),
            "done_tasks": len(done_tasks),
            "high_priority_todo": len(high_priority_todo),
            "medium_priority_todo": len(medium_priority_todo),
            "note_todo": len(note_todo)
        } 