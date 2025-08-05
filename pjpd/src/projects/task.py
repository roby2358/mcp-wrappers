"""
Task Management
Represents a single task in a project
"""

import logging
from dataclasses import dataclass
from typing import Optional

from textrec.record_id import RecordID

logger = logging.getLogger(__name__)

@dataclass
class Task:
    """Represents a single task in a project"""
    id: str
    tag: str
    priority: int  # Plain integer priority (higher numbers = higher priority)
    status: str    # "ToDo" or "Done"
    description: str

    @staticmethod
    def generate_task_id(tag: str) -> str:
        """Generate a unique task ID using the provided tag and RecordID."""
        return RecordID.generate_with_tag(tag)

    @staticmethod
    def _parse_priority(value: str, state: dict) -> tuple[bool, dict]:
        """Parse priority value and return updated state."""
        new_state = state.copy()
        if value.isdigit():
            new_state["priority"] = int(value)
        else:
            # If not a digit, keep the existing priority
            return False, state
        return True, new_state

    @staticmethod
    def _process_property_line(stripped: str, state: dict) -> tuple[bool, dict]:
        """Detect and update a property from a single stripped line."""

        # Split on first colon and check if it worked
        parts = stripped.split(":", 1)
        if len(parts) != 2:
            return False, state

        key, value = parts
        key = key.strip().lower()
        value = value.strip()

        # Property handlers
        if key == "priority":
            return Task._parse_priority(value, state)

        elif key == "status":
            new_state = state.copy()
            new_state["status"] = value
            return True, new_state

        elif key == "id":
            new_state = state.copy()
            new_state["task_id"] = value
            return True, new_state

        elif key == "tag":
            new_state = state.copy()
            new_state["tag"] = value
            return True, new_state

        return False, state
    
    @classmethod
    def from_text(cls, text: str) -> Optional['Task']:
        """Parse a task from text format with each property on its own line.

        Expected format::

            Priority: 1
            Status: ToDo
            Tag: {1-12-character-string}
            ID: {tag}-{4-character-random-string}
            This is the description which may span
            multiple lines until the record separator (---).
        """
        try:
            lines = text.strip().split('\n')

            # Defaults stored in mutable state dict for easy updating
            state = {
                "priority": 1,   # Default priority (lowest)
                "status": "ToDo",
                "task_id": "",
                "tag": "",
            }

            description_lines: list[str] = []

            for line in lines:
                stripped = line.strip()

                # Check if this line is a property and update state accordingly
                changed, state = cls._process_property_line(stripped, state)
                if not changed:
                    description_lines.append(line)

            # Generate ID if missing
            if not state["task_id"]:
                if state["tag"]:
                    state["task_id"] = Task.generate_task_id(state["tag"])
                else:
                    # Fallback to old format for backward compatibility
                    state["task_id"] = RecordID.generate()
                    state["tag"] = "legacy"
                logger.warning(f"Generated missing task ID for malformed record: {state["task_id"]}")

            # Extract tag from ID if it follows the new format
            if "-" in state["task_id"] and len(state["task_id"].split("-")[0]) <= 12:
                state["tag"] = state["task_id"].split("-")[0]
            else:
                state["tag"] = "legacy"

            description = "\n".join(description_lines).strip()

            return cls(
                id=state["task_id"],
                tag=state["tag"],
                priority=state["priority"],
                status=state["status"],
                description=description,
            )

        except Exception as e:
            logger.warning(f"Malformed task record ignored: {e}")
            return None
    
    def to_text(self) -> str:
        """Convert task to text format (each property on its own line)."""
        lines = [
            f"Priority: {self.priority:4d}",
            f"Status: {self.status}",
            f"ID: {self.id}",
            self.description.strip(),
        ]
        return "\n".join(lines) 
    
    def to_dict(self) -> dict:
        """Convert task to dictionary format for API responses."""
        return {
            "id": self.id,
            "priority": self.priority,
            "status": self.status,
            "description": self.description,
        } 