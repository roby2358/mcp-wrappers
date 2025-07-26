"""
Task Management
Represents a single task in a project
"""

import logging
from dataclasses import dataclass
from typing import Optional

logger = logging.getLogger(__name__)

@dataclass
class Task:
    """Represents a single task in a project"""
    # Priority mapping: text -> integer
    PRIORITY_MAP = {"high": 1, "medium": 2, "note": 3}

    id: str
    priority: int  # 1=High, 2=Medium, 3=Note
    status: str    # "ToDo" or "Done"
    description: str

    @staticmethod
    def _parse_priority(value: str, state: dict) -> tuple[bool, dict]:
        """Parse priority value and return updated state."""
        new_state = state.copy()
        if value.isdigit():
            new_state["priority"] = int(value)
        else:
            new_state["priority"] = Task.PRIORITY_MAP.get(value.lower(), state.get("priority", 2))
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

        return False, state
    
    @classmethod
    def from_text(cls, text: str) -> Optional['Task']:
        """Parse a task from text format with each property on its own line.

        Expected format::

            Priority: 1
            Status: ToDo
            ID: a12bcdef34
            This is the description which may span
            multiple lines until the record separator (---).
        """
        try:
            lines = text.strip().split('\n')

            # Defaults stored in mutable state dict for easy updating
            state = {
                "priority": 2,   # Medium by default
                "status": "ToDo",
                "task_id": "",
            }

            description_lines: list[str] = []

            for line in lines:
                stripped = line.strip()

                # Check if this line is a property and update state accordingly
                changed, state = cls._process_property_line(stripped, state)
                if not changed:
                    description_lines.append(line)

            # Must have an ID to be valid
            if not state["task_id"]:
                return None

            description = "\n".join(description_lines).strip()

            return cls(
                id=state["task_id"],
                priority=state["priority"],
                status=state["status"],
                description=description,
            )

        except Exception as e:
            logger.error(f"Error parsing task from text: {e}")
            return None
    
    def to_text(self) -> str:
        """Convert task to text format (each property on its own line)."""
        lines = [
            f"Priority: {self.priority}",
            f"Status: {self.status}",
            f"ID: {self.id}",
            self.description.strip(),
        ]
        return "\n".join(lines) 