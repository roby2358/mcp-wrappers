"""
Idea Management
Represents a single idea record.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass
from typing import Optional

from textrec.record_id import RecordID

logger = logging.getLogger(__name__)


@dataclass
class Idea:
    """Represents a single idea item.

    The *Idea Record Format* (see SPEC.md) requires::

        ID: {10-character-id}
        Score: {integer}
        Free-form description spanning multiple lines

    Records are separated in files by a line containing exactly three dashes
    (handled at a higher level by the TextRecords helper).
    """

    id: str
    score: int
    description: str

    # ------------------------------------------------------------------
    # ID generation
    # ------------------------------------------------------------------
    @classmethod
    def generate_idea_id(cls) -> str:
        """Generate a unique idea ID using the shared RecordID generator."""
        return RecordID.generate()

    # ------------------------------------------------------------------
    # Parsing helpers
    # ------------------------------------------------------------------
    @staticmethod
    def _parse_score(value: str, state: dict) -> tuple[bool, dict]:
        """Attempt to parse an integer score value.

        Returns a tuple (changed?, new_state).
        """
        new_state = state.copy()
        if value.isdigit():
            new_state["score"] = int(value)
            return True, new_state
        # Keep existing value if parsing failed so we can fall back later
        return False, state

    @staticmethod
    def _process_property_line(stripped: str, state: dict) -> tuple[bool, dict]:
        """Detect and process a property *key: value* line.

        For *Idea* records only *ID* and *Score* properties are supported.
        """
        parts = stripped.split(":", 1)
        if len(parts) != 2:
            return False, state

        key, value = parts
        key = key.strip().lower()
        value = value.strip()

        if key == "score":
            return Idea._parse_score(value, state)
        elif key == "id":
            new_state = state.copy()
            new_state["idea_id"] = value
            return True, new_state
        return False, state

    # ------------------------------------------------------------------
    # Public constructors / serializers
    # ------------------------------------------------------------------
    @classmethod
    def from_text(cls, text: str) -> Optional["Idea"]:
        """Create an *Idea* instance from its textual representation.

        Any malformed record returns *None* with a WARN-level log entry – this
        mirrors the behaviour of :pyclass:`projects.task.Task` so the calling
        code can simply filter out *None* during loading.
        """
        try:
            lines = text.strip().split("\n")

            state = {
                "score": 1,  # Reasonable default when absent / malformed
                "idea_id": "",
            }
            description_lines: list[str] = []

            for line in lines:
                stripped = line.strip()
                changed, state = cls._process_property_line(stripped, state)
                if not changed:
                    description_lines.append(line)

            # Handle missing ID
            if not state["idea_id"]:
                state["idea_id"] = RecordID.generate()
                logger.warning(
                    "Generated missing idea ID for malformed record: %s", state["idea_id"]
                )

            description = "\n".join(description_lines).strip()

            return cls(id=state["idea_id"], score=state["score"], description=description)
        except Exception as exc:  # pragma: no cover – broad catch mirrors Task.from_text
            logger.warning("Malformed idea record ignored: %s", exc)
            return None

    # --------------------------------------------------------------
    # Serialisation helpers
    # --------------------------------------------------------------
    def to_text(self) -> str:
        """Render the idea back to its on-disk record form."""
        lines = [
            f"ID: {self.id}",
            f"Score: {self.score:4d}",
            self.description.strip(),
        ]
        return "\n".join(lines)

    def to_dict(self) -> dict:
        """Convert to a plain dictionary for API responses or tests."""
        return {
            "id": self.id,
            "score": self.score,
            "description": self.description,
        }

