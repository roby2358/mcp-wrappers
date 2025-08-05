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

        Score: {integer}
        Tag: {1-12-character-string}
        ID: {tag}-{4-character-random-string}
        Free-form description spanning multiple lines

    Records are separated in files by a line containing exactly three dashes
    (handled at a higher level by the TextRecords helper).
    """

    id: str
    tag: str
    score: int
    description: str

    # ------------------------------------------------------------------
    # ID generation
    # ------------------------------------------------------------------
    @classmethod
    def generate_idea_id(cls, tag: str) -> str:
        """Generate a unique idea ID using the provided tag and RecordID generator."""
        return RecordID.generate_with_tag(tag)

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

        For *Idea* records *ID*, *Tag*, and *Score* properties are supported.
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
        elif key == "tag":
            new_state = state.copy()
            new_state["tag"] = value
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
                "tag": "",
            }
            description_lines: list[str] = []

            for line in lines:
                stripped = line.strip()
                changed, state = cls._process_property_line(stripped, state)
                if not changed:
                    description_lines.append(line)

            # Handle missing ID
            if not state["idea_id"]:
                if state["tag"]:
                    state["idea_id"] = Idea.generate_idea_id(state["tag"])
                else:
                    # Fallback to old format for backward compatibility
                    state["idea_id"] = RecordID.generate()
                    state["tag"] = "legacy"
                logger.warning(
                    "Generated missing idea ID for malformed record: %s", state["idea_id"]
                )

            # Extract tag from ID if it follows the new format
            if "-" in state["idea_id"] and len(state["idea_id"].split("-")[0]) <= 12:
                state["tag"] = state["idea_id"].split("-")[0]
            else:
                state["tag"] = "legacy"

            description = "\n".join(description_lines).strip()

            return cls(
                id=state["idea_id"], 
                tag=state["tag"],
                score=state["score"], 
                description=description
            )
        except Exception as exc:  # pragma: no cover – broad catch mirrors Task.from_text
            logger.warning("Malformed idea record ignored: %s", exc)
            return None

    # --------------------------------------------------------------
    # Serialisation helpers
    # --------------------------------------------------------------
    def to_text(self) -> str:
        """Render the idea back to its on-disk record form."""
        lines = [
            f"Score: {self.score:4d}",
            f"ID: {self.id}",
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

