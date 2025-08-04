"""Epics Management
Represents a single epic record.

An *Epic* extends the base *Idea* concept with additional properties linking
ideas and projects:

    Score: {integer}
    Ideas: {space-delimited idea IDs}
    Projects: {space-delimited project names}
    ID: {tag}-{4-character-random-string}
    Tag: {1-12-character-string}
    <free-form description>

Records are separated by a line containing exactly three dashes (---) which is
handled at a higher level by :pyclass:`textrec.text_records.TextRecords`.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field
from typing import List, Optional

from textrec.record_id import RecordID

logger = logging.getLogger(__name__)


@dataclass
class Epic:
    """Represents a single epic item."""

    id: str
    tag: str
    score: int
    ideas: List[str] = field(default_factory=list)
    projects: List[str] = field(default_factory=list)
    description: str = ""

    # ------------------------------------------------------------------
    # ID generation
    # ------------------------------------------------------------------
    @classmethod
    def generate_epic_id(cls, tag: str) -> str:
        """Generate a unique epic ID using the provided tag and RecordID generator."""
        return RecordID.generate_with_tag(tag)

    # ------------------------------------------------------------------
    # Parsing helpers
    # ------------------------------------------------------------------
    @staticmethod
    def _parse_score(value: str, state: dict) -> tuple[bool, dict]:
        new_state = state.copy()
        if value.isdigit():
            new_state["score"] = int(value)
            return True, new_state
        return False, state

    @staticmethod
    def _parse_ideas(value: str, state: dict) -> tuple[bool, dict]:
        new_state = state.copy()
        new_state["ideas"] = value.split()
        return True, new_state

    @staticmethod
    def _parse_projects(value: str, state: dict) -> tuple[bool, dict]:
        new_state = state.copy()
        new_state["projects"] = value.split()
        return True, new_state

    @staticmethod
    def _parse_id(value: str, state: dict) -> tuple[bool, dict]:
        new_state = state.copy()
        new_state["epic_id"] = value
        return True, new_state

    @staticmethod
    def _parse_tag(value: str, state: dict) -> tuple[bool, dict]:
        new_state = state.copy()
        new_state["tag"] = value
        return True, new_state

    @staticmethod
    def _process_property_line(stripped: str, state: dict) -> tuple[bool, dict]:
        parts = stripped.split(":", 1)
        if len(parts) != 2:
            return False, state

        key, value = parts
        key = key.strip().lower()
        value = value.strip()

        if key == "score":
            return Epic._parse_score(value, state)
        if key == "ideas":
            return Epic._parse_ideas(value, state)
        if key == "projects":
            return Epic._parse_projects(value, state)
        if key == "id":
            return Epic._parse_id(value, state)
        if key == "tag":
            return Epic._parse_tag(value, state)
        return False, state

    # ------------------------------------------------------------------
    # Public constructors / serializers
    # ------------------------------------------------------------------
    @classmethod
    def from_text(cls, text: str) -> Optional["Epic"]:
        """Create an *Epic* instance from its textual representation.

        Any malformed record returns *None* with a WARN-level log entry – this
        mirrors the behaviour of :pyclass:`projects.task.Task` and
        :pyclass:`ideas.idea.Idea` so the calling code can simply filter out
        *None* during loading.
        """
        try:
            lines = text.strip().split("\n")

            state = {
                "score": 1,
                "ideas": [],
                "projects": [],
                "epic_id": "",
                "tag": "",
            }
            description_lines: list[str] = []

            for line in lines:
                stripped = line.strip()
                changed, state = cls._process_property_line(stripped, state)
                if not changed:
                    description_lines.append(line)

            # Handle missing ID
            if not state["epic_id"]:
                if state["tag"]:
                    state["epic_id"] = Epic.generate_epic_id(state["tag"])
                else:
                    # Fallback to old format for backward compatibility
                    state["epic_id"] = RecordID.generate()
                    state["tag"] = "legacy"
                logger.warning(
                    "Generated missing epic ID for malformed record: %s", state["epic_id"]
                )

            # Ensure tag is set
            if not state["tag"]:
                # Try to extract tag from ID if it follows the new format
                if "-" in state["epic_id"] and len(state["epic_id"].split("-")[0]) <= 12:
                    state["tag"] = state["epic_id"].split("-")[0]
                else:
                    state["tag"] = "legacy"

            description = "\n".join(description_lines).strip()

            return cls(
                id=state["epic_id"],
                tag=state["tag"],
                score=state["score"],
                ideas=state["ideas"],
                projects=state["projects"],
                description=description,
            )
        except Exception as exc:  # pragma: no cover – broad catch mirrors others
            logger.warning("Malformed epic record ignored: %s", exc)
            return None

    # ------------------------------------------------------------------
    # Serialisation helpers
    # ------------------------------------------------------------------
    def to_text(self) -> str:
        """Render the epic back to its on-disk record form."""
        lines = [
            f"Score: {self.score:4d}",
            f"Ideas: {' '.join(self.ideas)}",
            f"Projects: {' '.join(self.projects)}",
            f"Tag: {self.tag}",
            f"ID: {self.id}",
            self.description.strip(),
        ]
        return "\n".join(lines)

    def to_dict(self) -> dict:
        """Convert to a plain dictionary for API responses or tests."""
        return {
            "id": self.id,
            "tag": self.tag,
            "score": self.score,
            "ideas": self.ideas,
            "projects": self.projects,
            "description": self.description,
        }
