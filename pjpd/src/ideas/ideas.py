"""
Ideas Management
================
Collection-level operations for *Idea* records stored in a single `ideas.txt`
file located alongside project task files. This class mirrors the public API
style of :pyclass:`projects.project.Project` so that higher-level orchestration
(code or MCP tools) can manage ideas and tasks in a symmetric fashion.
"""

from __future__ import annotations

import logging
from pathlib import Path
from typing import List, Optional, Dict, Any

from textrec.text_records import TextRecords
from .idea import Idea

logger = logging.getLogger(__name__)


class Ideas:
    """Manage a collection of :pyclass:`ideas.idea.Idea` records."""

    def __init__(self, directory: Path | str):
        self.directory = Path(directory).expanduser()
        self.ideas_file = self.directory / "pjpd" / "ideas.txt"
        self.text_records = TextRecords(self.directory)
        self._ideas = None

    @property
    def present(self) -> bool:
        """Check if the ideas directory structure is present on disk."""
        return self.ideas_file.parent.exists() and self.ideas_file.parent.is_dir()

    # ------------------------------------------------------------------
    # Configuration helpers
    # ------------------------------------------------------------------
    def set_directory(self, directory: Path | str) -> None:
        """Update the directory containing *ideas.txt*.

        The directory will be created automatically if it doesn't exist.
        Changing the projects directory at runtime allows the Ideas manager to
        follow the current *Projects* location configured by the user (for
        example via the *path* parameter to the *list_projects* tool).
        """
        self.directory = Path(directory).expanduser()
        self.ideas_file = self.directory / "pjpd" / "ideas.txt"
        self.text_records = TextRecords(self.directory)
        
        # Reset state for new directory
        self._ideas = None

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------
    def _load_ideas(self) -> None:
        """Load ideas from `ideas.txt` (lazily)."""
        if not self.present:
            self._ideas = []
            return
            
        if not self.ideas_file.exists():
            self._ideas = []
            return

        try:
            records = self.text_records.parse_file(self.ideas_file)
            loaded: list[Idea] = []
            for record in records:
                idea = Idea.from_text(record["text"])
                if idea:
                    loaded.append(idea)
            # Sort by score descending so we maintain spec requirement
            loaded.sort(key=lambda i: i.score, reverse=True)
            self._ideas = loaded
        except Exception as exc:
            logger.error("Error loading ideas from %s: %s", self.ideas_file, exc)
            self._ideas = []

    def _save_ideas(self) -> None:
        """Persist current in-memory ideas list to disk (sorted)."""
        if self._ideas is None:
            return  # Nothing to save

        # Ensure directory exists before saving
        self.ideas_file.parent.mkdir(parents=True, exist_ok=True)

        # Sort by score (desc) before serialisation – spec requirement
        sorted_ideas = sorted(self._ideas, key=lambda i: i.score, reverse=True)
        content = "\n---\n".join(idea.to_text() for idea in sorted_ideas)

        self.text_records.write_atomic(self.ideas_file, content)

    # ------------------------------------------------------------------
    # Public properties
    # ------------------------------------------------------------------
    @property
    def ideas(self) -> List[Idea]:
        """Return *all* ideas, loading them on-demand."""
        if self._ideas is None:
            self._load_ideas()
        # self._ideas is now non-None by construction
        return self._ideas  # type: ignore[return-value]

    # ------------------------------------------------------------------
    # Public operations – mirrors Project API for symmetry
    # ------------------------------------------------------------------
    def add_idea(self, description: str, score: int, tag: str = "idea") -> Idea:
        """Create and persist a new idea record."""
        idea = Idea(
            id=Idea.generate_idea_id(tag), 
            tag=tag,
            score=score, 
            description=description
        )
        self.ideas.append(idea)
        self._save_ideas()
        return idea

    def update_idea(self, idea_id: str, description: Optional[str] = None, score: Optional[int] = None) -> bool:
        """Update an existing idea by ID. Returns *True* if the idea was found and updated."""
        for idea in self.ideas:
            if idea.id == idea_id:
                if description is not None:
                    idea.description = description
                if score is not None:
                    idea.score = score
                self._save_ideas()
                return True
        return False

    def remove_idea(self, idea_id: str) -> bool:
        """Remove an idea by ID. Returns *True* if something was removed."""
        removed = False
        remaining: list[Idea] = []
        for idea in self.ideas:
            if idea.id == idea_id:
                removed = True
                continue
            remaining.append(idea)
        if removed:
            self._ideas = remaining
            self._save_ideas()
        return removed

    def mark_idea_done(self, idea_id: str) -> bool:
        """Mark an idea as done by setting its score to 0 and
        prepending "(Done)" to the first line of its description.

        Returns True if the idea was found and updated, False otherwise.
        """
        for idea in self.ideas:
            if idea.id == idea_id:
                # Set score to 0
                idea.score = 0

                # Prepend "(Done)" to the first line of the description
                description_text = idea.description or ""
                first_and_rest = description_text.split("\n", 1)
                first_line = first_and_rest[0]
                remaining_text = first_and_rest[1] if len(first_and_rest) > 1 else ""

                if not first_line.startswith("(Done)"):
                    first_line = f"(Done) {first_line}" if first_line else "(Done)"

                idea.description = (
                    first_line if not remaining_text else f"{first_line}\n{remaining_text}"
                )

                self._save_ideas()
                return True
        return False

    def list_ideas(self, max_results: Optional[int] = None) -> List[Dict[str, Any]]:
        """Return ideas as plain dictionaries (sorted by score descending)."""
        ideas_sorted = sorted(self.ideas, key=lambda i: i.score, reverse=True)
        if max_results is not None:
            ideas_sorted = ideas_sorted[:max_results]
        return [idea.to_dict() for idea in ideas_sorted]
