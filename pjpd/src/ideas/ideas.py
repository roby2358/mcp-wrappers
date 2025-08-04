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
        self.set_directory(directory)
        self._ideas: Optional[List[Idea]] = None

    # ------------------------------------------------------------------
    # Configuration helpers
    # ------------------------------------------------------------------
    def set_directory(self, directory: Path | str) -> None:
        """Update the directory containing *ideas.txt*.

        The directory must exist or an exception will be raised.
        Changing the projects directory at runtime allows the Ideas manager to
        follow the current *Projects* location configured by the user (for
        example via the *path* parameter to the *list_projects* tool).
        
        Raises:
            FileNotFoundError: If the specified directory doesn't exist.
        """
        self.directory = Path(directory).expanduser()
        
        # Check if directory exists and raise exception if it doesn't
        if not self.directory.exists():
            raise FileNotFoundError(f"Ideas directory does not exist: {self.directory}")
        
        if not self.directory.is_dir():
            raise FileNotFoundError(f"Path exists but is not a directory: {self.directory}")
            
        self.ideas_file = self.directory / "ideas.txt"
        # Re-initialise TextRecords so it points at the new directory
        self.text_records = TextRecords(self.directory)
        # Drop any cached data so it will be lazily re-loaded next access
        self._ideas = None

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------
    def _load_ideas(self) -> None:
        """Load ideas from `ideas.txt` (lazily)."""
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

    def list_ideas(self, max_results: Optional[int] = None) -> List[Dict[str, Any]]:
        """Return ideas as plain dictionaries (sorted by score descending)."""
        ideas_sorted = sorted(self.ideas, key=lambda i: i.score, reverse=True)
        if max_results is not None:
            ideas_sorted = ideas_sorted[:max_results]
        return [idea.to_dict() for idea in ideas_sorted]
