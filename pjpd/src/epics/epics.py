"""Epics Management
=================
Collection-level operations for *Epic* records stored in a single
`epics.txt` file located alongside project task files. This mirrors the public
API style of :pyclass:`ideas.ideas.Ideas` so that higher-level orchestration
(code or MCP tools) can manage epics symmetrically.
"""

from __future__ import annotations

import logging
from pathlib import Path
from typing import List, Optional, Dict, Any

from textrec.text_records import TextRecords
from .epic import Epic

logger = logging.getLogger(__name__)


class Epics:
    """Manage a collection of :pyclass:`epics.epic.Epic` records."""

    def __init__(self, directory: Path | str):
        self.set_directory(directory)
        self._epics: Optional[List[Epic]] = None

    # ------------------------------------------------------------------
    # Configuration helpers
    # ------------------------------------------------------------------
    def set_directory(self, directory: Path | str) -> None:
        """Update the directory containing *epics.txt*.

        The directory must exist or an exception will be raised.
        Keeping the Epics manager in sync with the active *Projects* directory
        ensures the `epics.txt` file is created beside project task files – not
        in a stale default location (e.g. `~/projects`).
        
        Raises:
            FileNotFoundError: If the specified directory doesn't exist.
        """
        self.directory = Path(directory).expanduser()
        
        # Check if directory exists and raise exception if it doesn't
        if not self.directory.exists():
            raise FileNotFoundError(f"Epics directory does not exist: {self.directory}")
        
        if not self.directory.is_dir():
            raise FileNotFoundError(f"Path exists but is not a directory: {self.directory}")
            
        self.epics_file = self.directory / "epics.txt"
        self.text_records = TextRecords(self.directory)
        # Invalidate cache so data is re-loaded on next access
        self._epics = None

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------
    def _load_epics(self) -> None:
        """Load epics from `epics.txt` (lazily)."""
        if not self.epics_file.exists():
            self._epics = []
            return

        try:
            records = self.text_records.parse_file(self.epics_file)
            loaded: list[Epic] = []
            for record in records:
                epic = Epic.from_text(record["text"])
                if epic:
                    loaded.append(epic)
            # Sort by score descending (spec requirement)
            loaded.sort(key=lambda e: e.score, reverse=True)
            self._epics = loaded
        except Exception as exc:
            logger.error("Error loading epics from %s: %s", self.epics_file, exc)
            self._epics = []

    def _save_epics(self) -> None:
        """Persist current in-memory epics list to disk (sorted)."""
        if self._epics is None:
            return  # Nothing to save

        # Sort by score (desc) before serialisation – spec requirement
        sorted_epics = sorted(self._epics, key=lambda e: e.score, reverse=True)
        content = "\n---\n".join(epic.to_text() for epic in sorted_epics)

        self.text_records.write_atomic(self.epics_file, content)

    # ------------------------------------------------------------------
    # Public properties
    # ------------------------------------------------------------------
    @property
    def epics(self) -> List[Epic]:
        """Return *all* epics, loading them on-demand."""
        if self._epics is None:
            self._load_epics()
        # self._epics is now non-None by construction
        return self._epics  # type: ignore[return-value]

    # ------------------------------------------------------------------
    # Public operations – mirrors Ideas API for symmetry
    # ------------------------------------------------------------------
    def add_epic(
        self,
        description: str,
        score: int,
        tag: str = "epic",
        ideas: Optional[List[str]] = None,
        projects: Optional[List[str]] = None,
    ) -> Epic:
        """Create and persist a new epic record."""
        ideas = ideas or []
        projects = projects or []
        epic = Epic(
            id=Epic.generate_epic_id(tag),
            tag=tag,
            score=score,
            ideas=ideas,
            projects=projects,
            description=description,
        )
        self.epics.append(epic)
        self._save_epics()
        return epic

    def update_epic(
        self,
        epic_id: str,
        description: Optional[str] = None,
        score: Optional[int] = None,
        ideas: Optional[List[str]] = None,
        projects: Optional[List[str]] = None,
    ) -> bool:
        """Update an existing epic by ID. Returns *True* if found and updated."""
        for epic in self.epics:
            if epic.id == epic_id:
                if description is not None:
                    epic.description = description
                if score is not None:
                    epic.score = score
                if ideas is not None:
                    epic.ideas = ideas
                if projects is not None:
                    epic.projects = projects
                self._save_epics()
                return True
        return False

    def mark_epic_done(self, epic_id: str) -> bool:
        """Mark an epic as done by setting its score to 0. Returns *True* if updated."""
        for epic in self.epics:
            if epic.id == epic_id:
                epic.score = 0
                self._save_epics()
                return True
        return False

    def list_epics(self, max_results: Optional[int] = None) -> List[Dict[str, Any]]:
        """Return epics as plain dictionaries (sorted by score descending)."""
        epics_sorted = sorted(self.epics, key=lambda e: e.score, reverse=True)
        if max_results is not None:
            epics_sorted = epics_sorted[:max_results]
        return [epic.to_dict() for epic in epics_sorted]
