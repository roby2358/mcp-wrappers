"""
Tests for idea Created/Updated timestamps.
"""

import pytest
from pathlib import Path

from src.ideas.ideas import Ideas
from src.ideas.idea import Idea


class TestIdeaTimestamps:
    """Verify Created and Updated timestamps on ideas."""

    @pytest.fixture
    def ideas_manager(self, tmp_path):
        return Ideas(tmp_path)

    def test_new_idea_has_timestamps(self, ideas_manager):
        """A newly created idea has both created and updated set."""
        idea = ideas_manager.add_idea("Test idea", 50, "test")

        assert idea.created is not None
        assert idea.updated is not None
        assert idea.created == idea.updated

    def test_updated_idea_refreshes_updated(self, ideas_manager):
        """Updating an idea refreshes updated but preserves created."""
        idea = ideas_manager.add_idea("Test idea", 50, "test")
        original_created = idea.created

        ideas_manager.update_idea(idea.id, "Changed", None)

        reloaded = [i for i in ideas_manager.ideas if i.id == idea.id][0]
        assert reloaded.created == original_created
        assert reloaded.updated >= original_created

    def test_mark_done_refreshes_updated(self, ideas_manager):
        """Marking an idea done refreshes its updated timestamp."""
        idea = ideas_manager.add_idea("Test idea", 50, "test")
        original_created = idea.created

        ideas_manager.mark_idea_done(idea.id)

        reloaded = [i for i in ideas_manager.ideas if i.id == idea.id][0]
        assert reloaded.created == original_created
        assert reloaded.updated >= original_created

    def test_timestamps_persist_to_file(self, ideas_manager):
        """Timestamps are written to the file and can be read back."""
        idea = ideas_manager.add_idea("Test idea", 50, "test")

        content = ideas_manager.ideas_file.read_text(encoding="utf-8")
        assert f"Created: {idea.created}" in content
        assert f"Updated: {idea.updated}" in content

    def test_timestamps_roundtrip(self, ideas_manager):
        """Timestamps survive a write-then-read cycle."""
        idea = ideas_manager.add_idea("Test idea", 50, "test")
        original_created = idea.created

        reloaded = [i for i in ideas_manager.ideas if i.id == idea.id][0]

        assert reloaded.created == original_created
        assert reloaded.updated == idea.updated

    def test_legacy_idea_without_timestamps_parses(self):
        """An idea record without timestamps parses cleanly (backward compat)."""
        text = "Score:   50\nID: test-abcd\nA great idea"
        idea = Idea.from_text(text)

        assert idea is not None
        assert idea.id == "test-abcd"
        assert idea.description == "A great idea"
        assert idea.created is None
        assert idea.updated is None

    def test_timestamps_in_to_dict(self, ideas_manager):
        """Timestamps appear in the API dict representation."""
        idea = ideas_manager.add_idea("Test idea", 50, "test")
        d = idea.to_dict()

        assert "created" in d
        assert "updated" in d
        assert d["created"] == idea.created

    def test_legacy_idea_to_dict_omits_timestamps(self):
        """A legacy idea without timestamps omits them from to_dict."""
        text = "Score:   50\nID: test-abcd\nA great idea"
        idea = Idea.from_text(text)
        d = idea.to_dict()

        assert "created" not in d
        assert "updated" not in d
