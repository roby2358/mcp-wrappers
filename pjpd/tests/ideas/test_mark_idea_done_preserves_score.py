"""
Tests that marking ideas done preserves score and sorts correctly.
"""

import pytest
from pathlib import Path

from src.ideas.ideas import Ideas


class TestMarkIdeaDonePreservesScore:
    """Verify mark_idea_done preserves score and sorts active-first."""

    @pytest.fixture
    def ideas_manager(self, tmp_path):
        return Ideas(tmp_path)

    def test_mark_done_preserves_score(self, ideas_manager):
        """Marking an idea done should not change its score."""
        idea = ideas_manager.add_idea("Great idea", 75, "feat")
        ideas_manager.mark_idea_done(idea.id)

        reloaded = [i for i in ideas_manager.ideas if i.id == idea.id][0]
        assert reloaded.score == 75
        assert reloaded.description.startswith("(Done)")

    def test_active_ideas_sort_before_done(self, ideas_manager):
        """Active ideas appear before done ideas."""
        low_active = ideas_manager.add_idea("Low active", 10, "lo")
        high_done = ideas_manager.add_idea("High done", 90, "hi")
        ideas_manager.mark_idea_done(high_done.id)

        ideas = ideas_manager.ideas
        assert not ideas[0].is_done
        assert ideas[0].id == low_active.id
        assert ideas[1].is_done
        assert ideas[1].id == high_done.id

    def test_sort_within_same_done_status(self, ideas_manager):
        """Within active ideas, higher score comes first."""
        low = ideas_manager.add_idea("Low", 10, "lo")
        high = ideas_manager.add_idea("High", 90, "hi")

        ideas = ideas_manager.ideas
        assert ideas[0].score == 90
        assert ideas[1].score == 10

    def test_done_ideas_retain_relative_score_order(self, ideas_manager):
        """Done ideas are sorted by score among themselves."""
        i1 = ideas_manager.add_idea("Medium done", 50, "med")
        i2 = ideas_manager.add_idea("High done", 90, "hi")
        ideas_manager.mark_idea_done(i1.id)
        ideas_manager.mark_idea_done(i2.id)

        ideas = ideas_manager.ideas
        assert ideas[0].score == 90
        assert ideas[1].score == 50

    def test_is_done_property(self, ideas_manager):
        """is_done reflects the (Done) prefix on description."""
        idea = ideas_manager.add_idea("Test idea", 50, "test")
        assert not idea.is_done

        ideas_manager.mark_idea_done(idea.id)
        reloaded = [i for i in ideas_manager.ideas if i.id == idea.id][0]
        assert reloaded.is_done
