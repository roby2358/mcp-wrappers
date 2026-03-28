"""
Tests for pjpd subdirectory functionality
"""

import pytest
from pathlib import Path
from src.ideas.ideas import Ideas
from src.projects.projects import Projects


class TestPjpdSubdirectory:
    """Test the pjpd subdirectory functionality"""

    def test_projects_manager_uses_pjpd_subdirectory(self, tmp_path):
        """Projects manager stores tasks in pjpd/tasks.txt"""
        mgr = Projects(tmp_path)
        assert mgr.tasks_file == tmp_path / "pjpd" / "tasks.txt"

    def test_adding_task_creates_pjpd_dir(self, tmp_path):
        """Adding a task creates the pjpd subdirectory automatically"""
        mgr = Projects(tmp_path)
        mgr.add_task("Test task", 5, "task")
        assert (tmp_path / "pjpd").is_dir()
        assert (tmp_path / "pjpd" / "tasks.txt").exists()

    def test_ideas_manager_pjpd_subdirectory(self, tmp_path):
        """Test that Ideas manager looks in pjpd subdirectory"""
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        ideas_file = pjpd_dir / "ideas.txt"
        ideas_file.write_text("Score:   80\nID: test-abcd\nTest idea\n----")

        ideas = Ideas(tmp_path)

        assert len(ideas.ideas) == 1
        assert ideas.ideas[0].id == "test-abcd"
        assert ideas.ideas[0].score == 80

    def test_legacy_project_file_warning_present(self, tmp_path):
        """Warning returned when pjpd/<dir_name>.txt exists"""
        project_dir = tmp_path / "my-project"
        project_dir.mkdir()
        pjpd_dir = project_dir / "pjpd"
        pjpd_dir.mkdir()
        # Create the legacy file matching the directory name
        (pjpd_dir / "my-project.txt").write_text("old data")

        mgr = Projects(project_dir)
        warning = mgr.legacy_project_file_warning()
        assert warning is not None
        assert "my-project.txt" in warning

    def test_legacy_project_file_warning_absent(self, tmp_path):
        """No warning when no legacy file exists"""
        mgr = Projects(tmp_path)
        mgr.add_task("Test task", 5, "task")
        assert mgr.legacy_project_file_warning() is None

