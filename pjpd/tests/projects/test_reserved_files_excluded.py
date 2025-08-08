"""
Tests for excluding reserved system files (ideas.txt, epics.txt) from projects
"""

import pytest
from pathlib import Path

from src.projects.projects import Projects


class TestReservedFilesExcluded:
    def test_projects_excludes_reserved_files_on_load(self, tmp_path):
        """Projects should not treat ideas.txt and epics.txt as projects."""
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()

        # Create reserved files and one real project
        (pjpd_dir / "ideas.txt").write_text("")
        (pjpd_dir / "epics.txt").write_text("")
        (pjpd_dir / "regular_project.txt").write_text("")

        projects = Projects(tmp_path)
        projects.refresh_projects()

        assert "regular_project" in projects.projects
        assert "ideas" not in projects.projects
        assert "epics" not in projects.projects
        assert len(projects.projects) == 1

    def test_get_project_reserved_names_are_excluded(self, tmp_path):
        """Accessing reserved names via get_project should raise a clear excluded error."""
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        (pjpd_dir / "ideas.txt").write_text("")
        (pjpd_dir / "epics.txt").write_text("")

        projects = Projects(tmp_path)

        with pytest.raises(ValueError) as excinfo_ideas:
            projects.get_project("ideas")
        assert "excluded" in str(excinfo_ideas.value)

        with pytest.raises(ValueError) as excinfo_epics:
            projects.get_project("Epics")  # mixed case
        assert "excluded" in str(excinfo_epics.value)

    def test_create_project_reserved_names_are_excluded(self, tmp_path):
        """Creating a project with a reserved name should be disallowed and say excluded."""
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()

        projects = Projects(tmp_path)

        with pytest.raises(ValueError) as excinfo:
            projects.create_project("epics")
        assert "excluded" in str(excinfo.value)

        # Ensure file was not created
        assert not (pjpd_dir / "epics.txt").exists()


