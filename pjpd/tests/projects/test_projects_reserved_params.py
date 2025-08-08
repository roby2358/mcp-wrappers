"""
Tests for reserved stems passed via method parameters to Projects
"""

import pytest

from src.projects.projects import Projects


class TestProjectsReservedParams:
    def test_get_all_tasks_with_reserved_project_filter_raises(self, tmp_path):
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        (pjpd_dir / "regular.txt").write_text("")

        projects = Projects(tmp_path)

        with pytest.raises(ValueError) as excinfo:
            projects.get_all_tasks(project_filter="ideas")
        assert "excluded" in str(excinfo.value)

        with pytest.raises(ValueError) as excinfo2:
            projects.get_all_tasks(project_filter="Epics")
        assert "excluded" in str(excinfo2.value)

    def test_add_task_with_reserved_project_raises(self, tmp_path):
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        (pjpd_dir / "regular.txt").write_text("")

        projects = Projects(tmp_path)

        with pytest.raises(ValueError) as excinfo:
            projects.add_task("epics", "desc", 10, "tag")
        assert "excluded" in str(excinfo.value)

    def test_sort_project_with_reserved_project_raises(self, tmp_path):
        pjpd_dir = tmp_path / "pjpd"
        pjpd_dir.mkdir()
        (pjpd_dir / "regular.txt").write_text("")

        projects = Projects(tmp_path)

        with pytest.raises(ValueError) as excinfo:
            projects.sort_project("ideas")
        assert "excluded" in str(excinfo.value)


