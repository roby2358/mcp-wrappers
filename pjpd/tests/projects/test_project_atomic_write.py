import os
from pathlib import Path

import pytest

from src.projects.project import Project


@pytest.fixture()
def project_file(tmp_path: Path) -> Path:
    """Create an initial project file with dummy content inside a temp directory."""
    file_path = tmp_path / "project.txt"
    file_path.write_text("initial content", encoding="utf-8")
    return file_path


@pytest.fixture()
def project_file_nonexistent(tmp_path: Path) -> Path:
    """Create a path for a project file that doesn't exist initially."""
    return tmp_path / "project.txt"


def test_project_save_tasks_uses_text_records(project_file: Path) -> None:
    """Project._save_tasks should use TextRecords.write_atomic."""
    project = Project(name="TestProject", file_path=project_file)

    # Add a task to trigger _save_tasks
    project.add_task("Test task", 5)

    # The original path should now contain the task content
    content = project_file.read_text(encoding="utf-8")
    assert "Test task" in content
    assert "Priority:    5" in content

    # Ensure the `bak` directory exists (created by TextRecords.write_atomic)
    bak_dir = project_file.parent / "bak"
    assert bak_dir.is_dir(), "bak directory was not created"

    # There should be exactly one backup file
    bak_files = list(bak_dir.iterdir())
    assert len(bak_files) == 1, "Expected exactly one backup file"

    # The backup file should contain the original content
    backup_file = bak_files[0]
    assert backup_file.read_text(encoding="utf-8") == "initial content"


def test_project_save_tasks_creates_file_when_nonexistent(project_file_nonexistent: Path) -> None:
    """Project._save_tasks should create the file when it doesn't exist initially."""
    project = Project(name="TestProject", file_path=project_file_nonexistent)

    # Verify the file doesn't exist initially
    assert not project_file_nonexistent.exists()

    # Add a task to trigger _save_tasks
    project.add_task("Test task", 5)

    # The file should now exist and contain the task content
    assert project_file_nonexistent.exists()
    content = project_file_nonexistent.read_text(encoding="utf-8")
    assert "Test task" in content
    assert "Priority:    5" in content

    # Ensure the `bak` directory exists
    bak_dir = project_file_nonexistent.parent / "bak"
    assert bak_dir.is_dir(), "bak directory was not created"

    # There should be no backup files since the original file didn't exist
    bak_files = list(bak_dir.iterdir())
    assert len(bak_files) == 0, "Expected no backup files when original file didn't exist" 