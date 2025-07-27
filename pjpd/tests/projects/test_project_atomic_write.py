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


def test_write_atomic_creates_backup_and_replaces_file(project_file: Path) -> None:
    """_write_atomic should create a backup and replace the original file atomically."""
    project = Project(name="TestProject", file_path=project_file)

    # Perform atomic write with new content
    new_content = "updated content"
    project._write_atomic(new_content)

    # The original path should now contain the new content
    assert project_file.read_text(encoding="utf-8") == new_content

    # Ensure the `bak` directory exists
    bak_dir = project_file.parent / "bak"
    assert bak_dir.is_dir(), "bak directory was not created"

    # There should be exactly one backup file
    bak_files = list(bak_dir.iterdir())
    assert len(bak_files) == 1, "Expected exactly one backup file"

    # The backup file should contain the original content
    backup_file = bak_files[0]
    assert backup_file.read_text(encoding="utf-8") == "initial content"

    # Backup filename should follow the pattern <stem>.<timestamp><suffix>
    stem, suffix = project_file.stem, project_file.suffix
    assert backup_file.name.startswith(f"{stem}.") and backup_file.name.endswith(suffix)


def test_write_atomic_creates_file_when_nonexistent(project_file_nonexistent: Path) -> None:
    """_write_atomic should create the file when it doesn't exist initially."""
    project = Project(name="TestProject", file_path=project_file_nonexistent)

    # Verify the file doesn't exist initially
    assert not project_file_nonexistent.exists()

    # Perform atomic write with new content
    new_content = "new content"
    project._write_atomic(new_content)

    # The file should now exist and contain the new content
    assert project_file_nonexistent.exists()
    assert project_file_nonexistent.read_text(encoding="utf-8") == new_content

    # Ensure the `bak` directory exists
    bak_dir = project_file_nonexistent.parent / "bak"
    assert bak_dir.is_dir(), "bak directory was not created"

    # There should be no backup files since the original file didn't exist
    bak_files = list(bak_dir.iterdir())
    assert len(bak_files) == 0, "Expected no backup files when original file didn't exist" 