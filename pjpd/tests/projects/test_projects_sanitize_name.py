import pytest
import tempfile
import os

from src.projects.projects import Projects


@pytest.mark.parametrize(
    "raw, expected",
    [
        ("My Project! @#$%", "my_project!_@#$%"),
        ("  My   Project  ", "my_project"),
        ("", "project"),
        ("..", "project"),
        ("FileName*Inva|id", "filename_inva_id"),
        ("Multiple    Spaces", "multiple_spaces"),
        ("___", "project"),
        ("Project!Name!", "project!name!"),
    ],
)
def test_sanitize_name(raw: str, expected: str):
    """Ensure `_sanitize_name` normalises project names into safe filenames."""

    with tempfile.TemporaryDirectory() as temp_dir:
        projects = Projects(temp_dir)  # Directory needed but not used for sanitisation logic
        assert projects._sanitize_name(raw) == expected 