import pytest
import tempfile
from pathlib import Path

from src.projects.projects import Projects


# ----------------------------
# Valid name cases
# ----------------------------

@pytest.mark.parametrize(
    "raw, expected",
    [
        ("My Project! @#$%", "my_project!_@#$%"),
        ("  My   Project  ", "my_project"),
        ("FileName*Inva|id", "filename_inva_id"),
        ("Multiple    Spaces", "multiple_spaces"),
        ("Project!Name!", "project!name!"),
    ],
)
def test_sanitize_name_valid(raw: str, expected: str):
    """Valid names should be sanitized correctly."""

    with tempfile.TemporaryDirectory() as temp_dir:
        projects = Projects(temp_dir)
        assert projects._sanitize_name(raw) == expected


# ----------------------------
# Invalid name cases
# ----------------------------

@pytest.mark.parametrize("invalid", ["", "..", "___"])
def test_sanitize_name_invalid(invalid: str):
    """Invalid names should raise a ValueError."""

    with tempfile.TemporaryDirectory() as temp_dir:
        projects = Projects(temp_dir)
        with pytest.raises(ValueError):
            projects._sanitize_name(invalid)


# ----------------------------
# Reserved name cases
# ----------------------------

@pytest.mark.parametrize("reserved", ["ideas", "epics", "IDEAS", "Epics", "IdeAs"])
def test_sanitize_name_reserved(reserved: str):
    """Reserved names should raise a ValueError."""

    with tempfile.TemporaryDirectory() as temp_dir:
        projects = Projects(temp_dir)
        with pytest.raises(ValueError, match=f"Project name '{reserved}' is excluded"):
            projects._sanitize_name(reserved)


# ----------------------------
# Ignored pattern cases
# ----------------------------

def test_sanitize_name_ignored():
    """Names that would be ignored should raise a ValueError."""
    
    with tempfile.TemporaryDirectory() as temp_dir:
        projects = Projects(temp_dir)
        
        # Create a pjpd subdirectory and pjpdignore file
        pjpd_dir = Path(temp_dir) / "pjpd"
        pjpd_dir.mkdir()
        
        # Create a pjpdignore file with a pattern
        ignore_file = pjpd_dir / "pjpdignore"
        ignore_file.write_text("ignored_project.txt")
        
        # Refresh projects to load the ignore list
        projects.refresh_projects()
        
        # Test that ignored names raise ValueError
        with pytest.raises(ValueError, match="Project name ignored_project is ignored"):
            projects._sanitize_name("ignored_project")
        
        # Test that non-ignored names work
        result = projects._sanitize_name("valid_project")
        assert result == "valid_project"


def test_sanitize_name_when_system_not_present():
    """Names should be validated even when projects system is not present."""
    
    with tempfile.TemporaryDirectory() as temp_dir:
        projects = Projects(temp_dir)
        
        # System should not be present initially
        assert not projects.present
        
        # Reserved names should still be rejected
        with pytest.raises(ValueError, match="Project name 'ideas' is excluded"):
            projects._sanitize_name("ideas")
        
        # Valid names should still work
        result = projects._sanitize_name("valid_project")
        assert result == "valid_project" 