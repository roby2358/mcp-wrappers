import pytest
import tempfile

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