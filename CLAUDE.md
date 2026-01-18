# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This is a monorepo containing multiple MCP (Model Context Protocol) server wrappers. Each wrapper is an independent project with its own dependencies, tests, and build process. The wrappers provide controlled access to various system tools and services through the MCP protocol.

## Project Structure

```
mcp-wrappers/
├── hello-world/     # Simple echo tool for testing MCP integration
├── shell/           # Secure shell execution wrappers (CMD, bash)
├── atproto/         # Bluesky social network integration
├── vecbook/         # Local vector document search
└── pjpd/            # Local project management system
```

Each project is self-contained with its own:
- `pyproject.toml` - Python dependencies and build configuration
- `README.md` - Project-specific documentation
- `tests/` - Unit tests using pytest
- `.venv/` - Virtual environment (created by `uv sync`)

## Common Development Commands

### Installation and Setup
Each project uses `uv` for dependency management:
```bash
cd <project-directory>
uv sync                          # Create venv and install all dependencies
.venv\Scripts\activate           # Windows
source .venv/bin/activate        # macOS/Linux
```

### Running MCP Servers
```bash
# Direct execution
python <project-name>.py

# With uv (recommended)
uv run python <project-name>.py

# pjpd example
cd pjpd && python pjpd.py

# vecbook with HTTP server
cd vecbook && python vecbook.py --http
```

### Testing
All projects use pytest with consistent configuration:
```bash
# Run all tests
pytest -v

# Run with coverage
pytest -v --cov=src

# Run specific test file
pytest -v tests/path/to/test_file.py

# Run specific test class or function
pytest -v tests/test_file.py::TestClassName::test_function_name
```

### Code Quality (pjpd specific)
```bash
# Format code
black src/ tests/

# Sort imports
isort src/ tests/

# Type checking
mypy src/
```

## Architecture Patterns

### MCP Server Pattern
All wrappers follow the FastMCP framework pattern:

1. **Entry Point**: Main `.py` file (e.g., `pjpd.py`, `vecbook.py`) that imports and runs the MCP server
2. **MCP Wrapper**: `src/mcp_wrapper.py` contains the FastMCP server implementation
3. **Configuration**: TOML file for project-specific settings
4. **Business Logic**: Organized in `src/` subdirectories by domain

Example structure:
```python
from mcp.server.fastmcp import FastMCP

mcp = FastMCP("server-name")

@mcp.tool()
async def tool_name(param: str) -> Dict[str, Any]:
    """Tool description for MCP client"""
    try:
        # Implementation
        return {"success": True, "result": data, "error": ""}
    except Exception as e:
        return {"success": False, "result": "", "error": str(e)}
```

### Text Records Pattern
Both `pjpd` and `vecbook` use a shared text record parsing pattern via `src/textrec/text_records.py`:

- Records stored in `.txt` files
- Records separated by `---` on a line by itself
- Optional metadata headers using `Key: Value` format
- Multi-line content support
- URL decoding for paths (handles Cursor encoding like `%3A` for `:`)

Example format:
```
Priority: 10
ID: task-ABC
This is the task description.
It can span multiple lines.
---
Priority: 5
ID: task-XYZ
Another task.
---
```

### Configuration Management
Projects use TOML files for configuration:

- **pjpd**: `projectmcp.toml` - projects directory, max results
- **vecbook**: `vecbook.toml` - data directory, embedding model, similarity metric

Configuration is loaded via `src/config.py` which provides typed access to settings.

### MCP Response Format
All MCP tools return a consistent response structure:
```python
# Success
{"success": True, "result": <data>, "error": ""}

# Failure
{"success": False, "result": "", "error": "error message"}
```

**IMPORTANT: Error Message Directive**

Error messages must be instructive prompts that guide the LLM on how to fix the problem. Instead of generic errors, provide actionable guidance.

❌ Bad: `"Error: file not found"`

✅ Good: `"The file 'project.txt' was not found in ~/projects. Possible solutions: 1) Verify the project name is correct, 2) Check that the file exists using list_projects(), 3) Create a new project using new_project() if it doesn't exist."`

Error messages should:
- Explain what went wrong in context
- Provide 2-3 specific steps to resolve the issue
- Reference relevant MCP tools or commands that can help
- Include actual values (file paths, IDs, etc.) that were problematic

## Project-Specific Details

### pjpd (Project Management)
- **Storage**: Plain text files in `~/projects` (configurable)
- **Entities**: Tasks, Ideas, Epics (all use TextRecords pattern)
- **ID Generation**: Tag-based format `<tag>-XXXX`
- **Ignore Files**: `pjpdignore` file in `pjpd/` subdirectory under projects directory
- **Module Structure**:
  - `src/projects/` - Task and project management
  - `src/ideas/` - Idea tracking with scoring
  - `src/epics/` - Epic management linking ideas and projects
  - `src/validation.py` - Pydantic models for all entities

### vecbook (Vector Search)
- **Storage**: Text records in `data/` directory
- **Embeddings**: sentence-transformers (all-MiniLM-L6-v2)
- **Search**: FAISS index for similarity search
- **HTTP Server**: Port 51539 for embedding API
- **Module Structure**:
  - `src/mcp_wrapper.py` - MCP server for semantic search
  - `src/http_server.py` - HTTP API for embeddings
  - `src/vecx/` - Vector indexing logic
  - `src/textrec/` - Text record parsing

### shell
- **CMD Shell**: Allowlist-based command execution on Windows
- **Security**: Rejects shell operators (`&&`, `;`, `|`, etc.)
- **Persistent Process**: Maintains CMD process across requests
- **Allowed Commands**: dir, echo, curl, type, find, findstr, cd, where, set, podman

### atproto
- **Authentication**: Stored credentials in platform-specific location
  - Windows: `%APPDATA%\atproto\credentials.json`
  - Unix-like: `~/.atproto/credentials.json`
- **Setup**: `python atproto-wrapper.py -u username password`
- **Session Management**: Persistent sessions with automatic re-authentication

## Testing Standards

### Test Organization
- Mirror source directory structure in `tests/`
- Use `test_` prefix for files, classes, and functions
- Use `pytest.mark.asyncio` for async tests
- Use `conftest.py` for shared fixtures
- Clean up test files in teardown

### Test Pattern
```python
import pytest
from pathlib import Path

class TestModuleName:
    def test_function_name(self):
        # Arrange
        # Act
        # Assert

    @pytest.mark.asyncio
    async def test_async_function(self):
        # Async test implementation
```

### Coverage
```bash
pytest -v --cov=src          # Run with coverage
```

## Development Preferences (from pjpd/.cursor/rules)

- **No one-time test scripts**: All tests must be proper unit tests in `tests/`
- **Functional programming**: Favor functional constructions over imperative
- **No globals**: Use class instance properties instead
- **Minimal metadata**: Avoid excessive metadata fields
- **Simplicity**: Keep implementations simple, ask before extending functionality

## Claude Desktop Configuration

MCP servers are configured in `claude_desktop_config.json`:

**Windows**: `%APPDATA%\Claude\claude_desktop_config.json`
**macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
**Linux**: `~/.config/Claude/claude_desktop_config.json`

Example configuration:
```json
{
  "mcpServers": {
    "pjpd": {
      "command": "uv",
      "args": ["--directory", "C:\\work\\mcp-wrappers\\pjpd", "run", "python", "pjpd.py"]
    },
    "vecbook": {
      "command": "C:/work/mcp-wrappers/vecbook/.venv/Scripts/python.exe",
      "args": ["C:/work/mcp-wrappers/vecbook/vecbook.py"]
    }
  }
}
```

## Dependencies

All projects share these core dependencies:
- `fastmcp>=0.1.0` - MCP server framework
- `mcp>=1.9.1` - MCP protocol implementation
- `pydantic>=2.0.0` - Data validation
- `toml>=0.10.0` - Configuration parsing

Project-specific:
- **vecbook**: `sentence-transformers`, `faiss-cpu`, `fastapi`, `uvicorn`
- **atproto**: `atproto>=0.0.50` - Official atproto Python SDK

Dev dependencies:
- `pytest>=7.0.0` - Testing framework
- `pytest-asyncio` - Async test support
- `pytest-cov` - Coverage reporting
- `black`, `isort`, `mypy` - Code quality tools (pjpd)

## Security Considerations

- **Shell wrappers**: Use allowlists to prevent command injection
- **Credential storage**: Platform-specific secure locations with proper permissions (600 on Unix)
- **Input validation**: All MCP tool inputs validated via Pydantic models
- **Atomic writes**: File operations use atomic writes to prevent corruption
- **Error handling**: Comprehensive try-catch blocks prevent information leakage
