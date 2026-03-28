# ProjectMCP

A lightweight, local-first project management system built on plain `.txt` files using the Model Context Protocol (MCP). ProjectMCP manages tasks and ideas for a single project rooted at the current working directory.

## Features

- **Local-first**: All data stored in plain text files on your local machine
- **Single-project**: One project per directory, tied to the current working directory
- **Simple format**: Tasks and ideas stored in human-readable `.txt` files
- **Priority-based**: Higher numbers = higher priority task management
- **Idea management**: Track and score ideas for future development
- **MCP integration**: Full Model Context Protocol support for AI assistant integration
- **Atomic operations**: Safe file writing with timestamped backups to prevent data corruption
- **Cross-platform**: Works on Windows, macOS, and Linux

## Installation

### Prerequisites

- Python 3.11 or higher
- pip or uv package manager

### Install from source

```bash
uv sync
source .venv/bin/activate  # macOS/Linux
# or
.venv\Scripts\activate     # Windows
```

## Quick Start

### Run in Claude Desktop

Add this to your desktop configuration:

```json
  "mcpServers": {
    "pjpd": {
      "command": "uv",
      "args": ["--directory", "C:\\work\\mcp-wrappers\\pjpd", "run", "python", "pjpd.py"]
    }
  }
```

### Start the MCP Server

```bash
python pjpd.py
```

The server starts and listens for MCP connections via stdio transport. It operates on the current working directory — all data is stored under `<cwd>/pjpd/`.

### Common Operations

Using an MCP client (like Claude Desktop or Claude Code), you can:

**Task Management:**
- "Add a task: 'Design homepage mockup' with tag 'design' and priority 3"
- "Show me all high-priority tasks (priority >= 3)"
- "List my tasks"
- "Show me completed tasks too"
- "Mark task 'dev-a2c4' as completed"
- "Show me project statistics"

**Idea Management:**
- "Add a new idea: 'Implement dark mode' with score 8 and tag 'ui'"
- "List my top 10 ideas"
- "Update idea 'ui-a2c4' to have score 9"

## Configuration

ProjectMCP uses a TOML configuration file named `projectmcp.toml` in the project root:

```toml
# Maximum number of results to return in list operations
max_results = 50
```

### Default Settings

- **Max Results**: 50 items per query
- **File Encoding**: UTF-8
- **Transport**: stdio (for MCP communication)

## Data Format

All data is stored under `<cwd>/pjpd/`:

```
<cwd>/pjpd/
├── tasks.txt     # All tasks
├── ideas.txt     # All ideas
└── bak/          # Timestamped backups from atomic writes
```

### Task Storage

```
Priority:    1
Status: ToDo
ID: bug-ab12
Add functionality to encapsulate the cardinal graham meters.
---
Priority:   10
Status: Done
ID: doc-3456
Update documentation for the new API endpoints.
---
```

### Idea Storage

```
Score:   75
ID: ai-abcd
Implement experimental AI-assisted code review workflow.
---
Score:    5
ID: ui-klmn
Investigate alternative color palette for dark mode.
---
```

### Record Properties

> **Note**: Tags are used internally for ID generation but are not exposed in API responses. The tag field is only used when creating new tasks or ideas.

#### Tasks
- **ID**: Tag-based unique identifier (format: `<tag>-XXXX`)
- **Priority**: Integer value (higher numbers = higher priority)
- **Status**: `ToDo` or `Done`
- **Description**: Multi-line task description

#### Ideas
- **ID**: Tag-based unique identifier (format: `<tag>-XXXX`)
- **Score**: Integer value (higher numbers = higher relevance)
- **Description**: Multi-line idea description

### Legacy Project File Warning

If pjpd detects a file named `pjpd/<directory-name>.txt` (from the old multi-project format), task tool responses will include a `"warning"` property alerting you to its presence. This helps with migration from the previous multi-project layout.

## API Reference

For complete API documentation including all MCP tools and prompts, see [README_API.md](README_API.md).

## Usage Examples

### Basic Workflow

1. **Add tasks:**
   ```
   add_task("Design new homepage layout", "design", 10)
   add_task("Update contact form", "form", 5)
   add_task("Test responsive design", "test", 8)
   ```

2. **List tasks by priority:**
   ```
   list_tasks(priority=5)
   ```

3. **List including completed tasks:**
   ```
   list_tasks(show_done=True)
   ```

4. **Mark a task complete:**
   ```
   mark_done("design-ab12")
   ```

### Idea Management

1. **Add ideas:**
   ```
   add_idea(75, "Implement AI-powered code review", "ai-review")
   add_idea(50, "Add dark mode support", "dark-mode")
   ```

2. **List high-scoring ideas:**
   ```
   list_ideas(max_results=5)
   ```

### Advanced Filtering

```
# List all high-priority tasks
list_tasks(priority=8)

# Include completed tasks
list_tasks(show_done=True)

# Limit results
list_tasks(count=10)
```

## Development

### Project Structure

```
pjpd/
├── src/
│   ├── mcp_wrapper.py      # Main MCP server implementation
│   ├── config.py            # Configuration management
│   ├── validation.py        # Pydantic request models
│   ├── projects/
│   │   ├── projects.py      # Single-project manager
│   │   ├── project.py       # Project (task collection) handling
│   │   └── task.py          # Task data structures
│   ├── ideas/
│   │   ├── ideas.py         # Idea management logic
│   │   └── idea.py          # Idea data structures
│   └── textrec/
│       ├── text_records.py  # Text record parsing and atomic writes
│       └── record_id.py     # Tag-based ID generation
├── tests/                   # Unit tests
├── resources/
│   └── intro.txt            # System introduction text
├── pjpd.py                  # Entry point
├── projectmcp.toml          # Configuration
└── SPEC.md                  # Detailed specification
```

### Running Tests

```bash
pytest -v                    # Run all tests
pytest -v --cov=src          # Run with coverage
pytest -v tests/projects/test_project_creation_and_saving.py  # Run specific file
```

### Code Quality

```bash
black src/ tests/            # Format code
isort src/ tests/            # Sort imports
mypy src/                    # Type checking
```

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

For detailed technical specifications, see [SPEC.md](SPEC.md).
