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
- "Add a task: 'Design homepage mockup' with tag 'design' and priority 70"
- "List my tasks"
- "Show me completed tasks too"
- "Mark tasks 'dev-a2c4' and 'bug-x3y5' as completed"
- "Bump 'dev-a2c4' to priority 90"
- "Show me project statistics"

**Idea Management:**
- "Add a new idea: 'Implement dark mode' with score 80 and tag 'ui'"
- "List my top 10 ideas"
- "Update idea 'ui-a2c4' to have score 90"
- "Mark ideas 'ui-a2c4' and 'ai-bb12' as done"

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

1. **Create tasks** (provide `tag` to create a new task):
   ```
   pjpd_put_task(description="Design new homepage layout", tag="design", priority=80)
   pjpd_put_task(description="Update contact form", tag="form", priority=50)
   pjpd_put_task(description="Test responsive design", tag="test", priority=70)
   ```

2. **List tasks** (sorted ToDo-first, then by priority descending):
   ```
   pjpd_list_tasks()
   pjpd_list_tasks(count=10)
   pjpd_list_tasks(show_done=True)
   ```

3. **Update a task** (provide `id` to update):
   ```
   pjpd_put_task(id="design-ab12", description="Design new homepage layout (v2)", priority=90)
   ```

4. **Reprioritize without resending the description:**
   ```
   pjpd_reprioritize_task(priority=90, task_ids=["design-ab12", "test-cd34"])
   ```

5. **Mark tasks complete** (all-or-nothing):
   ```
   pjpd_mark_task_done(task_ids=["design-ab12", "form-cd34"])
   ```

6. **Project statistics:**
   ```
   pjpd_get_statistics()
   ```

### Idea Management

1. **Create ideas:**
   ```
   pjpd_put_idea(score=75, description="Implement AI-powered code review", tag="ai-review")
   pjpd_put_idea(score=50, description="Add dark mode support", tag="dark-mode")
   ```

2. **Update an idea:**
   ```
   pjpd_put_idea(id="ai-review-ab12", score=90, description="AI code review with inline suggestions")
   ```

3. **List ideas (highest score first):**
   ```
   pjpd_list_ideas(count=5)
   ```

4. **Mark ideas done** (score → 0, description prefixed with `(Done)`):
   ```
   pjpd_mark_idea_done(idea_ids=["ai-review-ab12", "dark-mode-cd34"])
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
