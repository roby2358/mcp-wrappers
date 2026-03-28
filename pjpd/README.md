# ProjectMCP

A lightweight, local-first project management system built on plain `.txt` files using the Model Context Protocol (MCP). ProjectMCP manages tasks, ideas, and epics for a single project rooted at the current working directory.

## Features

- **Local-first**: All data stored in plain text files on your local machine
- **Single-project**: One project per directory, tied to the current working directory
- **Simple format**: Tasks, ideas, and epics stored in human-readable `.txt` files
- **Priority-based**: Higher numbers = higher priority task management
- **Idea management**: Track and score ideas for future development
- **Epic organization**: Group related ideas and projects into higher-level workstreams
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
- "List all pending tasks"
- "Mark task 'dev-a2c4' as completed"
- "What should I work on next?"
- "Show me project statistics"

**Idea Management:**
- "Add a new idea: 'Implement dark mode' with score 8 and tag 'ui'"
- "List my top 10 ideas"
- "Update idea 'ui-a2c4' to have score 9"

**Epic Management:**
- "Create a new epic 'User Experience Improvements' with score 7 and tag 'ux'"
- "Show me all my epics"
- "Mark epic 'ux-a2c4' as completed"

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
├── epics.txt     # All epics
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

### Epic Storage

```
Score:   85
Ideas: ai-abcd ui-klmn
Projects: website-redesign mobile-app
ID: platform-efgh
Build a unified platform for web and mobile development.
---
```

### Record Properties

> **Note**: Tags are used internally for ID generation but are not exposed in API responses. The tag field is only used when creating new tasks, ideas, or epics.

#### Tasks
- **ID**: Tag-based unique identifier (format: `<tag>-XXXX`)
- **Priority**: Integer value (higher numbers = higher priority)
- **Status**: `ToDo` or `Done`
- **Description**: Multi-line task description

#### Ideas
- **ID**: Tag-based unique identifier (format: `<tag>-XXXX`)
- **Score**: Integer value (higher numbers = higher relevance)
- **Description**: Multi-line idea description

#### Epics
- **Score**: Integer value (higher numbers = higher relevance)
- **Ideas**: Space-delimited list of idea IDs
- **Projects**: Space-delimited list of project names
- **ID**: Tag-based unique identifier (format: `<tag>-XXXX`)
- **Description**: Multi-line epic description

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

3. **Mark a task complete:**
   ```
   mark_done("design-ab12")
   ```

4. **Get next steps:**
   ```
   next_steps(max_results=3)
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

### Epic Organization

1. **Create an epic:**
   ```
   add_epic(85, "Platform unification", "platform", "ai-abcd ui-klmn", "website-redesign mobile-app")
   ```

2. **List epics:**
   ```
   list_epics(max_results=3)
   ```

### Advanced Filtering

```
# List all high-priority tasks
list_tasks(priority=8)

# List only completed tasks
list_tasks(status="Done")

# List tasks with limit
list_tasks(max_results=10)
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
│   ├── epics/
│   │   ├── epics.py         # Epic management logic
│   │   └── epic.py          # Epic data structures
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
