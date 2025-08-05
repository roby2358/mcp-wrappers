# ProjectMCP

A lightweight, local-first project management system built on plain `.txt` files using the Model Context Protocol (MCP). ProjectMCP provides task tracking, prioritization, project overview, and idea management capabilities through a simple text-based storage format.

## Features

- **Local-first**: All data stored in plain text files on your local machine
- **Simple format**: Tasks, ideas, and epics stored in human-readable `.txt` files
- **Priority-based**: Higher numbers = higher priority task management
- **Idea management**: Track and score ideas for future development
- **Epic organization**: Group related ideas and projects into higher-level workstreams
- **MCP integration**: Full Model Context Protocol support for AI assistant integration
- **No dependencies**: Minimal external dependencies, just Python and text files
- **Cross-platform**: Works on Windows, macOS, and Linux
- **Ignore file support**: Configure which project files to exclude
- **Atomic operations**: Safe file writing to prevent data corruption

## Installation

### Prerequisites

- Python 3.11 or higher
- pip or uv package manager

### Install from source

```bash
# Install with uv
uv sync
.venv\Scripts\activate  # Windows
# or
source .venv/bin/activate  # macOS/Linux
```

## Quick Start

### Run in Claude Desktop

Add this to your desktop configuration

```json
  "mcpServers": {
    "pjpd": {
      "command": "uv",
      "args": ["--directory", "C:\\work\\mcp-wrappers\\pjpd", "run", "python", "pjpd.py"]
    }
  }
```

### 1. Start the MCP Server

```bash
# Run the server directly
python pjpd.py
```

The server will start and listen for MCP connections via stdio transport.

### 2. Create Your First Project

Using an MCP client (like Claude Desktop), you can now:

- Create new projects
- Add tasks with priorities and tags
- Track ideas with scoring
- Organize work into epics
- List and filter tasks, ideas, and epics
- Mark tasks as complete
- Get next steps recommendations

## Configuration

ProjectMCP uses a TOML configuration file named `projectmcp.toml` in the project root:

```toml
# Directory where project files are stored
projects_directory = "~/projects"

# Maximum number of results to return in list operations
max_results = 50
```

### Default Settings

- **Projects Directory**: `~/projects` (expanded to user's home directory)
- **Max Results**: 50 items per query
- **File Encoding**: UTF-8
- **Transport**: stdio (for MCP communication)

## Data Format

### Task Storage

Tasks are stored in plain text files with the following format:

```
Priority:    1
Status: ToDo
ID: bug-AB12
Add functionality to encapsulate the cardinal graham meters.
---
Priority:   10
Status: Done
ID: doc-3456
Update documentation for the new API endpoints.
---
```

### Idea Storage

Ideas are stored in `ideas.txt` files with the following format:

```
Score:   75
ID: ai-ABCD
Implement experimental AI-assisted code review workflow.
---
Score:    5
ID: ui-KLMN
Investigate alternative color palette for dark mode.
---
```

### Epic Storage

Epics are stored in `epics.txt` files with the following format:

```
Score:   85
Ideas: ai-ABCD ui-KLMN
Projects: website-redesign mobile-app
ID: platform-EFGH
Build a unified platform for web and mobile development.
---
```

### File Organization

- Each project is stored as a separate `.txt` file
- Project names are converted to lowercase with underscores
- Files are stored in the configured projects directory
- Example: `My Project` becomes `my_project.txt`
- Ideas are stored in `ideas.txt` in the projects directory
- Epics are stored in `epics.txt` in the projects directory

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

### Ignore File Support

Create a `.pjpdignore` file in your projects directory to exclude specific files:

```
# Ignore backup files
*.bak
*.backup

# Ignore temporary files
temp_*
```

## API Reference

For complete API documentation including all MCP tools and prompts, see [README_API.md](README_API.md).

## Usage Examples

### Basic Workflow

1. **Create a project and add tasks:**
   ```
   new_project("website-redesign")
   add_task("website-redesign", "Design new homepage layout", "design", 10)
   add_task("website-redesign", "Update contact form", "form", 5)
   add_task("website-redesign", "Test responsive design", "test", 8)
   ```

2. **List tasks by priority:**
   ```
   list_tasks("website-redesign", priority=5)
   ```

3. **Mark a task complete:**
   ```
   mark_done("website-redesign", "design-AB12")
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
   add_epic(85, "Platform unification", "platform", "ai-ABCD ui-KLMN", "website-redesign mobile-app")
   ```

2. **List epics:**
   ```
   list_epics(max_results=3)
   ```

### Advanced Filtering

```bash
# List all high-priority tasks across all projects
list_tasks(priority=8)

# List only completed tasks
list_tasks(status="Done")

# List tasks from specific project with limit
list_tasks("my-project", max_results=10)

# List high-scoring ideas
list_ideas(max_results=10)
```

## Development

### Project Structure

```
pjpd/
├── src/
│   ├── mcp_wrapper.py      # Main MCP server implementation
│   ├── config.py           # Configuration management
│   ├── projects/
│   │   ├── projects.py     # Project management logic
│   │   ├── project.py      # Individual project handling
│   │   ├── task.py         # Task data structures
│   │   └── ignore_list.py  # File ignore functionality
│   ├── ideas/
│   │   ├── ideas.py        # Idea management logic
│   │   └── idea.py         # Idea data structures
│   ├── epics/
│   │   ├── epics.py        # Epic management logic
│   │   └── epic.py         # Epic data structures
│   └── textrec/
│       └── text_records.py # Text record parsing utilities
├── tests/                  # Unit tests
├── resources/
│   └── intro.txt          # System introduction text
├── pjpd.py                # Entry point
├── projectmcp.toml        # Configuration
└── SPEC.md               # Detailed specification
```

### Running Tests

```bash
# Run all tests
pytest -v

# Run with coverage
pytest -v --cov=src

# Run specific test file
pytest -v tests/projects/test_project_creation_and_saving.py
```

### Code Quality

```bash
# Format code
black src/ tests/

# Sort imports
isort src/ tests/

# Type checking
mypy src/
```

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Ensure all tests pass
6. Submit a pull request

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Status

ProjectMCP is currently in alpha development. The core functionality is implemented and stable, but the API may evolve as the project matures.

For detailed technical specifications, see [SPEC.md](SPEC.md).
