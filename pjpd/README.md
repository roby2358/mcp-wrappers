# ProjectMCP

A lightweight, local-first project management system built on plain `.txt` files using the Model Context Protocol (MCP). ProjectMCP provides task tracking, prioritization, and project overview capabilities through a simple text-based storage format.

## Features

- **Local-first**: All data stored in plain text files on your local machine
- **Simple format**: Tasks stored in human-readable `.txt` files
- **Priority-based**: Higher numbers = higher priority task management
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

### 1. Start the MCP Server

```bash
# Run the server directly
python pjpd.py
```

The server will start and listen for MCP connections via stdio transport.

### 2. Create Your First Project

Using an MCP client (like Claude Desktop), you can now:

- Create new projects
- Add tasks with priorities
- List and filter tasks
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
- **Max Results**: 50 tasks per query
- **File Encoding**: UTF-8
- **Transport**: stdio (for MCP communication)

## Data Format

### Task Storage

Tasks are stored in plain text files with the following format:

```
ID: AB-CDEF-GH
Priority:    1
Status: ToDo
Add functionality to encapsulate the cardinal graham meters.
---
ID: 12-3456-78
Priority:   10
Status: Done
Update documentation for the new API endpoints.
---
```

### File Organization

- Each project is stored as a separate `.txt` file
- Project names are converted to lowercase with underscores
- Files are stored in the configured projects directory
- Example: `My Project` becomes `my_project.txt`

### Task Properties

- **ID**: 10-character unique identifier (base32 alphabet)
- **Priority**: Integer value (higher numbers = higher priority)
- **Status**: `ToDo` or `Done`
- **Description**: Multi-line task description

### Ignore File Support

Create a `.ignore` file in your projects directory to exclude specific files:

```
# Ignore backup files
*.bak
*.backup

# Ignore temporary files
temp_*
```

## API Reference

### MCP Tools

#### `new_project`
Create a new empty project file.

**Parameters:**
- `project` (string, required): Project name

#### `add_task`
Create a new task with parameters.

**Parameters:**
- `project` (string, required): Project name
- `description` (string, required): Task description
- `priority` (integer, required): Priority level (higher numbers = higher priority)

#### `list_tasks`
List tasks with optional filtering.

**Parameters:**
- `project` (string, optional): Filter by specific project
- `priority` (integer, optional): Filter by priority level (returns all tasks >= this priority)
- `status` (string, optional): Filter by status ("ToDo" or "Done")
- `max_results` (integer, optional): Maximum number of results to return

#### `update_task`
Update an existing task.

**Parameters:**
- `project` (string, required): The name of the project containing the task
- `task_id` (string, required): 10-character task ID
- `description` (string, optional): New task description
- `priority` (integer, optional): New priority level
- `status` (string, optional): New status ("ToDo" or "Done")

#### `mark_done`
Mark a task as completed.

**Parameters:**
- `project` (string, required): The name of the project containing the task
- `task_id` (string, required): 10-character task ID

#### `next_steps`
Determine high-priority tasks to work on next.

**Parameters:**
- `max_results` (integer, optional): Maximum number of suggestions to return (default: 5)

#### `list_projects`
Return list of all projects with task counts.

**Parameters:**
- `path` (string, optional): Path to projects directory (default: ~/projects)

#### `get_statistics`
Get comprehensive statistics about all projects.

**Parameters:** None

### MCP Prompts

#### `intro`
Return introductory description of the ProjectMCP system.

**Parameters:** None

## Usage Examples

### Basic Workflow

1. **Create a project and add tasks:**
   ```
   new_project("website-redesign")
   add_task("website-redesign", "Design new homepage layout", 10)
   add_task("website-redesign", "Update contact form", 5)
   add_task("website-redesign", "Test responsive design", 8)
   ```

2. **List tasks by priority:**
   ```
   list_tasks("website-redesign", priority=5)
   ```

3. **Mark a task complete:**
   ```
   mark_done("website-redesign", "AB-CDEF-GH")
   ```

4. **Get next steps:**
   ```
   next_steps(max_results=3)
   ```

### Advanced Filtering

```bash
# List all high-priority tasks across all projects
list_tasks(priority=8)

# List only completed tasks
list_tasks(status="Done")

# List tasks from specific project with limit
list_tasks("my-project", max_results=10)
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
