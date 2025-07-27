# ProjectMCP — Local Project Management Server

## Overview

ProjectMCP is a lightweight, local-first project management system built on plain `.txt` files using the text_records utility. It provides task tracking, prioritization, and project overview capabilities through an MCP interface. The system maintains projects as collections of tasks stored in human-readable format, with each project residing in its own text file.

This specification outlines the design, structure, and operational requirements of ProjectMCP. It is intended for developers contributing to the core system, as well as those building tools and extensions atop it.

---

## Configuration

* All configuration files **MUST** be in TOML format
* Configuration file **MUST** be named `projectmcp.toml` and located in the project root
* Default configuration values:
    * `projects_directory` = "~/projects"
    * `max_results` = 50

## API

### MCP Interface

* The system **MUST** present an MCP tools interface
* Use MCP SDK "fastmcp>=0.1.0" https://atproto.blue/en/latest/
* Server **MUST** support stdio transport by default

#### Required Tools

* `new_project` - Create a new empty project file:
    * `project` (string, required): Project name (becomes filename without .txt)
* `add_task` - Create a new task with parameters:
    * `project` (string, required): Project name (becomes filename without .txt)
    * `description` (string, required): Task description
    * `priority` (integer, required): Priority level (1=High, 2=Medium, 3=Note)
* `list_tasks` - List tasks with optional filtering:
    * `project` (string, optional): Filter by specific project
    * `priority` (integer, optional): Filter by priority level
    * `status` (string, optional): Filter by status ("ToDo" or "Done")
    * `max_results` (integer, optional): Maximum number of results to return
* `update_task` - Update an existing task:
    * `task_id` (string, required): 12-character task ID
    * `description` (string, optional): New task description
    * `priority` (integer, optional): New priority level
    * `status` (string, optional): New status ("ToDo" or "Done")
* `mark_done` - Mark a task as completed:
    * `task_id` (string, required): 12-character task ID
* `get_overview` - Return summary of all projects and tasks:
    * `include_done` (boolean, optional): Include completed tasks in overview (default: false)
* `next_steps` - Determine high-priority tasks to work on next:
    * `max_results` (integer, optional): Maximum number of suggestions to return (default: 5)
* `list_projects` - Return list of all projects with task counts:
    * `path` (string, optional): Path to projects directory (default: ~/projects)
* `sort_project` - Re-sort tasks within a project:
    * `project` (string, required): Project name to sort
    * `sort_by` (string, optional): Sort criteria (default: "priority_text")
        * "priority_text": Sort by priority (1, 2, 3) then alphabetically by task description

## Startup Behavior

* Projects **MUST NOT** be indexed at startup (let the user initiate via tool calls)
* System **MUST** create projects directory if it doesn't exist
* Startup **MUST** complete successfully even if some project files contain malformed tasks
* All logging output **MUST** be directed to stderr

---

## Data Format and Storage

### Task Record Format

* Each task **MUST** be delimited by a separator line consisting of exactly three hyphens (`---`) on a line by itself
* Each task **MUST** contain exactly four lines in this order:
    1. `ID: {12-character-random-string}`
    2. `Priority: {1|2|3} {High|Medium|Note}`
    3. `Status: {ToDo|Done}`
    4. Task description (may span multiple lines)
* Task IDs **MUST** be exactly 12 characters using the URL-safe Base64 alphabet (A-Z, a-z, 0-9, -, _)
* Task IDs **MUST** be unique within the entire system (across all projects)
* Tasks **MUST** be parsed in order of appearance within each file
* Empty or malformed tasks **MUST** be ignored with a WARN-level log message

### Example Task Format

```
ID: aB3dEf7gHiJk
Priority: 1 High
Status: ToDo
Add functionality to encapsulate the cardinal graham meters.
---
ID: mN9pQr2sT4uV
Priority: 2 Medium
Status: Done
Update documentation for the new API endpoints.
---
ID: wX6yZ1aB5cDe
Priority: 3 Note
Status: ToDo
Consider refactoring the error handling in the main loop for better readability.
---
```

### File Organization

* Each project **MUST** be stored as a separate `.txt` file in the projects directory
* Project files **MUST** be named using the project name with `.txt` extension (e.g., `schedule-mcp.txt`)
* Project names **MUST** be converted to lowercase and spaces replaced with hyphens for filenames
* Each file **MUST** use UTF-8 encoding
* Files **MAY** be created automatically when adding the first task to a new project

---

## Task Management

### Priority Levels

* **Priority 1 (High)**: Tasks that act as dependencies for other work
* **Priority 2 (Medium)**: Standard tasks
* **Priority 3 (Note)**: Nice-to-have items, reminders, refactoring notes

### Status Values

* **ToDo**: Task needs to be completed (default for new tasks)
* **Done**: Task has been completed

### Task Operations

* Tasks **MUST** be identified by their unique 12-character ID across all projects
* Task IDs **MUST** be generated automatically when creating new tasks
* Task updates **MUST** preserve the original file structure and separator format
* Completed tasks **MAY** be filtered out of normal listings but **MUST** remain in the file
* Task descriptions **MAY** span multiple lines but **MUST NOT** contain the `---` separator
* The system **MUST** be able to locate any task by ID across all project files
* Tasks within a project **MAY** be re-sorted by priority (1, 2, 3) followed by alphabetical order of task description
* Sorting operations **MUST** preserve all task data including IDs, status, and descriptions
* Sorting **MUST** rewrite the entire project file with tasks in the new order

---

## Querying and Reporting

### Overview Generation

* System **MUST** provide project summaries including:
    * Total tasks per project
    * Count of tasks by priority level
    * Count of completed vs. pending tasks
    * Projects with no pending high-priority tasks

### Next Steps Algorithm

* **MUST** prioritize tasks in this order:
    1. Priority 1 (High) tasks with Status: ToDo
    2. Priority 2 (Medium) tasks with Status: ToDo
    3. Priority 3 (Note) tasks with Status: ToDo
* **MUST** return tasks from multiple projects when available
* **SHOULD** indicate which project each suggested task belongs to

### Error Handling

* Invalid project names **MUST** return appropriate error messages
* Missing files **MUST** be handled gracefully (empty project)
* Malformed task records **MUST** be logged and skipped
* Invalid task IDs **MUST** return clear error messages
* Duplicate task IDs **MUST** be prevented during task creation

---

## Performance Requirements

* The system **SHOULD** handle at least 100 projects with 1000 total tasks efficiently
* File operations **SHOULD** complete in under 500ms for typical project sizes
* Task listing and filtering **SHOULD** return results in under 200ms
* System **MUST NOT** cache file contents between operations (always read from disk)

---

## Developer Experience

* The system **MUST** be runnable as an MCP server with standard stdio transport
* Code **SHOULD** follow standard Python style guidelines (PEP 8) and be documented
* The system **SHOULD** provide clear error messages for common issues
* Logging **SHOULD** be configurable (INFO level by default)
* All logging output **MUST** be directed to stderr to avoid interfering with MCP stdio communication
* Sample project files **SHOULD** be included for testing

---

## Integration with TextRecords

* **MUST** use the existing `text_records.py` utility for file parsing
* **MUST** extend TextRecords parsing to handle the specific task format
* **MUST** maintain compatibility with the existing record separator (`---`)
* **MAY** add project-specific metadata parsing on top of the base TextRecords functionality

---

## Out of Scope

* No due dates or time tracking in the initial version
* No task dependencies or hierarchical organization
* No user authentication or multi-user support
* No web interface or REST API
* No persistent caching or database storage
* No file watching or real-time updates

---

## Future Extensions (Non-Binding)

* Due date tracking and deadline notifications
* Task dependencies and blocking relationships
* Project templates and task automation
* Time tracking and effort estimation
* Integration with calendar systems
* Bulk task operations (import/export)
* Task history and change tracking
* Project archiving and cleanup tools

---

## Status

> This spec is a working draft. Contributions and revisions welcome.