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

---

## Data Format and Storage

### Task Record Format

* Each task **MUST** be delimited by a separator line consisting of exactly three hyphens (`---`) on a line by itself
* Each task **MUST** contain exactly four lines in this order:
    1. `ID: {10-character-random-string}`
    2. `Priority: {integer}`
    3. `Status: {ToDo|Done}`
    4. Task description (may span multiple lines)
* Task IDs **MUST** be exactly 10 characters
* Task ID character sets **SHOULD** use base32 alphabet (a-z, 2-9) excluding visually ambiguous characters (1, l, o, 0) to facilitate manual entry
* Task IDs **MUST** be unique within the entire system (across all projects)
* Task ID uniqueness **MAY** rely on entropy/randomness without coordination – no global registry or coordination mechanism is required
* Tasks **MUST** be parsed in order of appearance within each file
* Tasks **MAY** be sorted by priority when saving to disk
* Empty or malformed tasks **MUST** be ignored with a WARN-level log message


### Example Task Format
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
ID: aB-cDeF-gH
Priority:  100
Status: ToDo
Refactor the error handling in the main loop for 
better readability.
---

### Idea Record Format (NEW)

*See also: [Epic Record Format](#epic-record-format-new) for grouping ideas and projects into higher-level workstreams.*

* Each idea **MUST** be delimited by the same separator line of exactly three hyphens (`---`).
* Each idea **MUST** contain **three or more** lines in this order:
    1. `ID: {10-character-random-string}`
    2. `Score: {integer}`
    3. Idea description (may span multiple lines)
* Idea records **MUST NOT** include a `Status:` line. Ideas are considered non-actionable until promoted to a task.
* Idea IDs **MUST** follow the same uniqueness rules as task IDs and share the same global ID space.
* Ideas **MUST** be sorted by score when saving to disk (higher scores first).
* Ideas missing an ID **MUST** be given an ID when read or written.
* Empty or malformed idea records **MUST** be ignored with a WARN-level log message.

#### Example Idea Format

```
ID: ABCDEFGHIJ
Score:   75
Implement experimental AI-assisted code review workflow.
---
ID: KLMNOPQRST
Score:    5
Investigate alternative color palette for dark mode.
---
```

### Epic Record Format (NEW)

* Each epic **MUST** be delimited by the same separator line of exactly three hyphens (`---`).
* Each epic **MUST** contain **five or more** lines in this order:
    1. `Score: {integer}`
    2. `Ideas: {space-delimited-list-of-idea-ids}`
    3. `Projects: {space-delimited-list-of-project-names}`
    4. `ID: {10-character-random-string}`
    5. Epic description (may span multiple lines)
* Epic IDs **MUST** follow the same uniqueness rules as task and idea IDs and share the same global ID space.
* Epics **MUST** be sorted by score when saving to disk (higher scores first).
* `mark_epic_done` **MUST NOT** delete the record; instead it **MUST** set the epic's score to `0`.
* Epics **MUST NOT** require referential integrity. It is acceptable if referenced idea IDs or project names do not exist.
* Empty or malformed epic records **MUST** be ignored with a WARN-level log message.

### File Organization

* Each project **MUST** be stored as a separate `.txt` file in the projects directory
* Project files **MUST** be named using the project name with `.txt` extension (e.g., `schedule-mcp.txt`)
* Project names **MUST** be converted to lowercase and all disallowed characters replaced with underscores for filenames
* Runs of multiple underscores in project names **MUST** be collapsed to a single underscore
* In addition to the project task file, the system **MAY** load a single companion file named `ideas.txt` located in the same directory as the project files.
* If `ideas.txt` exists, it **MUST** be parsed as an Ideas file following the Idea Record Format.
* Each file **MUST** use UTF-8 encoding
* Files **MAY** be created automatically when adding the first task or idea to a new project

### Ignore File Support

* When scanning for project files, the system **MUST** honor a `.pjpdignore` file in the projects directory
* The `.pjpdignore` file **MAY** contain a list of file patterns to ignore, one per line
* Ignore patterns **MUST** support simple wildcard semantics:
    * `*` matches any sequence of characters
    * Patterns are matched against the full filename (including extension)
    * Patterns are case-sensitive
* Empty lines and lines starting with `#` **MUST** be treated as comments and ignored
* Leading and trailing whitespace **MUST** be stripped from ignore patterns
* If a `.pjpdignore` file does not exist, files **MUST NOT** be ignored
* The system **MUST** only scan the projects directory itself (no recursive traversal)

---

## Task Management

### Priority and Status

* **Priority Levels**: Higher numbers = higher priority (e.g., priority 100 > priority 1)
* **Priority Storage**: Stored as plain integers, formatted as 4 digits with space padding when rendered
* **Status Values**:
    * `ToDo`: Task needs to be completed (default for new tasks)
    * `Done`: Task has been completed

### Idea Scoring

* **Score Levels**: Higher numbers = higher relevance/desirability (e.g., score 100 > score 1)
* **Score Storage**: Stored as plain integers, formatted as 4 digits with space padding when rendered

### Task Operations

* Tasks **MUST** be identified by their project and 10-character ID
* Task IDs **MUST** be generated automatically when creating new tasks
* Task updates **MUST** preserve the original file structure and separator format
* Completed tasks **MAY** be filtered out of normal listings but **MUST** remain in the file
* Task descriptions **MAY** span multiple lines but **MUST NOT** contain the `---` separator
* The system **MUST** be able to locate any task by ID across all project files
* **Task Access Requirement**: All task operations **MUST** be performed through a project, id pair. The system **MUST** validate that the specified project exists before attempting to access or modify any task.

### Idea Operations

* Ideas **MUST** be identified by their unique 10-character ID within the project directory idea.txt file.
* Idea IDs **MUST** be generated automatically when creating new ideas.
* Idea updates **MUST** preserve the original file structure and separator format while sorted for score.

---

## API

### MCP Interface

* The system **MUST** present an MCP tools interface
* Use MCP SDK "fastmcp>=0.1.0" https://atproto.blue/en/latest/
* Server **MUST** support stdio transport by default

#### Required Prompts

* `intro` – Return introductory description of the ProjectMCP system:
    * No parameters required

#### Required Tools

* `list_projects` – Return list of all projects with task counts:
    * `path` (string, optional): Path to projects directory (default: ~/projects)
* `new_project` – Create a new empty project file:
    * `project` (string, required): Project name (becomes filename without .txt)
* `list_tasks` – List tasks with optional filtering:
    * `project` (string, optional): Filter by specific project
    * `priority` (integer, optional): Filter by priority level (returns all tasks >= this priority)
    * `status` (string, optional): Filter by status ("ToDo" or "Done")
    * `max_results` (integer, optional): Maximum number of results to return
* `add_task` – Create a new task with parameters:
    * `project` (string, required): Project name (becomes filename without .txt)
    * `description` (string, required): Task description
    * `priority` (integer, required): Priority level (higher numbers = higher priority)
* `update_task` – Update an existing task:
    * `project` (string, required): The name of the project containing the task
    * `task_id` (string, required): 10-character task ID
    * `description` (string, optional): New task description
    * `priority` (integer, optional): New priority level
    * `status` (string, optional): New status ("ToDo" or "Done")
* `mark_done` – Mark a task as completed:
    * `project` (string, required): The name of the project containing the task
    * `task_id` (string, required): 10-character task ID
* `next_steps` – Determine high-priority tasks to work on next:
    * `max_results` (integer, optional): Maximum number of suggestions to return (default: 5)
* `get_statistics` – Get comprehensive statistics about all projects:
    * No parameters required
* `list_ideas` – List ideas:
    * `max_results` (integer, optional): Maximum number of results to return
* `add_idea` – Create a new idea in ideas.txt with parameters:
    * `score` (integer, required): Score value (higher numbers = higher relevance)
        * `description` (string, required): Idea description
* `update_idea` – Update an existing idea:
    * `idea_id` (string, required): 10-character idea ID
    * `score` (integer, optional): New score value
    * `description` (string, optional): New idea description
* `remove_idea` – Remove an idea completely:
    * `idea_id` (string, required): 10-character idea ID
* `list_epics` – List epics:
    * `max_results` (integer, optional): Maximum number of results to return
* `add_epic` – Create a new epic in epics.txt with parameters:
    * `score` (integer, required): Score value (higher numbers = higher relevance)
    * `description` (string, required): Epic description
    * `ideas` (string, optional): Space-delimited list of idea IDs
    * `projects` (string, optional): Space-delimited list of project names
* `update_epic` – Update an existing epic:
    * `epic_id` (string, required): 10-character epic ID
    * `score` (integer, optional): New score value
    * `description` (string, optional): New epic description
    * `ideas` (string, optional): Space-delimited list of idea IDs
    * `projects` (string, optional): Space-delimited list of project names
* `mark_epic_done` – Mark an epic as done (sets score to 0):
    * `epic_id` (string, required): 10-character epic ID

---

## Querying and Reporting

### Overview Generation

* System **MUST** provide project summaries including:
    * Total tasks per project
    * Count of tasks by priority level
    * Count of completed vs. pending tasks
    * Projects with no pending high-priority tasks
    * Total ideas and highest-scored ideas per project

### Next Steps Algorithm

* **MUST** prioritize tasks in this order:
    1. Higher priority number tasks with Status: ToDo (e.g., priority 100 before priority 1)
    2. Tasks are sorted by priority value in descending order
* **MUST** return tasks from multiple projects when available
* **SHOULD** indicate which project each suggested task belongs to

---

## Error Handling

* Invalid project names **MUST** return appropriate error messages
* Missing or ignored files **MUST** be handled gracefully (empty project)
* Malformed task or idea records **MUST** be logged and skipped
* Invalid task or ideas **MUST** return clear error messages

---

## Startup Behavior

* Projects **MUST NOT** be indexed at startup (let the user initiate via tool calls)
* System **MUST** create projects directory if it doesn't exist
* On loading a project directory, the system **MUST** look for a companion `ideas.txt` file and load ideas if the file exists.
* Startup **MUST** complete successfully even if some project or idea files contain malformed records
* All logging output **MUST** be directed to stderr

---

## Performance Requirements

* The system **SHOULD** handle at least 100 projects with 1000 total tasks and 1000 total ideas efficiently
* File operations **SHOULD** complete in under 500ms for typical project sizes
* Task and idea listing and filtering **SHOULD** return results in under 200ms
* System **MUST NOT** cache file contents between operations (always read from disk)

---

## Developer Experience

* The system **MUST** be runnable as an MCP server with standard stdio transport
* Code **SHOULD** follow standard Python style guidelines (PEP 8) and be documented
* The system **SHOULD** provide clear error messages for common issues
* Logging **SHOULD** be configurable (INFO level by default)
* All logging output **MUST** be directed to stderr to avoid interfering with MCP stdio communication
* Sample project and idea files **SHOULD** be included for testing

---

## Integration with TextRecords

* **MUST** use the existing `text_records.py` utility for file parsing
* **MUST** extend TextRecords parsing to handle both Task and Idea formats
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
* Task and idea history and change tracking
* Project archiving and cleanup tools

---

## Status

> This spec is a working draft. Contributions and revisions welcome.
