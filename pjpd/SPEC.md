# ProjectMCP — Local Project Management Server

## Overview

ProjectMCP is a lightweight, local-first project management system built on plain `.txt` files using the text_records utility. It manages tasks, ideas, and epics for a single project rooted at the current working directory. All data lives under `<cwd>/pjpd/`.

This specification outlines the design, structure, and operational requirements of ProjectMCP. It is intended for developers contributing to the core system, as well as those building tools and extensions atop it.

---

## Configuration

* All configuration files **MUST** be in TOML format
* Configuration file **MUST** be named `projectmcp.toml` and located in the project root
* Default configuration values:
    * `max_results` = 50

---

## Data Format and Storage

### Task Record Format

* Each task **MUST** be delimited by a separator line consisting of exactly three hyphens (`---`) on a line by itself
* Each task **MUST** contain **at least three** property lines followed by a free-form description.
  The system writes the properties in this recommended order:

    1. `Priority: {integer}`
    2. `Status: {ToDo|Done}`
    3. `ID: {tag}-{4-character-random-string}`

* **Note**: The tag is extracted from the ID for internal use but is not stored separately
* Task IDs **MUST** be in the format `<tag>-XXXX` where:
    * `<tag>` is a 1-12 character string provided at creation
    * `XXXX` is a 4-character random string using base32 alphabet (a-z, 2-9) excluding visually ambiguous characters (1, l, o, 0)
* Task tags **MUST** be 1-12 characters long and contain only alphanumeric characters and hyphens
* Task IDs **MUST** be unique within the system
* Task ID uniqueness **MAY** rely on entropy/randomness without coordination – no global registry or coordination mechanism is required
* Tasks **MUST** be parsed in order of appearance within the file
* Tasks **MAY** be sorted by priority when saving to disk
* Empty or malformed tasks **MUST** be ignored with a WARN-level log message


### Example Task Format
```
ID: bug-AB12
Priority:    1
Status: ToDo
Add functionality to encapsulate the cardinal graham meters.
---
ID: doc-3456
Priority:   10
Status: Done
Update documentation for the new API endpoints.
---
ID: refactor-cDeF
Priority:  100
Status: ToDo
Refactor the error handling in the main loop for
better readability.
---

### Idea Record Format

*See also: [Epic Record Format](#epic-record-format) for grouping ideas and projects into higher-level workstreams.*

* Each idea **MUST** be delimited by the same separator line of exactly three hyphens (`---`).
* Each idea **MUST** contain **at least two** property lines followed by a free-form description.
  The system writes the properties in this recommended order:

    1. `Score: {integer}`
    2. `ID: {tag}-{4-character-random-string}`

* **Note**: The tag is extracted from the ID for internal use but is not stored separately
* Idea IDs **MUST** be in the format `<tag>-XXXX` where:
    * `<tag>` is a 1-12 character string provided at creation
    * `XXXX` is a 4-character random string using base32 alphabet (a-z, 2-9) excluding visually ambiguous characters (1, l, o, 0)
* Idea tags **MUST** be 1-12 characters long and contain only alphanumeric characters and hyphens
* Idea records **MUST NOT** include a `Status:` line. Ideas are considered non-actionable until promoted to a task.
* Idea IDs **MUST** follow the same uniqueness rules as task IDs and share the same global ID space.
* Ideas **MUST** be sorted by score when saving to disk (higher scores first).
* Ideas missing an ID **MUST** be given an ID when read or written.
* Empty or malformed idea records **MUST** be ignored with a WARN-level log message.

#### Example Idea Format

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

### Epic Record Format

* Each epic **MUST** be delimited by the same separator line of exactly three hyphens (`---`).
* Each epic **MUST** contain **five or more** lines in this order:
    1. `Score: {integer}`
    2. `Ideas: {space-delimited-list-of-idea-ids}`
    3. `Projects: {space-delimited-list-of-project-names}`
    4. `ID: {tag}-{4-character-random-string}`
    5. Epic description (may span multiple lines)
* **Note**: The tag is extracted from the ID for internal use but is not stored separately
* Epic IDs **MUST** be in the format `<tag>-XXXX` where:
    * `<tag>` is a 1-12 character string provided at creation
    * `XXXX` is a 4-character random string using base32 alphabet (a-z, 2-9) excluding visually ambiguous characters (1, l, o, 0)
* Epic tags **MUST** be 1-12 characters long and contain only alphanumeric characters and hyphens
* Epic IDs **MUST** follow the same uniqueness rules as task and idea IDs and share the same global ID space.
* Epics **MUST** be sorted by score when saving to disk (higher scores first).
* `mark_epic_done` **MUST NOT** delete the record; instead it **MUST** set the epic's score to `0`.
* Epics **MUST NOT** require referential integrity. It is acceptable if referenced idea IDs or project names do not exist.
* Empty or malformed epic records **MUST** be ignored with a WARN-level log message.

### File Organization

* The system **MUST** store all data under a `pjpd` subdirectory of the current working directory
* Tasks **MUST** be stored in a single file: `<cwd>/pjpd/tasks.txt`
* Ideas **MUST** be stored in: `<cwd>/pjpd/ideas.txt`
* Epics **MUST** be stored in: `<cwd>/pjpd/epics.txt`
* Each file **MUST** use UTF-8 encoding
* The `pjpd` directory and `tasks.txt` file **MAY** be created automatically when adding the first task

### Legacy Project File Warning

* If a file named `pjpd/<directory-name>.txt` exists (where `<directory-name>` is the last component of the current working directory), the system **MUST** include a `warning` property in task tool responses alerting the user to its presence
* This supports migration from the previous multi-project layout

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

* Tasks **MUST** be identified by their tag-based ID (format: `<tag>-XXXX`)
* Task IDs **MUST** be generated automatically when creating new tasks using the provided tag
* Task updates **MUST** preserve the original file structure and separator format
* Completed tasks **MAY** be filtered out of normal listings but **MUST** remain in the file
* Task descriptions **MAY** span multiple lines but **MUST NOT** contain the `---` separator

### Idea Operations

* Ideas **MUST** be identified by their unique tag-based ID (format: `<tag>-XXXX`) within `pjpd/ideas.txt`.
* Idea IDs **MUST** be generated automatically when creating new ideas using the provided tag.
* Idea updates **MUST** preserve the original file structure and separator format while sorted for score.

---

## API

### MCP Interface

* The system **MUST** present an MCP tools interface
* Use MCP SDK "fastmcp>=0.1.0"
* Server **MUST** support stdio transport by default

### Response Format

* All tools **MUST** return `{"success": bool, "result": ..., "error": "..."}`
* All successful results **MUST** include a `project_file` property with the full path to the data file being operated on
* Task tool results **MAY** include a `warning` property when a legacy project file is detected

#### Required Prompts

* `intro` – Return introductory description of the ProjectMCP system:
    * No parameters required

#### Required Tools

* `list_tasks` – List tasks with optional filtering (only ToDo tasks by default):
    * `priority` (integer, optional): Filter by priority level (returns all tasks >= this priority)
    * `count` (integer, optional): Maximum number of tasks to return (default: 20)
    * `show_done` (boolean, optional): Include completed tasks (default: false)
* `add_task` – Create a new task:
    * `description` (string, required): Task description
    * `tag` (string, required): Tag string (1-12 characters, alphanumeric and hyphens only)
    * `priority` (integer, optional): Priority level (higher numbers = higher priority, defaults to 2)
* `update_task` – Update an existing task:
    * `task_id` (string, required): Tag-based task ID (format: `<tag>-XXXX`)
    * `description` (string, optional): New task description
    * `priority` (integer, optional): New priority level
    * `status` (string, optional): New status ("ToDo" or "Done")
* `mark_done` – Mark a task as completed:
    * `task_id` (string, required): Tag-based task ID (format: `<tag>-XXXX`)
* `get_statistics` – Get comprehensive statistics about the project:
    * No parameters required
* `list_ideas` – List ideas:
    * `max_results` (integer, optional): Maximum number of results to return
* `add_idea` – Create a new idea in pjpd/ideas.txt:
    * `score` (integer, required): Score value (higher numbers = higher relevance)
    * `description` (string, required): Idea description
    * `tag` (string, required): Tag string (1-12 characters, alphanumeric and hyphens only)
* `update_idea` – Update an existing idea:
    * `idea_id` (string, required): Tag-based idea ID (format: `<tag>-XXXX`)
    * `score` (integer, optional): New score value
    * `description` (string, optional): New idea description
* `mark_idea_done` – Mark an idea as done (score to 0, prefix description with "(Done)"):
    * `idea_id` (string, required): Tag-based idea ID (format: `<tag>-XXXX`)
* `list_epics` – List epics:
    * `max_results` (integer, optional): Maximum number of results to return
* `add_epic` – Create a new epic in epics.txt:
    * `score` (integer, required): Score value (higher numbers = higher relevance)
    * `description` (string, required): Epic description
    * `tag` (string, required): Tag string (1-12 characters, alphanumeric and hyphens only)
    * `ideas` (string, optional): Space-delimited list of idea IDs
    * `projects` (string, optional): Space-delimited list of project names
* `update_epic` – Update an existing epic:
    * `epic_id` (string, required): Tag-based epic ID (format: `<tag>-XXXX`)
    * `score` (integer, optional): New score value
    * `description` (string, optional): New epic description
    * `ideas` (string, optional): Space-delimited list of idea IDs
    * `projects` (string, optional): Space-delimited list of project names
* `mark_epic_done` – Mark an epic as done (sets score to 0):
    * `epic_id` (string, required): Tag-based epic ID (format: `<tag>-XXXX`)

---

## Querying and Reporting

### Overview Generation

* System **MUST** provide project summaries including:
    * Total tasks
    * Count of tasks by priority level
    * Count of completed vs. pending tasks

---

## Error Handling

* Missing files **MUST** be handled gracefully (empty project)
* Malformed task or idea records **MUST** be logged and skipped
* Invalid task or idea IDs **MUST** return clear error messages

---

## Startup Behavior

* The system **MUST NOT** index tasks at startup (let the user initiate via tool calls)
* The `pjpd` directory **MUST** be created automatically when adding the first task
* Startup **MUST** complete successfully even if data files contain malformed records
* All logging output **MUST** be directed to stderr

---

## Performance Requirements

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

---

## Integration with TextRecords

* **MUST** use the existing `text_records.py` utility for file parsing
* **MUST** extend TextRecords parsing to handle Task, Idea, and Epic formats
* **MUST** maintain compatibility with the existing record separator (`---`)

---

## Out of Scope

* No due dates or time tracking in the initial version
* No task dependencies or hierarchical organization
* No user authentication or multi-user support
* No web interface or REST API
* No persistent caching or database storage
* No file watching or real-time updates

---

## Status

> This spec is a working draft. Contributions and revisions welcome.
