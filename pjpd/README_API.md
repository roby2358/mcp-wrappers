# ProjectMCP API Reference

This document provides the complete API reference for ProjectMCP's MCP tools and prompts.

## API Response Format

All tools return a consistent response structure:

```json
{
  "success": true,
  "result": { ... },
  "error": ""
}
```

Every successful result includes a `project_file` property with the full path to the data file being operated on. Task tool results may also include a `warning` property if a legacy project file is detected (see [Legacy Warning](#legacy-project-file-warning)).

> **Note**: Tag fields are used internally for ID generation but are not included in API responses. When creating new tasks or ideas, you must provide a tag, but the tag will not be returned in response data.

## MCP Tools

### Task Management

#### `add_task`
Create a new task.

**Parameters:**
- `description` (string, required): Task description
- `tag` (string, required): Tag string (1-12 characters, alphanumeric and hyphens only)
- `priority` (integer, optional): Priority level (higher numbers = higher priority, defaults to 2)

#### `list_tasks`
List tasks with optional filtering. By default only ToDo tasks are returned.

**Parameters:**
- `priority` (integer, optional): Filter by priority level (returns all tasks >= this priority)
- `count` (integer, optional): Maximum number of tasks to return (default: 20)
- `show_done` (boolean, optional): Include completed tasks (default: false)

#### `update_task`
Update an existing task.

**Parameters:**
- `task_id` (string, required): Tag-based task ID (format: `<tag>-XXXX`)
- `description` (string, optional): New task description
- `priority` (integer, optional): New priority level
- `status` (string, optional): New status ("ToDo" or "Done")

#### `mark_done`
Mark a task as completed.

**Parameters:**
- `task_id` (string, required): Tag-based task ID (format: `<tag>-XXXX`)

#### `get_statistics`
Get comprehensive statistics about the project.

**Parameters:** None

### Idea Management

#### `list_ideas`
List ideas with optional filtering.

**Parameters:**
- `max_results` (integer, optional): Maximum number of results to return

#### `add_idea`
Create a new idea in ideas.txt.

**Parameters:**
- `score` (integer, required): Score value (higher numbers = higher relevance)
- `description` (string, required): Idea description
- `tag` (string, required): Tag string (1-12 characters, alphanumeric and hyphens only)

#### `update_idea`
Update an existing idea.

**Parameters:**
- `idea_id` (string, required): Tag-based idea ID (format: `<tag>-XXXX`)
- `score` (integer, optional): New score value
- `description` (string, optional): New idea description

#### `mark_idea_done`
Mark an idea as done (sets score to 0, prefixes description with "(Done)").

**Parameters:**
- `idea_id` (string, required): Tag-based idea ID (format: `<tag>-XXXX`)

## MCP Prompts

### `intro`
Return introductory description of the ProjectMCP system.

**Parameters:** None

## Legacy Project File Warning

If pjpd detects a file at `pjpd/<directory-name>.txt` (from the old multi-project format where each project was a separate `.txt` file), task tool responses will include:

```json
{
  "warning": "Existing project file <filename>.txt exists"
}
```

This helps identify directories that were previously used with the multi-project layout.
