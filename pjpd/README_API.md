# ProjectMCP API Reference

This document provides the complete API reference for ProjectMCP's MCP tools and prompts.

## MCP Tools

### Project Management

#### `list_projects`
Return list of all projects with task counts.

**Parameters:**
- `path` (string, optional): Path to projects directory (default: ~/projects)

#### `new_project`
Create a new empty project file.

**Parameters:**
- `project` (string, required): Project name

### Task Management

#### `add_task`
Create a new task with parameters.

**Parameters:**
- `project` (string, required): Project name
- `description` (string, required): Task description
- `tag` (string, required): Tag string (1-12 characters, alphanumeric and hyphens only)
- `priority` (integer, optional): Priority level (higher numbers = higher priority, defaults to 2)

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
- `task_id` (string, required): Tag-based task ID (format: `<tag>-XXXX`)
- `description` (string, optional): New task description
- `priority` (integer, optional): New priority level
- `status` (string, optional): New status ("ToDo" or "Done")

#### `mark_done`
Mark a task as completed.

**Parameters:**
- `project` (string, required): The name of the project containing the task
- `task_id` (string, required): Tag-based task ID (format: `<tag>-XXXX`)

#### `next_steps`
Determine high-priority tasks to work on next.

**Parameters:**
- `max_results` (integer, optional): Maximum number of suggestions to return (default: 5)

#### `get_statistics`
Get comprehensive statistics about all projects.

**Parameters:** None

### Idea Management

#### `list_ideas`
List ideas with optional filtering.

**Parameters:**
- `max_results` (integer, optional): Maximum number of results to return

#### `add_idea`
Create a new idea in ideas.txt with parameters.

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

#### `remove_idea`
Remove an idea completely.

**Parameters:**
- `idea_id` (string, required): Tag-based idea ID (format: `<tag>-XXXX`)

### Epic Management

#### `list_epics`
List epics with optional filtering.

**Parameters:**
- `max_results` (integer, optional): Maximum number of results to return

#### `add_epic`
Create a new epic in epics.txt with parameters.

**Parameters:**
- `score` (integer, required): Score value (higher numbers = higher relevance)
- `description` (string, required): Epic description
- `tag` (string, required): Tag string (1-12 characters, alphanumeric and hyphens only)
- `ideas` (string, optional): Space-delimited list of idea IDs
- `projects` (string, optional): Space-delimited list of project names

#### `update_epic`
Update an existing epic.

**Parameters:**
- `epic_id` (string, required): Tag-based epic ID (format: `<tag>-XXXX`)
- `score` (integer, optional): New score value
- `description` (string, optional): New epic description
- `ideas` (string, optional): Space-delimited list of idea IDs
- `projects` (string, optional): Space-delimited list of project names

#### `mark_epic_done`
Mark an epic as done (sets score to 0).

**Parameters:**
- `epic_id` (string, required): Tag-based epic ID (format: `<tag>-XXXX`)

## MCP Prompts

### `intro`
Return introductory description of the ProjectMCP system.

**Parameters:** None 