# CLAUDE.md Integration Specification

## Purpose

Docmem manages hierarchical memory trees in an in-memory database. The CLAUDE.md integration allows an LLM to dynamically inject docmem content into its own system prompt by writing expanded tree representations into the CLAUDE.md file in the current working directory. A single MCP tool, `docmem_view`, gives the model direct control over which nodes are active in its prompt context.

The key insight: CLAUDE.md is loaded into the system prompt on every turn. By writing docmem expansions there, the model gains real-time, persistent control over its own context without requiring external orchestration.

## Functional Requirements

### CLAUDE.md File Resolution

- The tool MUST operate on the CLAUDE.md file in the current working directory.
- If no CLAUDE.md file exists in the current working directory, the tool MUST return successfully with no side effects (no-op).

### DOCMEM Dynamic Section

- All docmem content MUST appear under a `# DOCMEM Dynamic` markdown header in CLAUDE.md.
- The `# DOCMEM Dynamic` section MUST be the last top-level section in CLAUDE.md.
- The section MUST NOT be created until the first `docmem_view` add call.
- The section MUST be removed entirely (header and all content) when the last viewed node is removed.
- Existing CLAUDE.md content above the `# DOCMEM Dynamic` header MUST NOT be modified by the tool.

### Startup Behavior

- On server startup, the MCP server MUST remove any existing `# DOCMEM Dynamic` section and all content below it from CLAUDE.md.
- This ensures a clean slate: the in-memory active list and the file are always consistent.
- If no CLAUDE.md file exists in the current working directory, startup MUST proceed without error.

### docmem_view Tool

- The tool MUST accept two parameters: an action (`add` or `remove`) and a node ID.
- The node ID MAY be any node in the docmem database, not only root nodes. The expansion starts from whatever node is specified.

#### Add Action

- The tool MUST validate that the given node ID exists in the docmem database.
- The tool MUST expand the subtree rooted at the given node using the expand-to-length algorithm with a fixed token budget of 10000.
- The tool MUST maintain an ordered list of active node IDs.
- When a node is added that is not already in the active list, it MUST be appended to the end of the list.
- When a node is added that is already in the active list, its entry MUST be moved to the end of the list (most recently touched last, for KV cache efficiency).
- After updating the active list, the tool MUST rewrite the entire `# DOCMEM Dynamic` section with the expanded representations of all active nodes, ordered by the active list.
- Each node expansion MUST be preceded by a `## <node_id>` markdown subheader.

#### Remove Action

- The tool MUST remove the given node ID from the active list.
- If the active list becomes empty, the tool MUST remove the `# DOCMEM Dynamic` section and header from CLAUDE.md entirely.
- If active nodes remain, the tool MUST rewrite the `# DOCMEM Dynamic` section with the remaining nodes in their current list order.
- Removing a node ID that is not in the active list MUST succeed as a no-op.

### Expanded Representation

- Each node MUST be rendered using the existing expand-to-length output format: blocks separated by double newlines, each block containing the node metadata line followed by content.
- The expand-to-length algorithm (reverse-BFS priority, budget consumption, DFS render) MUST be used as specified in the main docmem specification.

### Active List State

- The active list of node IDs MUST be maintained in memory by the MCP server process.
- The active list MUST survive across tool calls within the same server session.
- The active list MUST NOT require persistence beyond the server process lifetime.

## Error Handling

- If the specified node ID does not exist in the docmem database, the add action MUST return an error with guidance to verify the node ID using the docmem query tools.
- If CLAUDE.md exists but cannot be read or written (permissions error), the tool MUST return an error describing the file access issue.
- If the `# DOCMEM Dynamic` section is malformed or cannot be located for rewrite, the tool MUST append a new section rather than corrupting existing content.

## Implementation Notes

- The CLAUDE.md file write MUST preserve all content before the `# DOCMEM Dynamic` header. The simplest approach is to find the header position, truncate at that point, and append the regenerated section.
- The active list ordering (most recently touched last) optimizes for KV cache hit rates, since the end of the prompt is the part most likely to change between turns.
- The fixed 10000 token budget per node bounds the total prompt impact. With multiple active nodes, the total injected content scales linearly.
- The startup cleanup ensures the server never inherits stale state from a previous session. This is simpler than parsing the file to reconstruct the active list, and avoids ambiguity about whether file state or memory state is authoritative.
