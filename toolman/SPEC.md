# Toolman — MCP Gateway Server

## Purpose

Toolman is an MCP server that acts as a gateway to multiple upstream MCP servers. It aggregates tools, resources, and prompts from upstream servers and presents them to the downstream model through a single MCP connection. The model can dynamically activate and deactivate tools and resources, keeping the visible surface small and relevant to the current task.

## Configuration

### Server Registry

Toolman MUST read its configuration from a TOML file named `tools.toml` located in the current working directory. This makes configuration per-project rather than global.

The configuration MUST define:

- A list of upstream servers, each with:
  - **namespace**: A prefix string prepended (with `_` separator) to all tool, resource, and prompt names from that server. MAY be empty, in which case upstream names are used as-is.
    - Tool example: namespace `pjpd` + tool `list_projects` produces `pjpd_list_projects`
    - Resource example: namespace `pjpd` + resource `projects://list` produces `pjpd_projects://list`
    - Prompt example: namespace `pjpd` + prompt `summarize` produces `pjpd_summarize`
  - **command**: A single shell string to spawn the server subprocess. Stdio transport only in v1.
- An **active_toolsets** list of wildcard patterns matched against the concatenation of namespace and name. This determines which tools and resources are active at startup.
  - Tools and resources MUST be matched independently against these patterns.
  - Prompts are not affected — they are always active.

### Name Collisions

- If two servers produce the same namespaced name, the first server listed in the configuration MUST win. The duplicate MUST be discarded.

## Startup

- Toolman MUST spawn all configured servers and connect via stdio at startup.
- Toolman MUST query each server for its tools, resources, and prompts, and cache the results.
- Toolman MUST apply namespace prefixes to all cached names.
- Toolman MUST evaluate the active_toolsets wildcard patterns and mark matching tools and resources as active. Non-matching items MUST start as inactive.

## Functional Requirements

### Activation Tool

- Toolman MUST register exactly one tool with the MCP framework: `toolman_activate`.
- `toolman_activate` MUST accept four required parameters:
  - `tools_on`: list of strings — tool names to activate
  - `tools_off`: list of strings — tool names to deactivate
  - `resources_on`: list of strings — resource names to activate
  - `resources_off`: list of strings — resource names to deactivate
- Items not mentioned in any list MUST retain their current state.
- If all four lists are empty, `toolman_activate` MUST return an error guiding the model to specify at least one name.
- Toolman MUST validate all names against the cache before applying changes. If any name is unknown, it MUST return an error listing the bad names and suggesting corrections. No partial application — all names MUST be valid or no changes are applied.
- On success, `toolman_activate` MUST return a short confirmation message.

### Dynamic Tool Description

- The description of `toolman_activate` MUST contain a live catalog of all available tools and resources showing their active/inactive state.
- The catalog MUST be regenerated whenever activation state changes.
- Each catalog entry MUST show the namespaced name and the upstream description truncated to 132 characters.
- Active items MUST be marked with a `*` prefix. Inactive items MUST have no prefix marker.

### Tool Proxying

- The tool list MUST return `toolman_activate` plus full descriptions (including schemas) of all active tools with namespaced names.
- When the model invokes an active tool, toolman MUST strip the namespace prefix and route the request to the upstream server, then relay the response directly.
- Invoking an inactive tool MUST return an error with guidance to activate it first.
- Invoking an unknown tool MUST return an error listing similar available names.
- Buffered I/O is acceptable for v1.

### Resource Proxying

- The resource list MUST return descriptions of all active resources (including resource templates) with namespaced URIs.
- When the model reads an active resource, toolman MUST strip the namespace prefix and route the request to the upstream server, then relay the result.
- Resource templates MUST be proxied the same way — toolman passes through the parameterized URI.
- Reading an inactive resource MUST return an error with guidance to activate it first.
- Resource subscriptions are not supported in v1.

### Prompt Proxying

- Prompts MUST always be active — no activation or deactivation.
- The prompt list MUST return the union of all cached upstream prompts with namespace prefixes applied.
- When the model invokes a prompt, toolman MUST strip the namespace prefix and route to the upstream server, then relay the response.

## Server Lifecycle

- All upstream server connections and caches MUST be maintained for the lifetime of toolman, regardless of activation state.
- If an upstream server process exits unexpectedly, toolman MUST remove its tools, resources, and prompts from both the active list and the cache. They MUST no longer appear in the activation catalog. The event SHOULD be logged.
- Toolman MUST NOT attempt to restart crashed servers in v1.
- On shutdown, toolman MUST close all client sessions, terminate all spawned server subprocesses, then exit.

## Error Handling

- Errors from upstream tool, resource, and prompt calls MUST be relayed directly to the model without wrapping.
- Toolman's own errors (inactive item, unknown item, connection failure, bad configuration) MUST follow the project convention of returning a success flag, result, and an actionable error message.

## Non-Functional Requirements

- Toolman SHOULD start up and be ready to accept requests within a reasonable time, bounded by upstream server startup.
- Toolman SHOULD handle upstream server crashes gracefully without itself crashing.

## Dependencies

- fastmcp >= 0.1.0 — MCP server framework
- mcp >= 1.9.1 — MCP protocol and client transport
- toml >= 0.10.0 — Configuration parsing
- pydantic >= 2.0.0 — Parameter validation

## Implementation Notes

- Namespace prefix stripping: when routing to an upstream server, the namespace and separator are removed from the beginning of the name to recover the original upstream name.
- Wildcard matching for active_toolsets uses glob-style patterns (e.g. `pjpd*`) against the full concatenated string of namespace + name.
- The MCP Python SDK provides interchangeable client transports — stdio, SSE, and streamable HTTP all share the same session interface. This will simplify adding network transports in the future.
- The activation catalog embedded in the tool description serves as a compressed index. The model always sees what is available without needing an extra round-trip to a resource or list call.

## Future Considerations (not in v1)

- SSE and streamable-http transport for upstream servers
- Streaming I/O proxying
- Server auto-restart on crash
- Activate/deactivate entire toolsets by server-level granularity
- Resource subscriptions
- List-changed notifications to the downstream client when activation state changes
