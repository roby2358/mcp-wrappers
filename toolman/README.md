# Toolman — MCP Gateway Server

Toolman is an MCP server that aggregates multiple upstream MCP servers behind a single connection. It namespaces their tools, resources, and prompts, and lets the model dynamically activate and deactivate them so only the relevant ones are visible at any time.

## Why

MCP clients like Claude Desktop and Claude Code connect to multiple MCP servers. Each server exposes its own tools and resources, and all of them land in the model's context window at once. With a handful of servers this adds up fast — the model sees dozens of tool definitions it doesn't need for the current task.

Toolman solves this by sitting between the model and the upstream servers. It caches everything at startup, starts with only a configured subset active, and exposes a single `toolman_activate` tool whose description contains a live catalog. The model reads the catalog, activates what it needs, and the rest stays out of the way.

## How It Works

1. Toolman reads `tools.toml` from the working directory to discover upstream servers
2. It spawns each server as a subprocess and connects via stdio
3. It queries every server for tools, resources, and prompts, caches the results, and applies namespace prefixes
4. It evaluates `active_toolsets` wildcard patterns to decide which items start active
5. The model sees `toolman_activate` (with the full catalog in its description) plus the currently active tools
6. The model calls `toolman_activate` to turn tools and resources on or off as needed
7. When the model calls an active tool, toolman strips the namespace and forwards the request to the upstream server

## Installation

Requires Node.js 18+.

```bash
cd toolman
npm install
npm run build
```

## Configuration

Create a `tools.toml` file in the directory where toolman will run. This file lists the upstream servers and the initial activation patterns.

```toml
active_toolsets = ["pjpd*", "vec_search"]

[[servers]]
namespace = "pjpd"
command = "node /path/to/pjpd/build/index.js"

[[servers]]
namespace = "vec"
command = "node /path/to/vecbook/build/index.js"

[[servers]]
namespace = ""
command = "node /path/to/standalone-tool/index.js"
```

### Fields

**`active_toolsets`** — A list of glob patterns matched against the full namespaced name (namespace + `_` + original name). Matching tools and resources start active. Non-matching ones start inactive. Prompts are always active.

**`[[servers]]`** — Each entry defines an upstream MCP server:
- **`namespace`** — Prefix prepended to all names from this server, separated by `_`. Use an empty string to pass names through as-is.
- **`command`** — Shell command to spawn the server subprocess. Stdio transport only.

### Namespacing Examples

With namespace `pjpd`:
- Tool `list_projects` becomes `pjpd_list_projects`
- Resource `projects://all` becomes `pjpd_projects://all`
- Prompt `summarize` becomes `pjpd_summarize`

### Name Collisions

If two servers produce the same namespaced name, the first one listed in `tools.toml` wins. The duplicate is discarded.

## The Activation Catalog

The `toolman_activate` tool description contains a live catalog of all available tools and resources. It looks like this:

```
TOOLS:
* pjpd_list_projects: List all projects in the workspace
* pjpd_get_task: Get a task by ID
  pjpd_create_task: Create a new task in a project
  vec_search: Search documents by semantic similarity

RESOURCES:
* pjpd_projects://all: All project summaries
  vec_data://stats: Index statistics
```

Items marked with `*` are currently active. The model sees the catalog every time it lists tools, so it always knows what's available without an extra call.

Each description is truncated to 132 characters.

## Running

Toolman reads `tools.toml` from the current working directory, so run it from the directory containing your config:

```bash
# Development
cd /path/to/project
npx tsx /path/to/toolman/src/index.ts

# Production
cd /path/to/project
node /path/to/toolman/build/index.js
```

## Claude Code Configuration

Add toolman to your Claude Code MCP settings (`~/.claude/settings.json` or project-level `.claude/settings.json`):

```json
{
  "mcpServers": {
    "toolman": {
      "command": "node",
      "args": ["/path/to/toolman/build/index.js"],
      "cwd": "/path/to/project"
    }
  }
}
```

The `cwd` field is important — it determines where toolman looks for `tools.toml`.

### Example: Aggregating Project Tools

Suppose you have `pjpd` (project management) and `vecbook` (document search) and want both available through a single connection. Create `tools.toml` in your project directory:

```toml
active_toolsets = ["pjpd_list*", "pjpd_get*"]

[[servers]]
namespace = "pjpd"
command = "node /home/user/mcp-wrappers/pjpd/build/index.js"

[[servers]]
namespace = "vec"
command = "node /home/user/mcp-wrappers/vecbook/build/index.js"
```

Then point Claude Code at toolman with that project directory as `cwd`. The model starts with only the `pjpd_list*` and `pjpd_get*` tools active, and can activate vecbook tools on demand via `toolman_activate`.

## Claude Desktop Configuration

Add to `claude_desktop_config.json`:

**Windows**: `%APPDATA%\Claude\claude_desktop_config.json`
**macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
**Linux**: `~/.config/Claude/claude_desktop_config.json`

```json
{
  "mcpServers": {
    "toolman": {
      "command": "node",
      "args": ["C:/work/mcp-wrappers/toolman/build/index.js"],
      "cwd": "C:/work/my-project"
    }
  }
}
```

## Error Handling

Toolman's own errors (inactive tool, unknown name, empty activation) return a JSON object with `success`, `result`, and `error` fields. The error messages are written as actionable prompts that tell the model how to fix the problem.

Errors from upstream servers are relayed directly without wrapping.

If an upstream server crashes, toolman removes all of its tools, resources, and prompts from the catalog. The model sees them disappear on the next `listTools` call.

## Project Structure

```
toolman/
├── src/
│   ├── index.ts       # MCP server entry point and request handlers
│   ├── config.ts      # tools.toml loading
│   └── gateway.ts     # Upstream connection management, caching, activation
├── package.json
├── tsconfig.json
├── tools.toml         # Per-project configuration (not checked in)
├── SPEC.md            # Technical specification
└── README.md
```

## Dependencies

- `@modelcontextprotocol/sdk` — MCP protocol and transport
- `smol-toml` — TOML parser

## Related

- [SPEC.md](SPEC.md) — Full technical specification
- [Model Context Protocol](https://modelcontextprotocol.io/) — MCP documentation
