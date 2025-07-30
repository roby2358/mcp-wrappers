# MCP Wrappers

A collection of Model Context Protocol (MCP) server wrappers that provide controlled access to various system tools and services through the MCP protocol. These wrappers enable AI assistants like Claude to safely interact with your system while maintaining security boundaries.

## What is MCP?

The Model Context Protocol (MCP) is a standard for AI assistants to safely access external tools and data sources. It provides a secure way for AI models to interact with your system while maintaining proper access controls.

## Available Wrappers

### 1. Hello World (`hello-world/`)
A simple FastMCP application that provides an Echo tool for testing MCP integration.

**Features:**
- Simple Echo tool that returns any message sent to it
- Built-in intro prompt for model instruction
- Error handling for common issues
- Easy integration with Claude Desktop

**Use case:** Perfect for testing MCP setup and understanding how the protocol works.

### 2. Shell Wrappers (`shell/`)
Secure shell execution wrappers that provide controlled access to command-line tools.

- **CMD Shell** (`cmd_shell.py`) - Controlled Windows CMD shell with allowlisted commands
- **Bash Shell** (`bash_shell.py`) - Unix bash wrapper (work in progress)
- **Persistent CMD Shell** (`persistent_cmd_shell.py`) - Long-running CMD process
- **Background Reader** (`background_reader.py`) - Read background process output

**Features:**
- Secure execution of allowlisted commands
- Protection against command injection
- Persistent shell processes
- Clear command output separation
- Background process monitoring

**Use case:** Safe execution of system commands through Claude with security controls.

### 3. Atproto (`atproto/`)
An MCP server for interacting with the Bluesky social network via the atproto protocol.

**Features:**
- Post messages to Bluesky accounts
- Secure credential storage
- Real-time authentication with Bluesky servers
- Official atproto Python SDK integration

**Use case:** Social media automation and interaction through Claude.

### 4. VecBook (`vecbook/`)
A lightweight, local-first vector database for semantic search over plain text documents.

**Features:**
- Semantic search over multi-line text records
- Human-readable `.txt` file storage
- Vector embeddings using sentence-transformers
- Fast similarity search with configurable results
- HTTP server for web-based access
- Support for multiple document formats

**Use case:** Local document search and knowledge management through natural language queries.

### 5. ProjectMCP (`pjpd/`)
A lightweight, local-first project management system built on plain `.txt` files.

**Features:**
- Task management with priority-based organization
- Project organization with separate `.txt` files
- Simple, human-readable task format
- MCP tools for adding, listing, updating, and completing tasks
- Project overviews and next steps recommendations
- Ignore file support for flexible project management
- Atomic operations for data safety

**Use case:** Local project management and task tracking through AI assistants.

## Quick Start

Each wrapper has its own installation and setup instructions. See the individual README.md files in each wrapper directory:

- [`hello-world/README.md`](hello-world/README.md) - Simple echo tool
- [`shell/README.md`](shell/README.md) - Shell execution wrappers
- [`atproto/README.md`](atproto/README.md) - Bluesky social media integration
- [`vecbook/README.md`](vecbook/README.md) - Local vector document search
- [`pjpd/README.md`](pjpd/README.md) - Local project management

## Usage Examples

Each wrapper provides an "intro" prompt that informs the model about the available tools and how to use them. This is the starting point for working with the wrapper tools.

### Hello World
Once configured, first send the intro prompt to Claude.

Then you can ask Claude to echo messages:
- "Please echo 'Hello, MCP!'"
- "Can you echo back this message?"

### Shell Wrappers
Once configured, first send the intro prompt to Claude.

With the shell wrappers, you can safely execute commands:
- "List the files in the current directory"
- "Show me the content of README.md"
- "What's the current working directory?"

### Atproto
Once configured with your Bluesky credentials, you can:
- "Post 'Hello from Claude!' to my Bluesky account"
- "Share this update on Bluesky: [your message]"

### VecBook
Once configured with your document collection, you can:
- "Search for documents about machine learning"
- "Find records related to project planning"
- "What documents mention vector databases?"
- "Index this new document: [content]"

### ProjectMCP
Once configured, you can manage projects and tasks:
- "Create a new project called 'website-redesign'"
- "Add a high-priority task to fix the login bug"
- "List all tasks in the current project"
- "Mark task 'AB-CDEF-GH' as complete"
- "What are the next steps I should work on?"

## Development

### Project Structure
```
mcp-wrappers/
├── hello-world/          # Simple echo tool wrapper
├── shell/               # Shell execution wrappers
├── atproto/             # Bluesky/atproto social media wrapper
├── vecbook/             # Local vector document search
└── pjpd/                # Local project management system
```

### Adding New Wrappers

To add a new wrapper:

1. Create a new directory for your wrapper. Each directory has its own build process.
2. Use the FastMCP framework: `from mcp.server.fastmcp import FastMCP`
3. Follow the stdio pattern for MCP communication
4. Include proper error handling and security measures
5. Add a comprehensive README.md for your wrapper
6. Include unit tests in a `tests/` directory

### Common Patterns

All wrappers follow these common patterns:
- **FastMCP Integration**: Use `from mcp.server.fastmcp import FastMCP`
- **Stdio Transport**: Default to stdio for MCP communication
- **Error Handling**: Comprehensive try-catch blocks with meaningful error messages
- **Configuration**: TOML-based configuration files
- **Testing**: Unit tests with pytest
- **Documentation**: Clear README.md with usage examples

### Dependencies

All wrappers use:
- `fastmcp>=0.1.0` - The FastMCP framework for simplified MCP development
- `mcp>=1.9.1` - The MCP protocol implementation
- `uv` - For dependency management (recommended)

## Security Considerations

- **Shell Wrappers**: Use allowlists to prevent command injection
- **Atproto**: Secure credential storage and authentication
- **File Operations**: Atomic writes and proper error handling
- **Input Validation**: All user inputs are validated and sanitized

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Acknowledgments

- Built with [FastMCP](https://github.com/jlowin/fastmcp) for simplified MCP server development
- Uses the [Model Context Protocol](https://modelcontextprotocol.io/) standard
- Designed for integration with Claude Desktop and other MCP clients

## Support

For issues, questions, or contributions, please open an issue on the repository or submit a pull request.
