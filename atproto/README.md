# Atproto MCP Wrapper

An MCP (Model Context Protocol) server that provides tools for interacting with the Bluesky social network via the atproto protocol.

### Example Claude Desktop Configuration

**Location:** `%APPDATA%\Claude\claude_desktop_config.json`

```json
{
  "mcpServers": {
    "atproto-wrapper": {
      "command": "C:/work/mcp-wrappers/hello-world/.venv/Scripts/python.exe",
      "args": ["C:/work/mcp-wrappers/hello-world/atproto-wrapper.py"]
    }
  }
}
```

## Features

- **Bluesky Posting**: Post messages to your Bluesky account using the official atproto Python SDK
- **MCP Integration**: Works with any MCP-compatible client
- **Simple Interface**: Easy-to-use tools for social media interaction
- **Secure Credential Storage**: Credentials are stored securely with proper permissions
- **Real-time Authentication**: Authenticates with Bluesky servers for each posting session

## Installation

1. Create and activate a virtual environment using uv:
```bash
uv venv
uv sync
```

2. Activate the virtual environment:
```bash
# On Windows
.venv\Scripts\activate

# On macOS/Linux
source .venv/bin/activate
```

3. Install the dependencies:
```bash
pip install -e .
```

4. Set up your Bluesky credentials (see Configuration section below)

## Atproto Client Docs

https://atproto.blue/en/latest/

### Bluesky Credentials

The server stores your Bluesky credentials securely in a JSON file located at:
- Windows: `%APPDATA%\atproto\credentials.json`
- Unix-like systems: `~/.atproto/credentials.json`

#### Setting Up Credentials

You can set your credentials using the command line:

```bash
python atproto-wrapper.py -u your.bluesky.username your_password
```

This will create the credentials directory and save your credentials securely to the appropriate location for your operating system.

#### Credentials File Format

The credentials file is automatically created with the following JSON structure:

```json
{
  "username": "your.bluesky.username",
  "password": "your_bluesky_password"
}
```


**Note:** Replace the example values with your actual Bluesky username and password. The username should be in the format `handle.bsky.social` or your custom domain.

**⚠️ Security Warning:** The JSON file will contain your actual password in plain text. Ensure the file has proper permissions (600) and never share this file or its contents with anyone.

#### Security Features

- **Location**: Credentials are stored in the appropriate system location:
  - Windows: `%APPDATA%\atproto\credentials.json`
  - Unix-like systems: `~/.atproto/credentials.json`
- **Permissions**: File is set to owner-only access (600 permissions on Unix-like systems)
- **Auto-loading**: Credentials are automatically loaded when the server starts
- **Validation**: The server validates that both username and password fields exist

#### Loading Saved Credentials

Credentials are automatically loaded when the MCP server starts. If you need to update your credentials, simply run the setup command again:

```bash
python atproto-wrapper.py -u your.bluesky.username your_new_password
```


## Usage

Run the MCP server:

```bash
python atproto-wrapper.py
```

The server provides the following tool:

### `post_to_bluesky(message: str)`

Posts a message to your Bluesky account using the official atproto client.

**Parameters:**
- `message` (str): The text to post (max 300 characters)

**Returns:**
- Success response with post details including URI, CID, and timestamp
- Error response if posting fails

**Example Response:**
```json
{
  "success": true,
  "result": {
    "posted": true,
    "message": "Hello, Bluesky!",
    "username": "alice.bsky.social",
    "timestamp": "2024-01-01T12:00:00.000Z",
    "uri": "at://did:plc:example/app.bsky.feed.post/1234567890",
    "cid": "bafyrei..."
  },
  "error": ""
}
```

**Note:** You must set up credentials using the command line before posting.

## Implementation Details

This MCP server uses the official atproto Python SDK to:

1. **Authenticate** with Bluesky servers using stored credentials with proper session management
2. **Create posts** using the proper atproto data models
3. **Handle errors** gracefully with detailed error messages and automatic session recovery
4. **Validate messages** for length and content requirements
5. **Return real post data** including URIs and CIDs for tracking
6. **Session persistence** - maintains authenticated sessions across operations
7. **Automatic re-authentication** - handles expired sessions by re-authenticating automatically

The server maintains a persistent client session and intelligently re-authenticates when sessions expire or become invalid.

## Dependencies

- `fastmcp`: MCP server framework
- `atproto`: Official Python client for the atproto protocol (>=0.0.50)

## License

[Add your license here] 