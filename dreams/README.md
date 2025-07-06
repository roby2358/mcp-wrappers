# Dreams MCP Server

This project provides a minimal TypeScript MCP (Model Context Protocol) server using the official `@modelcontextprotocol/sdk` that:

- Exposes a tool called `sayHello` that returns the string `Hello!` when invoked.
- Uses the standard MCP protocol for communication.

## Prerequisites

- [Node.js](https://nodejs.org/) (v18 or newer recommended)
- [npm](https://www.npmjs.com/) (comes with Node.js)

## Setup

1. **Install dependencies:**
   
   ```sh
   npm install
   ```

2. **Build the server:**
   
   ```sh
   npm run build
   ```
   This will produce the compiled JavaScript in the `dist/` directory.

3. **Run the server:**
   
   ```sh
   npm start
   ```
   
   Or for development:
   
   ```sh
   npm run dev
   ```

## Features

- **Tool**: `sayHello` - Returns "Hello!" when called
- **Transport**: Uses stdio for communication
- **Protocol**: Implements the official MCP specification

## Usage

The server implements the standard MCP protocol:

1. **Tool Listing**: Responds to `tools/list` requests with available tools
2. **Tool Execution**: Handles `tools/call` requests for the `sayHello` tool
3. **Error Handling**: Proper error responses for unknown tools

## Claude Desktop Configuration

To use this MCP server with Claude Desktop:

1. **Locate your Claude Desktop configuration file:**
   - **macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
   - **Windows**: `%APPDATA%\Claude\claude_desktop_config.json`

2. **Add the server configuration:**
   
   ```json
   {
     "mcpServers": {
       "dreams": {
         "command": "node",
         "args": ["C:/work/mcp-wrappers/dreams/dist/mcp-server.js"],
         "env": {}
       }
     }
   }
   ```

3. **Replace the path:**
   - Update the path in the `args` array with the actual absolute path to your compiled server file in the `dist/` directory

4. **Restart Claude Desktop** for the changes to take effect

5. **Verify the connection:**
   - The `sayHello` tool should now be available in your Claude Desktop conversations
   - You can test it by asking Claude to use the sayHello tool

**Note**: Make sure you have built the server (`npm run build`) before configuring Claude Desktop, as it needs the compiled JavaScript file in the `dist/` directory.

## Development

To modify the server:

1. Edit `src/mcp-server.ts`
2. Run `npm run build` to compile
3. Test with `npm start`

## License

MIT 