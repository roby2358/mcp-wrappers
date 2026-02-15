// Minimal MCP server for testing toolman
import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  ListResourcesRequestSchema,
  ReadResourceRequestSchema,
  ListPromptsRequestSchema,
  GetPromptRequestSchema,
} from "@modelcontextprotocol/sdk/types.js";

const server = new Server(
  { name: "test-server", version: "0.1.0" },
  { capabilities: { tools: {}, resources: {}, prompts: {} } },
);

server.setRequestHandler(ListToolsRequestSchema, async () => ({
  tools: [
    {
      name: "echo",
      description: "Echo back a message",
      inputSchema: {
        type: "object",
        properties: { message: { type: "string" } },
        required: ["message"],
      },
    },
    {
      name: "add",
      description: "Add two numbers",
      inputSchema: {
        type: "object",
        properties: {
          a: { type: "number" },
          b: { type: "number" },
        },
        required: ["a", "b"],
      },
    },
  ],
}));

server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;
  if (name === "echo") {
    return { content: [{ type: "text", text: `Echo: ${args.message}` }] };
  }
  if (name === "add") {
    return { content: [{ type: "text", text: String(args.a + args.b) }] };
  }
  throw new Error(`Unknown tool: ${name}`);
});

server.setRequestHandler(ListResourcesRequestSchema, async () => ({
  resources: [
    {
      uri: "info://version",
      name: "Version Info",
      description: "Server version information",
      mimeType: "text/plain",
    },
  ],
}));

server.setRequestHandler(ReadResourceRequestSchema, async (request) => ({
  contents: [
    {
      uri: String(request.params.uri),
      mimeType: "text/plain",
      text: "test-server v0.1.0",
    },
  ],
}));

server.setRequestHandler(ListPromptsRequestSchema, async () => ({
  prompts: [
    {
      name: "greet",
      description: "Generate a greeting",
      arguments: [{ name: "name", description: "Name to greet", required: true }],
    },
  ],
}));

server.setRequestHandler(GetPromptRequestSchema, async (request) => ({
  messages: [
    {
      role: "user",
      content: {
        type: "text",
        text: `Please greet ${request.params.arguments?.name ?? "world"}`,
      },
    },
  ],
}));

const transport = new StdioServerTransport();
await server.connect(transport);
