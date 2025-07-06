import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  Tool,
  CallToolRequest,
} from '@modelcontextprotocol/sdk/types.js';
import { z } from 'zod';

// Define the input schema for the sayHello tool
const SayHelloInputSchema = z.object({
  name: z.string().optional().describe('Optional name to include in greeting')
});

// Define the hello tool with proper input schema
const helloTool: Tool = {
  name: 'sayHello',
  description: 'Returns a greeting message with optional name parameter',
  inputSchema: {
    type: 'object',
    properties: {
      name: {
        type: 'string',
        description: 'Optional name to include in greeting'
      }
    },
    required: [],
  },
};

// Create the MCP server with correct capabilities
const server = new Server(
  {
    name: 'dreams-mcp-server',
    version: '1.0.0',
    capabilities: {
      tools: {},
    },
  }
);

// Handle tool listing
server.setRequestHandler(ListToolsRequestSchema, async () => {
  return {
    tools: [helloTool],
  };
});

// Handle tool calls with proper input validation and response format
server.setRequestHandler(CallToolRequestSchema, async (request: CallToolRequest) => {
  if (request.params.name === 'sayHello') {
    // Validate input using Zod schema
    const input = SayHelloInputSchema.parse(request.params.arguments || {});
    
    // Generate greeting based on input
    const greeting = input.name ? `Hello, ${input.name}!` : 'Hello!';
    
    return {
      content: [
        {
          type: 'text',
          text: greeting,
        },
      ],
    };
  }
  
  throw new Error(`Unknown tool: ${request.params.name}`);
});

// Start the server with stdio transport
async function startServer() {
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error('Dreams MCP Server started');
}

startServer().catch(console.error); 