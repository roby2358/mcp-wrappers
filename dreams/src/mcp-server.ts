import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  ListPromptsRequestSchema,
  GetPromptRequestSchema,
  Tool,
  CallToolRequest,
  ListPromptsRequest,
  GetPromptRequest,
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
      prompts: {},
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

// Handle prompt listing
server.setRequestHandler(ListPromptsRequestSchema, async () => {
  console.error('ListPromptsRequestSchema handler called');
  return {
    prompts: [
      {
        name: 'intro',
        description: 'Introduction prompt for the Dreams MCP wrapper',
        arguments: [],
      },
    ],
  };
});

// Handle prompt requests
server.setRequestHandler(GetPromptRequestSchema, async (request: GetPromptRequest) => {
  console.error('GetPromptRequestSchema handler called for:', request.params.name);
  if (request.params.name === 'intro') {
    return {
      description: 'Introduction prompt for the Dreams MCP wrapper',
      messages: [
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: 'MCP wrapper for dreams',
          },
        },
      ],
    };
  }
  
  throw new Error(`Unknown prompt: ${request.params.name}`);
});

// Start the server with stdio transport
async function startServer() {
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error('Dreams MCP Server started');
  console.error('Server has tools and prompts capabilities enabled');
}

startServer().catch(console.error); 