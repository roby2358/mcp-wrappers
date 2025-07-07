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
import { INTRO_TEXT } from './intro-text.js';
import {
  getDreamscapeState,
  addNarrative,
  shiftProperty,
  transitionDreamscape
} from './dreamscape.js';

// Define input schemas
const AttemptNarrativeInputSchema = z.object({
  narrative_entry: z.string().describe('The narrative entry to add to the dream story')
});

const AttemptPropertyShiftInputSchema = z.object({
  property: z.string().describe('The property to adjust (must be one of the 9 core properties)'),
  direction: z.enum(['increase', 'decrease']).describe('Whether to increase or decrease the property'),
  reason: z.string().describe('The reason for the property change')
});

// Define tools
const dreamscapeTool: Tool = {
  name: 'dreamscape',
  description: 'Returns the current full dreamscape state including all properties, scene, and narrative',
  inputSchema: {
    type: 'object',
    properties: {},
    required: [],
  },
};

const attemptNarrativeTool: Tool = {
  name: 'attempt_narrative',
  description: 'Adds a new entry to the dream narrative (may be altered by dream logic)',
  inputSchema: {
    type: 'object',
    properties: {
      narrative_entry: {
        type: 'string',
        description: 'The narrative entry to add to the dream story'
      }
    },
    required: ['narrative_entry'],
  },
};

const attemptPropertyShiftTool: Tool = {
  name: 'attempt_property_shift',
  description: 'Attempts to adjust one of the core dreamscape properties',
  inputSchema: {
    type: 'object',
    properties: {
      property: {
        type: 'string',
        description: 'The property to adjust (emotional_tone, familiarity_ratio, symbolic_density, sensory_cross_bleeding, coherence_level, boundary_stability, causality_strength, memory_persistence, agency_level)'
      },
      direction: {
        type: 'string',
        enum: ['increase', 'decrease'],
        description: 'Whether to increase or decrease the property'
      },
      reason: {
        type: 'string',
        description: 'The reason for the property change'
      }
    },
    required: ['property', 'direction', 'reason'],
  },
};

const attemptTransitionTool: Tool = {
  name: 'attempt_transition',
  description: 'Resets the dreamscape with new randomized properties and scene while preserving the narrative history',
  inputSchema: {
    type: 'object',
    properties: {},
    required: [],
  },
};

// Create the MCP server
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
    tools: [dreamscapeTool, attemptNarrativeTool, attemptPropertyShiftTool, attemptTransitionTool],
  };
});

// Handle tool calls
server.setRequestHandler(CallToolRequestSchema, async (request: CallToolRequest) => {
  const { name, arguments: args } = request.params;
  
  switch (name) {
    case 'dreamscape':
      return {
        content: [
          {
            type: 'text',
            text: JSON.stringify(getDreamscapeState(), null, 2),
          },
        ],
      };
    
    case 'attempt_narrative':
      const narrativeInput = AttemptNarrativeInputSchema.parse(args || {});
      const alteredNarrative = addNarrative(narrativeInput.narrative_entry);
      
      return {
        content: [
          {
            type: 'text',
            text: alteredNarrative,
          },
        ],
      };
    
    case 'attempt_property_shift':
      const propertyInput = AttemptPropertyShiftInputSchema.parse(args || {});
      const result = shiftProperty(propertyInput.property, propertyInput.direction, propertyInput.reason);
      
      return {
        content: [
          {
            type: 'text',
            text: result,
          },
        ],
      };
    
    case 'attempt_transition':
      const transitionResult = transitionDreamscape();
      
      return {
        content: [
          {
            type: 'text',
            text: transitionResult,
          },
        ],
      };
    
    default:
      throw new Error(`Unknown tool: ${name}`);
  }
});

// Handle prompt listing
server.setRequestHandler(ListPromptsRequestSchema, async () => {
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
  if (request.params.name === 'intro') {
    return {
      description: 'Introduction prompt for the Dreams MCP wrapper',
      messages: [
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: INTRO_TEXT,
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
  console.error('Dreamscape system initialized with 4 tools: dreamscape, attempt_narrative, attempt_property_shift, attempt_transition');
}

startServer().catch(console.error); 