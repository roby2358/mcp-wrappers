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
import { Dreamscape } from './dreamscape.js';
import { logger, LogLevel } from './logger.js';

// Set log level from environment variable or default to INFO
const logLevel = (process.env.LOG_LEVEL as LogLevel) || LogLevel.INFO;
logger.setLevel(logLevel);

// Create the dreamscape instance
const dreamscape = new Dreamscape();

// Define input schemas
const AttemptNarrativeInputSchema = z.object({
  narrative_entry: z.string().describe('The narrative entry to add to the dream story'),
  alternate_entry: z.string().describe('An alternate narrative guided by the emotions of the dream'),
  opposite_entry: z.string().describe('The opposite of what was intended to happen'),
  recede_entry: z.string().describe('The entry receding and becoming harder to achieve')
});

const AttemptTransitionInputSchema = z.object({
  alternate_entry: z.string().describe('An alternate transition guided by the emotions of the dream'),
  opposite_entry: z.string().describe('The opposite of what was intended to happen during transition'),
  recede_entry: z.string().describe('The transition receding and becoming harder to achieve')
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
      },
      alternate_entry: {
        type: 'string',
        description: 'An alternate narrative guided by the emotions of the dream'
      },
      opposite_entry: {
        type: 'string',
        description: 'The opposite of what was intended to happen'
      },
      recede_entry: {
        type: 'string',
        description: 'The entry receding and becoming harder to achieve'
      }
    },
    required: ['narrative_entry', 'alternate_entry', 'opposite_entry', 'recede_entry'],
  },
};

const attemptTransitionTool: Tool = {
  name: 'attempt_transition',
  description: 'Resets the dreamscape with new randomized properties and scene while preserving the narrative history',
  inputSchema: {
    type: 'object',
    properties: {
      alternate_entry: {
        type: 'string',
        description: 'An alternate transition guided by the emotions of the dream'
      },
      opposite_entry: {
        type: 'string',
        description: 'The opposite of what was intended to happen during transition'
      },
      recede_entry: {
        type: 'string',
        description: 'The transition receding and becoming harder to achieve'
      }
    },
    required: ['alternate_entry', 'opposite_entry', 'recede_entry'],
  },
};

const submergeTool: Tool = {
  name: 'submerge',
  description: 'Starts a completely new dreamscape with fresh narrative, clearing all previous dream history',
  inputSchema: {
    type: 'object',
    properties: {},
    required: [],
  },
};

// Collect all tools in an array for easier management
const allTools = [dreamscapeTool, attemptNarrativeTool, attemptTransitionTool, submergeTool];

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
    tools: allTools,
  };
});

// Handle tool calls
server.setRequestHandler(CallToolRequestSchema, async (request: CallToolRequest) => {
  const { name, arguments: args } = request.params;
  
  logger.info('Tool call received', { tool_name: name, arguments: args });
  
  try {
    switch (name) {
      case 'submerge':
        const submergeResult = dreamscape.submerge();
        
        logger.info('Tool call completed successfully', { 
          tool_name: name,
          new_dreamscape: submergeResult.dreamscape,
          emotional_tone: submergeResult.emotional_tone
        });
        
        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify(submergeResult, null, 2),
            },
          ],
        };

      case 'dreamscape':
        const state = dreamscape.getState();
        logger.info('Dreamscape state retrieved', { 
          current_scene: state.dreamscape,
          emotional_tone: state.emotional_tone,
          narrative_length: state.narrative.length
        });
        
        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify(state, null, 2),
            },
          ],
        };
      
      case 'attempt_narrative':
        const narrativeInput = AttemptNarrativeInputSchema.parse(args || {});
        logger.debug('Parsing narrative input', { input: narrativeInput });
        
        const alteredNarrative = dreamscape.addNarrative(
          narrativeInput.narrative_entry,
          narrativeInput.alternate_entry,
          narrativeInput.opposite_entry,
          narrativeInput.recede_entry
        );
        
        logger.info('Tool call completed successfully', { 
          tool_name: name,
          result_length: alteredNarrative.length
        });
        
        return {
          content: [
            {
              type: 'text',
              text: alteredNarrative,
            },
          ],
        };
      

      case 'attempt_transition':
        const transitionInput = AttemptTransitionInputSchema.parse(args || {});
        logger.debug('Parsing transition input', { input: transitionInput });
        const transitionResult = dreamscape.transitionDreamscape(
          transitionInput.alternate_entry,
          transitionInput.opposite_entry,
          transitionInput.recede_entry
        );
        
        logger.info('Tool call completed successfully', { 
          tool_name: name,
          result: transitionResult
        });
        
        return {
          content: [
            {
              type: 'text',
              text: transitionResult,
            },
          ],
        };
      
      default:
        logger.error('Unknown tool requested', { tool_name: name });
        throw new Error(`Unknown tool: ${name}`);
    }
  } catch (error) {
    logger.error('Tool call failed', { 
      tool_name: name, 
      error: error instanceof Error ? error.message : String(error),
      stack: error instanceof Error ? error.stack : undefined
    });
    throw error;
  }
});

// Handle prompt listing
server.setRequestHandler(ListPromptsRequestSchema, async () => {
  logger.debug('Prompt list requested');
  
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
  logger.info('Prompt requested', { prompt_name: request.params.name });
  
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
  
  logger.error('Unknown prompt requested', { prompt_name: request.params.name });
  throw new Error(`Unknown prompt: ${request.params.name}`);
});

// Start the server with stdio transport
async function startServer() {
  try {
    logger.info('Starting Dreams MCP Server', { log_level: logLevel });
    
    const transport = new StdioServerTransport();
    await server.connect(transport);
    
    logger.info('Dreams MCP Server started successfully');
    logger.info('Dreamscape system initialized', { 
      available_tools: allTools.map(tool => tool.name),
      tool_count: allTools.length
    });
  } catch (error) {
    logger.error('Failed to start server', { 
      error: error instanceof Error ? error.message : String(error),
      stack: error instanceof Error ? error.stack : undefined
    });
    throw error;
  }
}

startServer().catch((error) => {
  logger.error('Server startup failed', { 
    error: error instanceof Error ? error.message : String(error),
    stack: error instanceof Error ? error.stack : undefined
  });
  process.exit(1);
}); 