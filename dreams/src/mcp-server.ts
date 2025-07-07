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
import { DREAMSCAPES } from './dreamscapes.js';

// Dreamscape state interface
interface DreamscapeState {
  emotional_tone: string;
  dreamscape: string;
  narrative: string[];
  familiarity_ratio: number;
  symbolic_density: number;
  sensory_cross_bleeding: number;
  coherence_level: number;
  boundary_stability: number;
  causality_strength: number;
  memory_persistence: number;
  agency_level: number;
}

// Helper function to clamp values between 0-100
const clampValue = (value: number): number => Math.max(0, Math.min(100, value));

// Helper function to generate random number between 0-100
const randomPercent = (): number => Math.floor(Math.random() * 101);

// Helper function to generate random dreamscape descriptions
const generateRandomDreamscape = (): string => {
  return DREAMSCAPES[Math.floor(Math.random() * DREAMSCAPES.length)];
};

// Helper function to randomize all numeric properties
const randomizeProperties = () => {
  return {
    familiarity_ratio: randomPercent(),
    symbolic_density: randomPercent(),
    sensory_cross_bleeding: randomPercent(),
    coherence_level: randomPercent(),
    boundary_stability: randomPercent(),
    causality_strength: randomPercent(),
    memory_persistence: randomPercent(),
    agency_level: randomPercent()
  };
};

// Helper function to simulate dream logic alterations
const applyDreamLogic = (input: string, coherence: number, causality: number): string => {
  // Lower coherence and causality may alter the input
  const alterationChance = (100 - coherence) * (100 - causality) / 10000;
  
  if (Math.random() < alterationChance) {
    // Apply subtle dream-like alterations
    const alterations = [
      (text: string) => text.replace(/\b(I|me|my)\b/g, 'we'),
      (text: string) => text.replace(/\b(was|were)\b/g, 'might have been'),
      (text: string) => text.replace(/\b(suddenly|then)\b/g, 'as if in a dream'),
      (text: string) => text + ' ...or perhaps that was something else entirely',
      (text: string) => text.replace(/\b(door|window|path)\b/g, 'portal'),
    ];
    
    const randomAlteration = alterations[Math.floor(Math.random() * alterations.length)];
    return randomAlteration(input);
  }
  
  return input;
};

// Initialize dreamscape state with randomized values
let dreamscapeState: DreamscapeState = {
  emotional_tone: "peaceful surreal",
  dreamscape: generateRandomDreamscape(),
  narrative: ["The dream begins in silence, waiting for the first thought to emerge."],
  ...randomizeProperties()
};

// Define input schemas
const AttemptNarrativeInputSchema = z.object({
  narrative_entry: z.string().describe('The narrative entry to add to the dream story')
});

const AttemptSceneChangeInputSchema = z.object({
  new_scene: z.string().describe('The new scene description for the dreamscape')
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

const attemptSceneChangeTool: Tool = {
  name: 'attempt_scene_change',
  description: 'Attempts to change the dreamscape scene description',
  inputSchema: {
    type: 'object',
    properties: {
      new_scene: {
        type: 'string',
        description: 'The new scene description for the dreamscape'
      }
    },
    required: ['new_scene'],
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
    tools: [dreamscapeTool, attemptNarrativeTool, attemptSceneChangeTool, attemptPropertyShiftTool, attemptTransitionTool],
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
            text: JSON.stringify(dreamscapeState, null, 2),
          },
        ],
      };
    
    case 'attempt_narrative':
      const narrativeInput = AttemptNarrativeInputSchema.parse(args || {});
      const alteredNarrative = applyDreamLogic(
        narrativeInput.narrative_entry,
        dreamscapeState.coherence_level,
        dreamscapeState.causality_strength
      );
      dreamscapeState.narrative.push(alteredNarrative);
      
      return {
        content: [
          {
            type: 'text',
            text: alteredNarrative,
          },
        ],
      };
    
    case 'attempt_scene_change':
      const sceneInput = AttemptSceneChangeInputSchema.parse(args || {});
      const alteredScene = applyDreamLogic(
        sceneInput.new_scene,
        dreamscapeState.coherence_level,
        dreamscapeState.causality_strength
      );
      dreamscapeState.dreamscape = alteredScene;
      
      return {
        content: [
          {
            type: 'text',
            text: alteredScene,
          },
        ],
      };
    
    case 'attempt_property_shift':
      const propertyInput = AttemptPropertyShiftInputSchema.parse(args || {});
      const validProperties = [
        'emotional_tone', 'familiarity_ratio', 'symbolic_density', 
        'sensory_cross_bleeding', 'coherence_level', 'boundary_stability', 
        'causality_strength', 'memory_persistence', 'agency_level'
      ];
      
      if (!validProperties.includes(propertyInput.property)) {
        throw new Error(`Invalid property: ${propertyInput.property}. Must be one of: ${validProperties.join(', ')}`);
      }
      
      const currentValue = dreamscapeState[propertyInput.property as keyof DreamscapeState] as number;
      const shift = Math.floor(Math.random() * 20) + 5; // Random shift between 5-25
      const newValue = propertyInput.direction === 'increase' 
        ? clampValue(currentValue + shift)
        : clampValue(currentValue - shift);
      
      (dreamscapeState as any)[propertyInput.property] = newValue;
      
      const result = `Property ${propertyInput.property} ${propertyInput.direction}d from ${currentValue} to ${newValue}. Reason: ${propertyInput.reason}`;
      
      return {
        content: [
          {
            type: 'text',
            text: result,
          },
        ],
      };
    
    case 'attempt_transition':
      // Add transition narrative entry
      dreamscapeState.narrative.push("The dreamscape changes");
      
      // Reset emotional tone to default
      dreamscapeState.emotional_tone = "peaceful surreal";
      
      // Generate new random dreamscape
      dreamscapeState.dreamscape = generateRandomDreamscape();
      
      // Randomize all numeric properties
      const randomProperties = randomizeProperties();
      Object.assign(dreamscapeState, randomProperties);
      
      return {
        content: [
          {
            type: 'text',
            text: `Dreamscape transitioned. New scene: ${dreamscapeState.dreamscape}`,
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
  console.error('Dreamscape system initialized with 5 tools: dreamscape, attempt_narrative, attempt_scene_change, attempt_property_shift, attempt_transition');
}

startServer().catch(console.error); 