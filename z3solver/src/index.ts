#!/usr/bin/env node
/**
 * Z3Solver MCP Server - Simplified
 */
import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';
import { solve, SolveArgs } from './tools/solve.js';

const server = new Server(
  { name: 'z3_solver', version: '0.1.0' },
  { capabilities: { tools: {} } }
);

// List tools
server.setRequestHandler(ListToolsRequestSchema, async () => ({
  tools: [{
    name: 'solve_smtlib',
    description:
      'Execute Z3 solver on SMT-LIB input. Returns SMT-LIB with status comment ' +
      '("; sat", "; unsat", "; unknown") followed by model or unsat core.',
    inputSchema: {
      type: 'object',
      properties: {
        smtlib: {
          type: 'string',
          description: 'Valid SMT-LIB2 code'
        },
        timeout_ms: {
          type: 'number',
          description: 'Timeout in milliseconds (1-600000, default: 30000)',
          default: 30000
        }
      },
      required: ['smtlib']
    }
  }]
}));

// Call tool
server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;

  if (name !== 'solve_smtlib') {
    throw new Error(`Unknown tool: ${name}`);
  }

  try {
    const result = await solve(args as any);
    return {
      content: [{ type: 'text', text: result }]
    };
  } catch (error) {
    // Return instructive error directly - don't wrap with "Error:"
    const message = error instanceof Error ? error.message : String(error);
    return {
      content: [{ type: 'text', text: message }],
      isError: true
    };
  }
});

// Start
async function main() {
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error('Z3Solver MCP server running');
}

main().catch((error) => {
  console.error('Fatal:', error);
  process.exit(1);
});
