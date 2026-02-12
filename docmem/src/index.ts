#!/usr/bin/env node
/**
 * Docmem MCP Server - Hierarchical document memory with tree-structured nodes
 */
import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';
import { initSchema } from './db/schema.js';
import { tools } from './tools/registry.js';
import { handleTool } from './tools/handler.js';

const server = new Server(
  { name: 'docmem', version: '0.1.0' },
  { capabilities: { tools: {} } }
);

server.setRequestHandler(ListToolsRequestSchema, async () => ({ tools }));

server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;

  try {
    const response = await handleTool(name, args ?? {});
    if (response.success) {
      const text = typeof response.result === 'string'
        ? response.result
        : JSON.stringify(response.result, null, 2);
      return { content: [{ type: 'text', text }] };
    } else {
      return { content: [{ type: 'text', text: response.error }], isError: true };
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return { content: [{ type: 'text', text: message }], isError: true };
  }
});

async function main() {
  await initSchema();
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error('Docmem MCP server running');
}

main().catch((error) => {
  console.error('Fatal:', error);
  process.exit(1);
});
