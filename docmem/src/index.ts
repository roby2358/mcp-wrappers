#!/usr/bin/env node
/**
 * Docmem MCP Server - Hierarchical document memory with tree-structured nodes
 */
import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  ListResourcesRequestSchema,
  ReadResourceRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';
import { initSchema } from './db/schema.js';
import { tools } from './tools/registry.js';
import { handleTool } from './tools/handler.js';
import { startHttpServer } from './http/server.js';
import { getRootNodes } from './db/queries.js';
import { structure } from './operations/query.js';

const server = new Server(
  { name: 'docmem', version: '0.1.0' },
  { capabilities: { tools: {}, resources: {} } }
);

server.setRequestHandler(ListToolsRequestSchema, async () => ({ tools }));

server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;
  const text = await handleTool(name, args ?? {});
  const isError = text.startsWith('error>');
  return { content: [{ type: 'text', text }], isError };
});

server.setRequestHandler(ListResourcesRequestSchema, async () => {
  const roots = await getRootNodes();
  return {
    resources: roots.map((r) => ({
      uri: `docmem://${r.id}/structure`,
      name: r.id,
      mimeType: 'text/plain',
    })),
  };
});

server.setRequestHandler(ReadResourceRequestSchema, async (request) => {
  const uri = request.params.uri;
  const match = uri.match(/^docmem:\/\/([^/]+)\/structure$/);
  if (!match) {
    throw new Error(`Invalid resource URI: '${uri}'. Expected format: docmem://{rootId}/structure`);
  }
  const rootId = match[1];
  const res = await structure(rootId);
  if (!res.success) {
    throw new Error(res.error);
  }
  return {
    contents: [{ uri, mimeType: 'text/plain', text: res.result as string }],
  };
});

async function main() {
  await initSchema();
  startHttpServer();
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error('Docmem MCP server running');
}

main().catch((error) => {
  console.error('Fatal:', error);
  process.exit(1);
});
