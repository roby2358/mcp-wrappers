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
import { getRootNodes, findNodeById } from './db/queries.js';
import { structure } from './operations/query.js';
import { listDocmems } from './operations/docmem.js';
import { cleanupOnStartup } from './operations/claudemd.js';

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
    resources: [
      {
        uri: 'docmem:///roots_all',
        name: 'all nodes',
        mimeType: 'text/plain',
      },
      ...roots.flatMap((r) => [
        {
          uri: `docmem:///structure/${r.id}`,
          name: `${r.id} structure`,
          mimeType: 'text/plain',
        },
        {
          uri: `docmem:///node/${r.id}`,
          name: `${r.id} node`,
          mimeType: 'application/json',
        },
      ]),
    ],
  };
});

server.setRequestHandler(ReadResourceRequestSchema, async (request) => {
  const uri = request.params.uri;

  if (uri === 'docmem:///roots_all') {
    const res = await listDocmems();
    return {
      contents: [{ uri, mimeType: 'text/plain', text: (res.result as string) ?? '' }],
    };
  }

  const match = uri.match(/^docmem:\/\/\/(structure|node)\/(.+)$/);
  if (!match) {
    throw new Error(`Invalid resource URI: '${uri}'. Expected: docmem:///structure/{id}, docmem:///node/{id}, or docmem:///roots_all`);
  }

  const [, type, nodeId] = match;

  if (type === 'structure') {
    const res = await structure(nodeId);
    if (!res.success) throw new Error(res.error);
    return {
      contents: [{ uri, mimeType: 'text/plain', text: res.result as string }],
    };
  }

  // type === 'node'
  const node = await findNodeById(nodeId);
  if (!node) throw new Error(`Node '${nodeId}' not found.`);
  return {
    contents: [{ uri, mimeType: 'application/json', text: JSON.stringify(node, null, 2) }],
  };
});

async function main() {
  await initSchema();
  await cleanupOnStartup();
  startHttpServer();
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error('Docmem MCP server running');
}

main().catch((error) => {
  console.error('Fatal:', error);
  process.exit(1);
});
