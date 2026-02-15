#!/usr/bin/env node
import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  ListResourcesRequestSchema,
  ReadResourceRequestSchema,
  ListResourceTemplatesRequestSchema,
  ListPromptsRequestSchema,
  GetPromptRequestSchema,
} from "@modelcontextprotocol/sdk/types.js";

import { loadConfig } from "./config.js";
import { Gateway } from "./gateway.js";

const config = loadConfig();
const gateway = new Gateway(config);

const server = new Server(
  { name: "toolman", version: "0.1.0" },
  { capabilities: { tools: {}, resources: {}, prompts: {} } },
);

gateway.setServer(server);

// --- Tools ---

server.setRequestHandler(ListToolsRequestSchema, async () => ({
  tools: [
    {
      name: "toolman_activate",
      description: gateway.buildCatalog(),
      inputSchema: {
        type: "object" as const,
        properties: {
          tools_on: {
            type: "array",
            items: { type: "string" },
            description: "Tool names to activate",
          },
          tools_off: {
            type: "array",
            items: { type: "string" },
            description: "Tool names to deactivate",
          },
          resources_on: {
            type: "array",
            items: { type: "string" },
            description: "Resource names to activate",
          },
          resources_off: {
            type: "array",
            items: { type: "string" },
            description: "Resource names to deactivate",
          },
        },
        required: ["tools_on", "tools_off", "resources_on", "resources_off"],
      },
    },
    ...gateway.getActiveTools().map((t) => ({
      name: t.namespacedName,
      description: t.description,
      inputSchema: t.inputSchema,
    })),
    ...gateway.getInactiveTools().map((t) => ({
      name: t.namespacedName,
      description: `Enable via toolman_activate(tools_on=["${t.namespacedName}"]) to get full signature.`,
      inputSchema: { type: "object" as const, properties: {} },
    })),
  ],
}));

server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;
  const safeArgs = (args ?? {}) as Record<string, unknown>;

  if (name === "toolman_activate") {
    const result = gateway.activate(
      (safeArgs.tools_on as string[]) ?? [],
      (safeArgs.tools_off as string[]) ?? [],
      (safeArgs.resources_on as string[]) ?? [],
      (safeArgs.resources_off as string[]) ?? [],
    );
    return {
      content: [{ type: "text" as const, text: JSON.stringify(result) }],
    };
  }

  const result = await gateway.callTool(name, safeArgs);

  // Toolman's own error (has success field)
  if ("success" in result) {
    return {
      content: [{ type: "text" as const, text: JSON.stringify(result) }],
    };
  }

  // Upstream CallToolResult — relay directly
  return result;
});

// --- Resources ---

server.setRequestHandler(ListResourcesRequestSchema, async () => ({
  resources: [...gateway.resources.values()]
    .filter((r) => r.active)
    .map((r) => ({
      uri: r.namespacedUri,
      name: r.name,
      description: r.description,
      mimeType: r.mimeType,
    })),
}));

server.setRequestHandler(ListResourceTemplatesRequestSchema, async () => ({
  resourceTemplates: [...gateway.resourceTemplates.values()]
    .filter((rt) => rt.active)
    .map((rt) => ({
      uriTemplate: rt.namespacedUriTemplate,
      name: rt.name,
      description: rt.description,
      mimeType: rt.mimeType,
    })),
}));

server.setRequestHandler(ReadResourceRequestSchema, async (request) => {
  const uri = String(request.params.uri);
  const result = await gateway.readResource(uri);

  // Toolman's own error
  if ("success" in result) {
    return {
      contents: [
        {
          uri,
          mimeType: "application/json",
          text: JSON.stringify(result),
        },
      ],
    };
  }

  // Upstream ReadResourceResult — relay directly
  return result;
});

// --- Prompts ---

server.setRequestHandler(ListPromptsRequestSchema, async () => ({
  prompts: [...gateway.prompts.values()].map((p) => ({
    name: p.namespacedName,
    description: p.description,
    arguments: p.arguments,
  })),
}));

server.setRequestHandler(GetPromptRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;
  const result = await gateway.getPrompt(name, args);
  if (!result) {
    throw new Error(`Unknown prompt '${name}'. Check available prompts.`);
  }
  return result as { messages: Array<{ role: string; content: unknown }> };
});

// --- Start ---

async function main() {
  await gateway.startup();

  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error("Toolman MCP gateway running");

  const cleanup = async () => {
    await gateway.shutdown();
    process.exit(0);
  };
  process.on("SIGINT", cleanup);
  process.on("SIGTERM", cleanup);
}

main().catch((error) => {
  console.error("Fatal:", error);
  process.exit(1);
});
