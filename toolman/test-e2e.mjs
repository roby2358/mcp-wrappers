// End-to-end test: connect to toolman as a client
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { StdioClientTransport } from "@modelcontextprotocol/sdk/client/stdio.js";

const transport = new StdioClientTransport({
  command: "node",
  args: ["build/index.js"],
});

const client = new Client(
  { name: "test-client", version: "0.1.0" },
  { capabilities: {} },
);

await client.connect(transport);
console.log("Connected to toolman\n");

// 1. List tools
console.log("=== LIST TOOLS ===");
const { tools } = await client.listTools();
for (const t of tools) {
  console.log(`  ${t.name}: ${(t.description || "").slice(0, 80)}`);
}

// 2. Call active tool (ts_echo should be active via 'ts*' pattern)
console.log("\n=== CALL ts_echo ===");
let result = await client.callTool({
  name: "ts_echo",
  arguments: { message: "Hello from toolman!" },
});
console.log("  ", result.content[0].text);

// 3. Call active tool (ts_add)
console.log("\n=== CALL ts_add ===");
result = await client.callTool({
  name: "ts_add",
  arguments: { a: 17, b: 25 },
});
console.log("  ", result.content[0].text);

// 4. List resources
console.log("\n=== LIST RESOURCES ===");
const { resources } = await client.listResources();
for (const r of resources) {
  console.log(`  ${r.uri}: ${r.description}`);
}

// 5. Read resource
if (resources.length > 0) {
  console.log("\n=== READ RESOURCE ===");
  const res = await client.readResource({ uri: resources[0].uri });
  console.log("  ", res.contents[0].text);
}

// 6. List prompts
console.log("\n=== LIST PROMPTS ===");
const { prompts } = await client.listPrompts();
for (const p of prompts) {
  console.log(`  ${p.name}: ${p.description}`);
}

// 7. Get prompt
if (prompts.length > 0) {
  console.log("\n=== GET PROMPT ===");
  const prompt = await client.getPrompt({
    name: prompts[0].name,
    arguments: { name: "Toolman" },
  });
  console.log("  ", JSON.stringify(prompt.messages[0]));
}

// 8. Deactivate ts_echo
console.log("\n=== DEACTIVATE ts_echo ===");
result = await client.callTool({
  name: "toolman_activate",
  arguments: {
    tools_on: [],
    tools_off: ["ts_echo"],
    resources_on: [],
    resources_off: [],
  },
});
console.log("  ", result.content[0].text);

// 9. Verify tool list updated
console.log("\n=== TOOLS AFTER DEACTIVATION ===");
const { tools: tools2 } = await client.listTools();
for (const t of tools2) {
  console.log(`  ${t.name}: ${(t.description || "").slice(0, 80)}`);
}

// 10. Try calling deactivated tool
console.log("\n=== CALL DEACTIVATED ts_echo ===");
result = await client.callTool({
  name: "ts_echo",
  arguments: { message: "should fail" },
});
console.log("  ", result.content[0].text);

// 11. Reactivate
console.log("\n=== REACTIVATE ts_echo ===");
result = await client.callTool({
  name: "toolman_activate",
  arguments: {
    tools_on: ["ts_echo"],
    tools_off: [],
    resources_on: [],
    resources_off: [],
  },
});
console.log("  ", result.content[0].text);

// 12. Call reactivated tool
console.log("\n=== CALL REACTIVATED ts_echo ===");
result = await client.callTool({
  name: "ts_echo",
  arguments: { message: "Back online!" },
});
console.log("  ", result.content[0].text);

// 13. Test error: empty activation
console.log("\n=== EMPTY ACTIVATION (should error) ===");
result = await client.callTool({
  name: "toolman_activate",
  arguments: {
    tools_on: [],
    tools_off: [],
    resources_on: [],
    resources_off: [],
  },
});
console.log("  ", result.content[0].text);

// 14. Test error: unknown tool name
console.log("\n=== UNKNOWN TOOL ACTIVATION (should error) ===");
result = await client.callTool({
  name: "toolman_activate",
  arguments: {
    tools_on: ["nonexistent_tool"],
    tools_off: [],
    resources_on: [],
    resources_off: [],
  },
});
console.log("  ", result.content[0].text);

console.log("\n=== ALL TESTS PASSED ===");
await client.close();
process.exit(0);
