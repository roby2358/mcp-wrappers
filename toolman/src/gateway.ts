import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { StdioClientTransport } from "@modelcontextprotocol/sdk/client/stdio.js";
import type { Server } from "@modelcontextprotocol/sdk/server/index.js";
import type { ServerConfig, ToolmanConfig } from "./config.js";

// --- Cached types ---

export interface CachedTool {
  namespacedName: string;
  originalName: string;
  namespace: string;
  description: string;
  inputSchema: Record<string, unknown>;
  active: boolean;
}

export interface CachedResource {
  namespacedUri: string;
  originalUri: string;
  namespace: string;
  name: string;
  description: string;
  mimeType?: string;
  active: boolean;
}

export interface CachedResourceTemplate {
  namespacedUriTemplate: string;
  originalUriTemplate: string;
  namespace: string;
  name: string;
  description: string;
  mimeType?: string;
  active: boolean;
}

export interface CachedPrompt {
  namespacedName: string;
  originalName: string;
  namespace: string;
  description: string;
  arguments: Array<{
    name: string;
    description?: string;
    required?: boolean;
  }>;
}

interface UpstreamServer {
  namespace: string;
  client: Client;
  alive: boolean;
}

// --- Helpers ---

function globMatch(name: string, pattern: string): boolean {
  const escaped = pattern
    .replace(/[.+^${}()|[\]\\]/g, "\\$&")
    .replace(/\*/g, ".*")
    .replace(/\?/g, ".");
  return new RegExp(`^${escaped}$`).test(name);
}

// --- Gateway ---

export class Gateway {
  private config: ToolmanConfig;
  private server: Server | null = null;
  private upstreams: UpstreamServer[] = [];
  readonly tools = new Map<string, CachedTool>();
  readonly resources = new Map<string, CachedResource>();
  readonly resourceTemplates = new Map<string, CachedResourceTemplate>();
  readonly prompts = new Map<string, CachedPrompt>();

  constructor(config: ToolmanConfig) {
    this.config = config;
  }

  setServer(server: Server): void {
    this.server = server;
  }

  private applyNamespace(namespace: string, name: string): string {
    return namespace ? `toolman_${namespace}_${name}` : `toolman_${name}`;
  }

  private stripNamespace(namespace: string, name: string): string {
    // Strip "toolman_<namespace>_" prefix
    const prefix = namespace ? `toolman_${namespace}_` : "toolman_";
    return name.startsWith(prefix) ? name.slice(prefix.length) : name;
  }

  private matchesActive(name: string): boolean {
    return this.config.activeToolsets.some((pat) => globMatch(name, pat));
  }

  private findUpstream(namespace: string): UpstreamServer | undefined {
    return this.upstreams.find((u) => u.namespace === namespace && u.alive);
  }

  // --- Lifecycle ---

  async startup(): Promise<void> {
    await Promise.all(
      this.config.servers.map((sc) =>
        this.connectServer(sc).catch((e) =>
          console.error(`Failed to connect to '${sc.namespace}':`, e),
        ),
      ),
    );
  }

  private async connectServer(sc: ServerConfig): Promise<void> {
    const parts = sc.command.split(/\s+/);
    const transport = new StdioClientTransport({
      command: parts[0],
      args: parts.slice(1),
    });

    const client = new Client(
      { name: `toolman-${sc.namespace}`, version: "0.1.0" },
      { capabilities: {} },
    );
    await client.connect(transport);

    const upstream: UpstreamServer = {
      namespace: sc.namespace,
      client,
      alive: true,
    };
    this.upstreams.push(upstream);

    await this.cacheTools(client, sc);
    await this.cacheResources(client, sc);
    await this.cacheResourceTemplates(client, sc);
    await this.cachePrompts(client, sc);
  }

  private async cacheTools(
    client: Client,
    sc: ServerConfig,
  ): Promise<void> {
    try {
      const result = await client.listTools();
      for (const t of result.tools) {
        const ns = this.applyNamespace(sc.namespace, t.name);
        if (!this.tools.has(ns)) {
          this.tools.set(ns, {
            namespacedName: ns,
            originalName: t.name,
            namespace: sc.namespace,
            description: t.description ?? "",
            inputSchema: t.inputSchema as Record<string, unknown>,
            active: this.matchesActive(ns),
          });
        }
      }
    } catch (e) {
      console.error(`Failed to list tools from '${sc.namespace}':`, e);
    }
  }

  private async cacheResources(
    client: Client,
    sc: ServerConfig,
  ): Promise<void> {
    try {
      const result = await client.listResources();
      for (const r of result.resources) {
        const uri = String(r.uri);
        const ns = this.applyNamespace(sc.namespace, uri);
        if (!this.resources.has(ns)) {
          this.resources.set(ns, {
            namespacedUri: ns,
            originalUri: uri,
            namespace: sc.namespace,
            name: r.name ?? "",
            description: r.description ?? "",
            mimeType: r.mimeType,
            active: this.matchesActive(ns),
          });
        }
      }
    } catch (e) {
      console.error(`Failed to list resources from '${sc.namespace}':`, e);
    }
  }

  private async cacheResourceTemplates(
    client: Client,
    sc: ServerConfig,
  ): Promise<void> {
    try {
      const result = await client.listResourceTemplates();
      for (const rt of result.resourceTemplates) {
        const ns = this.applyNamespace(sc.namespace, rt.uriTemplate);
        if (!this.resourceTemplates.has(ns)) {
          this.resourceTemplates.set(ns, {
            namespacedUriTemplate: ns,
            originalUriTemplate: rt.uriTemplate,
            namespace: sc.namespace,
            name: rt.name ?? "",
            description: rt.description ?? "",
            mimeType: (rt as Record<string, unknown>).mimeType as
              | string
              | undefined,
            active: this.matchesActive(ns),
          });
        }
      }
    } catch (e) {
      console.error(
        `Failed to list resource templates from '${sc.namespace}':`,
        e,
      );
    }
  }

  private async cachePrompts(
    client: Client,
    sc: ServerConfig,
  ): Promise<void> {
    try {
      const result = await client.listPrompts();
      for (const p of result.prompts) {
        const ns = this.applyNamespace(sc.namespace, p.name);
        if (!this.prompts.has(ns)) {
          this.prompts.set(ns, {
            namespacedName: ns,
            originalName: p.name,
            namespace: sc.namespace,
            description: p.description ?? "",
            arguments: (p.arguments ?? []) as CachedPrompt["arguments"],
          });
        }
      }
    } catch (e) {
      console.error(`Failed to list prompts from '${sc.namespace}':`, e);
    }
  }

  async shutdown(): Promise<void> {
    for (const up of this.upstreams) {
      try {
        await up.client.close();
      } catch (e) {
        console.error(`Error closing '${up.namespace}':`, e);
      }
    }
  }

  // --- Catalog ---

  getActiveTools(): CachedTool[] {
    return [...this.tools.values()].filter((t) => t.active);
  }

  getInactiveTools(): CachedTool[] {
    return [...this.tools.values()].filter((t) => !t.active);
  }

  buildCatalog(): string {
    const lines = [
      "Activate or deactivate tools and resources. " +
        "Pass names in the corresponding on/off lists. " +
        "Current catalog:\n",
      "TOOLS:",
    ];

    const sorted = [...this.tools.values()].sort((a, b) =>
      a.namespacedName.localeCompare(b.namespacedName),
    );
    for (const t of sorted) {
      const marker = t.active ? "*" : " ";
      lines.push(`${marker} ${t.namespacedName}: ${t.description.slice(0, 132)}`);
    }

    const allRes: Array<{
      uri: string;
      description: string;
      active: boolean;
    }> = [];
    for (const r of this.resources.values()) {
      allRes.push({
        uri: r.namespacedUri,
        description: r.description,
        active: r.active,
      });
    }
    for (const rt of this.resourceTemplates.values()) {
      allRes.push({
        uri: rt.namespacedUriTemplate,
        description: rt.description,
        active: rt.active,
      });
    }
    if (allRes.length > 0) {
      lines.push("\nRESOURCES:");
      allRes.sort((a, b) => a.uri.localeCompare(b.uri));
      for (const r of allRes) {
        const marker = r.active ? "*" : " ";
        lines.push(`${marker} ${r.uri}: ${r.description.slice(0, 132)}`);
      }
    }

    return lines.join("\n");
  }

  // --- Activation ---

  activate(
    toolsOn: string[],
    toolsOff: string[],
    resourcesOn: string[],
    resourcesOff: string[],
  ): { success: boolean; result: string; error: string } {
    if (
      !toolsOn.length &&
      !toolsOff.length &&
      !resourcesOn.length &&
      !resourcesOff.length
    ) {
      return {
        success: false,
        result: "",
        error:
          "All lists are empty. Specify at least one tool or resource name " +
          "to activate or deactivate. Use the catalog in the toolman_activate " +
          "description to see available names.",
      };
    }

    const bad: string[] = [];
    for (const n of [...toolsOn, ...toolsOff]) {
      if (!this.tools.has(n)) bad.push(`tool '${n}'`);
    }
    const allResKeys = new Set([
      ...this.resources.keys(),
      ...this.resourceTemplates.keys(),
    ]);
    for (const n of [...resourcesOn, ...resourcesOff]) {
      if (!allResKeys.has(n)) bad.push(`resource '${n}'`);
    }

    if (bad.length) {
      return {
        success: false,
        result: "",
        error:
          `Unknown names: ${bad.join(", ")}. ` +
          "No changes applied. Check the catalog in the toolman_activate " +
          "description for valid names.",
      };
    }

    for (const n of toolsOn) this.tools.get(n)!.active = true;
    for (const n of toolsOff) this.tools.get(n)!.active = false;
    for (const n of resourcesOn) {
      const r = this.resources.get(n);
      if (r) r.active = true;
      const rt = this.resourceTemplates.get(n);
      if (rt) rt.active = true;
    }
    for (const n of resourcesOff) {
      const r = this.resources.get(n);
      if (r) r.active = false;
      const rt = this.resourceTemplates.get(n);
      if (rt) rt.active = false;
    }

    if (resourcesOn.length || resourcesOff.length) {
      this.notifyResourcesChanged();
    }

    // Build result with full descriptions of newly activated tools
    const activated: Array<{
      name: string;
      description: string;
      inputSchema: Record<string, unknown>;
    }> = [];
    for (const n of toolsOn) {
      const t = this.tools.get(n)!;
      activated.push({
        name: t.namespacedName,
        description: t.description,
        inputSchema: t.inputSchema,
      });
    }

    const result = activated.length
      ? JSON.stringify({ activated })
      : "OK";

    return { success: true, result, error: "" };
  }

  private notifyResourcesChanged(): void {
    this.server?.notification({
      method: "notifications/resources/list_changed",
    });
  }

  // --- Proxying ---

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  async callTool(name: string, args: Record<string, unknown>): Promise<any> {
    const tool = this.tools.get(name);
    if (!tool) {
      const similar = [...this.tools.keys()]
        .filter((n) => name.includes(n) || n.includes(name))
        .slice(0, 5);
      const hint = similar.length ? ` Similar: ${similar.join(", ")}.` : "";
      return {
        success: false,
        result: "",
        error: `Unknown tool '${name}'.${hint} Use toolman_activate to see available tools.`,
      };
    }

    if (!tool.active) {
      return {
        success: false,
        result: "",
        error:
          `Tool '${name}' is inactive. ` +
          `Use toolman_activate with tools_on=["${name}"] to activate it first.`,
      };
    }

    const upstream = this.findUpstream(tool.namespace);
    if (!upstream) {
      return {
        success: false,
        result: "",
        error: `Upstream server for '${name}' is unavailable.`,
      };
    }

    try {
      return await upstream.client.callTool({
        name: tool.originalName,
        arguments: args,
      });
    } catch (e) {
      console.error(`Upstream call failed for '${name}':`, e);
      this.removeServer(tool.namespace);
      return {
        success: false,
        result: "",
        error: `Upstream server for '${name}' crashed and has been removed from the catalog. Error: ${e}`,
      };
    }
  }

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  async readResource(uri: string): Promise<any> {
    const resource = this.resources.get(uri);

    if (!resource) {
      // Try namespace prefix matching for template-derived URIs
      for (const up of this.upstreams) {
        if (up.alive && up.namespace && uri.startsWith(`${up.namespace}_`)) {
          const hasActiveTemplate = [...this.resourceTemplates.values()].some(
            (rt) => rt.active && rt.namespace === up.namespace,
          );
          if (hasActiveTemplate) {
            const originalUri = this.stripNamespace(up.namespace, uri);
            try {
              return await up.client.readResource({ uri: originalUri });
            } catch (e) {
              console.error(`Upstream read failed for '${uri}':`, e);
              this.removeServer(up.namespace);
              return {
                success: false,
                result: "",
                error: `Upstream server for '${uri}' crashed. Error: ${e}`,
              };
            }
          } else {
            return {
              success: false,
              result: "",
              error:
                `Resource templates for namespace '${up.namespace}' are inactive. ` +
                "Use toolman_activate to activate them.",
            };
          }
        }
      }
      return {
        success: false,
        result: "",
        error: `Unknown resource '${uri}'. Use toolman_activate to see available resources.`,
      };
    }

    if (!resource.active) {
      return {
        success: false,
        result: "",
        error:
          `Resource '${uri}' is inactive. ` +
          `Use toolman_activate with resources_on=["${uri}"] to activate it first.`,
      };
    }

    const upstream = this.findUpstream(resource.namespace);
    if (!upstream) {
      return {
        success: false,
        result: "",
        error: `Upstream server for '${uri}' is unavailable.`,
      };
    }

    try {
      return await upstream.client.readResource({ uri: resource.originalUri });
    } catch (e) {
      console.error(`Upstream read failed for '${uri}':`, e);
      this.removeServer(resource.namespace);
      return {
        success: false,
        result: "",
        error: `Upstream server for '${uri}' crashed. Error: ${e}`,
      };
    }
  }

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  async getPrompt(name: string, args?: Record<string, string>): Promise<any> {
    const prompt = this.prompts.get(name);
    if (!prompt) return null;

    const upstream = this.findUpstream(prompt.namespace);
    if (!upstream) return null;

    try {
      return await upstream.client.getPrompt({
        name: prompt.originalName,
        arguments: args,
      });
    } catch (e) {
      console.error(`Upstream get_prompt failed for '${name}':`, e);
      this.removeServer(prompt.namespace);
      return null;
    }
  }

  // --- Crash handling ---

  removeServer(namespace: string): void {
    for (const [key, val] of this.tools) {
      if (val.namespace === namespace) this.tools.delete(key);
    }
    for (const [key, val] of this.resources) {
      if (val.namespace === namespace) this.resources.delete(key);
    }
    for (const [key, val] of this.resourceTemplates) {
      if (val.namespace === namespace) this.resourceTemplates.delete(key);
    }
    for (const [key, val] of this.prompts) {
      if (val.namespace === namespace) this.prompts.delete(key);
    }
    for (const up of this.upstreams) {
      if (up.namespace === namespace) up.alive = false;
    }
    console.error(`Removed server '${namespace}' after crash`);
    this.notifyResourcesChanged();
  }
}
