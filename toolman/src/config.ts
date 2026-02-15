import { readFileSync } from "fs";
import { parse } from "smol-toml";

export interface ServerConfig {
  namespace: string;
  command: string;
}

export interface ToolmanConfig {
  servers: ServerConfig[];
  activeToolsets: string[];
}

export function loadConfig(path = "tools.toml"): ToolmanConfig {
  const raw = readFileSync(path, "utf-8");
  const data = parse(raw) as Record<string, unknown>;

  const serversRaw = (data.servers ?? []) as Array<Record<string, unknown>>;
  const servers: ServerConfig[] = serversRaw.map((s) => ({
    namespace: (s.namespace as string) ?? "",
    command: s.command as string,
  }));

  return {
    servers,
    activeToolsets: (data.active_toolsets ?? []) as string[],
  };
}
