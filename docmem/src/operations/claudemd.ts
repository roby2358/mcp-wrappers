import { readFile, writeFile } from 'fs/promises';
import { join } from 'path';
import { findNodeById } from '../db/queries.js';
import { expandToLength } from './query.js';
import { ToolResponse, ok, fail } from '../domain/types.js';

const SECTION_HEADER = '# DOCMEM Dynamic';
const TOKEN_BUDGET = 10000;

let activeList: string[] = [];

function claudeMdPath(): string {
  return join(process.cwd(), 'CLAUDE.md');
}

async function readBase(): Promise<string | null> {
  let content: string;
  try {
    content = await readFile(claudeMdPath(), 'utf-8');
  } catch {
    return null;
  }
  const idx = content.indexOf(`\n${SECTION_HEADER}`);
  return idx === -1 ? content : content.slice(0, idx).trimEnd();
}

async function writeSection(section: string | null): Promise<void> {
  const base = (await readBase()) ?? '';
  const out = section ? `${base.trimEnd()}\n\n${section}` : `${base.trimEnd()}\n`;
  await writeFile(claudeMdPath(), out, 'utf-8');
}

async function buildSection(): Promise<string> {
  const parts: string[] = [`${SECTION_HEADER}\n`];
  for (const nodeId of activeList) {
    const res = await expandToLength(nodeId, TOKEN_BUDGET);
    const body = res.success ? (res.result as string) : `(expand failed for ${nodeId})`;
    parts.push(`## ${nodeId}\n\n${body}\n`);
  }
  return parts.join('\n');
}

export function getActiveList(): string[] {
  return activeList;
}

export async function cleanupOnStartup(): Promise<void> {
  const base = await readBase();
  if (base === null) return;
  await writeSection(null);
}

export async function viewAdd(nodeId: string): Promise<ToolResponse> {
  const node = await findNodeById(nodeId);
  if (!node) {
    return fail(`Node '${nodeId}' not found. Verify the ID using docmem_query_nodes or docmem_get_root.`);
  }

  activeList = activeList.filter((id) => id !== nodeId);
  activeList.push(nodeId);

  await writeSection(await buildSection());
  return ok(`Added '${nodeId}'. Active views: [${activeList.join(', ')}]`);
}

export async function viewRemove(nodeId: string): Promise<ToolResponse> {
  if (!activeList.includes(nodeId)) {
    return fail(`Node '${nodeId}' is not in the active view list. Current views: [${activeList.join(', ')}]`);
  }

  activeList = activeList.filter((id) => id !== nodeId);
  await writeSection(activeList.length > 0 ? await buildSection() : null);
  return ok(`Removed '${nodeId}'. Active views: [${activeList.join(', ')}]`);
}
