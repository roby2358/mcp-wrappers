import { parse, stringify } from 'smol-toml';
import { NodeRow, ToolResponse, ok, fail } from '../domain/types.js';
import { computeHash } from '../domain/hash.js';
import { countTokens } from '../domain/token.js';
import { insertNode, findNodeById, getChildren } from '../db/queries.js';

function parseContext(context: string): { type: string; name: string; value: string } | null {
  const parts = context.split(':');
  if (parts.length !== 3) return null;
  return { type: parts[0], name: parts[1], value: parts[2] };
}

function formatContext(node: NodeRow): string {
  return `${node.context_type}:${node.context_name}:${node.context_value}`;
}

export async function importToml(toml: string): Promise<ToolResponse> {
  let parsed: Record<string, unknown>;
  try {
    parsed = parse(toml) as Record<string, unknown>;
  } catch (e: unknown) {
    const msg = e instanceof Error ? e.message : String(e);
    return fail(`Failed to parse TOML: ${msg}. Ensure the input is valid TOML with [section] headers for each node.`);
  }

  const entries = Object.entries(parsed);
  if (entries.length === 0) {
    return fail('TOML contains no node sections. Each node should be a [section-id] with parent-node-id, context, and content fields.');
  }

  interface ParsedNode {
    id: string;
    parentId: string | null;
    context: { type: string; name: string; value: string };
    content: string;
  }

  const nodes: ParsedNode[] = [];
  const idSet = new Set<string>();

  for (const [id, value] of entries) {
    if (typeof value !== 'object' || value === null) {
      return fail(`Section '${id}' is not a valid node object. Each section needs parent-node-id, context, and content fields.`);
    }
    const section = value as Record<string, unknown>;

    const rawParent = section['parent-node-id'];
    if (rawParent !== undefined && typeof rawParent !== 'string') {
      return fail(`Section '${id}' has invalid 'parent-node-id' field (must be a string or omitted for root nodes).`);
    }
    if (typeof section.context !== 'string') {
      return fail(`Section '${id}' is missing 'context' field (format: "type:name:value").`);
    }
    if (typeof section.content !== 'string') {
      return fail(`Section '${id}' is missing 'content' field.`);
    }

    const ctx = parseContext(section.context as string);
    if (!ctx) {
      return fail(`Section '${id}' has invalid context format '${section.context}'. Expected "type:name:value" with exactly two colons.`);
    }

    const parentId = (rawParent as string | undefined) ?? '';
    if (idSet.has(id)) {
      return fail(`Duplicate section ID '${id}'. Each node must have a unique ID.`);
    }
    idSet.add(id);

    nodes.push({
      id,
      parentId: parentId === '' ? null : parentId,
      context: ctx,
      content: section.content as string,
    });
  }

  // Validate parent references
  for (const node of nodes) {
    if (node.parentId !== null && !idSet.has(node.parentId)) {
      return fail(`Section '${node.id}' references parent '${node.parentId}' which does not exist in the TOML. Ensure all parent nodes are defined.`);
    }
  }

  // Check for existing IDs in the database
  for (const node of nodes) {
    const existing = await findNodeById(node.id);
    if (existing) {
      return fail(`Node ID '${node.id}' already exists in the database. Use delete_node() to remove it first, or use different IDs in the TOML.`);
    }
  }

  // Topological sort: roots first, then children
  const sorted: ParsedNode[] = [];
  const inserted = new Set<string>();

  while (sorted.length < nodes.length) {
    let progress = false;
    for (const node of nodes) {
      if (inserted.has(node.id)) continue;
      if (node.parentId === null || inserted.has(node.parentId)) {
        sorted.push(node);
        inserted.add(node.id);
        progress = true;
      }
    }
    if (!progress) {
      return fail('Circular parent references detected in TOML. Check parent-node-id fields for cycles.');
    }
  }

  // Track per-parent order counters
  const orderCounters = new Map<string, number>();
  const roots: NodeRow[] = [];

  for (const node of sorted) {
    const parentKey = node.parentId ?? '__root__';
    const currentOrder = (orderCounters.get(parentKey) ?? 0) + 1.0;
    orderCounters.set(parentKey, currentOrder);

    const now = new Date().toISOString();
    const hash = computeHash(
      node.parentId,
      node.context.type,
      node.context.name,
      node.context.value,
      node.content,
      currentOrder,
    );

    const row: NodeRow = {
      id: node.id,
      parent_id: node.parentId,
      content: node.content,
      order_value: currentOrder,
      token_count: countTokens(node.content),
      created_at: now,
      updated_at: now,
      context_type: node.context.type,
      context_name: node.context.name,
      context_value: node.context.value,
      readonly: 0,
      hash,
    };

    await insertNode(row);
    if (node.parentId === null) roots.push(row);
  }

  return ok(roots);
}

export async function exportToml(nodeId: string): Promise<ToolResponse> {
  const root = await findNodeById(nodeId);
  if (!root) {
    return fail(`Node '${nodeId}' not found. Verify the ID using find() or list_docmems().`);
  }

  const sections: Record<string, Record<string, string>> = {};

  async function dfs(node: NodeRow): Promise<void> {
    sections[node.id] = {
      'parent-node-id': node.parent_id ?? '',
      context: formatContext(node),
      content: node.content,
    };
    const children = await getChildren(node.id);
    for (const child of children) {
      await dfs(child);
    }
  }

  await dfs(root);
  return ok(stringify(sections));
}
