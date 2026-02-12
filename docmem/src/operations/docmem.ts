import { NodeRow, ToolResponse, ok, fail } from '../domain/types.js';
import { generateId } from '../domain/id.js';
import { computeHash } from '../domain/hash.js';
import { countTokens } from '../domain/token.js';
import { insertNode, getRootNodes, findNodeById } from '../db/queries.js';

function formatContext(node: NodeRow): string {
  return `${node.context_type}:${node.context_name}:${node.context_value}`;
}

function formatNodeMeta(node: NodeRow): string {
  return `${node.id} ${formatContext(node)} ${node.updated_at}`;
}

export async function createDocmem(
  rootId: string | undefined,
): Promise<ToolResponse> {
  const id = rootId ?? generateId();

  const existing = await findNodeById(id);
  if (existing) {
    return fail(`A node with id '${id}' already exists. Choose a different root_id or omit it to auto-generate.`);
  }

  const now = new Date().toISOString();
  const hash = computeHash(null, '', '', '', '', 1.0);

  const node: NodeRow = {
    id,
    parent_id: null,
    content: '',
    order_value: 1.0,
    token_count: countTokens(''),
    created_at: now,
    updated_at: now,
    context_type: '',
    context_name: '',
    context_value: '',
    readonly: 0,
    hash,
  };

  await insertNode(node);
  return ok(node);
}

export async function listDocmems(): Promise<ToolResponse> {
  const roots = await getRootNodes();
  const lines = roots.map(formatNodeMeta);
  return ok(lines.join('\n'));
}
