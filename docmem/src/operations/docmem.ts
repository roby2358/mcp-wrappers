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
  content: string | undefined,
  contextType: string,
  contextName: string,
  contextValue: string,
): Promise<ToolResponse> {
  if (!contextType && contextType !== '' || contextName === undefined || contextValue === undefined) {
    return fail('All context fields (context_type, context_name, context_value) are required.');
  }
  if (contextType.length > 24 || contextName.length > 24 || contextValue.length > 24) {
    return fail('Context fields must be 0 to 24 characters.');
  }

  const id = rootId ?? generateId();

  const existing = await findNodeById(id);
  if (existing) {
    return fail(`A node with id '${id}' already exists. Choose a different root_id or omit it to auto-generate.`);
  }

  const nodeContent = content ?? '';
  const now = new Date().toISOString();
  const hash = computeHash(null, contextType, contextName, contextValue, nodeContent, 1.0);

  const node: NodeRow = {
    id,
    parent_id: null,
    content: nodeContent,
    order_value: 1.0,
    token_count: countTokens(nodeContent),
    created_at: now,
    updated_at: now,
    context_type: contextType,
    context_name: contextName,
    context_value: contextValue,
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
