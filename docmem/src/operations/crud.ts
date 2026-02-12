import { NodeRow, ToolResponse, ok, fail } from '../domain/types.js';
import { generateId } from '../domain/id.js';
import { computeHash } from '../domain/hash.js';
import { countTokens } from '../domain/token.js';
import {
  insertNode, findNodeById, getMaxChildOrder,
  updateNode, deleteNodeById, getDescendants,
} from '../db/queries.js';

function validateContext(contextType: string, contextName: string, contextValue: string): string | null {
  if (contextType === undefined || contextName === undefined || contextValue === undefined) {
    return 'All context fields (context_type, context_name, context_value) are required.';
  }
  if (contextType.length > 24 || contextName.length > 24 || contextValue.length > 24) {
    return 'Context fields must be 0 to 24 characters.';
  }
  return null;
}

export async function append(
  parentId: string,
  content: string,
  contextType: string,
  contextName: string,
  contextValue: string,
  readonly?: number,
): Promise<ToolResponse> {
  const ctxErr = validateContext(contextType, contextName, contextValue);
  if (ctxErr) return fail(ctxErr);

  const parent = await findNodeById(parentId);
  if (!parent) {
    return fail(`Parent node '${parentId}' not found. Use find() to verify the node exists, or list_docmems() to see available roots.`);
  }

  const maxOrder = await getMaxChildOrder(parentId);
  const orderValue = maxOrder !== null ? maxOrder + 1.0 : 1.0;
  const id = generateId();
  const now = new Date().toISOString();
  const hash = computeHash(parentId, contextType, contextName, contextValue, content, orderValue);

  const node: NodeRow = {
    id,
    parent_id: parentId,
    content,
    order_value: orderValue,
    token_count: countTokens(content),
    created_at: now,
    updated_at: now,
    context_type: contextType,
    context_name: contextName,
    context_value: contextValue,
    readonly: readonly ?? 0,
    hash,
  };

  await insertNode(node);
  return ok(node);
}

export async function find(id: string): Promise<ToolResponse> {
  const node = await findNodeById(id);
  if (!node) {
    return fail(`Node '${id}' not found. Verify the ID is correct using structure() or list_docmems().`);
  }
  return ok(node);
}

export async function deleteNode(id: string): Promise<ToolResponse> {
  const node = await findNodeById(id);
  if (!node) {
    return fail(`Node '${id}' not found. Verify the ID is correct using structure() or list_docmems().`);
  }

  const descendants = await getDescendants(id);
  // Post-order: delete children before parents (reverse the collected list)
  const toDelete = [...descendants.reverse(), node];
  for (const n of toDelete) {
    await deleteNodeById(n.id);
  }

  return ok({ deleted: toDelete.length });
}

export async function updateContent(
  id: string,
  content: string,
): Promise<ToolResponse> {
  const node = await findNodeById(id);
  if (!node) {
    return fail(`Node '${id}' not found. Verify the ID using find() or structure().`);
  }
  if (node.readonly === 1) {
    return fail(`Node '${id}' is readonly. Create a note node as a sibling instead using insert_after().`);
  }

  const now = new Date().toISOString();
  const newHash = computeHash(node.parent_id, node.context_type, node.context_name, node.context_value, content, node.order_value);

  await updateNode(id, {
    content,
    token_count: countTokens(content),
    updated_at: now,
    hash: newHash,
  });

  const updated = await findNodeById(id);
  return ok(updated);
}

export async function updateContext(
  id: string,
  contextType: string,
  contextName: string,
  contextValue: string,
): Promise<ToolResponse> {
  const ctxErr = validateContext(contextType, contextName, contextValue);
  if (ctxErr) return fail(ctxErr);

  const node = await findNodeById(id);
  if (!node) {
    return fail(`Node '${id}' not found. Verify the ID using find() or structure().`);
  }
  if (node.readonly === 1) {
    return fail(`Node '${id}' is readonly. Create a note node as a sibling instead using insert_after().`);
  }

  const now = new Date().toISOString();
  const newHash = computeHash(node.parent_id, contextType, contextName, contextValue, node.content, node.order_value);

  await updateNode(id, {
    context_type: contextType,
    context_name: contextName,
    context_value: contextValue,
    updated_at: now,
    hash: newHash,
  });

  const updated = await findNodeById(id);
  return ok(updated);
}
