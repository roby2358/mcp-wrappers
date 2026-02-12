import { NodeRow, ToolResponse, ok, fail } from '../domain/types.js';
import { generateId } from '../domain/id.js';
import { computeHash } from '../domain/hash.js';
import { countTokens } from '../domain/token.js';
import { orderBefore, orderAfter } from '../domain/order.js';
import { insertNode, findNodeById, getSiblings } from '../db/queries.js';

function validateContext(contextType: string, contextName: string, contextValue: string): string | null {
  if (contextType === undefined || contextName === undefined || contextValue === undefined) {
    return 'All context fields (context_type, context_name, context_value) are required.';
  }
  if (contextType.length > 24 || contextName.length > 24 || contextValue.length > 24) {
    return 'Context fields must be 0 to 24 characters.';
  }
  return null;
}

export async function insertBefore(
  targetId: string,
  content: string,
  contextType: string,
  contextName: string,
  contextValue: string,
  readonly?: number,
): Promise<ToolResponse> {
  const ctxErr = validateContext(contextType, contextName, contextValue);
  if (ctxErr) return fail(ctxErr);

  const target = await findNodeById(targetId);
  if (!target) {
    return fail(`Target node '${targetId}' not found. Verify the ID using find() or structure().`);
  }
  if (!target.parent_id) {
    return fail(`Cannot insert before root node '${targetId}'. Use append() to add children to a root node.`);
  }

  const siblings = await getSiblings(target.parent_id);
  const targetIdx = siblings.findIndex(s => s.id === targetId);
  const prevOrder = targetIdx > 0 ? siblings[targetIdx - 1].order_value : null;
  const orderValue = orderBefore(target.order_value, prevOrder);

  const id = generateId();
  const now = new Date().toISOString();
  const hash = computeHash(target.parent_id, contextType, contextName, contextValue, content, orderValue);

  const node: NodeRow = {
    id,
    parent_id: target.parent_id,
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

export async function insertAfter(
  targetId: string,
  content: string,
  contextType: string,
  contextName: string,
  contextValue: string,
  readonly?: number,
): Promise<ToolResponse> {
  const ctxErr = validateContext(contextType, contextName, contextValue);
  if (ctxErr) return fail(ctxErr);

  const target = await findNodeById(targetId);
  if (!target) {
    return fail(`Target node '${targetId}' not found. Verify the ID using find() or structure().`);
  }
  if (!target.parent_id) {
    return fail(`Cannot insert after root node '${targetId}'. Use append() to add children to a root node.`);
  }

  const siblings = await getSiblings(target.parent_id);
  const targetIdx = siblings.findIndex(s => s.id === targetId);
  const nextOrder = targetIdx < siblings.length - 1 ? siblings[targetIdx + 1].order_value : null;
  const orderValue = orderAfter(target.order_value, nextOrder);

  const id = generateId();
  const now = new Date().toISOString();
  const hash = computeHash(target.parent_id, contextType, contextName, contextValue, content, orderValue);

  const node: NodeRow = {
    id,
    parent_id: target.parent_id,
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
