import { NodeRow, ToolResponse, ok, fail } from '../domain/types.js';
import { generateId } from '../domain/id.js';
import { computeHash } from '../domain/hash.js';
import { countTokens } from '../domain/token.js';
import { orderBefore, orderAfter } from '../domain/order.js';
import {
  findNodeById, getChildren, getMaxChildOrder, getSiblings,
  insertNode, updateNode, getAncestors,
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

async function copySubtree(sourceId: string, newParentId: string, orderValue: number): Promise<NodeRow> {
  const source = await findNodeById(sourceId);
  if (!source) throw new Error(`Source node '${sourceId}' not found.`);

  const id = generateId();
  const now = new Date().toISOString();
  const hash = computeHash(newParentId, source.context_type, source.context_name, source.context_value, source.content, orderValue);

  const newNode: NodeRow = {
    id,
    parent_id: newParentId,
    content: source.content,
    order_value: orderValue,
    token_count: source.token_count,
    created_at: now,
    updated_at: now,
    context_type: source.context_type,
    context_name: source.context_name,
    context_value: source.context_value,
    readonly: source.readonly,
    hash,
  };

  await insertNode(newNode);

  // Recursively copy children with sequential ordering
  const children = await getChildren(sourceId);
  for (let i = 0; i < children.length; i++) {
    await copySubtree(children[i].id, id, i + 1.0);
  }

  return newNode;
}

export async function copyNode(
  sourceId: string,
  targetId: string,
  position: 'child' | 'before' | 'after',
): Promise<ToolResponse> {
  const source = await findNodeById(sourceId);
  if (!source) {
    return fail(`Source node '${sourceId}' not found. Verify the ID using find() or structure().`);
  }
  const target = await findNodeById(targetId);
  if (!target) {
    return fail(`Target node '${targetId}' not found. Verify the ID using find() or structure().`);
  }

  let parentId: string;
  let orderValue: number;

  if (position === 'child') {
    parentId = targetId;
    const maxOrder = await getMaxChildOrder(targetId);
    orderValue = maxOrder !== null ? maxOrder + 1.0 : 1.0;
  } else {
    if (!target.parent_id) {
      return fail(`Cannot copy ${position} root node '${targetId}'. Use position 'child' instead.`);
    }
    parentId = target.parent_id;
    const siblings = await getSiblings(target.parent_id);
    const targetIdx = siblings.findIndex(s => s.id === targetId);

    if (position === 'before') {
      const prevOrder = targetIdx > 0 ? siblings[targetIdx - 1].order_value : null;
      orderValue = orderBefore(target.order_value, prevOrder);
    } else {
      const nextOrder = targetIdx < siblings.length - 1 ? siblings[targetIdx + 1].order_value : null;
      orderValue = orderAfter(target.order_value, nextOrder);
    }
  }

  const newRoot = await copySubtree(sourceId, parentId, orderValue);
  return ok(newRoot);
}

export async function moveNode(
  sourceId: string,
  targetId: string,
  position: 'child' | 'before' | 'after',
  expectedHash: string,
): Promise<ToolResponse> {
  const source = await findNodeById(sourceId);
  if (!source) {
    return fail(`Source node '${sourceId}' not found. Verify the ID using find() or structure().`);
  }
  if (source.hash !== expectedHash) {
    return fail(`Hash mismatch on node '${sourceId}': expected '${expectedHash}' but current is '${source.hash}'. Re-read the node with find() to get the current hash before retrying.`);
  }
  const target = await findNodeById(targetId);
  if (!target) {
    return fail(`Target node '${targetId}' not found. Verify the ID using find() or structure().`);
  }

  // Same-root check
  const sourceAncestors = await getAncestors(sourceId);
  const targetAncestors = await getAncestors(targetId);
  const sourceRoot = sourceAncestors.find(a => a.parent_id === null);
  const targetRoot = targetAncestors.find(a => a.parent_id === null);
  if (!sourceRoot || !targetRoot || sourceRoot.id !== targetRoot.id) {
    return fail(`Source and target must be in the same docmem tree. Use copy_node() for cross-tree operations.`);
  }

  // Cycle detection: target must not be a descendant of source
  if (targetId === sourceId) {
    return fail(`Cannot move node '${sourceId}' to itself.`);
  }
  const targetAncestorIds = new Set(targetAncestors.map(a => a.id));
  if (targetAncestorIds.has(sourceId)) {
    return fail(`Cannot move node '${sourceId}' to its own descendant '${targetId}'. This would create a cycle.`);
  }

  let newParentId: string;
  let orderValue: number;

  if (position === 'child') {
    newParentId = targetId;
    const maxOrder = await getMaxChildOrder(targetId);
    orderValue = maxOrder !== null ? maxOrder + 1.0 : 1.0;
  } else {
    if (!target.parent_id) {
      return fail(`Cannot move ${position} root node '${targetId}'. Use position 'child' instead.`);
    }
    newParentId = target.parent_id;
    const siblings = await getSiblings(target.parent_id);
    const targetIdx = siblings.findIndex(s => s.id === targetId);

    if (position === 'before') {
      const prevOrder = targetIdx > 0 ? siblings[targetIdx - 1].order_value : null;
      orderValue = orderBefore(target.order_value, prevOrder);
    } else {
      const nextOrder = targetIdx < siblings.length - 1 ? siblings[targetIdx + 1].order_value : null;
      orderValue = orderAfter(target.order_value, nextOrder);
    }
  }

  const now = new Date().toISOString();
  const newHash = computeHash(newParentId, source.context_type, source.context_name, source.context_value, source.content, orderValue);

  await updateNode(sourceId, {
    parent_id: newParentId,
    order_value: orderValue,
    updated_at: now,
    hash: newHash,
  });

  const updated = await findNodeById(sourceId);
  return ok(updated);
}

export async function summarize(
  nodeIds: string[],
  content: string,
  contextType: string,
  contextName: string,
  contextValue: string,
): Promise<ToolResponse> {
  const ctxErr = validateContext(contextType, contextName, contextValue);
  if (ctxErr) return fail(ctxErr);

  if (!nodeIds || nodeIds.length === 0) {
    return fail('At least one node_id is required for summarization.');
  }

  // Validate all nodes exist, share the same parent, and are leaves
  const nodes: NodeRow[] = [];
  for (const nid of nodeIds) {
    const node = await findNodeById(nid);
    if (!node) {
      return fail(`Node '${nid}' not found. Verify the ID using find() or structure().`);
    }
    nodes.push(node);
  }

  const parentId = nodes[0].parent_id;
  if (!parentId) {
    return fail('Cannot summarize root nodes. Nodes must have a parent.');
  }
  for (const node of nodes) {
    if (node.parent_id !== parentId) {
      return fail(`All nodes must share the same parent. Node '${node.id}' has parent '${node.parent_id}' but expected '${parentId}'.`);
    }
  }

  // Check all are leaves
  for (const node of nodes) {
    const children = await getChildren(node.id);
    if (children.length > 0) {
      return fail(`Node '${node.id}' has children and cannot be summarized. Only leaf nodes can be summarized.`);
    }
  }

  // Order the summary at the midpoint between first and last nodes
  const orders = nodes.map(n => n.order_value).sort((a, b) => a - b);
  const summaryOrder = (orders[0] + orders[orders.length - 1]) / 2;

  const summaryId = generateId();
  const now = new Date().toISOString();
  const summaryHash = computeHash(parentId, contextType, contextName, contextValue, content, summaryOrder);

  const summaryNode: NodeRow = {
    id: summaryId,
    parent_id: parentId,
    content,
    order_value: summaryOrder,
    token_count: countTokens(content),
    created_at: now,
    updated_at: now,
    context_type: contextType,
    context_name: contextName,
    context_value: contextValue,
    readonly: 0,
    hash: summaryHash,
  };

  await insertNode(summaryNode);

  // Reparent nodes to summary with optimistic locking
  for (let i = 0; i < nodes.length; i++) {
    const node = nodes[i];
    const freshNode = await findNodeById(node.id);
    if (!freshNode || freshNode.hash !== node.hash) {
      // Rollback: set parent back to original for any already-reparented nodes
      for (let j = 0; j < i; j++) {
        const rn = nodes[j];
        const newHash = computeHash(parentId, rn.context_type, rn.context_name, rn.context_value, rn.content, rn.order_value);
        await updateNode(rn.id, { parent_id: parentId, updated_at: now, hash: newHash });
      }
      return fail(`Optimistic lock failed on node '${node.id}' during reparenting. Node may have been modified concurrently. Re-read the nodes and retry.`);
    }

    const newOrder = i + 1.0;
    const newHash = computeHash(summaryId, node.context_type, node.context_name, node.context_value, node.content, newOrder);
    await updateNode(node.id, {
      parent_id: summaryId,
      order_value: newOrder,
      updated_at: now,
      hash: newHash,
    });
  }

  return ok(summaryNode);
}
