import { NodeRow, ToolResponse, ok, fail } from '../domain/types.js';
import { findNodeById, getChildren, getAncestors, queryFreeform } from '../db/queries.js';

function formatContext(node: NodeRow): string {
  return `${node.context_type}:${node.context_name}:${node.context_value}`;
}

function formatNodeMeta(node: NodeRow): string {
  return `${node.id} ${formatContext(node)} ${node.updated_at}`;
}

export async function serialize(nodeId: string): Promise<ToolResponse> {
  const root = await findNodeById(nodeId);
  if (!root) {
    return fail(`Node '${nodeId}' not found. Verify the ID using find() or list_docmems().`);
  }

  const texts: string[] = [];

  async function dfs(parentId: string): Promise<void> {
    const children = await getChildren(parentId);
    for (const child of children) {
      if (child.content.trim().length > 0) {
        texts.push(child.content);
      }
      await dfs(child.id);
    }
  }

  await dfs(nodeId);
  return ok(texts.join('\n\n'));
}

export async function expandToLength(nodeId: string, tokenBudget: number): Promise<ToolResponse> {
  const root = await findNodeById(nodeId);
  if (!root) {
    return fail(`Node '${nodeId}' not found. Verify the ID using find() or list_docmems().`);
  }
  if (tokenBudget <= 0) {
    return fail('token_budget must be a positive number.');
  }

  // Phase 1: Build priority list via reverse BFS
  // Parents always appear before children. Within each level, reverse order (most recent first).
  const priorityList: NodeRow[] = [];
  let currentLevel: NodeRow[] = [root];

  while (currentLevel.length > 0) {
    const reversed = [...currentLevel].reverse();
    priorityList.push(...reversed);
    const nextLevel: NodeRow[] = [];
    for (const node of currentLevel) {
      const children = await getChildren(node.id);
      nextLevel.push(...children);
    }
    currentLevel = nextLevel;
  }

  // Phase 2: Consume budget
  const includedSet = new Set<string>();
  let runningTotal = 0;
  for (const node of priorityList) {
    if (runningTotal + node.token_count > tokenBudget) {
      break;
    }
    runningTotal += node.token_count;
    includedSet.add(node.id);
  }

  // Phase 3: Preorder DFS render
  const result: NodeRow[] = [];

  async function dfs(node: NodeRow): Promise<void> {
    if (!includedSet.has(node.id)) return;
    result.push(node);
    const children = await getChildren(node.id);
    for (const child of children) {
      await dfs(child);
    }
  }

  await dfs(root);
  return ok(result);
}

export async function structure(nodeId: string): Promise<ToolResponse> {
  const root = await findNodeById(nodeId);
  if (!root) {
    return fail(`Node '${nodeId}' not found. Verify the ID using find() or list_docmems().`);
  }

  const lines: string[] = [];

  async function dfs(node: NodeRow, depth: number): Promise<void> {
    const indent = '  '.repeat(depth);
    lines.push(`${indent}- ${formatNodeMeta(node)}`);
    const children = await getChildren(node.id);
    for (const child of children) {
      await dfs(child, depth + 1);
    }
  }

  await dfs(root, 0);
  return ok(lines.join('\n'));
}

export async function queryNodes(sql: string): Promise<ToolResponse> {
  try {
    const rows = await queryFreeform(sql);
    return ok(rows);
  } catch (e: unknown) {
    const msg = e instanceof Error ? e.message : String(e);
    return fail(`Query failed: ${msg}. Write a full SELECT statement against the "nodes" table. Columns: id, parent_id, content, order_value, token_count, created_at, updated_at, context_type, context_name, context_value, readonly, hash. A LIMIT 20 is appended automatically.`);
  }
}

export async function getRoot(nodeId: string): Promise<ToolResponse> {
  const node = await findNodeById(nodeId);
  if (!node) {
    return fail(`Node '${nodeId}' not found. Verify the ID using find() or list_docmems().`);
  }

  const ancestors = await getAncestors(nodeId);
  // Reverse to get root-first order (getAncestors returns node-first)
  const rootFirst = [...ancestors].reverse();

  const lines = rootFirst.map((a, i) => {
    const indent = '  '.repeat(i);
    return `${indent}- ${formatNodeMeta(a)}`;
  });

  return ok(lines.join('\n'));
}
