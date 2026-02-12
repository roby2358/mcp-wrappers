import { query, run } from './connection.js';
import { NodeRow } from '../domain/types.js';

function toNodeRow(row: Record<string, unknown>): NodeRow {
  return {
    id: row.id as string,
    parent_id: row.parent_id as string | null,
    content: row.content as string,
    order_value: row.order_value as number,
    token_count: row.token_count as number,
    created_at: row.created_at as string,
    updated_at: row.updated_at as string,
    context_type: row.context_type as string,
    context_name: row.context_name as string,
    context_value: row.context_value as string,
    readonly: row.readonly as number,
    hash: row.hash as string | null,
  };
}

export async function insertNode(node: NodeRow): Promise<void> {
  await run(
    `INSERT INTO nodes (id, parent_id, content, order_value, token_count, created_at, updated_at, context_type, context_name, context_value, readonly, hash)
     VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
    node.id,
    node.parent_id,
    node.content,
    node.order_value,
    node.token_count,
    node.created_at,
    node.updated_at,
    node.context_type,
    node.context_name,
    node.context_value,
    node.readonly,
    node.hash,
  );
}

export async function findNodeById(id: string): Promise<NodeRow | null> {
  const rows = await query('SELECT * FROM nodes WHERE id = ?', id);
  return rows.length > 0 ? toNodeRow(rows[0]) : null;
}

export async function getChildren(parentId: string): Promise<NodeRow[]> {
  const rows = await query(
    'SELECT * FROM nodes WHERE parent_id = ? ORDER BY order_value',
    parentId,
  );
  return rows.map(toNodeRow);
}

export async function getRootNodes(): Promise<NodeRow[]> {
  const rows = await query(
    'SELECT * FROM nodes WHERE parent_id IS NULL ORDER BY created_at',
  );
  return rows.map(toNodeRow);
}

export async function getMaxChildOrder(parentId: string): Promise<number | null> {
  const rows = await query(
    'SELECT MAX(order_value) as max_order FROM nodes WHERE parent_id = ?',
    parentId,
  );
  const val = rows[0]?.max_order;
  return val === null || val === undefined ? null : val as number;
}

export async function getSiblings(parentId: string): Promise<NodeRow[]> {
  return getChildren(parentId);
}

export async function updateNode(
  id: string,
  fields: Partial<Pick<NodeRow, 'parent_id' | 'content' | 'order_value' | 'token_count' | 'updated_at' | 'context_type' | 'context_name' | 'context_value' | 'hash'>>,
): Promise<void> {
  const sets: string[] = [];
  const params: unknown[] = [];
  for (const [key, value] of Object.entries(fields)) {
    sets.push(`${key} = ?`);
    params.push(value);
  }
  params.push(id);
  await run(`UPDATE nodes SET ${sets.join(', ')} WHERE id = ?`, ...params);
}

export async function deleteNodeById(id: string): Promise<void> {
  await run('DELETE FROM nodes WHERE id = ?', id);
}

export async function getDescendants(nodeId: string): Promise<NodeRow[]> {
  const rows = await query(
    `WITH RECURSIVE descendants AS (
       SELECT * FROM nodes WHERE parent_id = ?
       UNION ALL
       SELECT n.* FROM nodes n JOIN descendants d ON n.parent_id = d.id
     )
     SELECT * FROM descendants`,
    nodeId,
  );
  return rows.map(toNodeRow);
}

export async function getSubtree(nodeId: string): Promise<NodeRow[]> {
  const rows = await query(
    `WITH RECURSIVE subtree AS (
       SELECT *, 0 as depth FROM nodes WHERE id = ?
       UNION ALL
       SELECT n.*, s.depth + 1 FROM nodes n JOIN subtree s ON n.parent_id = s.id
     )
     SELECT * FROM subtree ORDER BY depth, order_value`,
    nodeId,
  );
  return rows.map(toNodeRow);
}

export async function queryFreeform(sql: string): Promise<Record<string, unknown>[]> {
  return query(`${sql} LIMIT 20`);
}

export async function getAncestors(nodeId: string): Promise<NodeRow[]> {
  const rows = await query(
    `WITH RECURSIVE ancestors AS (
       SELECT * FROM nodes WHERE id = ?
       UNION ALL
       SELECT n.* FROM nodes n JOIN ancestors a ON n.id = a.parent_id
     )
     SELECT * FROM ancestors`,
    nodeId,
  );
  return rows.map(toNodeRow);
}
