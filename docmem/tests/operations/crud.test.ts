import { describe, it, expect, beforeAll, beforeEach } from 'vitest';
import { setupTestDb, clearTestDb } from '../setup.js';
import { createDocmem } from '../../src/operations/docmem.js';
import { append, find, deleteNode, updateContent, updateContext } from '../../src/operations/crud.js';

describe('crud operations', () => {
  beforeAll(async () => { await setupTestDb(); });
  beforeEach(async () => { await clearTestDb(); });

  it('appends a child node', async () => {
    await createDocmem('root0001', '', 'root', 'a', 'b');
    const res = await append('root0001', 'Child text', 'message', 'user', 'alice');
    expect(res.success).toBe(true);
    const node = res.result as any;
    expect(node.parent_id).toBe('root0001');
    expect(node.content).toBe('Child text');
    expect(node.order_value).toBe(1.0);
  });

  it('appends sequential children with incrementing order', async () => {
    await createDocmem('root0001', '', 'root', 'a', 'b');
    await append('root0001', 'First', 'msg', 'u', 'a');
    const res = await append('root0001', 'Second', 'msg', 'u', 'a');
    expect((res.result as any).order_value).toBe(2.0);
  });

  it('finds a node by id', async () => {
    await createDocmem('root0001', 'hello', 'root', 'a', 'b');
    const res = await find('root0001');
    expect(res.success).toBe(true);
    expect((res.result as any).content).toBe('hello');
  });

  it('returns error for missing node', async () => {
    const res = await find('nonexist');
    expect(res.success).toBe(false);
  });

  it('deletes a node and its descendants', async () => {
    await createDocmem('root0001', '', 'root', 'a', 'b');
    const child = await append('root0001', 'Child', 'msg', 'u', 'a');
    const childId = (child.result as any).id;
    await append(childId, 'Grandchild', 'msg', 'u', 'a');

    const res = await deleteNode(childId);
    expect(res.success).toBe(true);
    expect((res.result as any).deleted).toBe(2);

    const findRes = await find(childId);
    expect(findRes.success).toBe(false);
  });

  it('updates content with correct hash', async () => {
    await createDocmem('root0001', 'original', 'root', 'a', 'b');
    const node = (await find('root0001')).result as any;
    const res = await updateContent('root0001', 'updated', node.hash);
    expect(res.success).toBe(true);
    expect((res.result as any).content).toBe('updated');
  });

  it('rejects update with wrong hash', async () => {
    await createDocmem('root0001', 'original', 'root', 'a', 'b');
    const res = await updateContent('root0001', 'updated', 'wronghash');
    expect(res.success).toBe(false);
    expect(res.error).toContain('Hash mismatch');
  });

  it('rejects update on readonly node', async () => {
    await createDocmem('root0001', '', 'root', 'a', 'b');
    const child = await append('root0001', 'readonly text', 'msg', 'u', 'a', 1);
    const node = (child.result as any);
    const res = await updateContent(node.id, 'new text', node.hash);
    expect(res.success).toBe(false);
    expect(res.error).toContain('readonly');
  });

  it('updates context with correct hash', async () => {
    await createDocmem('root0001', '', 'root', 'a', 'b');
    const node = (await find('root0001')).result as any;
    const res = await updateContext('root0001', 'root', 'newname', 'newval', node.hash);
    expect(res.success).toBe(true);
    expect((res.result as any).context_name).toBe('newname');
  });
});
