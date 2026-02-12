import { describe, it, expect, beforeAll, beforeEach } from 'vitest';
import { setupTestDb, clearTestDb } from '../setup.js';
import { createDocmem } from '../../src/operations/docmem.js';
import { append } from '../../src/operations/crud.js';
import { insertBefore, insertAfter } from '../../src/operations/insert.js';

describe('insert operations', () => {
  beforeAll(async () => { await setupTestDb(); });
  beforeEach(async () => { await clearTestDb(); });

  it('inserts before a target node', async () => {
    await createDocmem('root0001');
    const c1 = await append('root0001', 'First', 'msg', 'u', 'a');
    const c1Id = (c1.result as any).id;

    const res = await insertBefore(c1Id, 'Before first', 'msg', 'u', 'a');
    expect(res.success).toBe(true);
    const node = res.result as any;
    expect(node.order_value).toBeLessThan((c1.result as any).order_value);
    expect(node.parent_id).toBe('root0001');
  });

  it('inserts after a target node', async () => {
    await createDocmem('root0001');
    const c1 = await append('root0001', 'First', 'msg', 'u', 'a');
    const c1Id = (c1.result as any).id;

    const res = await insertAfter(c1Id, 'After first', 'msg', 'u', 'a');
    expect(res.success).toBe(true);
    const node = res.result as any;
    expect(node.order_value).toBeGreaterThan((c1.result as any).order_value);
  });

  it('rejects insert before root', async () => {
    await createDocmem('root0001');
    const res = await insertBefore('root0001', 'text', 'msg', 'u', 'a');
    expect(res.success).toBe(false);
    expect(res.error).toContain('root node');
  });

  it('inserts between two existing siblings', async () => {
    await createDocmem('root0001');
    const c1 = await append('root0001', 'First', 'msg', 'u', 'a');
    const c2 = await append('root0001', 'Second', 'msg', 'u', 'a');
    const c2Id = (c2.result as any).id;

    const res = await insertBefore(c2Id, 'Between', 'msg', 'u', 'a');
    expect(res.success).toBe(true);
    const node = res.result as any;
    expect(node.order_value).toBeGreaterThan((c1.result as any).order_value);
    expect(node.order_value).toBeLessThan((c2.result as any).order_value);
  });
});
