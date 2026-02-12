import { describe, it, expect, beforeAll, beforeEach } from 'vitest';
import { setupTestDb, clearTestDb } from '../setup.js';
import { createDocmem, listDocmems } from '../../src/operations/docmem.js';

describe('docmem operations', () => {
  beforeAll(async () => { await setupTestDb(); });
  beforeEach(async () => { await clearTestDb(); });

  it('creates a docmem with auto-generated id', async () => {
    const res = await createDocmem(undefined);
    expect(res.success).toBe(true);
    const node = res.result as any;
    expect(node.id).toHaveLength(8);
    expect(node.parent_id).toBeNull();
    expect(node.content).toBe('');
    expect(node.context_type).toBe('');
  });

  it('creates a docmem with custom id', async () => {
    const res = await createDocmem('myroot01');
    expect(res.success).toBe(true);
    expect((res.result as any).id).toBe('myroot01');
  });

  it('fails on duplicate id', async () => {
    await createDocmem('dup00001');
    const res = await createDocmem('dup00001');
    expect(res.success).toBe(false);
    expect(res.error).toContain('already exists');
  });

  it('lists docmems', async () => {
    await createDocmem('root0001');
    await createDocmem('root0002');
    const res = await listDocmems();
    expect(res.success).toBe(true);
    const text = res.result as string;
    expect(text).toContain('root0001');
    expect(text).toContain('root0002');
  });
});
