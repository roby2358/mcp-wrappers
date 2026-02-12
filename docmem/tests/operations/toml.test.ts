import { describe, it, expect, beforeAll, beforeEach } from 'vitest';
import { setupTestDb, clearTestDb } from '../setup.js';
import { importToml, exportToml } from '../../src/operations/toml.js';
import { find } from '../../src/operations/crud.js';

describe('toml operations', () => {
  beforeAll(async () => { await setupTestDb(); });
  beforeEach(async () => { await clearTestDb(); });

  it('imports a single root node', async () => {
    const toml = `[stooges]
parent-node-id=""
context="root:comedy:classic"
content="The Three Stooges"
`;
    const res = await importToml(toml);
    expect(res.success).toBe(true);
    const roots = res.result as any[];
    expect(roots).toHaveLength(1);
    expect(roots[0].id).toBe('stooges');
    expect(roots[0].parent_id).toBeNull();
    expect(roots[0].context_type).toBe('root');
    expect(roots[0].readonly).toBe(0);
  });

  it('imports a multi-level tree (three stooges)', async () => {
    const toml = `[stooges]
parent-node-id=""
context="root:comedy:classic"
content="The Three Stooges"

[larry]
parent-node-id="stooges"
context="member:stooge:fine"
content="Larry Fine"

[curly]
parent-node-id="stooges"
context="member:stooge:howard"
content="Curly Howard"

[moe]
parent-node-id="stooges"
context="member:stooge:howard"
content="Moe Howard"

[slap]
parent-node-id="moe"
context="action:gag:physical"
content="Moe slaps Larry"
`;
    const res = await importToml(toml);
    expect(res.success).toBe(true);

    // Verify root
    const root = (await find('stooges')).result as any;
    expect(root.content).toBe('The Three Stooges');
    expect(root.parent_id).toBeNull();

    // Verify children ordering
    const larry = (await find('larry')).result as any;
    expect(larry.parent_id).toBe('stooges');
    expect(larry.order_value).toBe(1.0);

    const curly = (await find('curly')).result as any;
    expect(curly.parent_id).toBe('stooges');
    expect(curly.order_value).toBe(2.0);

    const moe = (await find('moe')).result as any;
    expect(moe.parent_id).toBe('stooges');
    expect(moe.order_value).toBe(3.0);

    // Verify grandchild
    const slap = (await find('slap')).result as any;
    expect(slap.parent_id).toBe('moe');
    expect(slap.order_value).toBe(1.0);
    expect(slap.context_type).toBe('action');
    expect(slap.context_name).toBe('gag');
    expect(slap.context_value).toBe('physical');
  });

  it('exports a tree to TOML', async () => {
    const toml = `[stooges]
parent-node-id=""
context="root:comedy:classic"
content="The Three Stooges"

[larry]
parent-node-id="stooges"
context="member:stooge:fine"
content="Larry Fine"

[curly]
parent-node-id="stooges"
context="member:stooge:howard"
content="Curly Howard"
`;
    await importToml(toml);

    const res = await exportToml('stooges');
    expect(res.success).toBe(true);
    const exported = res.result as string;

    // Verify the exported TOML contains expected sections
    expect(exported).toContain('[stooges]');
    expect(exported).toContain('[larry]');
    expect(exported).toContain('[curly]');
    expect(exported).toContain('parent-node-id = ""');
    expect(exported).toContain('parent-node-id = "stooges"');
    expect(exported).toContain('context = "root:comedy:classic"');
    expect(exported).toContain('content = "The Three Stooges"');
  });

  it('round-trips: import then export preserves structure', async () => {
    const toml = `[root01]
parent-node-id=""
context="root:test:roundtrip"
content="Root node"

[child1]
parent-node-id="root01"
context="msg:user:alice"
content="First child"

[child2]
parent-node-id="root01"
context="msg:user:bob"
content="Second child"

[grand1]
parent-node-id="child1"
context="reply:user:carol"
content="Grandchild"
`;
    const importRes = await importToml(toml);
    expect(importRes.success).toBe(true);

    const exportRes = await exportToml('root01');
    expect(exportRes.success).toBe(true);
    const exported = exportRes.result as string;

    // Re-import the exported TOML into a fresh DB after clearing
    await clearTestDb();
    const reimportRes = await importToml(exported);
    expect(reimportRes.success).toBe(true);

    // Verify all nodes survived the round-trip
    const root = (await find('root01')).result as any;
    expect(root.content).toBe('Root node');
    expect(root.context_type).toBe('root');

    const child1 = (await find('child1')).result as any;
    expect(child1.parent_id).toBe('root01');
    expect(child1.content).toBe('First child');

    const grand1 = (await find('grand1')).result as any;
    expect(grand1.parent_id).toBe('child1');
    expect(grand1.content).toBe('Grandchild');
  });

  it('rejects invalid TOML syntax', async () => {
    const res = await importToml('not valid toml [[[');
    expect(res.success).toBe(false);
    expect(res.error).toContain('Failed to parse TOML');
  });

  it('rejects section with missing parent in TOML', async () => {
    const toml = `[orphan]
parent-node-id="nonexistent"
context="msg:user:alice"
content="I have no parent"
`;
    const res = await importToml(toml);
    expect(res.success).toBe(false);
    expect(res.error).toContain('nonexistent');
    expect(res.error).toContain('does not exist');
  });

  it('rejects section with bad context format', async () => {
    const toml = `[badctx]
parent-node-id=""
context="only-one-part"
content="Bad context"
`;
    const res = await importToml(toml);
    expect(res.success).toBe(false);
    expect(res.error).toContain('invalid context format');
  });

  it('rejects empty TOML', async () => {
    const res = await importToml('');
    expect(res.success).toBe(false);
    expect(res.error).toContain('no node sections');
  });

  it('rejects duplicate node IDs that already exist in DB', async () => {
    const toml = `[existing]
parent-node-id=""
context="root:test:dup"
content="First import"
`;
    await importToml(toml);
    const res = await importToml(toml);
    expect(res.success).toBe(false);
    expect(res.error).toContain('already exists');
  });

  it('exports returns error for nonexistent node', async () => {
    const res = await exportToml('nonexist');
    expect(res.success).toBe(false);
    expect(res.error).toContain('not found');
  });

  it('exports a subtree (not just root)', async () => {
    const toml = `[root]
parent-node-id=""
context="root:test:sub"
content="Root"

[branch]
parent-node-id="root"
context="branch:test:sub"
content="Branch"

[leaf]
parent-node-id="branch"
context="leaf:test:sub"
content="Leaf"
`;
    await importToml(toml);

    const res = await exportToml('branch');
    expect(res.success).toBe(true);
    const exported = res.result as string;
    expect(exported).toContain('[branch]');
    expect(exported).toContain('[leaf]');
    expect(exported).not.toContain('[root]');
  });

  it('rejects section missing content field', async () => {
    const toml = `[nofield]
parent-node-id=""
context="root:test:missing"
`;
    const res = await importToml(toml);
    expect(res.success).toBe(false);
    expect(res.error).toContain('content');
  });
});
