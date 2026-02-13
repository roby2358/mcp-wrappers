import { describe, it, expect, beforeAll, beforeEach } from 'vitest';
import { setupTestDb, clearTestDb } from '../setup.js';
import { createDocmem } from '../../src/operations/docmem.js';
import { append } from '../../src/operations/crud.js';
import { serialize, expandToLength, structure, getRoot, queryNodes } from '../../src/operations/query.js';

describe('query operations', () => {
  beforeAll(async () => { await setupTestDb(); });
  beforeEach(async () => { await clearTestDb(); });

  describe('serialize', () => {
    it('serializes descendants depth-first', async () => {
      await createDocmem('root0001');
      await append('root0001', 'Line one', 'msg', 'u', 'a');
      await append('root0001', 'Line two', 'msg', 'u', 'a');
      const res = await serialize('root0001');
      expect(res.success).toBe(true);
      expect(res.result).toBe('Line one\n\nLine two');
    });

    it('excludes nodes with empty text', async () => {
      await createDocmem('root0001');
      await append('root0001', '', 'msg', 'u', 'a');
      await append('root0001', 'Visible', 'msg', 'u', 'a');
      const res = await serialize('root0001');
      expect(res.result).toBe('Visible');
    });

    it('excludes the starting node from output', async () => {
      await createDocmem('root0001');
      await append('root0001', 'Child', 'msg', 'u', 'a');
      const res = await serialize('root0001');
      expect(res.result).toBe('Child');
    });
  });

  describe('expandToLength', () => {
    it('returns nodes within budget', async () => {
      await createDocmem('root0001');
      await append('root0001', 'Short', 'msg', 'u', 'a');
      await append('root0001', 'Also short', 'msg', 'u', 'a');
      const res = await expandToLength('root0001', 100);
      expect(res.success).toBe(true);
      const text = res.result as string;
      expect(text).toContain('Short');
      expect(text).toContain('Also short');
      // 3 blocks: root + 2 children, separated by double newlines
      expect(text.split('\n\n').length).toBe(3);
    });

    it('truncates when budget is exceeded', async () => {
      await createDocmem('root0001');
      await append('root0001', 'a'.repeat(40), 'msg', 'u', 'a'); // 10 tokens
      await append('root0001', 'b'.repeat(40), 'msg', 'u', 'a'); // 10 tokens
      // Budget = 5, root is 0 tokens (empty text), first child is 10 tokens -> only root fits
      const res = await expandToLength('root0001', 5);
      expect(res.success).toBe(true);
      const text = res.result as string;
      // Only root (metadata only, no content)
      expect(text.split('\n\n').length).toBe(1);
      expect(text).toContain('root0001');
    });
  });

  describe('structure', () => {
    it('returns indented tree', async () => {
      await createDocmem('root0001');
      const c1 = await append('root0001', 'Child', 'msg', 'u', 'a');
      const c1Id = (c1.result as any).id;
      await append(c1Id, 'Grandchild', 'msg', 'u', 'a');

      const res = await structure('root0001');
      expect(res.success).toBe(true);
      const lines = (res.result as string).split('\n');
      expect(lines).toHaveLength(3);
      expect(lines[0]).toMatch(/^- root0001/);
      expect(lines[1]).toMatch(/^  - /);
      expect(lines[2]).toMatch(/^    - /);
    });
  });

  describe('getRoot', () => {
    it('returns indented ancestor path from root to child', async () => {
      await createDocmem('root0001');
      const c1 = await append('root0001', 'Child', 'msg', 'u', 'a');
      const c1Id = (c1.result as any).id;
      const c2 = await append(c1Id, 'Grandchild', 'msg', 'u', 'a');
      const c2Id = (c2.result as any).id;

      const res = await getRoot(c2Id);
      expect(res.success).toBe(true);
      const lines = (res.result as string).split('\n');
      expect(lines).toHaveLength(3);
      expect(lines[0]).toMatch(/^- root0001/);
      expect(lines[1]).toMatch(/^  - /);
      expect(lines[2]).toMatch(/^    - /);
      expect(lines[2]).toContain(c2Id);
    });

    it('returns single line if already root', async () => {
      await createDocmem('root0001');
      const res = await getRoot('root0001');
      expect(res.success).toBe(true);
      const lines = (res.result as string).split('\n');
      expect(lines).toHaveLength(1);
      expect(lines[0]).toMatch(/^- root0001/);
    });
  });

  describe('queryNodes', () => {
    it('finds nodes by context_type', async () => {
      await createDocmem('root0001');
      await append('root0001', 'Hello', 'message', 'user', 'alice');
      await append('root0001', 'World', 'message', 'user', 'bob');
      const res = await queryNodes("SELECT * FROM nodes WHERE context_type = 'message'");
      expect(res.success).toBe(true);
      expect((res.result as any[]).length).toBe(2);
    });

    it('finds nodes by content LIKE', async () => {
      await createDocmem('root0001');
      await append('root0001', 'The quick brown fox', 'msg', 'u', 'a');
      await append('root0001', 'Lazy dog', 'msg', 'u', 'a');
      const res = await queryNodes("SELECT * FROM nodes WHERE content LIKE '%fox%'");
      expect(res.success).toBe(true);
      const nodes = res.result as any[];
      expect(nodes.length).toBe(1);
      expect(nodes[0].content).toBe('The quick brown fox');
    });

    it('returns at most 20 rows', async () => {
      await createDocmem('root0001');
      for (let i = 0; i < 25; i++) {
        await append('root0001', `Node ${i}`, 'msg', 'u', 'a');
      }
      const res = await queryNodes('SELECT * FROM nodes');
      expect(res.success).toBe(true);
      expect((res.result as any[]).length).toBe(20);
    });

    it('returns error for invalid SQL', async () => {
      const res = await queryNodes('NOT A VALID QUERY');
      expect(res.success).toBe(false);
      expect(res.error).toContain('Query failed');
    });
  });
});
