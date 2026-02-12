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
      await createDocmem('root0001', '', 'root', 'a', 'b');
      await append('root0001', 'Line one', 'msg', 'u', 'a');
      await append('root0001', 'Line two', 'msg', 'u', 'a');
      const res = await serialize('root0001');
      expect(res.success).toBe(true);
      expect(res.result).toBe('Line one\n\nLine two');
    });

    it('excludes nodes with empty text', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      await append('root0001', '', 'msg', 'u', 'a');
      await append('root0001', 'Visible', 'msg', 'u', 'a');
      const res = await serialize('root0001');
      expect(res.result).toBe('Visible');
    });

    it('excludes the starting node from output', async () => {
      await createDocmem('root0001', 'Root text', 'root', 'a', 'b');
      await append('root0001', 'Child', 'msg', 'u', 'a');
      const res = await serialize('root0001');
      expect(res.result).toBe('Child');
    });
  });

  describe('expandToLength', () => {
    it('returns nodes within budget', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      await append('root0001', 'Short', 'msg', 'u', 'a');
      await append('root0001', 'Also short', 'msg', 'u', 'a');
      const res = await expandToLength('root0001', 100);
      expect(res.success).toBe(true);
      expect((res.result as any[]).length).toBe(3); // root + 2 children
    });

    it('truncates when budget is exceeded', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      await append('root0001', 'a'.repeat(40), 'msg', 'u', 'a'); // 10 tokens
      await append('root0001', 'b'.repeat(40), 'msg', 'u', 'a'); // 10 tokens
      // Budget = 5, root is 0 tokens (empty text), first child is 10 tokens -> only root fits
      const res = await expandToLength('root0001', 5);
      expect(res.success).toBe(true);
      expect((res.result as any[]).length).toBe(1); // just root
    });
  });

  describe('structure', () => {
    it('returns indented tree', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
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
    it('returns root from a child', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      const c1 = await append('root0001', 'Child', 'msg', 'u', 'a');
      const childId = (c1.result as any).id;

      const res = await getRoot(childId);
      expect(res.success).toBe(true);
      expect((res.result as any).id).toBe('root0001');
    });

    it('returns itself if already root', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      const res = await getRoot('root0001');
      expect(res.success).toBe(true);
      expect((res.result as any).id).toBe('root0001');
    });
  });

  describe('queryNodes', () => {
    it('finds nodes by context_type', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      await append('root0001', 'Hello', 'message', 'user', 'alice');
      await append('root0001', 'World', 'message', 'user', 'bob');
      const res = await queryNodes("SELECT * FROM nodes WHERE context_type = 'message'");
      expect(res.success).toBe(true);
      expect((res.result as any[]).length).toBe(2);
    });

    it('finds nodes by content LIKE', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      await append('root0001', 'The quick brown fox', 'msg', 'u', 'a');
      await append('root0001', 'Lazy dog', 'msg', 'u', 'a');
      const res = await queryNodes("SELECT * FROM nodes WHERE content LIKE '%fox%'");
      expect(res.success).toBe(true);
      const nodes = res.result as any[];
      expect(nodes.length).toBe(1);
      expect(nodes[0].content).toBe('The quick brown fox');
    });

    it('returns at most 20 rows', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      for (let i = 0; i < 25; i++) {
        await append('root0001', `Node ${i}`, 'msg', 'u', 'a');
      }
      const res = await queryNodes('SELECT * FROM nodes');
      expect(res.success).toBe(true);
      expect((res.result as any[]).length).toBe(20);
    });

    it('supports aggregates and GROUP BY', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      await append('root0001', 'A', 'message', 'user', 'alice');
      await append('root0001', 'B', 'message', 'user', 'bob');
      await append('root0001', 'C', 'note', 'user', 'alice');
      const res = await queryNodes("SELECT context_type, count(*) as cnt FROM nodes GROUP BY context_type ORDER BY cnt DESC");
      expect(res.success).toBe(true);
      const rows = res.result as any[];
      expect(rows[0].context_type).toBe('message');
      expect(Number(rows[0].cnt)).toBe(2);
    });

    it('supports self-joins', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      await append('root0001', 'Child', 'msg', 'u', 'a');
      const res = await queryNodes("SELECT c.id, p.id as parent FROM nodes c JOIN nodes p ON c.parent_id = p.id WHERE p.id = 'root0001'");
      expect(res.success).toBe(true);
      expect((res.result as any[]).length).toBe(1);
    });

    it('returns error for invalid SQL', async () => {
      const res = await queryNodes('NOT A VALID QUERY');
      expect(res.success).toBe(false);
      expect(res.error).toContain('Query failed');
    });
  });
});
