import { describe, it, expect, beforeAll, beforeEach } from 'vitest';
import { setupTestDb, clearTestDb } from '../setup.js';
import { createDocmem } from '../../src/operations/docmem.js';
import { append, find } from '../../src/operations/crud.js';
import { copyNode, moveNode, summarize } from '../../src/operations/tree.js';
import { getChildren } from '../../src/db/queries.js';

describe('tree operations', () => {
  beforeAll(async () => { await setupTestDb(); });
  beforeEach(async () => { await clearTestDb(); });

  describe('copyNode', () => {
    it('deep copies a subtree as child', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      const c1 = await append('root0001', 'Parent', 'msg', 'u', 'a');
      const c1Id = (c1.result as any).id;
      await append(c1Id, 'Child of parent', 'msg', 'u', 'a');

      await createDocmem('root0002', '', 'root', 'x', 'y');
      const res = await copyNode(c1Id, 'root0002', 'child');
      expect(res.success).toBe(true);

      const copiedRoot = res.result as any;
      expect(copiedRoot.id).not.toBe(c1Id);
      expect(copiedRoot.parent_id).toBe('root0002');
      expect(copiedRoot.content).toBe('Parent');

      // Check children were copied
      const copiedChildren = await getChildren(copiedRoot.id);
      expect(copiedChildren).toHaveLength(1);
      expect(copiedChildren[0].content).toBe('Child of parent');
    });

    it('copies as sibling before', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      const c1 = await append('root0001', 'First', 'msg', 'u', 'a');
      const c2 = await append('root0001', 'Second', 'msg', 'u', 'a');
      const c2Id = (c2.result as any).id;

      const c1Id = (c1.result as any).id;
      const res = await copyNode(c1Id, c2Id, 'before');
      expect(res.success).toBe(true);
      expect((res.result as any).parent_id).toBe('root0001');
    });
  });

  describe('moveNode', () => {
    it('moves a node as child of another', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      const c1 = await append('root0001', 'A', 'msg', 'u', 'a');
      const c2 = await append('root0001', 'B', 'msg', 'u', 'a');
      const c1Id = (c1.result as any).id;
      const c2Node = (c2.result as any);

      const res = await moveNode(c2Node.id, c1Id, 'child', c2Node.hash);
      expect(res.success).toBe(true);
      expect((res.result as any).parent_id).toBe(c1Id);
    });

    it('prevents cycle (move to own descendant)', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      const c1 = await append('root0001', 'Parent', 'msg', 'u', 'a');
      const c1Id = (c1.result as any).id;
      const c2 = await append(c1Id, 'Child', 'msg', 'u', 'a');
      const c2Id = (c2.result as any).id;
      const c1Node = (await find(c1Id)).result as any;

      const res = await moveNode(c1Id, c2Id, 'child', c1Node.hash);
      expect(res.success).toBe(false);
      expect(res.error).toContain('cycle');
    });

    it('prevents cross-tree moves', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      const c1 = await append('root0001', 'A', 'msg', 'u', 'a');
      await createDocmem('root0002', '', 'root', 'x', 'y');
      const c1Node = (c1.result as any);

      const res = await moveNode(c1Node.id, 'root0002', 'child', c1Node.hash);
      expect(res.success).toBe(false);
      expect(res.error).toContain('same docmem tree');
    });
  });

  describe('summarize', () => {
    it('creates summary node and reparents children', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      const c1 = await append('root0001', 'Memory 1', 'msg', 'u', 'a');
      const c2 = await append('root0001', 'Memory 2', 'msg', 'u', 'a');
      const c1Id = (c1.result as any).id;
      const c2Id = (c2.result as any).id;

      const res = await summarize([c1Id, c2Id], 'Summary of memories', 'summary', 's', 'v');
      expect(res.success).toBe(true);

      const summaryNode = res.result as any;
      expect(summaryNode.content).toBe('Summary of memories');
      expect(summaryNode.parent_id).toBe('root0001');

      // Children should be reparented to summary
      const children = await getChildren(summaryNode.id);
      expect(children).toHaveLength(2);
      expect(children.map(c => c.id).sort()).toEqual([c1Id, c2Id].sort());
    });

    it('rejects non-leaf nodes', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      const c1 = await append('root0001', 'Parent', 'msg', 'u', 'a');
      const c1Id = (c1.result as any).id;
      await append(c1Id, 'Grandchild', 'msg', 'u', 'a');

      const res = await summarize([c1Id], 'Summary', 'summary', 's', 'v');
      expect(res.success).toBe(false);
      expect(res.error).toContain('children');
    });

    it('rejects nodes with different parents', async () => {
      await createDocmem('root0001', '', 'root', 'a', 'b');
      const c1 = await append('root0001', 'A', 'msg', 'u', 'a');
      await createDocmem('root0002', '', 'root', 'x', 'y');
      const c2 = await append('root0002', 'B', 'msg', 'u', 'a');

      const res = await summarize([(c1.result as any).id, (c2.result as any).id], 'Sum', 'summary', 's', 'v');
      expect(res.success).toBe(false);
      expect(res.error).toContain('same parent');
    });
  });
});
