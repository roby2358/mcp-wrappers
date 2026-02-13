import { ToolResponse } from '../domain/types.js';
import { createDocmem } from '../operations/docmem.js';
import { append, find, deleteNode, updateContent, updateContext } from '../operations/crud.js';
import { insertBefore, insertAfter } from '../operations/insert.js';
import { serialize, expandToLength, getRoot, queryNodes } from '../operations/query.js';
import { copyNode, moveNode, addSummary } from '../operations/tree.js';

type Mode = 'append-child' | 'before' | 'after';

function mapMode(mode: Mode): 'child' | 'before' | 'after' {
  return mode === 'append-child' ? 'child' : mode;
}

function formatResult(toolName: string, action: string): string {
  return `result> ${toolName} ${action}`;
}

function formatQuery(toolName: string, data: string): string {
  return `result> ${toolName}:\n${data}`;
}

function formatError(error: string): string {
  return `error> ${error}`;
}

export async function handleTool(name: string, args: Record<string, unknown>): Promise<string> {
  try {
    return await dispatch(name, args);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return formatError(message);
  }
}

async function dispatch(name: string, args: Record<string, unknown>): Promise<string> {
  switch (name) {
    case 'docmem_create': {
      const res = await createDocmem(args.root_id as string | undefined);
      if (!res.success) return formatError(res.error);
      const node = res.result as any;
      return formatResult('docmem_create', `created docmem: ${node.id}`);
    }

    case 'docmem_create_node': {
      const mode = args.mode as Mode;
      const targetId = args.target_id as string;
      const content = args.content as string;
      const ctxType = args.context_type as string;
      const ctxName = args.context_name as string;
      const ctxValue = args.context_value as string;
      const readonly = args.readonly as number | undefined;

      let res: ToolResponse;
      if (mode === 'append-child') {
        res = await append(targetId, content, ctxType, ctxName, ctxValue, readonly);
      } else if (mode === 'before') {
        res = await insertBefore(targetId, content, ctxType, ctxName, ctxValue, readonly);
      } else {
        res = await insertAfter(targetId, content, ctxType, ctxName, ctxValue, readonly);
      }

      if (!res.success) return formatError(res.error);
      const node = res.result as any;
      return formatResult('docmem_create_node', `${mode}: ${node.id}`);
    }

    case 'docmem_find': {
      const res = await find(args.id as string);
      if (!res.success) return formatError(res.error);
      return formatQuery('docmem_find', JSON.stringify(res.result, null, 2));
    }

    case 'docmem_delete': {
      const res = await deleteNode(args.id as string);
      if (!res.success) return formatError(res.error);
      return formatResult('docmem_delete', `deleted node: ${args.id}`);
    }

    case 'docmem_update_content': {
      const res = await updateContent(args.id as string, args.content as string);
      if (!res.success) return formatError(res.error);
      return formatResult('docmem_update_content', `updated node: ${args.id}`);
    }

    case 'docmem_update_context': {
      const res = await updateContext(
        args.id as string,
        args.context_type as string,
        args.context_name as string,
        args.context_value as string,
      );
      if (!res.success) return formatError(res.error);
      return formatResult('docmem_update_context', `updated node: ${args.id}`);
    }

    case 'docmem_copy_node': {
      const mode = args.mode as Mode;
      const res = await copyNode(
        args.source_id as string,
        args.target_id as string,
        mapMode(mode),
      );
      if (!res.success) return formatError(res.error);
      const node = res.result as any;
      return formatResult('docmem_copy_node', `${mode}: ${node.id}`);
    }

    case 'docmem_move_node': {
      const mode = args.mode as Mode;
      const res = await moveNode(
        args.source_id as string,
        args.target_id as string,
        mapMode(mode),
      );
      if (!res.success) return formatError(res.error);
      return formatResult('docmem_move_node', String(mode));
    }

    case 'docmem_add_summary': {
      const res = await addSummary(
        args.context_type as string,
        args.context_name as string,
        args.context_value as string,
        args.content as string,
        args.start_node_id as string,
        args.end_node_id as string,
      );
      if (!res.success) return formatError(res.error);
      const node = res.result as any;
      return formatResult('docmem_add_summary', `added summary node: ${node.id}`);
    }

    case 'docmem_serialize': {
      const res = await serialize(args.node_id as string);
      if (!res.success) return formatError(res.error);
      return formatQuery('docmem_serialize', res.result as string);
    }

    case 'docmem_expand_to_length': {
      const tokenBudget = parseInt(args.max_tokens as string, 10);
      if (isNaN(tokenBudget)) {
        return formatError('max_tokens must be a valid number string. Example: "1000".');
      }
      const res = await expandToLength(args.node_id as string, tokenBudget);
      if (!res.success) return formatError(res.error);
      return formatQuery('docmem_expand_to_length', res.result as string);
    }

    case 'docmem_get_root': {
      const res = await getRoot(args.node_id as string);
      if (!res.success) return formatError(res.error);
      return formatQuery('docmem_get_root', res.result as string);
    }

    case 'docmem_query_nodes': {
      const res = await queryNodes(args.sql as string);
      if (!res.success) return formatError(res.error);
      return formatQuery('docmem_query_nodes', JSON.stringify(res.result, null, 2));
    }

    default:
      return formatError(`Unknown tool: '${name}'. Available tools have the 'docmem_' prefix.`);
  }
}
