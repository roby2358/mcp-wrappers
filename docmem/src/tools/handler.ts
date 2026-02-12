import { ToolResponse } from '../domain/types.js';
import { createDocmem, listDocmems } from '../operations/docmem.js';
import { append, find, deleteNode, updateContent, updateContext } from '../operations/crud.js';
import { insertBefore, insertAfter } from '../operations/insert.js';
import { serialize, expandToLength, structure, getRoot, queryNodes } from '../operations/query.js';
import { copyNode, moveNode, summarize } from '../operations/tree.js';
import { importToml, exportToml } from '../operations/toml.js';

export async function handleTool(name: string, args: Record<string, unknown>): Promise<ToolResponse> {
  switch (name) {
    case 'create_docmem':
      return createDocmem(
        args.root_id as string | undefined,
        args.content as string | undefined,
        args.context_type as string,
        args.context_name as string,
        args.context_value as string,
      );
    case 'list_docmems':
      return listDocmems();
    case 'append':
      return append(
        args.parent_id as string,
        args.content as string,
        args.context_type as string,
        args.context_name as string,
        args.context_value as string,
        args.readonly as number | undefined,
      );
    case 'insert_before':
      return insertBefore(
        args.target_id as string,
        args.content as string,
        args.context_type as string,
        args.context_name as string,
        args.context_value as string,
        args.readonly as number | undefined,
      );
    case 'insert_after':
      return insertAfter(
        args.target_id as string,
        args.content as string,
        args.context_type as string,
        args.context_name as string,
        args.context_value as string,
        args.readonly as number | undefined,
      );
    case 'find':
      return find(args.id as string);
    case 'delete_node':
      return deleteNode(args.id as string);
    case 'update_content':
      return updateContent(
        args.id as string,
        args.content as string,
        args.expected_hash as string,
      );
    case 'update_context':
      return updateContext(
        args.id as string,
        args.context_type as string,
        args.context_name as string,
        args.context_value as string,
        args.expected_hash as string,
      );
    case 'copy_node':
      return copyNode(
        args.source_id as string,
        args.target_id as string,
        args.position as 'child' | 'before' | 'after',
      );
    case 'move_node':
      return moveNode(
        args.source_id as string,
        args.target_id as string,
        args.position as 'child' | 'before' | 'after',
        args.expected_hash as string,
      );
    case 'summarize':
      return summarize(
        args.node_ids as string[],
        args.content as string,
        args.context_type as string,
        args.context_name as string,
        args.context_value as string,
      );
    case 'serialize':
      return serialize(args.node_id as string);
    case 'expand_to_length':
      return expandToLength(args.node_id as string, args.token_budget as number);
    case 'structure':
      return structure(args.node_id as string);
    case 'get_root':
      return getRoot(args.node_id as string);
    case 'query_nodes':
      return queryNodes(args.sql as string);
    case 'import_toml':
      return importToml(args.toml as string);
    case 'export_toml':
      return exportToml(args.node_id as string);
    default:
      return { success: false, result: '', error: `Unknown tool: '${name}'. Use list_tools to see available tools.` };
  }
}
