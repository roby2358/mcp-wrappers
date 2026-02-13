export const tools = [
  {
    name: 'docmem_create',
    description: 'Create a new docmem tree with a root node. Returns the root node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        root_id: { type: 'string', description: 'Optional custom root ID (8-char). Auto-generated if omitted.' },
      },
    },
  },
{
    name: 'docmem_create_node',
    description: 'Create a new node relative to a target. Mode "append-child" adds as last child; "before"/"after" insert as siblings.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        target_id: { type: 'string', description: 'ID of the target node (parent for append-child, sibling for before/after).' },
        content: { type: 'string', description: 'Content for the new node.' },
        context_type: { type: 'string', description: 'Node role type. Max 24 chars.' },
        context_name: { type: 'string', description: 'Context metadata name. Max 24 chars.' },
        context_value: { type: 'string', description: 'Context metadata value. Max 24 chars.' },
        mode: { type: 'string', enum: ['append-child', 'before', 'after'], description: 'Placement mode relative to target.' },
        readonly: { type: 'number', description: 'Set to 1 to make the node readonly. Default 0.' },
      },
      required: ['target_id', 'content', 'context_type', 'context_name', 'context_value', 'mode'],
    },
  },
  {
    name: 'docmem_find',
    description: 'Retrieve a node by its ID. Returns the full node or an error if not found.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        id: { type: 'string', description: 'The node ID to look up.' },
      },
      required: ['id'],
    },
  },
  {
    name: 'docmem_delete',
    description: 'Delete a node and all its descendants. Returns the count of deleted nodes.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        id: { type: 'string', description: 'ID of the node to delete.' },
      },
      required: ['id'],
    },
  },
  {
    name: 'docmem_update_content',
    description: 'Update the content of a node. Returns the updated node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        id: { type: 'string', description: 'ID of the node to update.' },
        content: { type: 'string', description: 'New content.' },
      },
      required: ['id', 'content'],
    },
  },
  {
    name: 'docmem_update_context',
    description: 'Update the context metadata of a node. Returns the updated node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        id: { type: 'string', description: 'ID of the node to update.' },
        context_type: { type: 'string', description: 'New context type. Max 24 chars.' },
        context_name: { type: 'string', description: 'New context name. Max 24 chars.' },
        context_value: { type: 'string', description: 'New context value. Max 24 chars.' },
      },
      required: ['id', 'context_type', 'context_name', 'context_value'],
    },
  },
  {
    name: 'docmem_copy_node',
    description: 'Deep copy a node and all descendants to a new position. Returns the new root of the copied subtree.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        source_id: { type: 'string', description: 'ID of the node to copy.' },
        target_id: { type: 'string', description: 'ID of the target node for positioning.' },
        mode: { type: 'string', enum: ['append-child', 'before', 'after'], description: 'Placement mode relative to target.' },
      },
      required: ['source_id', 'target_id', 'mode'],
    },
  },
  {
    name: 'docmem_move_node',
    description: 'Move a node to a new position within the same docmem tree. Returns the updated node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        source_id: { type: 'string', description: 'ID of the node to move.' },
        target_id: { type: 'string', description: 'ID of the target node for positioning.' },
        mode: { type: 'string', enum: ['append-child', 'before', 'after'], description: 'Placement mode relative to target.' },
      },
      required: ['source_id', 'target_id', 'mode'],
    },
  },
  {
    name: 'docmem_add_summary',
    description: 'Compress a range of sibling leaf nodes under a new summary parent. Specify start and end nodes; all siblings between them (inclusive) are reparented.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        start_node_id: { type: 'string', description: 'ID of the first sibling in the range.' },
        end_node_id: { type: 'string', description: 'ID of the last sibling in the range.' },
        content: { type: 'string', description: 'Summary content.' },
        context_type: { type: 'string', description: 'Summary node context type. Max 24 chars.' },
        context_name: { type: 'string', description: 'Summary node context name. Max 24 chars.' },
        context_value: { type: 'string', description: 'Summary node context value. Max 24 chars.' },
      },
      required: ['start_node_id', 'end_node_id', 'content', 'context_type', 'context_name', 'context_value'],
    },
  },
  {
    name: 'docmem_serialize',
    description: 'Depth-first serialization of all descendant content under a node, joined by double newlines.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        node_id: { type: 'string', description: 'ID of the starting node (excluded from output).' },
      },
      required: ['node_id'],
    },
  },
  {
    name: 'docmem_expand_to_length',
    description: 'Return nodes fitting within a token budget using reverse-BFS priority, budget consumption, and DFS render.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        node_id: { type: 'string', description: 'ID of the starting node.' },
        max_tokens: { type: 'string', description: 'Maximum token count for the result (as a string number).' },
      },
      required: ['node_id', 'max_tokens'],
    },
  },
{
    name: 'docmem_get_root',
    description: 'Walk up the parent chain to find the root node. Returns the indented ancestor path from root down to the given node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        node_id: { type: 'string', description: 'ID of any node in the tree.' },
      },
      required: ['node_id'],
    },
  },
  {
    name: 'docmem_query_nodes',
    description: 'Free-form SQL SELECT against the nodes table (DuckDB). Returns up to 20 rows. Supports full DuckDB SQL: CTEs, window functions, aggregates, self-joins, regexp_matches, etc. Columns: id, parent_id, content, order_value, token_count, created_at, updated_at, context_type, context_name, context_value, readonly, hash.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        sql: { type: 'string', description: 'Full SELECT statement (e.g. "SELECT id, content FROM nodes WHERE context_type = \'message\' ORDER BY created_at DESC"). LIMIT 20 is appended automatically.' },
      },
      required: ['sql'],
    },
  },
];
