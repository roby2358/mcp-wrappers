export const tools = [
  {
    name: 'create_docmem',
    description: 'Create a new docmem tree with a root node. Returns the root node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        root_id: { type: 'string', description: 'Optional custom root ID (8-char). Auto-generated if omitted.' },
        content: { type: 'string', description: 'Optional root node content.' },
        context_type: { type: 'string', description: 'Node role type (e.g., "root"). Max 24 chars.' },
        context_name: { type: 'string', description: 'Context metadata name. Max 24 chars.' },
        context_value: { type: 'string', description: 'Context metadata value. Max 24 chars.' },
      },
      required: ['context_type', 'context_name', 'context_value'],
    },
  },
  {
    name: 'list_docmems',
    description: 'List all docmem root nodes with their metadata.',
    inputSchema: { type: 'object' as const, properties: {} },
  },
  {
    name: 'append',
    description: 'Append a new node as the last child of the specified parent. Returns the new node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        parent_id: { type: 'string', description: 'ID of the parent node.' },
        content: { type: 'string', description: 'Content for the new node.' },
        context_type: { type: 'string', description: 'Node role type. Max 24 chars.' },
        context_name: { type: 'string', description: 'Context metadata name. Max 24 chars.' },
        context_value: { type: 'string', description: 'Context metadata value. Max 24 chars.' },
        readonly: { type: 'number', description: 'Set to 1 to make the node readonly. Default 0.' },
      },
      required: ['parent_id', 'content', 'context_type', 'context_name', 'context_value'],
    },
  },
  {
    name: 'insert_before',
    description: 'Insert a new node as a sibling immediately before the target node. Returns the new node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        target_id: { type: 'string', description: 'ID of the target node to insert before.' },
        content: { type: 'string', description: 'Content for the new node.' },
        context_type: { type: 'string', description: 'Node role type. Max 24 chars.' },
        context_name: { type: 'string', description: 'Context metadata name. Max 24 chars.' },
        context_value: { type: 'string', description: 'Context metadata value. Max 24 chars.' },
        readonly: { type: 'number', description: 'Set to 1 to make the node readonly. Default 0.' },
      },
      required: ['target_id', 'content', 'context_type', 'context_name', 'context_value'],
    },
  },
  {
    name: 'insert_after',
    description: 'Insert a new node as a sibling immediately after the target node. Returns the new node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        target_id: { type: 'string', description: 'ID of the target node to insert after.' },
        content: { type: 'string', description: 'Content for the new node.' },
        context_type: { type: 'string', description: 'Node role type. Max 24 chars.' },
        context_name: { type: 'string', description: 'Context metadata name. Max 24 chars.' },
        context_value: { type: 'string', description: 'Context metadata value. Max 24 chars.' },
        readonly: { type: 'number', description: 'Set to 1 to make the node readonly. Default 0.' },
      },
      required: ['target_id', 'content', 'context_type', 'context_name', 'context_value'],
    },
  },
  {
    name: 'find',
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
    name: 'delete_node',
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
    name: 'update_content',
    description: 'Update the content of a node. Requires optimistic locking hash. Returns the updated node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        id: { type: 'string', description: 'ID of the node to update.' },
        content: { type: 'string', description: 'New content.' },
        expected_hash: { type: 'string', description: 'Current hash of the node for optimistic locking.' },
      },
      required: ['id', 'content', 'expected_hash'],
    },
  },
  {
    name: 'update_context',
    description: 'Update the context metadata of a node. Requires optimistic locking hash. Returns the updated node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        id: { type: 'string', description: 'ID of the node to update.' },
        context_type: { type: 'string', description: 'New context type. Max 24 chars.' },
        context_name: { type: 'string', description: 'New context name. Max 24 chars.' },
        context_value: { type: 'string', description: 'New context value. Max 24 chars.' },
        expected_hash: { type: 'string', description: 'Current hash of the node for optimistic locking.' },
      },
      required: ['id', 'context_type', 'context_name', 'context_value', 'expected_hash'],
    },
  },
  {
    name: 'copy_node',
    description: 'Deep copy a node and all descendants to a new position. Returns the new root of the copied subtree.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        source_id: { type: 'string', description: 'ID of the node to copy.' },
        target_id: { type: 'string', description: 'ID of the target node for positioning.' },
        position: { type: 'string', enum: ['child', 'before', 'after'], description: 'Where to place the copy relative to target.' },
      },
      required: ['source_id', 'target_id', 'position'],
    },
  },
  {
    name: 'move_node',
    description: 'Move a node to a new position within the same docmem tree. Requires optimistic locking hash. Returns the updated node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        source_id: { type: 'string', description: 'ID of the node to move.' },
        target_id: { type: 'string', description: 'ID of the target node for positioning.' },
        position: { type: 'string', enum: ['child', 'before', 'after'], description: 'Where to place the node relative to target.' },
        expected_hash: { type: 'string', description: 'Current hash of the source node for optimistic locking.' },
      },
      required: ['source_id', 'target_id', 'position', 'expected_hash'],
    },
  },
  {
    name: 'summarize',
    description: 'Compress sibling leaf nodes under a new summary parent. Returns the new summary node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        node_ids: { type: 'array', items: { type: 'string' }, description: 'IDs of sibling leaf nodes to summarize.' },
        content: { type: 'string', description: 'Summary content.' },
        context_type: { type: 'string', description: 'Summary node context type. Max 24 chars.' },
        context_name: { type: 'string', description: 'Summary node context name. Max 24 chars.' },
        context_value: { type: 'string', description: 'Summary node context value. Max 24 chars.' },
      },
      required: ['node_ids', 'content', 'context_type', 'context_name', 'context_value'],
    },
  },
  {
    name: 'serialize',
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
    name: 'expand_to_length',
    description: 'Return nodes fitting within a token budget using reverse-BFS priority, budget consumption, and DFS render.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        node_id: { type: 'string', description: 'ID of the starting node.' },
        token_budget: { type: 'number', description: 'Maximum token count for the result.' },
      },
      required: ['node_id', 'token_budget'],
    },
  },
  {
    name: 'structure',
    description: 'Return the indented tree structure from a node without content.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        node_id: { type: 'string', description: 'ID of the starting node.' },
      },
      required: ['node_id'],
    },
  },
  {
    name: 'get_root',
    description: 'Walk up the parent chain to find the root node of the tree containing the given node.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        node_id: { type: 'string', description: 'ID of any node in the tree.' },
      },
      required: ['node_id'],
    },
  },
  {
    name: 'query_nodes',
    description: 'Free-form SQL SELECT against the nodes table (DuckDB). Returns up to 20 rows. Supports full DuckDB SQL: CTEs, window functions, aggregates, self-joins, regexp_matches, etc. Columns: id, parent_id, content, order_value, token_count, created_at, updated_at, context_type, context_name, context_value, readonly, hash.',
    inputSchema: {
      type: 'object' as const,
      properties: {
        sql: { type: 'string', description: 'Full SELECT statement (e.g. "SELECT id, content FROM nodes WHERE context_type = \'message\' ORDER BY created_at DESC"). LIMIT 20 is appended automatically.' },
      },
      required: ['sql'],
    },
  },
  {
    name: 'import_toml',
    description: 'Import a docmem tree from a TOML string. Each TOML section is a node with parent-node-id, context, and content fields. Returns the root node(s).',
    inputSchema: {
      type: 'object' as const,
      properties: {
        toml: { type: 'string', description: 'TOML string defining the tree. Each [section] is a node ID with parent-node-id, context ("type:name:value"), and content fields.' },
      },
      required: ['toml'],
    },
  },
  {
    name: 'export_toml',
    description: 'Export a docmem subtree as a TOML string. DFS traversal from the given node (inclusive).',
    inputSchema: {
      type: 'object' as const,
      properties: {
        node_id: { type: 'string', description: 'ID of the root node to export from.' },
      },
      required: ['node_id'],
    },
  },
];
