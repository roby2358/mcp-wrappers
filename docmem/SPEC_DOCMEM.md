# DOCMEM Specification

## Purpose

Docmem stores discrete bits of memory in a hierarchical tree structure. The tree structure is traversable and serializable directly into documents. A parallel vector database for semantic search SHOULD be implemented in the future.

The core insight: LLM output is linear and hierarchical (conversations, documents), but memory is high-dimensional and associative. Docmem makes the compression between these representations explicit and controllable, rather than leaving it implicit in generation.

## Design Principles

### Separation of Concerns
- Docmem MUST handle context construction and memory management.
- The LLM MUST handle decisions and text generation.
- Docmem MUST NOT generate text content except through explicit summarization operations.

### Tree as Document
- Serialization MUST be accomplished through tree traversal.
- Serialization MUST NOT require orchestration or generation logic beyond traversal.
- The reading order of a document MUST be determined by traversal order.

### Visible Compression
- Summarization operations MUST be explicit and auditable.
- Original memory nodes MUST be preserved when summaries are created.
- Summarization MUST be reversible (the original nodes remain accessible).

### Dual Representation (Planned)
- Tree structure MUST provide hierarchy and reading order.
- Vector DB (when implemented) MUST provide semantic access.
- Query operations SHOULD query via vectors and contextualize via tree structure.

## Tree Structure

The tree structure MUST be shallow with clear semantics at each level. For example:

- **Root:** MUST represent a single docmem instance. MAY represent a book, knowledge base, project, or chat session.
- **User node:** MAY partition by source or subject to enable scoped operations.
- **Summary:** MUST be a paragraph-length compression of its children. SHOULD be regenerated when new memories accumulate. Summary content SHOULD be LLM-generated when automatic summarization is implemented.
- **Memory:** MUST be an atomic unit, typically a sentence. MUST preserve ground truth—the actual text from the source.

## Node Structure

### Node ID Generation
- Node IDs MUST be randomly generated 8-character strings.
- The ONLY exception is the docmem root ID, which MAY be user-specified when creating a new docmem.

### Required Properties

| Property       | Type    | Nullable | Default | Description                                           |
|----------------|---------|----------|---------|-------------------------------------------------------|
| id             | text    | no       |         | Unique identifier, primary key                        |
| parent_id      | text    | yes      |         | Reference to parent node                              |
| text           | text    | no       |         | Text content                                          |
| order_value    | decimal | no       |         | Ordering within parent                                |
| token_count    | integer | no       |         | Approximate token count of text                       |
| created_at     | text    | no       |         | Creation timestamp in ISO 8601 format                 |
| updated_at     | text    | no       |         | Last update timestamp in ISO 8601 format              |
| context_type   | text    | no       |         | Node role type (e.g., "message", "summary", "root")   |
| context_name   | text    | no       |         | Context metadata name                                 |
| context_value  | text    | no       |         | Context metadata value                                |
| readonly       | integer | no       | 0       | Readonly flag, values 0 or 1                          |
| hash           | text    | yes      |         | Base64-encoded SHA-512 hash for optimistic locking    |

### Context Fields
- All context fields (context_type, context_name, context_value) MUST be strings of 0 to 24 characters.
- All three context fields MUST be provided for node creation and context updates.
- Node creation MUST fail if any context field is missing.

### Standard Display Formats
- Context metadata MUST be displayed in colon-delimited format: type, name, and value separated by colons (e.g., "root:purpose:document").
- Full node metadata MUST be displayed as the node ID, followed by the context format, followed by the updated_at timestamp.
- All UI and text output that displays node metadata MUST use these standard formats for consistency.

### Node Differentiation
- Nodes MUST be differentiated by their context metadata rather than an explicit node type field.
- The context_type field MUST distinguish node roles (e.g., "message", "summary", "root", "chat_session").
- Context metadata MUST provide semantic organization and enable filtering/querying by purpose, source, or role.

### Node Types
- Summary nodes MUST be distinguished from memory nodes by context_type.
- Memory nodes MUST preserve ground truth text.
- Summary nodes MUST represent interpretations of their children.
- Summary nodes MUST retain references to the nodes they summarize via parent-child relationships.
- Note nodes MUST be a system node type (distinguished by context_type) that allows agents to add annotations or updates to docmem without modifying readonly nodes.
- Note nodes MUST be created as siblings after readonly nodes to enable agent updates while preserving the original readonly content.

### Node Ordering
- Node ordering within a parent MUST use decimal values to allow insertion without reindexing.
- When inserting between two nodes, the new order value MUST use weighted interpolation biased 20% toward the target node and 80% toward the adjacent sibling.
- When no adjacent sibling exists, the new order value MUST be offset by 1.0 from the target node.
- This asymmetry optimizes for forward insertion patterns, allowing approximately three times more sequential insertions before hitting floating-point precision limits compared to midpoint interpolation.

### Token Counting
- Token count MUST be calculated for each node.
- Token count MUST be approximated as the text length in characters divided by four, rounded up to the nearest integer.
- Token counting MAY be replaced with a proper tokenizer in future implementations.

### Readonly Metadata
- The readonly field MUST be an integer value of 0 or 1.
- Nodes with readonly set to 1 MUST NOT be modified by update operations (content or context updates).
- Nodes with readonly set to 0 MAY be modified by update operations.
- Documents imported through file upload (non-TOML files) MUST have all their nodes marked as readonly.
- Nodes from TOML files MUST default to not readonly.
- When an agent needs to update docmem content that includes readonly nodes, it MUST create note nodes as siblings after the readonly nodes rather than modifying the readonly nodes directly.

## Database

### Storage
- All docmem instances MUST share a single database connection.
- The database MUST store nodes in a single table with the properties listed above.
- Indexes MUST be created on parent_id and on the combination of parent_id and order_value for performance.

### Cascade Behavior
- The database MUST NOT rely on cascade delete constraints. Deletion of descendants MUST be performed manually in post-order (children before parents).

### Updates
- The database MUST allow updates (not append-only) to support summary regeneration and content updates.
- When a node is updated, the updated_at timestamp MUST be set to the current time.
- All update operations MUST use optimistic locking with hash-based versioning (see Optimistic Locking section).

### Optimistic Locking
- All update operations MUST implement optimistic locking using SHA-512 hash-based versioning.
- Each node MUST have a hash field containing a Base64-encoded SHA-512 hash of the node's state.
- The hash MUST be computed from the pipe-delimited concatenation of: parent_id, context_type, context_name, context_value, text, and order_value.
- Null or undefined values MUST be normalized to empty strings for deterministic hashing.
- The hash MUST be recalculated whenever any hashed field changes.
- The readonly field MUST NOT be included in the hash calculation.
- Update operations MUST include an expected hash value and MUST only succeed if the node's current hash matches the expected hash.
- If the hash does not match, the operation MUST fail with an optimistic lock error indicating concurrent modification.

### Persistence (Planned)
- Database persistence to IndexedDB SHOULD be implemented to survive page reloads.
- Current implementation does NOT persist data (data is lost on page reload).

## Vector Database (Not Yet Implemented)

### Embedding Requirements (Planned)
- All nodes (memories and summaries) SHOULD be embedded and stored in a vector DB.
- When summaries are regenerated, their embeddings MUST be updated in the vector DB.

### Query Pattern (Planned)
- Semantic search MUST return matching nodes.
- The search MUST trace each hit up to its parent summary and/or user node.
- The search MUST deduplicate results (if a summary and its child both match, the child MUST be considered "covered by" the summary).
- Results MUST include nodes with structural context.

### Summary Attraction (Planned)
- Summaries SHOULD act as attractors—they're semantically denser and more likely to catch queries.
- Multiple hits tracing to the same parent SHOULD signal that the whole subtree is relevant.
- Trace-up operations MUST use parent pointers only (cheap operation after expensive vector search).

## Operations

### Import
- When importing documents through file upload (non-TOML files), all nodes created from the imported content MUST be marked readonly.
- When importing nodes from TOML files, all nodes MUST default to not readonly.
- Import operations MUST preserve the hierarchical structure of the source document.

### Serialization
- The serialize operation MUST perform depth-first tree traversal starting from the specified node, ordered by order_value.
- The starting node MUST be excluded from the output (only descendants are included).
- Nodes with empty or whitespace-only text MUST be excluded from the output.
- The operation MUST return a single string of the included nodes' text joined by double newlines.
- The reading order of a document MUST be determined by serialization order.

### Expand to Length
- The expand operation MUST return an array of nodes that fit within a given token budget, starting from the specified node.
- The algorithm MUST have three phases:

**Phase 1: Build priority list via reverse BFS**
- The tree MUST be traversed level-by-level starting from the root node.
- Within each level, nodes MUST be added to the priority list in reverse order (last/most recent children have higher priority).
- This ensures parents always appear before their children in the priority list.

**Phase 2: Consume budget**
- The system MUST iterate through the priority list, accumulating token counts.
- Each node MUST be added to the included set if the running total plus the node's token count does not exceed the budget.
- The system MUST stop on the first node that does not fit (no holes — the list is truncated, not skipped).
- This guarantees no orphan nodes (a child cannot be included without its parent).

**Phase 3: Preorder DFS render**
- The system MUST perform a preorder DFS traversal from the starting node.
- Only nodes present in the included set MUST be rendered.
- If a node is not included, its entire subtree MUST be skipped.
- The operation MUST return the resulting array of nodes in DFS order.

- Semantic prioritization and relevance-based expansion SHOULD be implemented in the future.

### Summarization
- The summarize operation MUST compress a contiguous range of sibling nodes under a new summary parent.
- Summary text content MUST be provided as a parameter (current implementation requires manual content).
- Summary text SHOULD be LLM-generated when automatic summarization is implemented.
- A summary node MUST be created as the new parent of the specified nodes, with the provided content and context metadata.
- All nodes to be summarized MUST share the same parent and MUST be leaf nodes (have no children).
- The summary node's order MUST be placed at the midpoint between the first and last nodes' orders.
- Memory nodes MUST be reparented to the summary node (they become children of the summary).
- Reparenting MUST use optimistic locking on each node. If any reparent fails, that node's parent reference MUST be rolled back to its original value.
- When vector DB is implemented, embeddings MUST be updated when summaries are created or regenerated.
- Summaries SHOULD be regenerated when their children change.
- The operation MUST return the new summary node.

### Append
- The append operation MUST add a new node as the last child of the specified parent node.
- The new node's order MUST be set to one greater than the maximum order among existing siblings, or 1.0 if no siblings exist.
- All context metadata fields and content MUST be provided.
- The operation MUST return the new node.

### Insert
- The insert-before operation MUST add a new node as a sibling immediately before the specified target node.
- The insert-after operation MUST add a new node as a sibling immediately after the specified target node.
- The target node MUST have a parent (cannot insert before/after root node).
- The new node MUST be inserted as a sibling of the target node (same parent).
- The new node's order MUST use the weighted interpolation described in Node Ordering.
- All context metadata fields and content MUST be provided.
- The operation MUST return the new node.

### Delete
- The delete operation MUST remove a node and all its descendants.
- Descendants MUST be collected first, then deleted in post-order (children before parents) to ensure safe deletion.
- When vector DB is implemented, embeddings MUST be removed for deleted nodes.

### Update Content
- The update content operation MUST replace the text content of an existing node.
- The operation MUST fail if the target node is readonly.
- Token count MUST be recalculated automatically when content is updated.
- The updated_at timestamp MUST be set to the current time.
- The hash MUST be recalculated after content changes.
- The operation MUST use optimistic locking (expected hash must match current hash).
- The operation MUST return the updated node.

### Update Context
- The update context operation MUST replace the context metadata of an existing node.
- The operation MUST fail if the target node is readonly.
- The updated_at timestamp MUST be set to the current time.
- All context metadata fields MUST be provided.
- The hash MUST be recalculated after context changes.
- The operation MUST use optimistic locking (expected hash must match current hash).
- The operation MUST return the updated node.

### Copy
- The copy operation MUST create a deep copy of a node and all its descendants at a specified position (as last child, as sibling before, or as sibling after a target node).
- Copy operations MAY operate across different docmem trees (no same-root constraint, unlike move operations).
- The target node for sibling copy operations MUST have a parent (cannot copy before/after root node).
- Copy operations MUST recursively copy all descendants, generating new IDs for each copied node.
- The copied subtree MUST maintain the same relative tree structure as the original.
- The root of the copied subtree MUST use the same positioning rules as insert operations.
- Children of copied nodes MUST use sequential ordering (same as append), preserving relative order but not original order values.
- Copied nodes' timestamps MUST be set to the current time.
- Copied nodes MUST preserve the readonly flag from the source nodes.
- The operation MUST return the new root node of the copied subtree.

### Move
- The move operation MUST relocate a node to a specified position (as last child, as sibling before, or as sibling after a target node).
- Move operations MUST only operate within the same docmem tree. The source node and target node MUST share the same root.
- For move-as-child, the moved node MUST be appended after all existing children of the new parent.
- For sibling moves, the moved node MUST be repositioned as a sibling of the target node.
- The target node for sibling move operations MUST have a parent (cannot move before/after root node).
- All move operations MUST prevent cycles (cannot move a node to be a child of itself or any of its descendants).
- The moved node's order MUST be recalculated using the same rules as insert operations.
- The updated_at timestamp MUST be set to the current time.
- The operation MUST use optimistic locking (expected hash must match current hash).
- The operation MUST return the updated node.

### Structure
- The structure operation MUST return the tree structure starting from the specified node without text content.
- The result MUST be a single string of indented lines, one per node.
- Each line MUST use the standard full node metadata format, prefixed by a dash and indented with two spaces per depth level.
- The result MUST include the starting node (at depth 0) and all descendants.
- Traversal MUST use preorder traversal ordered by order_value.

### Find
- The find operation MUST retrieve a node by ID.
- The operation MUST return the full node if found, or null if not found.

### Get Root of Node
- The get-root operation MUST walk the parent chain from the given node up to the root (where parent_id is null).
- The operation MUST return the root node.
- The operation MUST fail if any node in the chain is not found.

## Current Limitations

The following features are NOT REQUIRED in the current implementation:

- Vector database and semantic search are NOT REQUIRED (planned for future).
- Automatic LLM-based summarization is NOT REQUIRED (manual summarization is acceptable).
- Database persistence across page reloads is NOT REQUIRED.
- Version history for updates is NOT REQUIRED.
- Priority/importance flags for expansion ordering are NOT REQUIRED.
- Semantic prioritization in expand to length is NOT REQUIRED.

## Future Requirements

### Linking
Cross-entity relationships MUST be carried in content via @ tags rather than structural links. Vector similarity (when implemented) SHOULD surface these connections at query time.

### Vector Database
- Vector database implementation SHOULD be added with embeddings for all nodes.
- Semantic search with query-time trace-up and deduplication SHOULD be implemented.

### Query Operations (Planned)
- Semantic query operations SHOULD be implemented when vector DB is available.
- Query results SHOULD include structural context through trace-up operations.

### Summarization
- Automatic LLM-based summarization SHOULD be implemented.
- Extractive summarization approaches MAY be used as a first pass or optimization.

### Persistence
- Persistence across browser sessions SHOULD be implemented.

### Expansion
- Semantic prioritization in expand to length SHOULD be implemented.
- Partial expansion (mixed resolution in one document) SHOULD be implemented.
- Priority/importance flags for expansion ordering SHOULD be implemented.

### Additional Features
- Version history for non-destructive updates SHOULD be implemented.
- Ingest classification for incoming threads and documents SHOULD be implemented.

## Open Questions

### Summary Behavior on Expansion
When a summary is expanded, what SHOULD happen to the summary node itself? Options include:
- Replacing it entirely with children (clean but loses framing)
- Keeping it as a header (natural but redundant)
- Making it a parameter of the expand operation
- Having serialization modes that skip or include interior nodes

Current implementation includes summary nodes in serialization.

### Sticky Nodes
Some memories are tightly coupled and resist being separated. SHOULD there be a mechanism to mark this, or does summarization naturally preserve these relationships?
