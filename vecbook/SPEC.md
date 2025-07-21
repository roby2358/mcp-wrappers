# VecBook — Local Vector Document Book

## Overview

VecBook is a lightweight, local-first vector database built on plain `.txt` files. It provides fast semantic search over multi-line text records stored in human-readable format. The system parses and indexes these records into memory at startup, allowing vector similarity queries against the corpus without relying on external infrastructure.

This specification outlines the design, structure, and operational requirements of VecBook. It is intended for developers contributing to the core system, as well as those building tools and extensions atop it.

---

## Configuration

* All configuration files **MUST** be in TOML format
* Configuration file **MUST** be named `vecbook.toml` and located in the project root
* Default configuration values:
  * `data_directory` = "data"
  * `max_results` = 10
  * `embedding_model` = "sentence-transformers/all-MiniLM-L6-v2"
  * `similarity_metric` = "cosine"

## API

### MCP Interface

* The system **MUST** present an MCP tools interface
* Use MCP SDK "fastmcp>=0.1.0" https://atproto.blue/en/latest/
* Server **MUST** support stdio transport by default

#### Required Tools

* `search` - Perform semantic search with parameters:
  * `query` (string, required): Natural language search query
  * `max_results` (integer, optional): Maximum number of results to return
* `reindex` - Rebuild the vector index from all data files
* `stats` - Return indexing statistics

## Startup Behavior

* All files **MUST** be indexed at startup
* Indexing progress **SHOULD** be logged to stderr
* Startup **MUST** complete successfully even if some files contain malformed records

---

## Data Format and Storage

### Record Format

* Each record **MUST** be delimited by a separator line consisting of exactly three hyphens (`---`) on a line by itself
* Each record **MUST** contain at least one non-empty line of content
* Records **MAY** include optional metadata headers in a simple `Key: Value` format at the top of the record
* The entire record (including metadata) **MUST** be treated as a single unit for embedding purposes
* Records **MUST** be parsed in order of appearance within each file

### File Organization

* All `.txt` files **MUST** be stored under the configured data directory
* Files **MAY** be nested in subdirectories; the system **MUST** recursively discover all `.txt` files
* Each file **MUST** use UTF-8 encoding
* Each file **MUST** be identified by its full path from the data directory root
* Malformed or empty records **MUST** be ignored with a WARN-level log message
* File discovery **MUST** handle symlinks appropriately

---

## Indexing System

### Embeddings

* VecBook **MUST** generate vector embeddings for each record at load time
* The embedding model **MUST** be `sentence-transformers/all-MiniLM-L6-v2`
* Embeddings **MUST** be stored only in memory and **MUST NOT** be persisted between runs
* Embedding generation **MUST** handle text length limits gracefully

### Index Engine

* The system **MUST** use a fast approximate nearest neighbor index (FAISS)
* The index **MUST** support top-K queries by cosine or L2 similarity
* Index entries **MUST** maintain a mapping to:
  * Source file path (relative to data directory)
  * Record position as line number where record starts (1-indexed)
  * Original record text for retrieval

---

## Querying

### Search API

* VecBook **MUST** provide semantic search via the MCP `search` tool
* Query strings **MUST** be embedded using the same model as the index
* Results **MUST** return:
  * `text`: The matched record's full text (excluding metadata)
  * `file_path`: Source file path relative to data directory
  * `line_number`: Line number where record starts (1-indexed)
  * `similarity_score`: Float between 0.0 and 1.0, formatted as "0.000000"
  * `metadata`: Parsed metadata as key-value pairs (if present)
* Results **MUST** be sorted by similarity score (highest first)
* The system **MUST** support configurable number of results via `max_results` parameter

### Error Handling

* Invalid queries **MUST** return appropriate error messages
* Empty result sets **MUST** be handled gracefully
* System **MUST** continue operating even if individual records fail to embed

---

## Performance Requirements

* The system **SHOULD** be able to index at least 10,000 records in under 30 seconds on modern consumer hardware
* Memory use **MUST NOT** exceed reasonable bounds for the corpus size (e.g., <2GB for 10k records with MiniLM)
* Search queries **SHOULD** return results in under 1 second for typical corpora
* Cold start **MUST** re-index all records; caching is out-of-scope for initial versions

---

## Developer Experience

* The system **MUST** be runnable with a single Python script and a `requirements.txt`
* It **SHOULD** include simple test cases and example `.txt` files in a `samples/` directory
* Code **SHOULD** follow standard Python style guidelines (PEP 8) and be documented
* The system **SHOULD** provide clear error messages for common issues
* Logging **SHOULD** be configurable (INFO level by default)

---

## Out of Scope

* No persistent database engine (e.g., SQLite, Postgres) is included or required
* No real-time file watching or hot reload is supported in the first version
* No web frontend or REST API is included in the base implementation
* No authentication or access control mechanisms
* No support for binary file formats

---

## Future Extensions (Non-Binding)

* Web UI for browsing and querying
* Persistent vector cache to avoid re-embedding on each run
* Tagging, classification, and embedding summarization
* Integration with personal knowledge management systems (e.g., Obsidian)
* Support for additional embedding models (OpenAI, HuggingFace alternatives)
* Configurable search result formats (metadata only, text only, both)
* Parsing statistics and corpus analytics
* Batch operations for large-scale indexing

---

## Status

> This spec is a working draft. Contributions and revisions welcome.

