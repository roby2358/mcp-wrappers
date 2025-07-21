# SPEC.md



## Project Title: VecBook — Local Vector Document Book



VecBook is a lightweight, local-first vector database built on plain `.txt` files. It provides fast semantic search over multi-line text records stored in human-readable format. The system parses and indexes these records into memory at startup, allowing vector similarity queries against the corpus without relying on external infrastructure.



This specification outlines the design, structure, and operational requirements of VecBook. It is intended for developers contributing to the core system, as well as those building tools and extensions atop it.



---

## Configuration

* All configuration files must be in toml format

* data_directory (default: "data")

* max_results (default: 10)

* embedding_model (default: "sentence-transformers/all-MiniLM-L6-v2")

<The LLM will identify configuration parameters as we go>

## API

### MCP

* The system will present an MCP tools interface

* Use MCP SDK "fastmcp>=0.1.0" https://atproto.blue/en/latest/

#### Tools

* reindex

* search

<The LLM will identify other tools needed>

## Startup

* All files MUST be indexed at startup.

## Format and Storage



### Record Format



* Each record **MUST** be delimited by a separator line consisting of exactly three hyphens (`---`) on a line by itself.

* Each record **MUST** contain at least one non-empty line of content.

* Records **MAY** include optional metadata headers in a simple `Key: Value` format at the top of the record.

* The body of the record **MUST** be treated as a single unit for embedding purposes, including the key value pairs.



### File Organization



* All `.txt` files **MUST** be stored under a `data/` directory or a user-configurable root.

* Files **MAY** be nested in subdirectories; the system **SHOULD** recursively discover all `.txt` files.

* Each file **MUST** use UTF-8 encoding.

* Each file **MUST** be identified by its full path from the root directory, including any subdirectories traversed.

* Malformed or empty records **MUST** be ignored with a WARN message.



---



## Indexing



### Embeddings



* VecBook **MUST** generate vector embeddings for each record at load time.

* The initial embedding model will be HuggingFace sentence-transformers/all-MiniLM-L6-v2

* Embeddings **MUST** be stored only in memory and **MUST NOT** be persisted between runs.



### Index Engine



* The system **MUST** use a fast approximate nearest neighbor index such as FAISS, Annoy, or HNSWLib.

* The index **MUST** support top-K queries by cosine or L2 similarity.

* Index entries **MUST** maintain a mapping to the source file and record position as a line offset into the file (1-indexed).



---



## Querying



### Search API



* VecBook **MUST** provide a function to search by natural language input.

* A query string **MUST** be embedded and compared to the vector index.

* Results **MUST** return
  * the matched record’s text
  * its source (file path and line number in the text file)
  * similarity score formatted as [0..1] in format "0.000000"
  * but exclude metadata.

* The system **SHOULD** support a configurable number of results (`k`).



### Filters and Metadata (Future)



* The system **MAY** support filtering by metadata keys (e.g., tags, date) in future versions.

* Records with parseable metadata **SHOULD** expose it in the search result output.



---



## Performance and Limits



* The system **SHOULD** be able to index at least 10,000 records in under 30 seconds on modern consumer hardware.

* Memory use **MUST NOT** exceed reasonable bounds for the corpus size (e.g., <2GB for 10k records with MiniLM).

* Cold start **MUST** re-index all records; caching is out-of-scope for initial versions.



---



## Developer Experience



* The system **MUST** be runnable with a single Python script and a `requirements.txt`.

* It **SHOULD** include simple test cases and example `.txt` files in a `samples/` directory.

* Code **SHOULD** follow standard Python style guidelines and be documented.



---



## Out of Scope



* No persistent database engine (e.g., SQLite, Postgres) is included or required.

* No real-time file watching or hot reload is supported in the first version.

* No web frontend or REST API is included in the base implementation.



---



## Future Extensions (Non-Binding)



* Web UI for browsing and querying

* Persistent vector cache to avoid re-embedding on each run

* Tagging, classification, and embedding summarization

* Integration with personal knowledge management systems (e.g., Obsidian)

* The embedding model will be configurable (e.g., SentenceTransformer, OpenAI, HuggingFace)

* Return metadata, text, either, or both for search

* Parsing statistics

---



## Status



> This spec is a working draft. Contributions and revisions welcome.



