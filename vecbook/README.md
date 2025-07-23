# VecBook — Local Vector Document Book

A lightweight, local-first vector database built on plain `.txt` files. Provides fast semantic search over multi-line text records stored in human-readable format.

## Quick Start

### Claude Desktop

1. **Install dependencies:**
   ```bash
   uv sync
   ```
2. Update Claude Desktop config

**Location:** `%APPDATA%\Claude\claude_desktop_config.json`

```json
{
  "mcpServers": {
    "vecbook": {
      "command": "C:/work/mcp-wrappers/vecbook/.venv/Scripts/python.exe",
      "args": ["C:/work/mcp-wrappers/vecbook/vecbook.py"]
    }
  }
}
```

### Running from the command line

1. **Install dependencies:**
   ```bash
   uv sync
   ```

2. **Run the MCP server:**
   ```bash
   uv run python vecbook.py
   ```

3. **Run with HTTP interface:**
   ```bash
   uv run python vecbook.py --http
   ```

4. **Run HTTP server only:**
   ```bash
   uv run python vecbook_http.py
   ```

### Testing

```bash
uv add pytest --dev
uv run python -m unittest discover tests -v
```

## Configuration

The system uses `vecbook.toml` for configuration:

```toml
data_directory = "data"
max_results = 10
embedding_model = "sentence-transformers/all-MiniLM-L6-v2"
similarity_metric = "cosine"
```

## Data Format

Records are stored in `.txt` files with the following format:

```
Title: Document Title
Date: 2024-01-01
Tags: tag1, tag2

This is the content of the record. It can span multiple lines
and contain any text you want to search.

---
Title: Another Document
Category: example

Another record with different metadata and content.
```

Key points:
- Records are separated by `---` on a line by itself
- Optional metadata headers use `Key: Value` format
- All text (including metadata) is used for embedding

## MCP Tools

The system provides four main tools:

### `search`
Perform semantic search over indexed documents.

**Parameters:**
- `query` (string, required): Natural language search query
- `max_results` (integer, optional): Maximum number of results to return

### `reindex`
Rebuild the vector index from all data files.

**Parameters:**
- `path` (string, optional): Path to the data directory (uses config default if not specified)

### `stats`
Return indexing statistics and configuration.

### `prompt`
Send the VecBook introduction prompt to provide context about the available tools.

**Parameters:**
- None

## HTTP Interface

The system provides an HTTP interface on port 51539 for embedding text strings.

### Endpoints

#### `POST /embed`
Embed a list of text strings and return their vectors.

**Request:**
```json
{
  "texts": ["This is a test sentence.", "Another sentence to embed."]
}
```

**Response:**
```json
{
  "embeddings": [
    [0.123, -0.456, 0.789, ...],
    [0.234, -0.567, 0.890, ...]
  ]
}
```

#### `GET /health`
Health check endpoint.

**Response:**
```json
{
  "status": "healthy",
  "service": "vecbook"
}
```

#### `GET /stats`
Get indexing statistics.

**Response:**
```json
{
  "total_records": 100,
  "total_files": 5,
  "indexed_at": "2024-01-01T12:00:00"
}
```

### Testing the HTTP Interface

```bash
# Test the HTTP interface
uv run python test_http.py
```

## Intro Prompt

The system includes an introduction prompt stored in `resources/intro.txt` that provides context about VecBook's capabilities and available tools. This prompt is designed to be concise and informative, helping users understand how to interact with the vector document search system.

## Sample Data

The `samples/` directory contains example data files that demonstrate the record format and system capabilities.

## Development Status

This is a framework implementation with stub MCP tools. The tools return meaningful responses rather than simple "I did ___!" messages, but the actual vector indexing and search functionality will be implemented in future iterations.

## Architecture

- `vecbook.py`: Main entry point
- `src/mcp.py`: MCP server implementation
- `vecbook.toml`: Configuration file
- `data/`: Directory for your document files
- `samples/`: Example data files
- `resources/`: System resources including intro.txt prompt

## Next Steps

The framework is ready for implementing:
1. Record parsing from `.txt` files
2. Vector embedding generation using sentence-transformers
3. FAISS index for fast similarity search
4. Real search functionality in the MCP tools 