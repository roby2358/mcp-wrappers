"""
VecBook MCP Server Implementation
Provides tools for semantic search over vector-indexed documents
"""

import json
import logging
import sys
import toml
from pathlib import Path
from typing import Dict, List, Any, Optional

from mcp.server.fastmcp import FastMCP
from .vecx import VecBookIndex

# Initialize logging to stderr
logging.basicConfig(level=logging.INFO, stream=sys.stderr)
logger = logging.getLogger(__name__)

def get_script_dir() -> Path:
    """Get the script directory (parent of the src directory)"""
    return Path(__file__).parent.parent

def load_config() -> Dict[str, Any]:
    """Load configuration from vecbook.toml or return defaults"""
    config_path = get_script_dir() / "vecbook.toml"
    config = {}
    
    if config_path.exists():
        try:
            config = toml.load(config_path)
        except Exception as e:
            print(f"Error loading config: {e}, using defaults", file=sys.stderr)
    else:
        print("Warning: vecbook.toml not found, using defaults", file=sys.stderr)
    
    return config

# Load config and initialize index
config = load_config()
index = VecBookIndex(
    script_dir=get_script_dir(),
    data_directory=config.get("data_directory", "data"),
    max_results=config.get("max_results", 10),
    embedding_model=config.get("embedding_model", "sentence-transformers/all-MiniLM-L6-v2"),
    similarity_metric=config.get("similarity_metric", "cosine")
)

# Create the MCP server instance
mcp = FastMCP("vecbook")

def mcp_success(result: Any) -> Dict[str, Any]:
    """Return a successful MCP response with the given result."""
    return {
        "success": True,
        "result": result,
        "error": ""
    }

def mcp_failure(error_message: str) -> Dict[str, Any]:
    """Return a failed MCP response with the given error message."""
    return {
        "success": False,
        "result": "",
        "error": error_message
    }

@mcp.prompt()
def intro() -> str:
    """Send the VecBook introduction prompt"""
    # Look for resources relative to the script location
    intro_path = get_script_dir() / "resources" / "intro.txt"
    if not intro_path.exists():
        return "VecBook introduction not found. Please check that resources/intro.txt exists."
    
    try:
        with open(intro_path, "r", encoding="utf-8") as f:
            return f.read().strip()
    except Exception as e:
        return f"Error reading introduction: {e}"

@mcp.tool()
async def search(query: str, max_results: Optional[int] = None) -> Dict[str, Any]:
    """Perform semantic search over indexed documents"""
    if not query or not query.strip():
        return mcp_failure("Query cannot be empty")
    
    # Use configured max_results if not specified
    if max_results is None:
        max_results = index.max_results
    
    # Use the simple text search for now (vector search will be implemented later)
    results = index.search_simple(query, max_results)
    
    if not results:
        return mcp_success([])
    
    return mcp_success(results)

@mcp.tool()
async def reindex(path: Optional[str] = None) -> Dict[str, Any]:
    """Rebuild the vector index from all data files"""
    # Update data directory if path provided, otherwise use current
    if path:
        new_path = get_script_dir() / path
        logger.info(f"Path provided: {path}")
        logger.info(f"Script dir: {get_script_dir()}")
        logger.info(f"Calculated data_path: {new_path}")
        
        # Create a new TextRecords instance with the new path
        from .textrec import TextRecords
        index.text_records = TextRecords(new_path)
    else:
        logger.info(f"No path provided, using default: {index.text_records.path}")
    
    logger.info(f"Final data directory: {index.text_records.path}")
    logger.info(f"Data directory exists: {index.text_records.path.exists()}")

    if not index.text_records.path.exists():
        logger.error(f"Directory check failed for: {index.text_records.path}")
        return mcp_failure(f"Data directory '{str(index.text_records.path)}' does not exist")
    
    # Use the actual index building functionality
    result = index.build_index()
    
    if result["status"] == "error":
        return mcp_failure(result["message"])
    
    return mcp_success(result)

@mcp.tool()
async def stats() -> Dict[str, Any]:
    """Return indexing statistics"""
    if not index.stats["total_records"]:
        return mcp_failure("No records have been indexed yet. Use the reindex tool first.")
    
    result = {
        "status": "indexed",
        "stats": index.stats,
        "config": {
            "data_directory": str(index.text_records.path),
            "max_results": index.max_results,
            "embedding_model": index.embedding_model,
            "similarity_metric": index.similarity_metric
        }
    }
    
    return mcp_success(result)

def main():
    """Entry point for the application."""
    print("Starting VecBook MCP Server...", file=sys.stderr)
    mcp.run()

if __name__ == "__main__":
    main()
