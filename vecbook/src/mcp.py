"""
VecBook MCP Server Implementation
Provides tools for semantic search over vector-indexed documents
"""

import json
import logging
import sys
from pathlib import Path
from typing import Dict, List, Any, Optional

from mcp.server.fastmcp import FastMCP

# Create the MCP server instance
mcp = FastMCP("vecbook")

# Initialize logging to stderr
logging.basicConfig(level=logging.INFO, stream=sys.stderr)
logger = logging.getLogger(__name__)

class VecBookIndex:
    """Manages the vector index and document storage"""
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        # Resolve data directory relative to script location
        data_dir_name = config.get("data_directory", "data")
        self.data_directory = self._get_script_dir() / data_dir_name
        self.data_dir = self.data_directory
        
        # Debug logging for path resolution
        logger.info(f"Script directory: {self._get_script_dir()}")
        logger.info(f"Data directory: {self.data_directory}")
        logger.info(f"Data directory exists: {self.data_directory.exists()}")
        
        self.max_results = config.get("max_results", 10)
        self.embedding_model = config.get("embedding_model", "sentence-transformers/all-MiniLM-L6-v2")
        self.similarity_metric = config.get("similarity_metric", "cosine")
        
        # Placeholder for vector index (will be implemented later)
        self.index = None
        self.records = []
        self.stats = {
            "total_records": 0,
            "total_files": 0,
            "indexed_at": None
        }
    
    def _get_script_dir(self) -> Path:
        """Get the script directory (parent of the src directory)"""
        return Path(__file__).parent.parent

# Global index instance
index = VecBookIndex({})

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
    intro_path = index._get_script_dir() / "resources" / "intro.txt"
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
    
    # Stub implementation - return mock results
    # In the real implementation, this would query the vector index
    mock_results = [
        {
            "text": f"Sample record matching '{query}' - this is a placeholder result",
            "file_path": "samples/sample1.txt",
            "byte_offset": 0,
            "similarity_score": "0.850000",
            "metadata": {"title": "Sample Document", "date": "2024-01-01"}
        },
        {
            "text": f"Another record related to '{query}' - placeholder for demonstration",
            "file_path": "samples/sample2.txt", 
            "byte_offset": 150,
            "similarity_score": "0.720000",
            "metadata": {"category": "example", "tags": ["demo", "placeholder"]}
        }
    ]
    
    # Limit results to requested max
    return mcp_success(mock_results[:max_results])

@mcp.tool()
async def reindex(path: Optional[str] = None) -> Dict[str, Any]:
    """Rebuild the vector index from all data files"""
    # Update data directory if path provided, otherwise use current
    if path:
        index.data_dir = index._get_script_dir() / path
        logger.info(f"Path provided: {path}")
        logger.info(f"Script dir: {index._get_script_dir()}")
        logger.info(f"Calculated data_dir: {index.data_dir}")
    else:
        index.data_dir = index.data_directory
        logger.info(f"No path provided, using default: {index.data_directory}")
    
    logger.info(f"Final data directory: {index.data_dir}")
    logger.info(f"Data directory type: {type(index.data_dir)}")
    logger.info(f"Data directory exists: {index.data_dir.exists()}")

    if not index.data_dir.exists():
        logger.error(f"Directory check failed for: {index.data_dir}")
        return mcp_failure(f"Data directory '{str(index.data_dir)}' does not exist")
    
    # Stub implementation - simulate indexing process
    # In the real implementation, this would:
    # 1. Discover all .txt files recursively
    # 2. Parse records using --- separator
    # 3. Generate embeddings
    # 4. Build FAISS index
    
    # Simulate finding files
    txt_files = list(index.data_dir.rglob("*.txt"))
    
    # Simulate parsing records
    total_records = 0
    for file_path in txt_files:
        # Mock record count per file
        total_records += 5  # Placeholder
        
    # Update stats
    index.stats = {
        "total_records": total_records,
        "total_files": len(txt_files),
        "indexed_at": "2024-01-01T12:00:00Z"  # Placeholder timestamp
    }
    
    result = {
        "status": "success",
        "message": f"Indexed {total_records} records from {len(txt_files)} files",
        "stats": index.stats
    }
    
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
            "data_directory": str(index.data_directory),
            "max_results": index.max_results,
            "embedding_model": index.embedding_model,
            "similarity_metric": index.similarity_metric
        }
    }
    
    return mcp_success(result)

def main():
    """Entry point for the application."""
    print("Starting VecBook MCP Server...", file=sys.stderr)
    
    # Perform initial indexing
    print("Performing initial indexing...", file=sys.stderr)
    # Note: In a real implementation, you'd want to handle the async call properly
    # For now, we'll just start the server and let the client trigger reindexing
    
    mcp.run()

if __name__ == "__main__":
    main()
