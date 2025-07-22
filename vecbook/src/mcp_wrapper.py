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

class VecBookMCPServer:
    """VecBook MCP Server that manages configuration, indexing, and MCP tools"""
    
    def __init__(self, config_path: Optional[Path] = None):
        """Initialize the server with configuration and index"""
        self.script_dir = get_script_dir()
        self.config = self._load_config(config_path)
        self.index = self._build_index()
        self.mcp = FastMCP("vecbook")
        
        self._register_tools_and_prompts()

    def _load_config(self, config_path: Optional[Path] = None) -> Dict[str, Any]:
        """Load configuration from vecbook.toml or return defaults"""
        if config_path is None:
            config_path = self.script_dir / "vecbook.toml"
        
        config = {}
        
        if config_path.exists():
            try:
                config = toml.load(config_path)
            except Exception as e:
                print(f"Error loading config: {e}, using defaults", file=sys.stderr)
        else:
            print("Warning: vecbook.toml not found, using defaults", file=sys.stderr)
        
        return config

    def _build_index(self) -> VecBookIndex:
        """Build the vector index from configuration"""
        data_path = self.script_dir / self.config.get("data_directory", "data")
        return VecBookIndex(
            path=data_path,
            max_results=self.config.get("max_results", 10),
            embedding_model=self.config.get("embedding_model", "sentence-transformers/all-MiniLM-L6-v2"),
            similarity_metric=self.config.get("similarity_metric", "cosine")
        )

    def _register_tools_and_prompts(self):
        """Register all MCP tools and prompts"""
        # Register prompt
        @self.mcp.prompt(name="intro")
        def _intro() -> str:
            """Send the VecBook introduction prompt"""
            # Look for resources relative to the script location
            intro_path = self.script_dir / "resources" / "intro.txt"
            if not intro_path.exists():
                return "VecBook introduction not found. Please check that resources/intro.txt exists."
            
            try:
                with open(intro_path, "r", encoding="utf-8") as f:
                    return f.read().strip()
            except Exception as e:
                return f"Error reading introduction: {e}"

        # Register tools
        @self.mcp.tool(name="search")
        def _search(query: str, max_results: Optional[int] = None) -> Dict[str, Any]:
            """Perform semantic search over indexed documents"""
            if not query or not query.strip():
                return self._mcp_failure("Query cannot be empty")
            
            # Use configured max_results if not specified
            if max_results is None:
                max_results = self.index.max_results
            
            # Use the simple text search for now (vector search will be implemented later)
            results = self.index.search_simple(query, max_results)
            
            if not results:
                return self._mcp_success([])
            
            return self._mcp_success(results)

        @self.mcp.tool(name="reindex")
        def _reindex(path: Optional[str] = None) -> Dict[str, Any]:
            """Rebuild the vector index from all data files"""
            # Update data directory if path provided, otherwise use current
            if path:
                new_path = self.script_dir / path
                logger.info(f"Path provided: {path}")
                logger.info(f"Script dir: {self.script_dir}")
                logger.info(f"Calculated data_path: {new_path}")
                
                # Create a new TextRecords instance with the new path
                from .textrec import TextRecords
                self.index.text_records = TextRecords(new_path)
            else:
                logger.info(f"No path provided, using default: {self.index.text_records.path}")
            
            logger.info(f"Final data directory: {self.index.text_records.path}")
            logger.info(f"Data directory exists: {self.index.text_records.path.exists()}")

            if not self.index.text_records.path.exists():
                logger.error(f"Directory check failed for: {self.index.text_records.path}")
                return self._mcp_failure(f"Data directory '{str(self.index.text_records.path)}' does not exist")
            
            # Use the actual index building functionality
            result = self.index.build_index()
            
            if result["status"] == "error":
                return self._mcp_failure(result["message"])
            
            return self._mcp_success(result)

        @self.mcp.tool(name="stats")
        def _stats() -> Dict[str, Any]:
            """Return indexing statistics"""
            if not self.index.stats["total_records"]:
                return self._mcp_failure("No records have been indexed yet. Use the reindex tool first.")
            
            result = {
                "status": "indexed",
                **self.index.stats,
                "config": {
                    "data_directory": str(self.index.text_records.path),
                    "max_results": self.index.max_results,
                    "embedding_model": self.index.embedding_model,
                    "similarity_metric": self.index.similarity_metric
                }
            }
            
            return self._mcp_success(result)

    def _mcp_success(self, result: Any) -> Dict[str, Any]:
        """Return a successful MCP response with the given result."""
        return {
            "success": True,
            "result": result,
            "error": ""
        }

    def _mcp_failure(self, error_message: str) -> Dict[str, Any]:
        """Return a failed MCP response with the given error message."""
        return {
            "success": False,
            "result": "",
            "error": error_message
        }

    def run(self):
        """Start the MCP server"""
        print("Starting VecBook MCP Server...", file=sys.stderr)
        self.mcp.run()


def main():
    """Entry point for the application."""
    server = VecBookMCPServer()
    server.run()

if __name__ == "__main__":
    main()
