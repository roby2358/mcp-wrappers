#!/usr/bin/env python3
"""
VecBook - Local Vector Document Book
Main entry point for the MCP server
"""

import sys
import toml
from pathlib import Path
from src.mcp import mcp, index


def load_config():
    """Load configuration from vecbook.toml"""
    # Look for config file relative to the script location, not current working directory
    script_dir = Path(__file__).parent
    config_path = script_dir / "vecbook.toml"
    if not config_path.exists():
        print("Error: vecbook.toml not found", file=sys.stderr)
        sys.exit(1)
    
    try:
        config = toml.load(config_path)
        return config
    except Exception as e:
        print(f"Error loading config: {e}", file=sys.stderr)
        sys.exit(1)


def main():
    """Main entry point"""
    config = load_config()
    
    # Update the global index with the loaded config
    index.config = config
    data_dir_name = config.get("data_directory", "data")
    index.data_directory = index._get_script_dir() / data_dir_name
    index.data_dir = index.data_directory
    index.max_results = config.get("max_results", 10)
    index.embedding_model = config.get("embedding_model", "sentence-transformers/all-MiniLM-L6-v2")
    index.similarity_metric = config.get("similarity_metric", "cosine")
    
    # Start the MCP server
    print("Starting VecBook MCP Server...", file=sys.stderr)
    mcp.run()


if __name__ == "__main__":
    main()
