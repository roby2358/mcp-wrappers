#!/usr/bin/env python3
"""
VecBook HTTP Server
HTTP interface for VecBook embedding functionality
"""

import sys
import toml
from pathlib import Path

from src.http_server import VecBookHTTPServer
from src.vecx import VecBookIndex


def get_script_dir() -> Path:
    """Get the script directory"""
    return Path(__file__).parent


def load_config() -> dict:
    """Load configuration from vecbook.toml or return defaults"""
    script_dir = get_script_dir()
    config_path = script_dir / "vecbook.toml"
    
    config = {}
    
    if config_path.exists():
        try:
            config = toml.load(config_path)
        except Exception as e:
            print(f"Error loading config: {e}, using defaults", file=sys.stderr)
    else:
        print("Warning: vecbook.toml not found, using defaults", file=sys.stderr)
    
    return config


def main():
    """Main entry point for HTTP server"""
    config = load_config()
    
    # Build the index
    script_dir = get_script_dir()
    data_path = script_dir / config.get("data_directory", "data")
    
    index = VecBookIndex(
        path=data_path,
        max_results=config.get("max_results", 10),
        embedding_model=config.get("embedding_model", "sentence-transformers/all-MiniLM-L6-v2"),
        similarity_metric=config.get("similarity_metric", "cosine")
    )
    
    # Create and run HTTP server
    server = VecBookHTTPServer(index)
    server.run(host="0.0.0.0", port=51539)


if __name__ == "__main__":
    main() 