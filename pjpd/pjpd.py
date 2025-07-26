#!/usr/bin/env python3
"""
ProjectMCP - Local Project Management Server

A thin wrapper that invokes the MCP server implementation.
"""

import sys
from pathlib import Path

# Add src directory to Python path
src_path = Path(__file__).parent / "src"
sys.path.insert(0, str(src_path))

from mcp_wrapper import main

if __name__ == "__main__":
    main()
