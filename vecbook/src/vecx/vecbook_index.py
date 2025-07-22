"""
VecBook Index Management
Manages the vector index and document storage
"""

import logging
import sys
from pathlib import Path
from typing import Dict, List, Any, Optional

# Initialize logging to stderr
logging.basicConfig(level=logging.INFO, stream=sys.stderr)
logger = logging.getLogger(__name__)

class VecBookIndex:
    """Manages the vector index and document storage"""
    
    def __init__(self, script_dir: Path, data_directory: str = "data", max_results: int = 10, 
                 embedding_model: str = "sentence-transformers/all-MiniLM-L6-v2", 
                 similarity_metric: str = "cosine"):
        # Resolve data directory relative to script directory
        self.script_dir = script_dir
        self.data_path = self.script_dir / data_directory
        
        # Debug logging for path resolution
        logger.info(f"Script directory: {self.script_dir}")
        logger.info(f"Data directory: {self.data_path}")
        logger.info(f"Data directory exists: {self.data_path.exists()}")
        
        self.max_results = max_results
        self.embedding_model = embedding_model
        self.similarity_metric = similarity_metric
        
        # Placeholder for vector index (will be implemented later)
        self.index = None
        self.records = []
        self.stats = {
            "total_records": 0,
            "total_files": 0,
            "indexed_at": None
        } 