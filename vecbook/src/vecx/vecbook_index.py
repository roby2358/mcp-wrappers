"""
VecBook Index Management
Manages the vector index and document storage
"""

import logging
import sys
from pathlib import Path
from typing import Dict, List, Any, Optional
from datetime import datetime

from ..textrec.text_records import TextRecords

# Initialize logging to stderr
logging.basicConfig(level=logging.INFO, stream=sys.stderr)
logger = logging.getLogger(__name__)

class VecBookIndex:
    """Manages the vector index and document storage"""
    
    def __init__(self, script_dir: Path, data_directory: str = "data", max_results: int = 10, 
                 embedding_model: str = "sentence-transformers/all-MiniLM-L6-v2", 
                 similarity_metric: str = "cosine"):
        self.max_results = max_results
        self.embedding_model = embedding_model
        self.similarity_metric = similarity_metric
        
        # Use TextRecords for file handling
        data_path = script_dir / data_directory
        self.text_records = TextRecords(data_path)
        
        # Placeholder for vector index (will be implemented later)
        self.index = None
        self.records = []
        self.stats = {
            "total_records": 0,
            "total_files": 0,
            "indexed_at": None
        }
    
    def build_index(self) -> Dict[str, Any]:
        """Build the document index from all files in the data directory"""
        logger.info("Starting index build...")
        
        # Discover all text files
        txt_files = self.text_records.discover_files()
        if not txt_files:
            return {
                "status": "error",
                "message": "No .txt files found in data directory",
                "stats": self.stats
            }
        
        # Clear existing records
        self.records = []
        
        # Parse all files
        for file_path in txt_files:
            file_records = self.text_records.parse_file(file_path)
            self.records.extend(file_records)
        
        # Update statistics
        self.stats = {
            "total_records": len(self.records),
            "total_files": len(txt_files),
            "indexed_at": datetime.now().isoformat()
        }
        
        logger.info(f"Index build complete: {self.stats['total_records']} records from {self.stats['total_files']} files")
        
        return {
            "status": "success",
            "message": f"Indexed {self.stats['total_records']} records from {self.stats['total_files']} files",
            "stats": self.stats
        }
    
    def search_simple(self, query: str, max_results: Optional[int] = None) -> List[Dict[str, Any]]:
        """Simple text-based search (before vector search is implemented)"""
        if max_results is None:
            max_results = self.max_results
        
        if not self.records:
            logger.warning("No records available for search. Run reindex first.")
            return []
        
        # Simple keyword-based search for now
        query_lower = query.lower()
        matching_records = []
        
        for record in self.records:
            text_lower = record["text"].lower()
            if query_lower in text_lower:
                # Calculate simple relevance score based on word frequency
                score = text_lower.count(query_lower) / len(text_lower.split())
                
                search_result = record.copy()
                search_result["similarity_score"] = f"{score:.6f}"
                matching_records.append(search_result)
        
        # Sort by score (descending) and limit results
        matching_records.sort(key=lambda x: float(x["similarity_score"]), reverse=True)
        return matching_records[:max_results] 