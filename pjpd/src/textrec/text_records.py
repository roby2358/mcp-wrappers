"""
Text Records Management
Handles discovery and parsing of text files broken into records with --- separators
"""

import logging
import sys
from pathlib import Path
from typing import Dict, List, Any

# Initialize logging to stderr
logging.basicConfig(level=logging.INFO, stream=sys.stderr)
logger = logging.getLogger(__name__)

class TextRecords:
    """Handles discovery and parsing of text files broken into records with --- separators"""
    
    def __init__(self, path: Path):
        self.path = Path(path)
        
        # Debug logging for path resolution
        logger.info(f"TextRecords path: {self.path}")
        logger.info(f"Path exists: {self.path.exists()}")
    
    def discover_files(self) -> List[Path]:
        """Discover all .txt files in the path recursively"""
        if not self.path.exists():
            logger.error(f"Path does not exist: {self.path}")
            return []
        
        txt_files = list(self.path.rglob("*.txt"))
        logger.info(f"Found {len(txt_files)} .txt files")
        return txt_files
    
    def parse_file(self, file_path: Path) -> List[Dict[str, Any]]:
        """Parse a single file and extract records separated by ---"""
        records = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Split by --- separator and filter out empty parts
            parts = [part.strip() for part in content.split('---') if part.strip()]
            
            # Convert relative path for storage
            relative_path = file_path.relative_to(self.path)
            
            for i, text in enumerate(parts):
                # Calculate approximate byte offset (rough estimate)
                byte_offset = content.find(text)
                
                record = {
                    "text": text,
                    "file_path": str(relative_path),
                    "byte_offset": byte_offset,
                    "record_index": i,
                    "metadata": {
                        "source_file": str(relative_path),
                        "record_number": i + 1,
                        "total_records_in_file": len(parts)
                    }
                }
                records.append(record)
            
            logger.info(f"Parsed {len(records)} records from {relative_path}")
            
        except Exception as e:
            logger.error(f"Error parsing file {file_path}: {e}")
        
        return records 