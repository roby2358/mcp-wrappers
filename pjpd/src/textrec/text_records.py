"""
Text Records Management
Handles discovery and parsing of text files broken into records with --- separators
"""

import logging
import os
import urllib.parse
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any

logger = logging.getLogger(__name__)

class TextRecords:
    """Handles discovery and parsing of text files broken into records with --- separators"""
    
    def __init__(self, path: Path):
        # URL decode the path if it contains % characters
        # Cursor encodes : as %3A in file paths
        path_str = str(path)
        if '%' in path_str:
            path_str = urllib.parse.unquote(path_str)

        self.path = Path(path_str)
        
        # Debug logging for path resolution
        logger.info(f"TextRecords path: {self.path}")
        logger.info(f"Path exists: {self.path.exists()}")
        
        # Throw an exception if the path does not exist (cross-os, linux, Win 11, osx)
        if not Path(path_str).exists():
            raise FileNotFoundError(f"Path does not exist: {path_str}")
    
    def discover_files(self) -> List[Path]:
        """Discover all .txt files in the path recursively"""
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
    
    def write_atomic(self, file_path: Path, content: str) -> None:
        """Atomically (and safely) write content to a file with timestamped backup.
        
        A timestamped backup is stored in a sibling bak/ directory to keep
        behaviour consistent across record types.
        
        Args:
            file_path: The target file path to write to
            content: The content to write to the file
        """
        try:
            # Ensure the target directory exists
            file_path.parent.mkdir(parents=True, exist_ok=True)
            
            timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
            bak_dir = file_path.parent / "bak"
            bak_dir.mkdir(parents=True, exist_ok=True)

            # Write new content to timestamped file
            new_path = file_path.with_name(f"{file_path.stem}.{timestamp}{file_path.suffix}")
            with open(new_path, "w", encoding="utf-8") as fh:
                fh.write(content)

            # Move existing file to backup if it exists
            if file_path.exists():
                bak_path = bak_dir / f"{file_path.stem}.{timestamp}{file_path.suffix}"
                os.replace(file_path, bak_path)

            # Atomically move new file into place
            os.replace(new_path, file_path)
        except Exception as exc:
            logger.error("Error writing file %s: %s", file_path, exc)
            raise 