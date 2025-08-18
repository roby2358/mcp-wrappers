"""
Ignore List Management
Handles pjpdignore file parsing and pattern matching for project file filtering
"""

import logging
import re
from pathlib import Path
from typing import List, Set

logger = logging.getLogger(__name__)


class IgnoreList:
    """Manages ignore patterns for filtering project files"""
    
    def __init__(self, projects_dir: Path):
        """Initialize the ignore list for a projects directory.
        
        Args:
            projects_dir: Path to the projects directory containing the pjpdignore file
        """
        self.projects_dir = Path(projects_dir)
        self._patterns: List[str] = []
        self.load_patterns()
        
    def _match_pattern(self, filename: str, pattern: str) -> bool:
        """Case-sensitive pattern matching with wildcard support.
        
        Args:
            filename: The filename to match against
            pattern: The pattern to match (supports * wildcard)
            
        Returns:
            True if filename matches pattern, False otherwise
        """
        # Convert pattern to regex
        regex_pattern = pattern.replace('.', r'\.')  # Escape dots
        regex_pattern = regex_pattern.replace('*', '.*')  # * becomes .*
        regex_pattern = f'^{regex_pattern}$'  # Anchor to start and end
        
        try:
            return bool(re.match(regex_pattern, filename))
        except re.error:
            # If regex compilation fails, fall back to exact match
            return filename == pattern
        
    def load_patterns(self) -> None:
        """Load ignore patterns from the pjpdignore file"""
        self._patterns = []
        ignore_file = self.projects_dir / "pjpdignore"
        
        if not ignore_file.exists():
            logger.debug("No pjpdignore file found, no files will be ignored")
            return
            
        try:
            with open(ignore_file, 'r', encoding='utf-8') as f:
                for line_num, line in enumerate(f, 1):
                    # Strip whitespace
                    line = line.strip()
                    
                    # Skip empty lines and comments
                    if not line or line.startswith('#'):
                        continue
                    
                    # Add the pattern
                    self._patterns.append(line)
                    logger.debug(f"Loaded ignore pattern: {line}")
                    
            logger.info(f"Loaded {len(self._patterns)} ignore patterns from {ignore_file}")
            
        except Exception as e:
            logger.error(f"Error loading pjpdignore file: {e}")
            self._patterns = []
    
    def should_ignore(self, filename: str) -> bool:
        """Check if a filename should be ignored based on the loaded patterns.
        
        Args:
            filename: The filename to check (including extension)
            
        Returns:
            True if the file should be ignored, False otherwise
        """
        for pattern in self._patterns:
            if self._match_pattern(filename, pattern):
                logger.debug(f"File '{filename}' matches ignore pattern '{pattern}'")
                return True
                
        return False
    
    def filter_files(self, files: List[Path]) -> List[Path]:
        """Filter a list of files based on ignore patterns.
        
        Args:
            files: List of Path objects representing files to filter
            
        Returns:
            List of Path objects for files that should not be ignored
        """
        filtered_files = []
        
        for file_path in files:
            filename = file_path.name
            if not self.should_ignore(filename):
                filtered_files.append(file_path)
            else:
                logger.debug(f"Ignoring file: {filename}")
                
        return filtered_files
    
    def get_patterns(self) -> List[str]:
        """Get the currently loaded ignore patterns.
        
        Returns:
            List of ignore patterns
        """
        return self._patterns.copy()
    
    def reload(self) -> None:
        """Reload ignore patterns from the pjpdignore file"""
        self.load_patterns()


class NoIgnoreList:
    """No-op implementation of IgnoreList for when the projects system is not ready."""
    
    def filter_files(self, files: List[Path]) -> List[Path]:
        """Return all files unfiltered when not ready."""
        # Access .name on each file to match IgnoreList behavior
        # This will raise AttributeError if files contain None
        for file_path in files:
            _ = file_path.name  # Access .name to trigger AttributeError if file_path is None
        return files
    
    def should_ignore(self, filename: str) -> bool:
        """Never ignore files when not ready."""
        return False 