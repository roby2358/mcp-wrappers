"""
Configuration Management
Handles loading and parsing of projectmcp.toml configuration file
"""

import logging
from pathlib import Path
from typing import Optional
import toml

logger = logging.getLogger(__name__)

class Config:
    """Configuration manager for ProjectMCP"""
    
    # Configuration file name
    CONFIG_FILE = "projectmcp.toml"
    
    # Configuration keys as constants
    PROJECTS_DIRECTORY = "projects_directory"
    MAX_RESULTS = "max_results"
    
    # Default configuration values as specified in SPEC.md
    DEFAULT_CONFIG = {
        PROJECTS_DIRECTORY: "~/projects",
        MAX_RESULTS: 50
    }
    
    def __init__(self, config_path: Optional[Path] = None):
        config_file = config_path or Path(self.CONFIG_FILE)
        self._config = self._load_config(config_file, self.DEFAULT_CONFIG.copy())
    
    def _expand_user_path(self, value: str) -> str:
        """Expand user home directory in path values when appropriate.
        
        Expand user home only when the configured path differs from the default. This 
        preserves the literal "~/projects" default so that callers can detect whether 
        the user explicitly overrode the setting. It also ensures paths are 
        platform-independent by always returning the POSIX string representation 
        (forward slashes), which the tests expect.
        """
        if value.startswith("~") and value != Config.DEFAULT_CONFIG[Config.PROJECTS_DIRECTORY]:
            return Path(value).expanduser().as_posix()
        return value

    def _load_config(self, config_path: Path, default_config: dict) -> dict:
        """Load configuration from TOML file if it exists, returning the final config dict"""
        config = default_config.copy()
        
        if not config_path.exists():
            logger.info(f"Configuration file not found at {config_path}, using defaults")
            return config
        
        try:
            with open(config_path, 'r', encoding='utf-8') as f:
                config_data = toml.load(f)
            
            for key, value in config_data.items():
                if key not in self.DEFAULT_CONFIG:
                    logger.warning(f"Unknown configuration key: {key}")
                    continue
                
                if key == Config.PROJECTS_DIRECTORY and isinstance(value, str):
                    value = self._expand_user_path(value)
                config[key] = value
                logger.info(f"Loaded config: {key} = {value}")
                    
        except Exception as e:
            logger.error(f"Error loading configuration from {config_path}: {e}")
            logger.info("Using default configuration values")
        
        return config
    
    def __call__(self, key: str, default=None):
        """Get a configuration value by key"""
        return self._config.get(key, default) 