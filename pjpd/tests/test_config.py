"""
Unit tests for Config class
Tests configuration loading, parsing, and access functionality
"""

import pytest
import tempfile
import os
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock
from src.config import Config


class TestConfig:
    """Test cases for Config class"""
    
    def test_default_configuration(self):
        """Test that Config uses default values when no config file exists"""
        with patch('pathlib.Path.exists', return_value=False):
            config = Config()
            
            # Test default values
            assert config(Config.PROJECTS_DIRECTORY) == "~/projects"
            assert config(Config.MAX_RESULTS) == 50
            
            # Test with custom default
            assert config("nonexistent_key", "default_value") == "default_value"
    
    def test_config_with_custom_path(self):
        """Test Config initialization with custom config path"""
        custom_path = Path("/custom/path/config.toml")
        config = Config(config_path=custom_path)
        
        # Should still have default values
        assert config(Config.PROJECTS_DIRECTORY) == "~/projects"
        assert config(Config.MAX_RESULTS) == 50
    
    def test_load_valid_config_file(self):
        """Test loading configuration from a valid TOML file"""
        with patch('pathlib.Path.exists', return_value=True):
            with patch('builtins.open', mock_open(read_data="")):
                with patch('toml.load', return_value={
                    'projects_directory': '/custom/projects',
                    'max_results': 100
                }):
                    config = Config()
                    
                    assert config(Config.PROJECTS_DIRECTORY) == "/custom/projects"
                    assert config(Config.MAX_RESULTS) == 100
    
    def test_load_config_with_tilde_expansion(self):
        """Test that tilde expansion is applied when loading config"""
        with patch('pathlib.Path.exists', return_value=True):
            with patch('builtins.open', mock_open(read_data="")):
                with patch('toml.load', return_value={
                    'projects_directory': '~/my_projects',
                    'max_results': 25
                }):
                    with patch('pathlib.Path.expanduser', return_value=Path('/home/user/my_projects')):
                        config = Config()
                        
                        assert config(Config.PROJECTS_DIRECTORY) == "/home/user/my_projects"
    
    def test_load_config_with_unknown_keys(self):
        """Test that unknown configuration keys are logged but ignored"""
        config_content = """
        projects_directory = "/custom/projects"
        unknown_key = "some_value"
        another_unknown = 123
        """
        
        with patch('pathlib.Path.exists', return_value=True):
            with patch('builtins.open', mock_open(read_data=config_content)):
                with patch('toml.load', return_value={
                    'projects_directory': '/custom/projects',
                    'unknown_key': 'some_value',
                    'another_unknown': 123
                }):
                    with patch('src.config.logger') as mock_logger:
                        config = Config()
                        
                        # Should only load known keys
                        assert config(Config.PROJECTS_DIRECTORY) == "/custom/projects"
                        assert config(Config.MAX_RESULTS) == 50  # Default value
                        
                        # Should log warnings for unknown keys
                        mock_logger.warning.assert_called()
    
    def test_load_config_file_error(self):
        """Test handling of file reading errors"""
        with patch('pathlib.Path.exists', return_value=True):
            with patch('builtins.open', side_effect=FileNotFoundError("File not found")):
                with patch('src.config.logger') as mock_logger:
                    config = Config()
                    
                    # Should fall back to defaults
                    assert config(Config.PROJECTS_DIRECTORY) == "~/projects"
                    assert config(Config.MAX_RESULTS) == 50
                    
                    # Should log error
                    mock_logger.error.assert_called()
                    mock_logger.info.assert_called_with("Using default configuration values")
    
    def test_load_config_toml_parse_error(self):
        """Test handling of TOML parsing errors"""
        with patch('pathlib.Path.exists', return_value=True):
            with patch('builtins.open', mock_open(read_data="invalid toml content")):
                with patch('toml.load', side_effect=Exception("TOML parse error")):
                    with patch('src.config.logger') as mock_logger:
                        config = Config()
                        
                        # Should fall back to defaults
                        assert config(Config.PROJECTS_DIRECTORY) == "~/projects"
                        assert config(Config.MAX_RESULTS) == 50
                        
                        # Should log error
                        mock_logger.error.assert_called()
                        mock_logger.info.assert_called_with("Using default configuration values")
    
    def test_config_callable_interface(self):
        """Test the callable interface of Config"""
        config = Config()
        
        # Test getting existing keys
        assert config(Config.PROJECTS_DIRECTORY) == "~/projects"
        assert config(Config.MAX_RESULTS) == 50
        
        # Test getting non-existent key with default
        assert config("nonexistent", "default") == "default"
        assert config("nonexistent") is None
    
    def test_config_constants(self):
        """Test that configuration constants are properly defined"""
        assert Config.CONFIG_FILE == "projectmcp.toml"
        assert Config.PROJECTS_DIRECTORY == "projects_directory"
        assert Config.MAX_RESULTS == "max_results"
        
        # Test default config structure
        assert Config.DEFAULT_CONFIG == {
            "projects_directory": "~/projects",
            "max_results": 50
        }
    
    def test_config_with_real_file(self, tmp_path):
        """Test Config with a real temporary file"""
        # Create a temporary config file
        config_file = tmp_path / "test_config.toml"
        config_content = """
        projects_directory = "/test/projects"
        max_results = 75
        """
        config_file.write_text(config_content)
        
        # Test loading from the real file
        config = Config(config_path=config_file)
        
        assert config(Config.PROJECTS_DIRECTORY) == "/test/projects"
        assert config(Config.MAX_RESULTS) == 75
    
    def test_config_with_partial_file(self, tmp_path):
        """Test Config with a file that only contains some keys"""
        # Create a temporary config file with only one key
        config_file = tmp_path / "partial_config.toml"
        config_content = """
        max_results = 200
        """
        config_file.write_text(config_content)
        
        # Test loading from the partial file
        config = Config(config_path=config_file)
        
        # Should use file value for max_results
        assert config(Config.MAX_RESULTS) == 200
        # Should use default for projects_directory
        assert config(Config.PROJECTS_DIRECTORY) == "~/projects"
    
    def test_config_with_empty_file(self, tmp_path):
        """Test Config with an empty file"""
        # Create an empty config file
        config_file = tmp_path / "empty_config.toml"
        config_file.write_text("")
        
        # Test loading from the empty file
        config = Config(config_path=config_file)
        
        # Should use defaults
        assert config(Config.PROJECTS_DIRECTORY) == "~/projects"
        assert config(Config.MAX_RESULTS) == 50 

    def test_expand_user_path_method(self):
        """Test the _expand_user_path method with various scenarios"""
        config = Config()
        
        # Test 1: Default value should not be expanded (preserves literal "~/projects")
        result = config._expand_user_path("~/projects")
        assert result == "~/projects"
        
        # Test 2: Custom tilde path should be expanded
        with patch('pathlib.Path.expanduser', return_value=Path('/home/user/custom_projects')):
            result = config._expand_user_path("~/custom_projects")
            assert result == "/home/user/custom_projects"
        
        # Test 3: Non-tilde path should be returned as-is
        result = config._expand_user_path("/absolute/path")
        assert result == "/absolute/path"
        
        # Test 4: Empty string should be returned as-is
        result = config._expand_user_path("")
        assert result == ""
        
        # Test 5: Path with tilde in middle should not be expanded
        result = config._expand_user_path("/path/~/middle")
        assert result == "/path/~/middle"
        
        # Test 6: Path with tilde but not at start should not be expanded
        result = config._expand_user_path("path/~/middle")
        assert result == "path/~/middle"
        
        # Test 7: Path with multiple tildes should expand the leading tilde only
        with patch('pathlib.Path.expanduser', return_value=Path('/home/user/path/~')):
            result = config._expand_user_path("~/path/~")
            assert result == "/home/user/path/~" 