import unittest
from unittest.mock import patch, MagicMock, mock_open
from pathlib import Path
import sys
import os
import tempfile
import shutil
import toml
import json

# Add src to path so we can import the modules
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from src.mcp_wrapper import VecBookMCPServer, get_script_dir
from src.vecx.vecbook_index import VecBookIndex


class TestVecBookMCPServerIndex(unittest.TestCase):
    """Test the VecBookMCPServer index initialization and configuration"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.temp_dir = tempfile.mkdtemp()
        self.test_data_dir = Path(self.temp_dir) / "test_data"
        self.test_data_dir.mkdir()
        
        # Create some test files with proper record format
        (self.test_data_dir / "test1.txt").write_text(
            "This is a test document about Python programming.\n---\n"
            "Second record about advanced Python concepts."
        )
        (self.test_data_dir / "test2.txt").write_text(
            "Another document about machine learning and AI.\n---\n"
            "Deep learning algorithms and neural networks."
        )
        
        # Create a resources directory for intro.txt
        self.resources_dir = Path(self.temp_dir) / "resources"
        self.resources_dir.mkdir()
        (self.resources_dir / "intro.txt").write_text("Welcome to VecBook!")
    
    def tearDown(self):
        """Clean up test fixtures"""
        shutil.rmtree(self.temp_dir)
    
    @patch('src.mcp_wrapper.get_script_dir')
    def test_server_initialization_with_default_config(self, mock_get_script_dir):
        """Test server initialization with default configuration"""
        mock_get_script_dir.return_value = Path(self.temp_dir)
        
        # Create default config file
        config_path = Path(self.temp_dir) / "vecbook.toml"
        config_data = {
            "data_directory": "test_data",
            "max_results": 10,
            "embedding_model": "sentence-transformers/all-MiniLM-L6-v2",
            "similarity_metric": "cosine"
        }
        with open(config_path, 'w') as f:
            toml.dump(config_data, f)
        
        server = VecBookMCPServer()
        
        # Verify server initialization
        self.assertIsNotNone(server.index)
        self.assertEqual(server.index.max_results, 10)
        self.assertEqual(server.index.embedding_model, "sentence-transformers/all-MiniLM-L6-v2")
        self.assertEqual(server.index.similarity_metric, "cosine")
        self.assertEqual(server.index.text_records.path, Path(self.temp_dir) / "test_data")
    
    @patch('src.mcp_wrapper.get_script_dir')
    def test_server_initialization_with_custom_config(self, mock_get_script_dir):
        """Test server initialization with custom configuration"""
        mock_get_script_dir.return_value = Path(self.temp_dir)
        
        # Create custom config file
        config_path = Path(self.temp_dir) / "vecbook.toml"
        config_data = {
            "data_directory": "test_data",
            "max_results": 25,
            "embedding_model": "custom-model",
            "similarity_metric": "euclidean"
        }
        with open(config_path, 'w') as f:
            toml.dump(config_data, f)
        
        server = VecBookMCPServer()
        
        # Verify custom configuration was applied
        self.assertEqual(server.index.max_results, 25)
        self.assertEqual(server.index.embedding_model, "custom-model")
        self.assertEqual(server.index.similarity_metric, "euclidean")
        self.assertEqual(server.index.text_records.path, Path(self.temp_dir) / "test_data")
    
    @patch('src.mcp_wrapper.get_script_dir')
    def test_server_initialization_no_config_file(self, mock_get_script_dir):
        """Test server initialization when config file doesn't exist"""
        mock_get_script_dir.return_value = Path(self.temp_dir)
        
        # Don't create config file
        server = VecBookMCPServer()
        
        # Verify defaults were used
        self.assertEqual(server.index.max_results, 10)
        self.assertEqual(server.index.embedding_model, "sentence-transformers/all-MiniLM-L6-v2")
        self.assertEqual(server.index.similarity_metric, "cosine")
        self.assertEqual(server.index.text_records.path, Path(self.temp_dir) / "data")
    
    @patch('src.mcp_wrapper.get_script_dir')
    def test_server_initialization_invalid_config_file(self, mock_get_script_dir):
        """Test server initialization with invalid config file"""
        mock_get_script_dir.return_value = Path(self.temp_dir)
        
        # Create invalid config file
        config_path = Path(self.temp_dir) / "vecbook.toml"
        config_path.write_text("invalid toml content [[[")
        
        with patch('sys.stderr'):  # Suppress expected error output
            server = VecBookMCPServer()
        
        # Verify defaults were used when config loading failed
        self.assertEqual(server.index.max_results, 10)
        self.assertEqual(server.index.embedding_model, "sentence-transformers/all-MiniLM-L6-v2")
        self.assertEqual(server.index.similarity_metric, "cosine")
    
    @patch('src.mcp_wrapper.get_script_dir')
    def test_config_loading_partial_config(self, mock_get_script_dir):
        """Test that partial config files work with defaults for missing values"""
        mock_get_script_dir.return_value = Path(self.temp_dir)
        
        # Create partial config file
        config_path = Path(self.temp_dir) / "vecbook.toml"
        config_data = {
            "max_results": 15,
            "similarity_metric": "euclidean"
            # Missing data_directory and embedding_model
        }
        with open(config_path, 'w') as f:
            toml.dump(config_data, f)
        
        server = VecBookMCPServer()
        
        # Verify mix of custom and default values
        self.assertEqual(server.index.max_results, 15)  # Custom
        self.assertEqual(server.index.embedding_model, "sentence-transformers/all-MiniLM-L6-v2")  # Default
        self.assertEqual(server.index.similarity_metric, "euclidean")  # Custom
        self.assertEqual(server.index.text_records.path, Path(self.temp_dir) / "data")  # Default
    
    @patch('src.mcp_wrapper.get_script_dir')
    def test_index_functionality_after_initialization(self, mock_get_script_dir):
        """Test that the index can actually be used after initialization"""
        mock_get_script_dir.return_value = Path(self.temp_dir)
        
        # Create config pointing to our test data
        config_path = Path(self.temp_dir) / "vecbook.toml"
        config_data = {"data_directory": "test_data"}
        with open(config_path, 'w') as f:
            toml.dump(config_data, f)
        
        server = VecBookMCPServer()
        
        # Test that index can build and search
        build_result = server.index.build_index()
        self.assertEqual(build_result["status"], "success")
        self.assertEqual(build_result["stats"]["total_files"], 2)
        self.assertEqual(build_result["stats"]["total_records"], 4)  # 2 records per file
        
        # Test simple search functionality
        search_results = server.index.search_simple("Python", max_results=5)
        self.assertGreater(len(search_results), 0)
        self.assertIn("Python", search_results[0]["text"])
    
    def test_get_script_dir_function(self):
        """Test the get_script_dir utility function"""
        script_dir = get_script_dir()
        
        # Should return the parent directory of src
        expected_dir = Path(__file__).parent.parent
        self.assertEqual(script_dir, expected_dir)
        self.assertTrue(script_dir.exists())
        self.assertTrue((script_dir / "src").exists())
    
    @patch('src.mcp_wrapper.get_script_dir')
    def test_custom_config_path_initialization(self, mock_get_script_dir):
        """Test server initialization with custom config path"""
        mock_get_script_dir.return_value = Path(self.temp_dir)
        
        # Create custom config in different location
        custom_config_path = Path(self.temp_dir) / "custom_config.toml"
        config_data = {
            "data_directory": "test_data",
            "max_results": 50
        }
        with open(custom_config_path, 'w') as f:
            toml.dump(config_data, f)
        
        server = VecBookMCPServer(config_path=custom_config_path)
        
        # Verify custom config was loaded
        self.assertEqual(server.index.max_results, 50)
        self.assertEqual(server.index.text_records.path, Path(self.temp_dir) / "test_data")
    
    @patch('src.mcp_wrapper.get_script_dir')
    def test_mcp_tools_registration(self, mock_get_script_dir):
        """Test that MCP tools are properly registered during initialization"""
        mock_get_script_dir.return_value = Path(self.temp_dir)
        
        server = VecBookMCPServer()
        
        # Verify that the FastMCP instance was created and tools are registered
        self.assertIsNotNone(server.mcp)
        self.assertEqual(server.mcp.name, "vecbook")
        
        # Check that tools and prompts exist (they are registered as decorators)
        # We can't easily test the decorated functions, but we can verify the MCP instance
        self.assertTrue(hasattr(server, 'mcp'))
    
    @patch('src.mcp_wrapper.get_script_dir')
    def test_server_uses_instance_properties_not_globals(self, mock_get_script_dir):
        """Test that server uses instance properties rather than global variables per user preference"""
        mock_get_script_dir.return_value = Path(self.temp_dir)
        
        # Create two separate server instances with different configs
        config1_path = Path(self.temp_dir) / "config1.toml"
        config1_data = {"max_results": 10, "data_directory": "test_data"}
        with open(config1_path, 'w') as f:
            toml.dump(config1_data, f)
        
        config2_path = Path(self.temp_dir) / "config2.toml"  
        config2_data = {"max_results": 20, "data_directory": "test_data"}
        with open(config2_path, 'w') as f:
            toml.dump(config2_data, f)
        
        server1 = VecBookMCPServer(config_path=config1_path)
        server2 = VecBookMCPServer(config_path=config2_path)
        
        # Verify that each server instance maintains its own state
        self.assertEqual(server1.index.max_results, 10)
        self.assertEqual(server2.index.max_results, 20)
        
        # Verify they have separate index instances
        self.assertIsNot(server1.index, server2.index)
        self.assertIsNot(server1.config, server2.config)
        self.assertIsNot(server1.mcp, server2.mcp)


if __name__ == "__main__":
    unittest.main() 