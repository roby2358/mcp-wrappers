"""
Unit tests for TextRecords discover_files method
"""

import unittest
import tempfile
import shutil
from pathlib import Path
from src.textrec.text_records import TextRecords


class TestTextRecordsDiscover(unittest.TestCase):
    """Test cases for TextRecords discover_files method"""
    
    def setUp(self):
        """Set up test fixtures with temporary directory and test files"""
        self.test_dir = Path(tempfile.mkdtemp())
        
        # Create test directory structure with .txt files
        (self.test_dir / "file1.txt").write_text("content1")
        (self.test_dir / "file2.txt").write_text("content2")
        (self.test_dir / "not_txt.json").write_text('{"key": "value"}')
        
        # Create subdirectory with more .txt files
        subdir = self.test_dir / "subdir"
        subdir.mkdir()
        (subdir / "file3.txt").write_text("content3")
        (subdir / "file4.txt").write_text("content4")
        
        self.text_records = TextRecords(self.test_dir)
    
    def tearDown(self):
        """Clean up test fixtures"""
        shutil.rmtree(self.test_dir)
    
    def test_discover_files_finds_txt_files(self):
        """Test that discover_files finds all .txt files recursively"""
        found_files = self.text_records.discover_files()
        
        # Convert to relative paths for easier comparison
        found_names = {f.name for f in found_files}
        expected_names = {"file1.txt", "file2.txt", "file3.txt", "file4.txt"}
        
        self.assertEqual(found_names, expected_names)
        self.assertEqual(len(found_files), 4)
    
    def test_discover_files_ignores_non_txt(self):
        """Test that discover_files ignores non-.txt files"""
        found_files = self.text_records.discover_files()
        
        # Check that .json file is not included
        found_names = {f.name for f in found_files}
        self.assertNotIn("not_txt.json", found_names)
    
    def test_discover_files_empty_directory(self):
        """Test discover_files with empty directory"""
        empty_dir = Path(tempfile.mkdtemp())
        try:
            text_records = TextRecords(empty_dir)
            found_files = text_records.discover_files()
            self.assertEqual(len(found_files), 0)
        finally:
            shutil.rmtree(empty_dir)
    
    def test_discover_files_nonexistent_path(self):
        """Test discover_files with non-existent path"""
        nonexistent_path = Path("/nonexistent/path")
        text_records = TextRecords(nonexistent_path)
        found_files = text_records.discover_files()
        self.assertEqual(len(found_files), 0)
    
    def test_discover_files_returns_path_objects(self):
        """Test that discover_files returns Path objects"""
        found_files = self.text_records.discover_files()
        
        for file_path in found_files:
            self.assertIsInstance(file_path, Path)
            self.assertTrue(file_path.exists())
            self.assertTrue(file_path.is_file())


if __name__ == '__main__':
    unittest.main() 