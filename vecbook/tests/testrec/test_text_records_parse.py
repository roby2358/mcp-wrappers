"""
Unit tests for TextRecords parse_file method
"""

import unittest
import tempfile
import shutil
from pathlib import Path
from src.textrec.text_records import TextRecords


class TestTextRecordsParse(unittest.TestCase):
    """Test cases for TextRecords parse_file method"""
    
    def setUp(self):
        """Set up test fixtures with temporary directory"""
        self.test_dir = Path(tempfile.mkdtemp())
        self.text_records = TextRecords(self.test_dir)
    
    def tearDown(self):
        """Clean up test fixtures"""
        shutil.rmtree(self.test_dir)
    
    def test_parse_file_single_record(self):
        """Test parsing a file with a single record"""
        test_file = self.test_dir / "single.txt"
        test_file.write_text("This is a single record")
        
        records = self.text_records.parse_file(test_file)
        
        self.assertEqual(len(records), 1)
        record = records[0]
        self.assertEqual(record["text"], "This is a single record")
        self.assertEqual(record["file_path"], "single.txt")
        self.assertEqual(record["record_index"], 0)
        self.assertEqual(record["metadata"]["record_number"], 1)
        self.assertEqual(record["metadata"]["total_records_in_file"], 1)
    
    def test_parse_file_multiple_records(self):
        """Test parsing a file with multiple records separated by ---"""
        content = "First record\n---\nSecond record\n---\nThird record"
        test_file = self.test_dir / "multiple.txt"
        test_file.write_text(content)
        
        records = self.text_records.parse_file(test_file)
        
        self.assertEqual(len(records), 3)
        
        # Check first record
        self.assertEqual(records[0]["text"], "First record")
        self.assertEqual(records[0]["record_index"], 0)
        self.assertEqual(records[0]["metadata"]["record_number"], 1)
        
        # Check second record
        self.assertEqual(records[1]["text"], "Second record")
        self.assertEqual(records[1]["record_index"], 1)
        self.assertEqual(records[1]["metadata"]["record_number"], 2)
        
        # Check third record
        self.assertEqual(records[2]["text"], "Third record")
        self.assertEqual(records[2]["record_index"], 2)
        self.assertEqual(records[2]["metadata"]["record_number"], 3)
        
        # Check metadata consistency
        for record in records:
            self.assertEqual(record["file_path"], "multiple.txt")
            self.assertEqual(record["metadata"]["total_records_in_file"], 3)
    
    def test_parse_file_empty_file(self):
        """Test parsing an empty file"""
        test_file = self.test_dir / "empty.txt"
        test_file.write_text("")
        
        records = self.text_records.parse_file(test_file)
        
        self.assertEqual(len(records), 0)
    
    def test_parse_file_only_separators(self):
        """Test parsing a file with only --- separators"""
        test_file = self.test_dir / "separators.txt"
        test_file.write_text("---\n---\n---")
        
        records = self.text_records.parse_file(test_file)
        
        self.assertEqual(len(records), 0)
    
    def test_parse_file_whitespace_handling(self):
        """Test that whitespace around records is properly stripped"""
        content = "  First record  \n---\n\n  Second record  \n\n---\n  Third record  "
        test_file = self.test_dir / "whitespace.txt"
        test_file.write_text(content)
        
        records = self.text_records.parse_file(test_file)
        
        self.assertEqual(len(records), 3)
        self.assertEqual(records[0]["text"], "First record")
        self.assertEqual(records[1]["text"], "Second record")
        self.assertEqual(records[2]["text"], "Third record")
    
    def test_parse_file_subdirectory(self):
        """Test parsing a file in a subdirectory"""
        subdir = self.test_dir / "subdir"
        subdir.mkdir()
        test_file = subdir / "sub.txt"
        test_file.write_text("Record in subdirectory")
        
        records = self.text_records.parse_file(test_file)
        
        self.assertEqual(len(records), 1)
        # Use Path to normalize separators across platforms
        expected_path = str(Path("subdir") / "sub.txt")
        self.assertEqual(records[0]["file_path"], expected_path)
        self.assertEqual(records[0]["metadata"]["source_file"], expected_path)
    
    def test_parse_file_record_structure(self):
        """Test that each record has the correct structure"""
        test_file = self.test_dir / "structure.txt"
        test_file.write_text("Test record")
        
        records = self.text_records.parse_file(test_file)
        record = records[0]
        
        # Check required keys
        required_keys = ["text", "file_path", "byte_offset", "record_index", "metadata"]
        for key in required_keys:
            self.assertIn(key, record)
        
        # Check metadata structure
        metadata_keys = ["source_file", "record_number", "total_records_in_file"]
        for key in metadata_keys:
            self.assertIn(key, record["metadata"])
        
        # Check data types
        self.assertIsInstance(record["text"], str)
        self.assertIsInstance(record["file_path"], str)
        self.assertIsInstance(record["byte_offset"], int)
        self.assertIsInstance(record["record_index"], int)
        self.assertIsInstance(record["metadata"], dict)
    
    def test_parse_file_nonexistent_file(self):
        """Test parsing a non-existent file returns empty list"""
        nonexistent_file = self.test_dir / "nonexistent.txt"
        
        records = self.text_records.parse_file(nonexistent_file)
        
        self.assertEqual(len(records), 0)


if __name__ == '__main__':
    unittest.main() 