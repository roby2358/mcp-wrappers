import unittest
from unittest.mock import patch
import vecbook

class TestVecbook(unittest.TestCase):
    @patch('vecbook.mcp_main')
    def test_main_calls_mcp_main(self, mock_mcp_main):
        vecbook.main()
        mock_mcp_main.assert_called_once() 