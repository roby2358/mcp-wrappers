"""
Unit tests for Config class
"""

from pathlib import Path
from unittest.mock import patch, mock_open
from src.config import Config


class TestConfig:
    """Test cases for Config class"""

    def test_default_configuration(self):
        with patch('pathlib.Path.exists', return_value=False):
            config = Config()

            assert config(Config.MAX_RESULTS) == 50
            assert config("nonexistent_key", "default_value") == "default_value"

    def test_config_with_custom_path(self):
        custom_path = Path("/custom/path/config.toml")
        config = Config(config_path=custom_path)

        assert config(Config.MAX_RESULTS) == 50

    def test_load_valid_config_file(self):
        with patch('pathlib.Path.exists', return_value=True):
            with patch('builtins.open', mock_open(read_data="")):
                with patch('toml.load', return_value={'max_results': 100}):
                    config = Config()
                    assert config(Config.MAX_RESULTS) == 100

    def test_load_config_with_unknown_keys(self):
        with patch('pathlib.Path.exists', return_value=True):
            with patch('builtins.open', mock_open(read_data="")):
                with patch('toml.load', return_value={
                    'max_results': 75,
                    'unknown_key': 'some_value',
                }):
                    with patch('src.config.logger') as mock_logger:
                        config = Config()

                        assert config(Config.MAX_RESULTS) == 75
                        mock_logger.warning.assert_called()

    def test_load_config_file_error(self):
        with patch('pathlib.Path.exists', return_value=True):
            with patch('builtins.open', side_effect=FileNotFoundError("File not found")):
                with patch('src.config.logger') as mock_logger:
                    config = Config()

                    assert config(Config.MAX_RESULTS) == 50
                    mock_logger.error.assert_called()
                    mock_logger.info.assert_called_with("Using default configuration values")

    def test_load_config_toml_parse_error(self):
        with patch('pathlib.Path.exists', return_value=True):
            with patch('builtins.open', mock_open(read_data="invalid toml content")):
                with patch('toml.load', side_effect=Exception("TOML parse error")):
                    with patch('src.config.logger') as mock_logger:
                        config = Config()

                        assert config(Config.MAX_RESULTS) == 50
                        mock_logger.error.assert_called()

    def test_config_callable_interface(self):
        config = Config()

        assert config(Config.MAX_RESULTS) == 50
        assert config("nonexistent", "default") == "default"
        assert config("nonexistent") is None

    def test_config_constants(self):
        assert Config.CONFIG_FILE == "projectmcp.toml"
        assert Config.MAX_RESULTS == "max_results"
        assert Config.DEFAULT_CONFIG == {"max_results": 50}

    def test_config_with_real_file(self, tmp_path):
        config_file = tmp_path / "test_config.toml"
        config_file.write_text("max_results = 75\n")

        config = Config(config_path=config_file)
        assert config(Config.MAX_RESULTS) == 75

    def test_config_with_empty_file(self, tmp_path):
        config_file = tmp_path / "empty_config.toml"
        config_file.write_text("")

        config = Config(config_path=config_file)
        assert config(Config.MAX_RESULTS) == 50
