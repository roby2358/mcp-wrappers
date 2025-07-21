#!/usr/bin/env python3
"""
Simple Atproto MCP Server for Bluesky integration
"""

import argparse
import json
import os
import sys
import yaml
from pathlib import Path
from typing import Dict, Any

from mcp.server.fastmcp import FastMCP
from atproto import Client
from atproto import models
from atproto import AtUri

# Constants
MAX_MESSAGE_LENGTH = 300
SETUP_COMMAND = "python atproto-wrapper.py -u username password"


class AtprotoWrapper:
    def __init__(self):
        self.client = None
        self.credentials = None
        self.config_path = None

        if os.name == 'nt':
            self.config_path = Path(os.environ.get('APPDATA', Path.home())) / "atproto" / "credentials.yaml"
        else:
            self.config_path = Path.home() / ".atproto" / "credentials.yaml"

    def clean_to_ascii(self, text: str) -> str:
        """Keep only visible ASCII characters (32-126)."""
        return ''.join(char for char in text if 32 <= ord(char) <= 126).strip()


    @staticmethod
    def mcp_success(result: Any) -> Dict[str, Any]:
        """Return a successful MCP response with the given result."""
        return {
            "success": True,
            "result": result,
            "error": ""
        }


    @staticmethod
    def mcp_failure(error_message: str) -> Dict[str, Any]:
        """Return a failed MCP response with the given error message."""
        return {
            "success": False,
            "result": "",
            "error": error_message
        }

    def load_credentials(self) -> Dict[str, Any]:
        """Load credentials from config file."""
        if not self.config_path.exists():
            return self.mcp_failure(f"No credentials file found at {self.config_path} run {SETUP_COMMAND}")
        
        try:
            with open(self.config_path, 'r') as f:
                data = yaml.safe_load(f)
                # Extract credentials from the bluesky section
                if 'bluesky' in data and isinstance(data['bluesky'], dict):
                    creds = data['bluesky']
                    return self.mcp_success(creds)
                else:
                    return self.mcp_failure("Invalid YAML format: missing 'bluesky' section")
        except Exception as e:
            return self.mcp_failure(f"Error loading credentials: {e}")

    def save_credentials(self, username: str, password: str) -> bool:
        """Save credentials to config file."""
        try:
            # Debug: Print what we received
            print(f"DEBUG: Raw username received: {repr(username)}", file=sys.stderr)
            
            # Clean to visible ASCII only
            clean_username = self.clean_to_ascii(username)
            clean_password = self.clean_to_ascii(password)
            
            print(f"DEBUG: Cleaned username: {repr(clean_username)}", file=sys.stderr)
            
            # Create directory if it doesn't exist
            self.config_path.parent.mkdir(parents=True, exist_ok=True)
            
            # Create YAML structure
            data = {
                "bluesky": {
                    "username": clean_username,
                    "password": clean_password
                }
            }
            
            with open(self.config_path, 'w') as f:
                yaml.dump(data, f, default_flow_style=False, indent=2)
            
            if os.name != 'nt':
                self.config_path.chmod(0o600)
            
            print(f"Credentials saved to {self.config_path}", file=sys.stderr)
            return True
        except Exception as e:
            print(f"Error saving credentials: {e}", file=sys.stderr)
            return False

    def authenticate(self) -> Dict[str, Any]:
        """Authenticate with Bluesky."""
        if self.client:
            return self.mcp_success(f"Already authenticated as {self.credentials['username']}")
        
        if not self.credentials:
            creds_result = self.load_credentials()
            if not creds_result["success"]:
                return creds_result
            self.credentials = creds_result["result"]
            
        try:
            self.client = Client()
            self.client.login(self.credentials["username"], self.credentials["password"])
            return self.mcp_success(f"Authenticated as {self.credentials['username']}")
        except Exception as e:
            return self.mcp_failure(f"Authentication failed: {e}")

    def whoami(self) -> Dict[str, Any]:
        """Check authentication status."""
        return self.authenticate()

    def post_to_bluesky(self, message: str) -> Dict[str, Any]:
        """Post a message to Bluesky using the correct Atproto API."""
        auth = self.authenticate()
        if not auth["success"]:
            return auth

        if not message:
            return self.mcp_failure("No message provided")
        
        if len(message) > MAX_MESSAGE_LENGTH:
            return self.mcp_failure(f"Message too long at {len(message)} characters. Max {MAX_MESSAGE_LENGTH} characters.")
        
        try:
            post_ref = self.client.send_post(text=message)
            return self.mcp_success(f"Posted successfully! URI: {post_ref.uri}")
        except Exception as e:
            return self.mcp_failure(f"Failed to post: {str(e)}")


wrapper = AtprotoWrapper()

mcp = FastMCP("atproto-wrapper")


@mcp.prompt()
def intro() -> str:
    """Return an introductory prompt that describes the Bluesky posting tool."""
    return f"""
You have access to a Bluesky posting tool that can publish posts to the Bluesky social network.

To use this tool, you need to set up your Bluesky credentials first using the command line:
{SETUP_COMMAND}

Once authenticated, you can post messages using the post_to_bluesky function.
For example, to post "Hello, Bluesky!", you would use: "Hello, Bluesky!"

The tool will handle the authentication and posting process to your Bluesky account.
Please set up your credentials and then use the Bluesky posting tool to share a message.
"""


@mcp.tool()
async def atproto_whoami() -> Dict[str, Any]:
    """Check authentication status."""
    return wrapper.whoami()


@mcp.tool()
async def post_to_bluesky(message: str) -> Dict[str, Any]:
    """Post a message to Bluesky."""
    return wrapper.post_to_bluesky(message)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Atproto MCP Server for Bluesky integration")
    parser.add_argument("-u", "--username", help="Bluesky username")
    parser.add_argument("password", nargs="?", help="Bluesky password")
    return parser


def main():
    """Entry point for the application."""
    args = build_parser().parse_args()
    
    # Set up credentials if provided
    if args.username and args.password:
        if wrapper.save_credentials(args.username, args.password):
            print(f"Credentials for {args.username} saved successfully!", file=sys.stderr)
            return
        else:
            sys.exit(1)
    
    print("Starting Atproto MCP Server...", file=sys.stderr)
    mcp.run()


if __name__ == "__main__":
    main() 