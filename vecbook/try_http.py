#!/usr/bin/env python3
"""
Test script for VecBook HTTP interface
"""

import requests
import json
import time

def test_http_interface():
    """Test the HTTP interface"""
    base_url = "http://localhost:51539"
    
    # Test data
    test_texts = [
        "This is a test sentence for embedding.",
        "Another sentence to test the embedding functionality.",
        "The quick brown fox jumps over the lazy dog."
    ]
    
    print("Testing VecBook HTTP interface...")
    print(f"Base URL: {base_url}")
    
    # Test health endpoint
    try:
        response = requests.get(f"{base_url}/health")
        print(f"Health check: {response.status_code} - {response.json()}")
    except requests.exceptions.ConnectionError:
        print("❌ Could not connect to HTTP server. Make sure it's running on port 51539.")
        return False
    
    # Test stats endpoint
    try:
        response = requests.get(f"{base_url}/stats")
        print(f"Stats: {response.status_code} - {response.json()}")
    except Exception as e:
        print(f"❌ Stats endpoint error: {e}")
    
    # Test embed endpoint
    try:
        payload = {"texts": test_texts}
        response = requests.post(f"{base_url}/embed", json=payload)
        
        if response.status_code == 200:
            result = response.json()
            embeddings = result.get("embeddings", [])
            print(f"✅ Embed endpoint successful!")
            print(f"   Input texts: {len(test_texts)}")
            print(f"   Output embeddings: {len(embeddings)}")
            print(f"   Embedding dimension: {len(embeddings[0]) if embeddings else 0}")
            
            # Show first embedding (truncated)
            if embeddings:
                first_embedding = embeddings[0][:5]  # Show first 5 values
                print(f"   Sample embedding: {first_embedding}...")
            
            return True
        else:
            print(f"❌ Embed endpoint failed: {response.status_code} - {response.text}")
            return False
            
    except Exception as e:
        print(f"❌ Embed endpoint error: {e}")
        return False

if __name__ == "__main__":
    success = test_http_interface()
    if success:
        print("\n✅ HTTP interface test completed successfully!")
    else:
        print("\n❌ HTTP interface test failed!") 