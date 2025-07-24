#!/usr/bin/env python3
"""
Test script for VecBook cosine barycenter similarity
"""

import requests
import json

def test_cosine_barycenter():
    """Test the cosine barycenter similarity endpoint"""
    base_url = "http://localhost:51539"
    
    # Test data
    ## Simple
    target_strings = ["spoon","fork","knife"]

    test_strings = ["soup spoon","salad fork","plate","napkin","racecar","hippotomus"]

    ## ML Stuff
    # target_strings = [
    #     "Machine learning algorithms process large datasets efficiently.",
    #     "Deep learning models require significant computational resources.",
    #     "Neural networks learn patterns from training data."
    # ]

    # test_strings = [
    #     "The quick brown fox jumps over the lazy dog.",
    #     "Machine learning is a subset of artificial intelligence.",
    #     "Vector embeddings capture semantic meaning in high-dimensional space.",
    #     "Natural language processing enables computers to understand human language.",
    #     "Semantic search goes beyond keyword matching to understand context.",
    #     "Information retrieval systems help users find relevant documents.",
    #     "Text preprocessing is essential for effective NLP applications.",
    #     "Cosine similarity measures the angle between two vectors."
    # ]
    
    ## Mixed
    # target_strings = ["the quick brown fox", "jumps over", "the lazy dog."]

    # test_strings = ["clouds float",
    #                 "ocean waves break",
    #                 "green grass",
    #                 "crunchy red apple",
    #                 "songbird sings",
    #                 "squirrel runs"]
    
    print("Testing VecBook cosine barycenter similarity...")
    print(f"Base URL: {base_url}")
    print(f"Target strings: {len(target_strings)}")
    print(f"Test strings: {len(test_strings)}")
    
    # Test health endpoint first
    try:
        response = requests.get(f"{base_url}/health")
        print(f"Health check: {response.status_code} - {response.json()}")
    except requests.exceptions.ConnectionError:
        print("❌ Could not connect to HTTP server. Make sure it's running on port 51539.")
        return False
    
    # Step 1: Set target strings (this calculates barycenter once)
    print("\n1. Setting target strings...")
    try:
        response = requests.put(
            f"{base_url}/targets",
            json={"target_strings": target_strings},
            headers={"Content-Type": "application/json"}
        )
        
        if response.status_code == 200:
            result = response.json()
            print(f"✅ Targets set successfully!")
            print(f"   Target count: {result['target_count']}")
            print(f"   Barycenter dimension: {result['barycenter_dimension']}")
        else:
            print(f"❌ Error setting targets: {response.status_code} - {response.text}")
            return False
            
    except Exception as e:
        print(f"❌ Error setting targets: {e}")
        return False
    
    # Step 2: Compare test strings against stored barycenter
    print("\n2. Comparing test strings against barycenter...")
    try:
        response = requests.post(
            f"{base_url}/compare",
            json={"test_strings": test_strings},
            headers={"Content-Type": "application/json"}
        )
        
        if response.status_code == 200:
            result = response.json()
            print(f"✅ Cosine barycenter similarity calculation successful!")
            print(f"Results returned: {len(result['results'])}")
            
            # Show the target strings
            print("\nTarget strings:")
            for i, target_string in enumerate(target_strings):
                print(f"  {i+1}. {target_string}")

            # Show results sorted by similarity
            sorted_results = sorted(result['results'], 
                                  key=lambda x: float(x['cosine_similarity']), 
                                  reverse=True)
            
            print("\nResults (sorted by similarity to barycenter):")
            for i, result_item in enumerate(sorted_results):
                print(f"  {i+1}. Similarity: {result_item['cosine_similarity']}")
                print(f"     Text: {result_item['text'][:60]}...")
            
            return True
        else:
            print(f"❌ Error: {response.status_code} - {response.text}")
            return False
            
    except Exception as e:
        print(f"❌ Cosine barycenter test error: {e}")
        return False

if __name__ == "__main__":
    print("VecBook Cosine Barycenter Similarity Test")
    print("=" * 40)
    
    test_cosine_barycenter()
