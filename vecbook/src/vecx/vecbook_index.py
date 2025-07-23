"""
VecBook Index Management
Manages the vector index and document storage
"""

import logging
import sys
import numpy as np
from pathlib import Path
from typing import Dict, List, Any, Optional
from datetime import datetime

import faiss
from sentence_transformers import SentenceTransformer

from ..textrec.text_records import TextRecords

# Initialize logging to stderr
logging.basicConfig(level=logging.INFO, stream=sys.stderr)
logger = logging.getLogger(__name__)

class VecBookIndex:
    """Manages the vector index and document storage"""
    
    def __init__(self, path: Path, max_results: int = 10, 
                 embedding_model: str = "sentence-transformers/all-MiniLM-L6-v2", 
                 similarity_metric: str = "cosine"):
        self.max_results = max_results
        self.embedding_model = embedding_model
        self.similarity_metric = similarity_metric
        
        # Use TextRecords for file handling
        self.text_records = TextRecords(path)
        
        # Vector index components
        self.model = None
        self.faiss_index = None
        self.records = []
        self.embeddings = None
        
        self.stats = {
            "total_records": 0,
            "total_files": 0,
            "indexed_at": None
        }
    
    def _initialize_model(self):
        """Initialize the sentence transformer model"""
        if self.model is None:
            logger.info(f"Loading embedding model: {self.embedding_model}")
            self.model = SentenceTransformer(self.embedding_model)
            logger.info("Model loaded successfully")
    
    def _create_embeddings(self, texts: List[str]) -> np.ndarray:
        """Generate embeddings for a list of texts"""
        self._initialize_model()
        logger.info(f"Generating embeddings for {len(texts)} texts...")
        
        # Generate embeddings in batches for efficiency
        embeddings = self.model.encode(texts, show_progress_bar=True, convert_to_numpy=True)
        logger.info(f"Generated embeddings shape: {embeddings.shape}")
        
        return embeddings
    
    def _build_faiss_index(self, embeddings: np.ndarray):
        """Build FAISS index from embeddings"""
        dimension = embeddings.shape[1]
        logger.info(f"Building FAISS index with dimension: {dimension}")
        
        # Use IndexFlatIP for cosine similarity (inner product with normalized vectors)
        if self.similarity_metric == "cosine":
            # Normalize embeddings for cosine similarity
            faiss.normalize_L2(embeddings)
            self.faiss_index = faiss.IndexFlatIP(dimension)
        else:
            # Use L2 distance
            self.faiss_index = faiss.IndexFlatL2(dimension)
        
        # Add embeddings to index
        self.faiss_index.add(embeddings.astype(np.float32))
        logger.info(f"FAISS index built with {self.faiss_index.ntotal} vectors")
    
    def build_index(self) -> Dict[str, Any]:
        """Build the document index from all files in the data directory"""
        logger.info("Starting index build...")
        
        # Discover all text files
        txt_files = self.text_records.discover_files()
        if not txt_files:
            return {
                "status": "error",
                "message": "No .txt files found in data directory",
                "stats": self.stats
            }
        
        # Clear existing records
        self.records = []
        
        # Parse all files
        for file_path in txt_files:
            file_records = self.text_records.parse_file(file_path)
            self.records.extend(file_records)
        
        if not self.records:
            return {
                "status": "error",
                "message": "No valid records found in text files",
                "stats": self.stats
            }
        
        # Extract texts for embedding
        texts = [record["text"] for record in self.records]
        
        # Generate embeddings
        try:
            self.embeddings = self._create_embeddings(texts)
        except Exception as e:
            logger.error(f"Error generating embeddings: {e}")
            return {
                "status": "error",
                "message": f"Failed to generate embeddings: {str(e)}",
                "stats": self.stats
            }
        
        # Build FAISS index
        try:
            self._build_faiss_index(self.embeddings)
        except Exception as e:
            logger.error(f"Error building FAISS index: {e}")
            return {
                "status": "error",
                "message": f"Failed to build FAISS index: {str(e)}",
                "stats": self.stats
            }
        
        # Update statistics
        self.stats = {
            "total_records": len(self.records),
            "total_files": len(txt_files),
            "indexed_at": datetime.now().isoformat()
        }
        
        logger.info(f"Index build complete: {self.stats['total_records']} records from {self.stats['total_files']} files")
        
        return {
            "status": "success",
            "message": f"Indexed {self.stats['total_records']} records from {self.stats['total_files']} files",
            "stats": self.stats
        }
    
    def search_vector(self, query: str, max_results: Optional[int] = None) -> List[Dict[str, Any]]:
        """Perform vector similarity search"""
        if max_results is None:
            max_results = self.max_results
        
        if not self.records or self.faiss_index is None:
            logger.warning("No records or index available for search. Run reindex first.")
            return []
        
        if not query.strip():
            logger.warning("Empty query provided")
            return []
        
        # Generate embedding for query
        try:
            self._initialize_model()
            query_embedding = self.model.encode([query], convert_to_numpy=True)
            
            # Normalize for cosine similarity if needed
            if self.similarity_metric == "cosine":
                faiss.normalize_L2(query_embedding)
            
        except Exception as e:
            logger.error(f"Error generating query embedding: {e}")
            return []
        
        # Search the index
        try:
            # Limit search results to available records
            k = min(max_results, len(self.records))
            similarities, indices = self.faiss_index.search(query_embedding.astype(np.float32), k)
            
            # Build results
            results = []
            for i, (similarity, idx) in enumerate(zip(similarities[0], indices[0])):
                if idx == -1:  # FAISS returns -1 for invalid results
                    continue
                
                record = self.records[idx].copy()
                
                # Convert similarity score based on metric
                if self.similarity_metric == "cosine":
                    # FAISS IndexFlatIP returns inner product, which equals cosine for normalized vectors
                    # Ensure score is between 0 and 1
                    score = max(0.0, min(1.0, float(similarity)))
                else:
                    # For L2 distance, convert to similarity (smaller distance = higher similarity)
                    # Use negative exponential to convert distance to similarity
                    score = float(np.exp(-similarity))
                
                record["similarity_score"] = f"{score:.6f}"
                results.append(record)
            
            logger.info(f"Vector search returned {len(results)} results for query: '{query[:50]}...'")
            return results
            
        except Exception as e:
            logger.error(f"Error during vector search: {e}")
            return []
    
    def search_simple(self, query: str, max_results: Optional[int] = None) -> List[Dict[str, Any]]:
        """Simple text-based search (fallback when vector search is not available)"""
        logger.info("Using simple text search as fallback")
        
        if max_results is None:
            max_results = self.max_results
        
        if not self.records:
            logger.warning("No records available for search. Run reindex first.")
            return []
        
        # Simple keyword-based search for now
        query_lower = query.lower()
        matching_records = []
        
        for record in self.records:
            text_lower = record["text"].lower()
            if query_lower in text_lower:
                # Calculate simple relevance score based on word frequency
                score = text_lower.count(query_lower) / len(text_lower.split())
                
                search_result = record.copy()
                search_result["similarity_score"] = f"{score:.6f}"
                matching_records.append(search_result)
        
        # Sort by score (descending) and limit results
        matching_records.sort(key=lambda x: float(x["similarity_score"]), reverse=True)
        return matching_records[:max_results]
    
    def search(self, query: str, max_results: Optional[int] = None) -> List[Dict[str, Any]]:
        """Main search method that uses vector search when available, falls back to simple search"""
        if self.faiss_index is not None:
            return self.search_vector(query, max_results)
        else:
            return self.search_simple(query, max_results)
    
    def embed_texts(self, texts: List[str]) -> List[List[float]]:
        """Generate embeddings for a list of texts and return as list of vectors"""
        if not texts:
            return []
        
        try:
            self._initialize_model()
            embeddings = self.model.encode(texts, convert_to_numpy=True)
            
            # Convert numpy array to list of lists
            return embeddings.tolist()
        except Exception as e:
            logger.error(f"Error generating embeddings: {e}")
            return [] 