"""
VecBook HTTP Server Implementation
Provides HTTP interface for embedding text strings
"""

import json
import logging
import sys
from pathlib import Path
from typing import Dict, List, Any, Optional

from fastapi import FastAPI, HTTPException
from fastapi.responses import JSONResponse
from pydantic import BaseModel
import uvicorn

from .vecx import VecBookIndex

# Initialize logging to stderr
logging.basicConfig(level=logging.INFO, stream=sys.stderr)
logger = logging.getLogger(__name__)

class EmbedRequest(BaseModel):
    """Request model for embedding endpoint"""
    texts: List[str]

class EmbedResponse(BaseModel):
    """Response model for embedding endpoint"""
    embeddings: List[List[float]]

class CosineBarycenterRequest(BaseModel):
    """Request model for cosine barycenter similarity endpoint"""
    target_strings: List[str]
    test_strings: List[str]

class CosineBarycenterResponse(BaseModel):
    """Response model for cosine barycenter similarity endpoint"""
    results: List[Dict[str, Any]]

class TargetStringsRequest(BaseModel):
    """Request model for setting target strings"""
    target_strings: List[str]

class TargetStringsResponse(BaseModel):
    """Response model for target strings operations"""
    status: str
    message: str
    target_count: Optional[int] = None
    barycenter_dimension: Optional[int] = None
    target_strings: Optional[List[str]] = None

class CompareRequest(BaseModel):
    """Request model for compare endpoint"""
    test_strings: List[str]

class VecBookHTTPServer:
    """VecBook HTTP Server that provides embedding functionality"""
    
    def __init__(self, index: VecBookIndex):
        """Initialize the HTTP server with a VecBookIndex instance"""
        self.index = index
        self.app = FastAPI(title="VecBook HTTP Server", version="1.0.0")
        self._register_routes()
    
    def _register_routes(self):
        """Register all HTTP routes"""
        
        @self.app.post("/embed", response_model=EmbedResponse)
        async def embed_texts(request: EmbedRequest):
            """Embed a list of text strings and return their vectors"""
            try:
                if not request.texts:
                    raise HTTPException(status_code=400, detail="Texts list cannot be empty")
                
                # Validate input
                if not all(isinstance(text, str) for text in request.texts):
                    raise HTTPException(status_code=400, detail="All texts must be strings")
                
                if len(request.texts) > 1000:  # Reasonable limit
                    raise HTTPException(status_code=400, detail="Too many texts (max 1000)")
                
                # Generate embeddings
                embeddings = self.index.embed_texts(request.texts)
                
                if not embeddings:
                    raise HTTPException(status_code=500, detail="Failed to generate embeddings")
                
                return EmbedResponse(embeddings=embeddings)
                
            except HTTPException:
                raise
            except Exception as e:
                logger.error(f"Error in embed endpoint: {e}")
                raise HTTPException(status_code=500, detail=f"Internal server error: {str(e)}")
        
        @self.app.put("/targets", response_model=TargetStringsResponse)
        async def set_targets(request: TargetStringsRequest):
            """Set target strings and calculate their barycenter"""
            try:
                if not request.target_strings:
                    raise HTTPException(status_code=400, detail="Target strings list cannot be empty")
                
                # Validate input
                if not all(isinstance(text, str) for text in request.target_strings):
                    raise HTTPException(status_code=400, detail="All target strings must be strings")
                
                if len(request.target_strings) > 1000:  # Reasonable limit
                    raise HTTPException(status_code=400, detail="Too many target strings (max 1000)")
                
                # Set target strings and calculate barycenter
                result = self.index.set_target_strings(request.target_strings)
                
                if result["status"] == "error":
                    raise HTTPException(status_code=500, detail=result["message"])
                
                return TargetStringsResponse(
                    status=result["status"],
                    message=result["message"],
                    target_count=result["target_count"],
                    barycenter_dimension=result["barycenter_dimension"]
                )
                
            except HTTPException:
                raise
            except Exception as e:
                logger.error(f"Error in set targets endpoint: {e}")
                raise HTTPException(status_code=500, detail=f"Internal server error: {str(e)}")
        
        @self.app.get("/targets", response_model=TargetStringsResponse)
        async def get_targets():
            """Get information about currently stored target strings"""
            try:
                result = self.index.get_target_info()
                
                if result["status"] == "error":
                    raise HTTPException(status_code=404, detail=result["message"])
                
                return TargetStringsResponse(
                    status=result["status"],
                    message=result["message"],
                    target_count=result["target_count"],
                    target_strings=result["target_strings"],
                    barycenter_dimension=result["barycenter_dimension"]
                )
                
            except HTTPException:
                raise
            except Exception as e:
                logger.error(f"Error in get targets endpoint: {e}")
                raise HTTPException(status_code=500, detail=f"Internal server error: {str(e)}")
        
        @self.app.post("/cosine-similarity", response_model=CosineBarycenterResponse)
        async def cosine_similarity(request: CosineBarycenterRequest):
            """Calculate cosine barycenter of target strings and return similarities with test strings"""
            try:
                if not request.target_strings:
                    raise HTTPException(status_code=400, detail="Target strings list cannot be empty")
                
                if not request.test_strings:
                    raise HTTPException(status_code=400, detail="Test strings list cannot be empty")
                
                # Validate input
                if not all(isinstance(text, str) for text in request.target_strings):
                    raise HTTPException(status_code=400, detail="All target strings must be strings")
                
                if not all(isinstance(text, str) for text in request.test_strings):
                    raise HTTPException(status_code=400, detail="All test strings must be strings")
                
                if len(request.target_strings) > 1000 or len(request.test_strings) > 1000:  # Reasonable limit
                    raise HTTPException(status_code=400, detail="Too many strings (max 1000)")
                
                # Calculate cosine similarities
                results = self.index.cosine_barycenter_similarity(
                    request.target_strings, 
                    request.test_strings
                )
                
                if not results:
                    raise HTTPException(status_code=500, detail="Failed to calculate cosine similarities")
                
                return CosineBarycenterResponse(results=results)
                
            except HTTPException:
                raise
            except Exception as e:
                logger.error(f"Error in cosine similarity endpoint: {e}")
                raise HTTPException(status_code=500, detail=f"Internal server error: {str(e)}")
        
        @self.app.post("/compare", response_model=CosineBarycenterResponse)
        async def compare_against_barycenter(request: CompareRequest):
            """Compare test strings against the stored barycenter"""
            try:
                if not request.test_strings:
                    raise HTTPException(status_code=400, detail="Test strings list cannot be empty")
                
                # Validate input
                if not all(isinstance(text, str) for text in request.test_strings):
                    raise HTTPException(status_code=400, detail="All test strings must be strings")
                
                if len(request.test_strings) > 1000:  # Reasonable limit
                    raise HTTPException(status_code=400, detail="Too many test strings (max 1000)")
                
                # Compare against stored barycenter
                results = self.index.compare_against_barycenter(request.test_strings)
                
                if not results:
                    raise HTTPException(status_code=500, detail="Failed to compare against barycenter. Make sure targets are set first.")
                
                return CosineBarycenterResponse(results=results)
                
            except HTTPException:
                raise
            except Exception as e:
                logger.error(f"Error in compare endpoint: {e}")
                raise HTTPException(status_code=500, detail=f"Internal server error: {str(e)}")
        
        @self.app.get("/health")
        async def health_check():
            """Health check endpoint"""
            return {"status": "healthy", "service": "vecbook"}
        
        @self.app.get("/stats")
        async def get_stats():
            """Get indexing statistics"""
            return self.index.stats
    
    def run(self, host: str = "0.0.0.0", port: int = 51539):
        """Run the HTTP server"""
        logger.info(f"Starting VecBook HTTP server on {host}:{port}")
        uvicorn.run(self.app, host=host, port=port, log_level="info") 