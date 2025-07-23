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