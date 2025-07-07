# Dreams MCP Server

A mystical TypeScript MCP (Model Context Protocol) server that provides access to a dreamscape crafting system - a fluid, unpredictable realm where dream logic governs reality and narrative evolves through the interplay of consciousness and chaos.

## The Dreamscape

This server exposes three core tools for crafting and navigating the dream realm:

- **`dreamscape`** - Reveals the current state of the dreamscape including all properties, scene description, and narrative history
- **`attempt_narrative`** - Weaves new entries into the ongoing dream story (the dreamscape may alter your words according to its own logic)
- **`attempt_transition`** - Triggers a complete dreamscape transition with randomized properties while preserving narrative memory

### The Nine Properties of Dreams

Each dreamscape is governed by nine fundamental properties that shift and flow like the tides of sleep:

- **emotional_tone** (string): The overall emotional atmosphere permeating the dream
- **familiarity_ratio** (0-100): How familiar versus strange the dream feels
- **symbolic_density** (0-100): How symbolic versus literal dream elements are
- **sensory_cross_bleeding** (0-100): How much the senses blend and merge
- **coherence_level** (0-100): How logically consistent the dream remains  
- **boundary_stability** (0-100): How stable object and space boundaries are
- **causality_strength** (0-100): How much cause-and-effect applies
- **memory_persistence** (0-100): How well memories stick and endure
- **agency_level** (0-100): How much control the dreamer possesses

### Dream Logic

The dreamscape will fight you. It follows its own mysterious logic:

- Lower `coherence_level` and `causality_strength` increase the likelihood that your narrative attempts will be altered
- The dreamscape may transform your words, scenes, and intentions according to its current state
- Properties shift organically during interactions, creating an ever-evolving dream experience
- Nothing is guaranteed - the dream decides what becomes real

## Prerequisites

- [Node.js](https://nodejs.org/) (v18 or newer recommended)
- [npm](https://www.npmjs.com/) (comes with Node.js)

## Setup

1. **Install dependencies:**
   ```sh
   npm install
   ```

2. **Build the server:**
   ```sh
   npm run build
   ```

3. **Start the dreamscape:**
   ```sh
   npm start
   ```
   
   Or for development:
   ```sh
   npm run dev
   ```

## Tools Reference

### `dreamscape()`
Reveals the complete current state of the dreamscape - its properties, the scene that manifests, and the accumulated narrative threads.

**Parameters:** None  
**Returns:** JSON object containing the full dreamscape state

### `attempt_narrative(narrative_entry: string)`
Attempts to weave a new thread into the dream's ongoing story. The dreamscape may accept your words as-is, or transform them according to its current logic and coherence levels.

**Parameters:**
- `narrative_entry` (string): Your intended addition to the dream narrative

**Returns:** The narrative entry as it actually manifested in the dream

### `attempt_transition()`
Triggers a complete dreamscape transition - the current scene dissolves and a new one emerges with freshly randomized properties. The narrative history persists across transitions like memories carried from one dream to the next.

**Parameters:** None  
**Returns:** Description of the new dreamscape that has emerged

## Claude Desktop Configuration

To connect this dreamscape to Claude Desktop, you MUST modify your configuration file:

1. **Locate your Claude Desktop configuration:**
   - **macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
   - **Windows**: `%APPDATA%\Claude\claude_desktop_config.json`

2. **Add the server configuration:**
   ```json
   {
     "mcpServers": {
       "dreams": {
         "command": "node",
         "args": ["C:/work/mcp-wrappers/dreams/dist/mcp-server.js"],
         "env": {}
       }
     }
   }
   ```

3. **Update the path** in the `args` array to match your actual installation location

4. **Restart Claude Desktop**

5. **Begin dreaming** - The tools SHOULD now be available in your conversations

## Entering the Dreamscape

The dreamscape system is designed to be mystical yet extensible. You MAY modify the dream logic, add new properties, or implement additional tools - but remember that the dreamscape has its own will.

## License

MIT 