# Dreams MCP Server

This project provides a TypeScript MCP (Model Context Protocol) server using the official `@modelcontextprotocol/sdk` that implements a dreamscape simulation system with dynamic properties and narrative evolution.

## Features

The server exposes four main tools that simulate dream-like interactions:

- **`dreamscape()`** - Returns the complete current dreamscape state
- **`attempt_narrative(narrative_entry: string)`** - Adds entries to the ongoing narrative (may be altered by dream logic)
- **`attempt_scene_change(new_scene: string)`** - Attempts to change the dreamscape description
- **`attempt_property_shift(property: string, direction: "increase"|"decrease", reason: string)`** - Adjusts core dreamscape properties

### Dreamscape State Structure

The dreamscape maintains the following state:

```typescript
{
  // Core dream properties (0-100 range)
  emotional_tone: number,
  familiarity_ratio: number, 
  symbolic_density: number,
  sensory_cross_bleeding: number,
  coherence_level: number,
  boundary_stability: number,
  causality_strength: number,
  memory_persistence: number,
  agency_level: number,
  
  // Scene description
  dreamscape: string,
  
  // Ongoing narrative
  narrative: string[]
}
```

### Dream Logic

The system implements dream-like behavior where:
- Lower `coherence_level` and `causality_strength` increase the chance of input alterations
- Narrative entries and scene changes may be modified by dream logic
- Property shifts occur in random increments (5-25 points) within the 0-100 range
- All changes respect the dreamscape's internal consistency

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
   This will produce the compiled JavaScript in the `dist/` directory.

3. **Run the server:**
   
   ```sh
   npm start
   ```
   
   Or for development:
   
   ```sh
   npm run dev
   ```

## API Reference

### Tools

#### `dreamscape()`
Returns the complete current dreamscape state including all properties, scene description, and narrative history.

**Parameters:** None

**Returns:** JSON object with the full dreamscape state

#### `attempt_narrative(narrative_entry: string)`
Adds a new entry to the dream narrative. The entry may be altered by dream logic based on current coherence and causality levels.

**Parameters:**
- `narrative_entry` (string): The narrative entry to add to the dream story

**Returns:** The narrative entry as it was actually added (potentially altered)

#### `attempt_scene_change(new_scene: string)`
Attempts to change the dreamscape scene description. The new scene may be altered by dream logic.

**Parameters:**
- `new_scene` (string): The new scene description for the dreamscape

**Returns:** The scene description as it was actually set (potentially altered)

#### `attempt_property_shift(property: string, direction: "increase"|"decrease", reason: string)`
Attempts to adjust one of the nine core dreamscape properties.

**Parameters:**
- `property` (string): Must be one of: `emotional_tone`, `familiarity_ratio`, `symbolic_density`, `sensory_cross_bleeding`, `coherence_level`, `boundary_stability`, `causality_strength`, `memory_persistence`, `agency_level`
- `direction` (string): Either `"increase"` or `"decrease"`
- `reason` (string): The reason for the property change

**Returns:** Description of the property change that occurred

## Claude Desktop Configuration

To use this MCP server with Claude Desktop:

1. **Locate your Claude Desktop configuration file:**
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

3. **Replace the path:**
   - Update the path in the `args` array with the actual absolute path to your compiled server file in the `dist/` directory

4. **Restart Claude Desktop** for the changes to take effect

5. **Verify the connection:**
   - The dreamscape tools should now be available in your Claude Desktop conversations
   - You can test by asking Claude to check the current dreamscape state
   - Try adding narrative entries or changing scene descriptions
   - Experiment with property shifts to see how they affect dream logic

**Note**: Make sure you have built the server (`npm run build`) before configuring Claude Desktop, as it needs the compiled JavaScript file in the `dist/` directory.

## Usage Examples

Once connected to Claude Desktop, you can interact with the dreamscape:

- "What's the current dreamscape state?"
- "Add this to the narrative: 'I found myself walking through a forest of crystal trees'"
- "Change the scene to a vast library with floating books"
- "Increase the symbolic_density because the dream is becoming more metaphorical"
- "Decrease the coherence_level to make things more surreal"

## Development

To modify the server:

1. Edit `src/mcp-server.ts`
2. Run `npm run build` to compile
3. Test with `npm start`

The dreamscape system is designed to be extensible. You can modify the dream logic alterations, add new properties, or implement additional tools as needed.

## License

MIT 