# SPEC_UI: Docmem HTTP UI

## Purpose

Provide a minimal browser-based interface for inspecting and persisting docmem trees. The UI runs alongside the MCP server on port 8182 and reuses the same query and serialization functions the MCP tools call, so the user sees exactly what the model sees.

## UI Layout

```
+----------------------------------------------------------+
|  view | persist                            (navigation)   |
+----------------------------------------------------------+
|  expand | structure | serialize            (option bar)   |
+------------------+---------------------------------------+
|                  |                                         |
|  docmem list     |  content pane                          |
|  (scrolling)     |  (scrolling)                           |
|                  |                                         |
|  > root0001      |  [rendered output from selected        |
|    root0002      |   query function]                      |
|    root0003      |                                         |
|                  |                                         |
+------------------+---------------------------------------+
```

Persist view replaces the option bar and content pane:

```
+----------------------------------------------------------+
|  view | persist                            (navigation)   |
+----------------------------------------------------------+
|                                            (option bar)   |
+------------------+---------------------------------------+
|                  |                                         |
|  docmem list     |  load toml                             |
|  (scrolling)     |  save toml                             |
|                  |  save expanded                         |
|  > root0001      |  save serialized                       |
|    root0002      |  delete                                |
|    root0002      |                                         |
|    root0003      |                                         |
|                  |                                         |
+------------------+---------------------------------------+
```

## Functional Requirements

### HTTP Server

- The server MUST listen on port 8182 using Node's built-in `http` module
- The server MUST start automatically when the MCP server starts
- The server MUST serve static files (HTML, CSS, JS) from a `public/` directory
- The server MUST expose JSON API endpoints for the browser client to call

### API Endpoints

- The server MUST expose an endpoint to list all docmem roots
- The server MUST expose an endpoint to return serialized content for a given root
- The server MUST expose an endpoint to return expanded content for a given root
- The server MUST expose an endpoint to return structure output for a given root
- The server MUST expose an endpoint to save a docmem as TOML to a user-specified path
- The server MUST expose an endpoint to load a docmem from a TOML file at a user-specified path
- The server MUST expose an endpoint to save expanded output to a user-specified path
- The server MUST expose an endpoint to save serialized output to a user-specified path
- The server MUST expose an endpoint to delete a docmem root and all its descendants
- All query endpoints MUST call the same functions the MCP tools use (`serialize`, `expandToLength`, `structure`, `listDocmems`)

### Navigation

- The navigation bar MUST display two choices: "view" and "persist"
- The choices MUST be rendered as linked text with no button styling
- The currently active navigation choice MUST be visually distinguished

### View Mode

- The option bar MUST display three choices: "expand", "structure", "serialize"
- The choices MUST be rendered as linked text with no button styling
- The currently active option MUST be visually distinguished
- Selecting an option MUST refresh the content pane with output from the corresponding query function
- The default option on first load SHOULD be "structure"

### Persist Mode

- The option bar MUST be present but empty
- The right pane MUST display these persistence actions as a vertical list of linked text:
  - load toml
  - save toml
  - save expanded
  - save serialized
  - delete
- "save toml", "save expanded", and "save serialized" MUST prompt the user with a file dialogue to choose the save location and filename
  - use the built in file chooser, not a custom implementation
- "load toml" MUST prompt the user with a file dialogue to choose the file to load
    - use the built in file chooser, not a custom implementation
- "delete" MUST prompt the user with a confirmation dialogue before deleting
- "delete" MUST delete the selected docmem root and all its descendants
- After a successful delete, the docmem list MUST refresh
- After a successful load, the docmem list MUST refresh

### Docmem List Pane

- The left pane MUST display all docmem roots as a vertical scrolling list, one per line
- Each entry MUST show the root ID
- The currently selected docmem MUST appear with inverse coloring (white text on colored background)
- Clicking a docmem entry MUST select it and refresh the content pane
- If no docmems exist, the list MUST be empty

### Content Pane

- The content pane MUST be a scrolling view
- Content MUST be generated by calling the same functions the MCP tools use
- When "serialize" is active, the pane MUST display the output of the `serialize` function for the selected root
- When "structure" is active, the pane MUST display the output of the `structure` function for the selected root
- When "expand" is active, the pane MUST display the output of the `expandToLength` function for the selected root
- The expand view MUST use a high token budget with the expectation of showing the full docmem

### TOML Persistence

- A TOML export function MUST exist that serializes a docmem tree to TOML format
- A TOML import function MUST exist that loads a TOML file and creates a docmem tree from it
- These functions MUST NOT be exposed as MCP tools
- These functions MUST be available to the HTTP UI

## Non-Functional Requirements

### Styling

- The UI MUST use bare-bones styling with no frameworks or component libraries
- Controls MUST be rendered as linked text with no button styling
- The layout MUST use minimal CSS sufficient for the two-pane layout and scrolling
- The UI SHOULD be usable at typical browser window sizes (1024px and above)

### File Organization

- HTML, CSS, and JS MUST be served from separate files in a `public/` directory
- HTML MUST be generated dynamically on the server side (not static HTML with inline data)
- Client-side JS handles interaction and fetches data from the API endpoints

## Dependencies

- Node.js built-in `http` module
- Node.js built-in `fs` module (for serving static files and file persistence)
- Node.js built-in `path` module

## Implementation Notes

- The file dialogue for save/load operations is a browser-native `<input type="file">` for loading. For saving, the server writes to a path provided by the client; the client MAY use a prompt or input field to specify the path since browsers do not natively support save-location dialogues for server-side writes.
- The `expandToLength` default token budget for the UI view should enough to show a big docmem (e.g. 100000 tokens).
- Dynamic HTML generation means the server reads template files from `public/`, interpolates data where needed, and serves the result. Client JS then handles subsequent interactions via fetch calls to the API.

## Error Handling

- If a selected docmem no longer exists, the content pane MUST display an error message
- If a TOML file fails to parse on load, the UI MUST display the error to the user
- If a save operation fails (e.g. invalid path), the UI MUST display the error to the user
- API endpoints MUST return appropriate HTTP status codes and error messages in JSON format

# Examples

## Example .tomnl docmem
[three-stooges]
context="root:purpose:document"
content=""

[pmpwzyny]
parent-node-id="three-stooges"
context="stooge:name:moe"
content="Moe Howard - The leader of the group"

[x6qgccsn]
parent-node-id="pmpwzyny"
context="fun-fact:fact:1"
content="Moe was born Moses Harry Horwitz and had a real slap technique that was legendary in comedy"

[7jr8q2a8]
parent-node-id="pmpwzyny"
context="fun-fact:fact:2"
content="Moe appeared in over 190 films with the Three Stooges"

[u9jrzmht]
parent-node-id="pmpwzyny"
context="fun-fact:fact:3"
content="Moe was the only stooge to appear in all 190 shorts of the series"

[z8kfg4s3]
parent-node-id="three-stooges"
context="stooge:name:larry"
content="Larry Fine - The curly-haired one"

[435ueswz]
parent-node-id="z8kfg4s3"
context="fun-fact:fact:1"
content="Larry Fine was born Louis Feinberg and was an accomplished violinist"

[8zuxwshn]
parent-node-id="z8kfg4s3"
context="fun-fact:fact:2"
content="Larry's signature curly hair was natural, not a wig or perm"

[6uhf9xf5]
parent-node-id="z8kfg4s3"
context="fun-fact:fact:3"
content="Larry had a high-pitched voice that became iconic for his comedic timing"

[9xs9gemx]
parent-node-id="three-stooges"
context="stooge:name:curly"
content="Curly Howard - The bald one with the high voice"

[x2yvmu8j]
parent-node-id="9xs9gemx"
context="fun-fact:fact:1"
content="Curly was born Jerome Lester Horwitz and was Moe's younger brother"

[f8x3htcr]
parent-node-id="9xs9gemx"
context="fun-fact:fact:2"
content="Curly's famous 'Nyuk nyuk' laugh and eye-poke became his trademark moves"

[qjdhh3kr]
parent-node-id="9xs9gemx"
context="fun-fact:fact:3"
content="Curly shaved his head bald for the act, making him instantly recognizable"
