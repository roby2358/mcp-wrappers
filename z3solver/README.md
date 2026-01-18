# Z3Solver MCP Server

An MCP (Model Context Protocol) server that provides SMT (Satisfiability Modulo Theories) constraint solving capabilities using the Z3 theorem prover. Enables AI assistants to solve complex constraint satisfaction problems.

## How It Works

The workflow is simple:

1. **LLM translates** your natural language problem to SMT-LIB format (LLMs do this natively)
2. **LLM calls** the `solve_smtlib` tool with the SMT-LIB code
3. **The server** executes Z3 and returns raw solver results in SMT-LIB format
4. **LLM interprets** the SMT-LIB results and explains them to you in natural language

**The server only provides Z3 solving; LLM handles all natural language translation.**

## Features

- **Z3 Solver Integration**: Execute constraint solving using the Z3 SMT solver (WASM)
- **SMT-LIB2 Support**: Full support for SMT-LIB2 format input and output
- **Unsat Core Extraction**: Returns minimal conflicting constraint sets when problems are unsatisfiable
- **Model Generation**: Returns satisfying assignments when solutions exist
- **MCP Protocol**: Full integration with MCP clients
- **Zero Installation**: Users install via `npx` - no manual setup required

## What is SMT?

SMT (Satisfiability Modulo Theories) solvers can find solutions to constraint problems involving:
- Scheduling and resource allocation
- Logic puzzles (Sudoku, Einstein's riddle, N-Queens)
- Configuration problems with compatibility constraints
- Planning with discrete choices
- Mathematical constraint satisfaction

Z3 is a powerful SMT solver from Microsoft Research that can reason about integers, reals, booleans, arrays, and more.

## Installation

### Prerequisites

- Node.js 18 or higher
- npm or yarn package manager

### Install Dependencies

```bash
cd z3solver
npm install
```

This will install:
- `@modelcontextprotocol/sdk` - MCP protocol implementation
- `z3-solver` - Z3 SMT solver WASM bindings
- TypeScript and development tools

## Running the Server

### Development Mode

```bash
npm run dev
```

### Production Mode

```bash
npm run build
npm start
```

### Direct Execution

```bash
npx tsx src/index.ts
```

## Claude Desktop Configuration

Add this configuration to your Claude Desktop config file:

**Windows**: `%APPDATA%\Claude\claude_desktop_config.json`
**macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
**Linux**: `~/.config/Claude/claude_desktop_config.json`

### Production (from npm)

```json
{
  "mcpServers": {
    "z3solver": {
      "command": "npx",
      "args": ["-y", "yuwakisa-z3solver-mcp"]
    }
  }
}
```

### Development (local)

```json
{
  "mcpServers": {
    "z3solver": {
      "command": "node",
      "args": ["/path/to/mcp-wrappers/z3solver/build/index.js"]
    }
  }
}
```

## Available MCP Tools

### solve_smtlib

Execute the Z3 solver on SMT-LIB input and return raw SMT-LIB results.

**Parameters:**
- `smtlib` (string): Valid SMT-LIB2 code
- `timeout_ms` (number, optional): Timeout in milliseconds (default: 30000)

**Returns:** SMT-LIB formatted string with status as comment

**Example SMT-LIB Input:**
```smtlib
(set-option :produce-unsat-cores true)
(declare-const x Int)
(declare-const y Int)
(assert (! (> x 0) :named x-positive))
(assert (! (> y 0) :named y-positive))
(assert (! (< (+ x y) 10) :named sum-less-than-10))
(check-sat)
```

**Example Response (sat):**
```smtlib
; sat
(model
  (define-fun x () Int 3)
  (define-fun y () Int 4)
)
```

**Example Response (unsat):**
```smtlib
; unsat
(x-positive y-positive sum-less-than-10)
```

**Example Response (unknown):**
```smtlib
; unknown
```

## Usage Example

Once configured in Claude Desktop, you can interact with the solver through natural language:

```
You: I have 4 people (Alice, Bob, Carol, David) who need to be assigned to 2 teams.
     Alice and Bob can't be on the same team. Each team needs at least one person.
     Can you find a valid assignment?

Claude: I'll solve this constraint problem using the Z3 solver.

[Claude translates your problem to SMT-LIB]
[Claude calls solve_smtlib with the SMT-LIB code]
[Claude receives raw solver output]
[Claude interprets the results]

Claude: Here's a valid assignment:
- Team 1: Alice, Carol
- Team 2: Bob, David

This satisfies all constraints: Alice and Bob are on different teams,
and each team has at least one person.
```

## Typical Workflow

1. **You describe** your constraint problem in natural language
2. **Claude translates** to SMT-LIB format (using its native capabilities)
3. **Claude calls** `solve_smtlib` with the SMT-LIB code
4. **Server executes** Z3 and returns raw SMT-LIB results (model or unsat core)
5. **Claude interprets** the raw results and explains the solution or conflict to you

The server is stateless and only provides Z3 solving capability. All translation and interpretation happens in Claude.

## Development

### Project Structure

```
z3solver/
├── src/
│   ├── index.ts              # Main entry point
│   ├── server.ts             # MCP server setup
│   ├── tools/
│   │   └── solve.ts          # solve_smtlib tool
│   └── solver/
│       └── z3wrapper.ts      # Z3 solver wrapper
├── tests/                    # Unit tests
├── package.json
├── tsconfig.json
├── README.md
└── SPEC.md
```

### Building

```bash
npm run build
```

Output is generated in the `build/` directory.

### Testing

```bash
npm test
```

### Type Checking

```bash
npm run typecheck
```

### Linting

```bash
npm run lint
```

## Common Problems

### Z3 Initialization Fails

If the Z3 solver fails to initialize:
- Ensure z3-solver package is installed: `npm install z3-solver`
- Check Node.js version is 18 or higher
- Try reinstalling dependencies: `rm -rf node_modules && npm install`

### Invalid SMT-LIB Syntax

If you get syntax errors:
- Ensure your SMT-LIB code is valid SMT-LIB2 format
- Check that all variables are declared before use
- Verify parentheses are balanced
- For unsat cores, ensure you use `(set-option :produce-unsat-cores true)` and named assertions

### Solver Timeout

If the solver times out:
- Simplify your problem constraints
- Increase timeout in the tool call: `solve_smtlib(smtlib, 60000)` for 60 seconds
- Break the problem into smaller independent subproblems
- Consider if the problem size is too large for SMT solving

### Memory Access Violations

If you see WASM memory errors:
- Check for syntax errors in your SMT-LIB code
- Verify you're not using unsupported Z3 features
- Try simplifying the problem
- Ensure you're using valid SMT-LIB2 syntax

## Good Problems for SMT Solvers

SMT solvers excel at:
- **Scheduling**: Meeting times, resource allocation, shift scheduling
- **Logic Puzzles**: Sudoku, N-Queens, Einstein's riddle, graph coloring
- **Configuration**: Selecting compatible components, dependency resolution
- **Planning**: Sequencing tasks with constraints, route finding with rules
- **Verification**: Checking if a configuration satisfies all requirements

SMT solvers are less suitable for:
- Optimization problems (maximize/minimize) - use optimization solvers
- Continuous numerical problems - use numerical optimization
- Machine learning tasks - use ML frameworks
- Large-scale data processing - use databases or data pipelines

## Dependencies

**Core:**
- `@modelcontextprotocol/sdk` - MCP protocol implementation
- `z3-solver` - Z3 SMT solver WASM bindings

**Development:**
- `typescript` - TypeScript compiler
- `tsx` - TypeScript execution runtime
- `@types/node` - Node.js type definitions

**Runtime:**
- Node.js 18+ with fetch API support

## Related Documentation

- [SPEC.md](SPEC.md) - Technical specification with detailed requirements
- [Z3 SMT-LIB2 Guide](https://rise4fun.com/z3/tutorialcontent/guide) - SMT-LIB2 syntax reference
- [Model Context Protocol](https://modelcontextprotocol.io/) - MCP documentation
- [Z3 GitHub](https://github.com/Z3Prover/z3) - Z3 theorem prover

## License

MIT License - see [LICENSE](LICENSE) file for details

## Status

This project is under active development. The core functionality is implemented, but additional features and optimizations are planned.

## Contributing

Contributions are welcome! Please:
1. Fork the repository
2. Create a feature branch
3. Add tests for new functionality
4. Ensure all tests pass
5. Submit a pull request

## Acknowledgments

- Built with the [Model Context Protocol](https://modelcontextprotocol.io/)
- Uses [Z3 Theorem Prover](https://github.com/Z3Prover/z3) via z3-solver npm package
- Inspired by the web-based SMT solver demo in `example/solver/`
