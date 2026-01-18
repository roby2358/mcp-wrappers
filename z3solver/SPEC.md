# Z3Solver MCP Server - Technical Specification

An MCP server that provides SMT (Satisfiability Modulo Theories) constraint solving capabilities using the Z3 theorem prover.

## Purpose

This MCP server provides Z3 solver access to AI assistants for constraint satisfaction problems. The MCP client (e.g., Claude) handles all natural language translation:
- The MCP client translates user problems from natural language to SMT-LIB format
- MCP client calls `solve_smtlib` to execute the Z3 solver on SMT-LIB input
- The server returns raw SMT-LIB results (models or unsat cores)
- MCP client interprets the SMT-LIB results and explains them in natural language

**The server only provides Z3 solving; all translation is the client's responsibility.**

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│              MCP Client - Orchestrator             │
│  • Translates natural language to SMT-LIB                   │
│  • Calls solve_smtlib with SMT-LIB code                     │
│  • Receives raw SMT-LIB results                             │
│  • Interprets results back to natural language              │
└───────────┬─────────────────────────────────────────────────┘
            │
            │ MCP Protocol (stdio)
            │ solve_smtlib(smtlib, timeout_ms)
            │
┌───────────▼─────────────────────────────────────────────────┐
│                Z3Solver MCP Server                          │
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │  MCP Tool:                                          │   │
│  │  • solve_smtlib(smtlib, timeout_ms)                 │   │
│  │      → {status, output}                             │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                             │
│  ┌──────────────┐                                          │
│  │  Z3 Solver   │                                          │
│  │  (z3-solver) │                                          │
│  │    WASM      │                                          │
│  └──────────────┘                                          │
└─────────────────────────────────────────────────────────────┘
```

## Functional Requirements

### MCP Server Initialization

- The server MUST initialize using the MCP SDK for TypeScript
- The server MUST communicate via stdio transport
- The server MUST load the Z3 solver asynchronously during initialization
- The server SHOULD log initialization status to stderr
- The server MUST fail gracefully if Z3 initialization fails with an instructive error message

### Tool: solve_smtlib

**Purpose:** Execute Z3 solver on SMT-LIB input and return raw SMT-LIB results.

- The tool MUST accept a string parameter `smtlib` containing valid SMT-LIB2 code
- The tool MUST accept an optional number parameter `timeout_ms` in milliseconds (default: 30000)
- The tool MUST strip any existing `(get-model)` and `(get-unsat-core)` commands from input
- The tool MUST execute the SMT-LIB code through Z3 to obtain sat/unsat/unknown result
- The tool MUST conditionally retrieve additional information based on the result:
  - If sat: MUST retrieve the model using `(get-model)`
  - If unsat: MUST retrieve the unsat core using `(get-unsat-core)`
  - If unknown: SHOULD return the unknown status without additional queries
- The tool MUST return an SMT-LIB formatted string with the following structure:
  - Comment line with status: "; sat", "; unsat", or "; unknown"
  - Solver output (if any):
    - For sat: the model from `(get-model)`
    - For unsat: the unsat core from `(get-unsat-core)`
    - For unknown: no additional output (just the comment line)
- The tool MUST handle solver errors gracefully, including:
  - Syntax errors in SMT-LIB input
  - Timeout conditions
  - Memory access violations from WASM
  - Unsupported SMT-LIB features
- The tool MUST return instructive error messages that guide the client toward resolution

### Z3 Solver Integration

- The server MUST use the z3-solver npm package for constraint solving
- The server MUST load Z3 WASM asynchronously without blocking server startup
- The server MUST create fresh solver contexts for each solve operation to prevent state leakage
- The server MUST clean SMT-LIB input by removing comments and empty lines
- The server MUST parse solver output to determine sat/unsat/unknown status
- The server MUST handle Z3 WASM errors including memory access violations
- The server SHOULD support solver timeout configuration
- The server MUST properly dispose of solver contexts after use to prevent memory leaks

### Error Response Format

**MCP Error Response Directive:**

Error messages are consumed by an LLM client, not a human user directly. They must be instructive prompts that guide the LLM toward resolution, not generic error strings.

- Error messages MUST be instructive prompts that guide the LLM toward resolution
- Error messages MUST include:
  - Clear explanation of what went wrong in context
  - 2-3 specific steps to resolve the issue
  - References to relevant actions or parameters that can help
  - Actual values (parameters, status codes, etc.) that caused the error
- Error messages MUST NOT be generic (e.g., "Error: operation failed")

**Examples:**

❌ Bad: `"Error: file not found"`

✅ Good: `"The SMT-LIB input contains a syntax error at line 5: unbalanced parentheses. Please regenerate the SMT-LIB code ensuring all opening parentheses have matching closing parentheses."`

❌ Bad: `"Invalid parameter"`

✅ Good: `"The timeout_ms parameter must be a positive number between 1 and 600000 (10 minutes). Provided value: -1. Use a valid timeout value or omit the parameter to use the default 30000ms."`

## Non-Functional Requirements

### Performance

- The server SHOULD initialize within 5 seconds
- Z3 solver initialization SHOULD complete within 10 seconds
- The server SHOULD support concurrent tool invocations
- LLM API calls SHOULD include reasonable timeout values (30 seconds)
- Solver operations SHOULD support configurable timeouts (default 30 seconds)

### Reliability

- The server MUST maintain state isolation between solve operations
- The server MUST clean up resources (solver contexts, HTTP connections) properly
- The server MUST handle process termination gracefully
- The server SHOULD log errors to stderr for debugging
- The server MUST NOT crash on malformed SMT-LIB input

### Security

- The server MUST validate all input parameters before processing
- The server MUST sanitize SMT-LIB input before passing to Z3
- The server MUST NOT execute arbitrary system commands
- The server SHOULD handle untrusted SMT-LIB input safely without exposing system internals

### Compatibility

- The server MUST run on Node.js 18 or higher
- The server MUST work with TypeScript 5.0 or higher
- The server MUST be compatible with the MCP SDK (@modelcontextprotocol/sdk)
- The server MUST support stdio transport for MCP communication
- The server MUST work with the z3-solver npm package version 4.12.0 or higher

### Code Quality

- The server MUST use TypeScript with strict type checking
- The server SHOULD use async/await for asynchronous operations
- The server SHOULD separate concerns into modules (solver wrapper, MCP tool)
- The server SHOULD include JSDoc comments for public functions
- The server MUST handle promise rejections appropriately

## Dependencies

**Core Libraries:**
- `@modelcontextprotocol/sdk` - MCP protocol implementation
- `z3-solver` - Z3 SMT solver WASM bindings

**Development Tools:**
- `typescript` - TypeScript compiler
- `tsx` - TypeScript execution runtime
- `@types/node` - Node.js type definitions

## Implementation Notes

### Z3 WASM Initialization

The z3-solver package requires SharedArrayBuffer support, which works in Node.js but requires special HTTP headers in browsers. The MCP server runs in Node.js and does not face browser-specific COOP/COEP header requirements.

### Two-Phase Solver Execution

The solver must execute in two phases to maintain context state:
1. Execute constraints and (check-sat) to get sat/unsat/unknown
2. On the same context, execute (get-model) for sat or (get-unsat-core) for unsat

Executing both commands in one string may not preserve the context state properly in some Z3 WASM builds.

### Unsat Core Extraction

Named assertions using the `:named` annotation are required for unsat core extraction. The unsat core returns only the constraint names that form the minimal unsatisfiable subset. The MCP client is responsible for cross-referencing these names with the original SMT-LIB code to explain conflicts.

### SMT-LIB Input Requirements

The MCP client (Claude) should generate SMT-LIB code that:
- Uses valid SMT-LIB2 format
- Includes `(set-option :produce-unsat-cores true)` for unsat core support
- Uses named assertions with `:named` annotation for meaningful unsat cores
- Names should start with letters, not digits
- Ends with `(check-sat)` but not `(get-model)` or `(get-unsat-core)` (added by server)
- Avoids non-existent functions (e.g., "member") and unsupported Z3 WASM features

### MCP Tool Response Structure

The solve_smtlib tool returns SMT-LIB formatted strings:
- Success: Returns SMT-LIB with status as comment:
  ```smtlib
  ; [sat|unsat|unknown]
  [solver output]
  ```
  Example for sat:
  ```smtlib
  ; sat
  (model
    (define-fun x () Int 3)
  )
  ```
- Error: Standard MCP error response with instructive message

### Error Message Design

Error messages are consumed by the MCP client (an LLM), not a human user directly. They should read as instructions to the client about what went wrong and how to proceed. For example:

"The SMT-LIB input contains a syntax error at line 5: unbalanced parentheses. Please regenerate the SMT-LIB code ensuring all opening parentheses have matching closing parentheses."

## Error Handling

The server MUST handle these error conditions with instructive messages:

### Solver Errors

- **SMT-LIB syntax errors**: Provide specific error location and nature. Example: "Syntax error in SMT-LIB input at line 5: unbalanced parentheses. Regenerate the SMT-LIB code ensuring proper parenthesis matching."
- **Timeout**: Explain timeout occurred. Example: "Z3 solver timed out after 30000ms. Try simplifying the constraints, reducing the number of variables, or increasing the timeout_ms parameter."
- **Memory access violations**: Explain likely causes. Example: "Z3 WASM memory access violation. This typically indicates: (1) syntax error in SMT-LIB, (2) unsupported Z3 feature, or (3) problem too complex. Verify SMT-LIB syntax is valid."
- **Unknown result**: Explain solver uncertainty. Example: "Z3 returned 'unknown' - it could not determine satisfiability. Try simplifying constraints or reformulating the problem."

### Input Validation Errors

- **Empty or null SMT-LIB**: "The smtlib parameter is required and must contain valid SMT-LIB2 code. Provide SMT-LIB code with variable declarations, assertions, and (check-sat) command."
- **Invalid timeout values**: "timeout_ms must be a positive number between 1 and 600000 (10 minutes). Provided value: {value}."
- **Malformed SMT-LIB**: "The SMT-LIB code appears malformed. Ensure it follows SMT-LIB2 syntax with proper declarations and balanced parentheses."

### Resource Errors

- **Z3 initialization failure**: "Z3 solver failed to initialize. Ensure z3-solver npm package is installed. Try: npm install z3-solver"
- **Out of memory**: "Z3 WASM ran out of memory. Reduce problem complexity by using fewer variables or simpler constraints."
- **Context creation failure**: "Failed to create Z3 solver context. The MCP server may need to be restarted."

## Typical Workflow

The MCP client (Claude) handles the entire workflow:

1. **User** describes a constraint problem in natural language
2. **Client** translates the problem to SMT-LIB format (using Claude's native capabilities)
3. **Client** calls `solve_smtlib` with the SMT-LIB code
   - **Server** executes Z3 solver and returns SMT-LIB formatted response
4. **Client** parses the response (first line is "; [status]", rest is solver output):
   - If status is "sat": Interprets the model and explains the solution
   - If status is "unsat": Interprets the unsat core and explains why no solution exists
   - If status is "unknown": Explains that Z3 could not determine satisfiability
5. **Client** presents the final answer to the user in natural language

**Key Points:**
- The server is stateless and only provides Z3 solving
- The client handles all natural language translation
- The client maintains context across the conversation
- The workflow is a simple request-response pattern
- Response format is pure SMT-LIB with status as a comment
