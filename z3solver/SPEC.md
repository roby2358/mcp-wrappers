# Z3Solver MCP Server - Technical Specification

## Purpose

MCP server providing Z3 SMT solver access. The server executes Z3 on SMT-LIB input and returns raw SMT-LIB results. All natural language translation is the client's responsibility.

## Tool: solve_smtlib

Execute Z3 solver on SMT-LIB input.

**Parameters:**
- `smtlib` (string, required): SMT-LIB2 code
- `timeout_ms` (number, optional): Maximum wait time in milliseconds (default: 30000, range: 1-600000)
  - **Limitation:** Z3 WASM runs synchronously. Once solving starts, it cannot be canceled. Timeout prevents promises from hanging indefinitely but may not stop long-running solves.

**Returns:** SMT-LIB formatted string with status comment on first line, followed by solver output (if any):
```smtlib
; [sat|unsat|unknown]
[solver output]
```

For `sat`: Status line followed by model
For `unsat`: Status line followed by unsat core (if available)
For `unknown`: Status line only
Empty/whitespace-only output is trimmed.

**Examples:**

Input:
```smtlib
(declare-const x Int)
(assert (> x 0))
(check-sat)
```

Output (sat):
```smtlib
; sat
(model
  (define-fun x () Int 1)
)
```

Output (unsat):
```smtlib
; unsat
(core-constraint-name)
```

**Input Validation:**

- `smtlib` parameter MUST be non-empty string containing valid SMT-LIB2 code
- `timeout_ms` parameter (if provided) MUST be a finite number in range 1-600000

**Error Handling:**

Errors MUST be instructive prompts for the LLM client, not generic messages.

❌ Bad: `"Invalid input"`
✅ Good: `"SMT-LIB syntax error on line 5: missing closing parenthesis. Check that all S-expressions are properly balanced."`

Include:
- What went wrong (specific line/character if possible)
- Why it's wrong
- How to fix it (2-3 concrete steps)

**Error Examples:**

Empty input:
```
Parameter "smtlib" is required and must contain valid SMT-LIB2 code. Include variable declarations, assertions, and (check-sat).
```

Timeout exceeded:
```
Z3 solver timed out after 30000ms. Try: (1) simplify constraints, (2) reduce variables, or (3) increase timeout_ms parameter.
```

Invalid timeout:
```
Parameter "timeout_ms" must be 1-600000 (milliseconds). Given: NaN. Omit for default 30000ms.
```

## Functional Requirements

### Server
- MUST use MCP SDK stdio transport
- MUST load Z3 asynchronously without blocking
- MUST create fresh solver contexts per request (no state leakage)
- MUST handle timeouts (abort solving after timeout_ms)
- MUST dispose contexts after use (prevent memory leaks)

### Solver Execution
- MUST execute in two phases to maintain context:
  1. Run SMT-LIB + `(check-sat)` → get status
  2. On same context, run `(get-model)` for sat or `(get-unsat-core)` for unsat
- MUST parse status from first phase before second phase
- MUST strip any existing `(get-model)` or `(get-unsat-core)` from input

### Response Format
- First line: `; [sat|unsat|unknown]` comment
- Remaining lines: solver output (model or unsat core)
- For unknown: only the comment line

### Unsat Cores
- Require named assertions: `(assert (! expr :named name))`
- Core contains minimal conflicting constraint names
- Names MUST start with letter (not digit)
- Client responsible for cross-referencing names with SMT-LIB

## Non-Functional Requirements

- Run on Node.js 18+
- TypeScript with strict mode
- Initialize within 10 seconds
- Support concurrent requests (stateless)
- No API keys or external dependencies (only Z3)

## Dependencies

- `@modelcontextprotocol/sdk` - MCP protocol
- `z3-solver` - Z3 WASM bindings (chosen for zero-install npx distribution)

## Implementation Notes

**Why WASM over native Z3?**
Zero installation via npx. Trade-off: 2-5x slower, but acceptable for most problems.

**Two-phase execution required:**
Some Z3 WASM builds don't preserve context when `(check-sat)` and `(get-model)` are in one string.

**Timeout handling:**
Z3 WASM runs synchronously and cannot be canceled mid-execution. Implementation provides best-effort timeout using Promise.race() to prevent indefinite hangs, but cannot guarantee stopping long-running solves.
