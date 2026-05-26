/**
 * Regression tests for Z3Solver status parsing.
 *
 * Guards the bug documented in FIXES.md: `solve_smtlib` reported `unknown` for any
 * input carrying an output-producing command other than `(check-sat)` — most commonly
 * `(get-value …)` / `(get-objectives)`. `eval_smtlib2_string` returns the concatenated
 * output of every command, so phase-1 output was e.g. "sat\n((x 0) (y 1))", which the
 * old exact-match `parseStatus` (`output.trim() === 'sat'`) failed to recognise.
 *
 * Runs against the TypeScript source (via tsx) rather than build/ so it can't pass
 * against a stale build. `npm test` wires this up.
 */
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { Z3Solver } from '../src/solver/z3wrapper.ts';

describe('Z3Solver status parsing', () => {
  // One solver instance: initialize() is idempotent, so Z3 (WASM) loads once.
  const solver = new Z3Solver();

  it('reports sat for a query ending in (get-value …) — the regressed case', async () => {
    const result = await solver.solve(`
(declare-const x Int)
(declare-const y Int)
(assert (distinct x y))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
(get-value (x y))
`);
    assert.match(result, /^; sat/, `expected '; sat', got:\n${result}`);
  });

  it('reports sat when status is one line among others — pins the parseStatus fix', async () => {
    // print-success makes every command echo "success", so phase-1 output is
    // "success\n…\nsat". stripGetCommands does NOT remove this, so it isolates the
    // line-scan parseStatus: the old `output.trim() === 'sat'` returns `; unknown` here.
    const result = await solver.solve(`
(set-option :print-success true)
(declare-const x Int)
(assert (> x 0))
(check-sat)
`);
    assert.match(result, /^; sat/, `expected '; sat', got:\n${result}`);
  });

  it('reports sat for a query ending in (get-objectives)', async () => {
    const result = await solver.solve(`
(declare-const x Int)
(assert (>= x 0))
(maximize x)
(assert (<= x 10))
(check-sat)
(get-objectives)
`);
    assert.match(result, /^; sat/, `expected '; sat', got:\n${result}`);
  });

  it('still reports sat for a plain (check-sat) with no trailing get-* command', async () => {
    const result = await solver.solve('(declare-const x Int)\n(assert (> x 0))\n(check-sat)');
    assert.match(result, /^; sat/, `expected '; sat', got:\n${result}`);
  });

  it('reports unsat for an unsatisfiable problem', async () => {
    const result = await solver.solve(`
(declare-const x Int)
(assert (> x 10))
(assert (< x 5))
(check-sat)
`);
    assert.match(result, /^; unsat/, `expected '; unsat', got:\n${result}`);
  });
});
