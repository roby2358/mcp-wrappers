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

/**
 * Issue 2 (FIXES.md): best-so-far model on optimize timeout.
 *
 * For OMT (maximize/minimize), a solve that times out before proving the optimum
 * returns `unknown` while Z3 still holds a feasible incumbent. Previously the
 * wrapper had no `unknown` branch, so it discarded that model. It now surfaces the
 * incumbent and labels it distinctly.
 *
 * Validation finding: MaxSAT (assert-soft) does NOT expose an incumbent this way
 * (get-model errors), so it is intentionally not asserted here.
 */
describe('Z3Solver optimize-timeout incumbent', () => {
  const solver = new Z3Solver();

  // Knapsack: 0/1 items, value vs weight cap. Feasible (all-0) is instant and Z3
  // improves the incumbent fast, but proving the optimum for large n is infeasible
  // in a short budget — a reliable "unknown with incumbent" generator. Builds only
  // the problem; callers compose any (set-option :timeout) they need.
  function knapsack(n: number): string {
    const idx = Array.from({ length: n }, (_, i) => i);
    const val = idx.map((i) => ((i * 37 + 11) % 100) + 1);
    const wt = idx.map((i) => ((i * 53 + 7) % 100) + 1);
    const cap = Math.floor(wt.reduce((a, b) => a + b, 0) * 0.45);
    return [
      ...idx.map((i) => `(declare-const b${i} Int)`),
      ...idx.map((i) => `(assert (or (= b${i} 0) (= b${i} 1)))`),
      `(assert (<= (+ ${idx.map((i) => `(* ${wt[i]} b${i})`).join(' ')}) ${cap}))`,
      `(maximize (+ ${idx.map((i) => `(* ${val[i]} b${i})`).join(' ')}))`,
      `(check-sat)`,
    ].join('\n');
  }

  it('surfaces a labelled incumbent on OMT maximize timeout (was: bare unknown)', async () => {
    // Caller sets their own short internal timeout; large JS wall so the wall can't fire.
    const result = await solver.solve(`(set-option :timeout 1000)\n${knapsack(60)}`, 20000);
    assert.match(result, /^; unknown \(incumbent - not proven optimal\)/,
      `expected a labelled incumbent, got:\n${result.slice(0, 200)}`);
    assert.match(result, /define-fun b0 /, `expected a model body, got:\n${result.slice(0, 200)}`);
  });

  it('returns the proven optimum as sat for an easily-solved optimize', async () => {
    const result = await solver.solve(knapsack(6), 20000);
    assert.match(result, /^; sat/, `expected '; sat', got:\n${result.slice(0, 200)}`);
  });

  it('clamps an internal timeout so a no-:timeout hard optimize returns instead of hitting the JS wall', async () => {
    // No (set-option :timeout) in the input — the wrapper must inject one (~50% of
    // timeoutMs = 2000ms) so the 4000ms JS wall never fires and the incumbent survives.
    const result = await solver.solve(knapsack(60), 4000);
    assert.match(result, /^; unknown \(incumbent - not proven optimal\)/,
      `expected injected-timeout incumbent, got:\n${result.slice(0, 200)}`);
  });
});
