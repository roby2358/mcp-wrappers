/**
 * MCP tool: solve_smtlib - Simplified
 */
import { Z3Solver } from '../solver/z3wrapper.js';

const solver = new Z3Solver();

export interface SolveArgs {
  smtlib: string;
  timeout_ms?: number;
}

/**
 * Solve SMT-LIB with Z3
 * Validation and error handling done in Z3Solver
 */
export async function solve(args: SolveArgs): Promise<string> {
  const { smtlib, timeout_ms } = args;

  // Validate timeout if provided
  if (timeout_ms !== undefined) {
    if (typeof timeout_ms !== 'number' || !Number.isFinite(timeout_ms) ||
        timeout_ms < 1 || timeout_ms > 600000) {
      throw new Error(
        `Parameter "timeout_ms" must be 1-600000 (milliseconds). ` +
        `Given: ${timeout_ms}. ` +
        `Omit for default 30000ms.`
      );
    }
  }

  return solver.solve(smtlib, timeout_ms);
}
