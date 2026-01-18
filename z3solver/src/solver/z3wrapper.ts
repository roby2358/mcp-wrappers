/**
 * Z3 Solver Wrapper - Simplified and Fixed
 */
import { init } from 'z3-solver';

export class Z3Solver {
  private z3: any = null;
  private initPromise: Promise<void> | null = null;

  async initialize(): Promise<void> {
    if (this.z3) return;
    if (!this.initPromise) {
      this.initPromise = this.doInit();
    }
    await this.initPromise;
  }

  private async doInit(): Promise<void> {
    try {
      const { Z3 } = await init();
      this.z3 = Z3;
      console.error('Z3 initialized');
    } catch (error) {
      const msg = error instanceof Error ? error.message : String(error);
      throw new Error(
        `Z3 initialization failed: ${msg}. ` +
        `Ensure z3-solver is installed: npm install z3-solver`
      );
    }
  }

  /**
   * Strip (get-model) and (get-unsat-core) commands
   *
   * Note: Uses simple regex replacement. May incorrectly match inside string literals,
   * but this is acceptable as SMT-LIB strings are rare and get-* commands in strings
   * would be unusual.
   */
  private stripGetCommands(smtlib: string): string {
    return smtlib
      .replace(/\(\s*get-model\s*\)/g, '')
      .replace(/\(\s*get-unsat-core\s*\)/g, '');
  }

  /**
   * Parse check-sat result - exact match only
   */
  private parseStatus(output: string): 'sat' | 'unsat' | 'unknown' {
    const trimmed = output.trim();
    if (trimmed === 'sat') return 'sat';
    if (trimmed === 'unsat') return 'unsat';
    return 'unknown';
  }

  async solve(smtlib: string, timeoutMs: number = 30000): Promise<string> {
    if (!smtlib?.trim()) {
      throw new Error(
        'Parameter "smtlib" is required and must contain valid SMT-LIB2 code. ' +
        'Include variable declarations, assertions, and (check-sat).'
      );
    }

    await this.initialize();

    // Setup timeout with cleanup
    let timeoutId: NodeJS.Timeout | undefined;
    const timeoutPromise = new Promise<never>((_, reject) => {
      timeoutId = setTimeout(() => {
        reject(new Error(
          `Z3 solver timed out after ${timeoutMs}ms. ` +
          `Try: (1) simplify constraints, (2) reduce variables, or (3) increase timeout_ms parameter.`
        ));
      }, timeoutMs);
    });

    try {
      return await Promise.race([
        this.solveImpl(smtlib),
        timeoutPromise
      ]);
    } catch (error) {
      if (error instanceof Error) {
        if (error.message.includes('memory access out of bounds')) {
          throw new Error(
            'Z3 WASM memory error. Common causes: ' +
            '(1) syntax error in SMT-LIB (check parentheses), ' +
            '(2) unsupported Z3 feature, or ' +
            '(3) problem too complex for WASM. ' +
            'Verify SMT-LIB syntax is valid.'
          );
        }
        throw error;
      }
      throw new Error(`Unexpected error: ${String(error)}`);
    } finally {
      // Clear timeout to prevent memory leak
      if (timeoutId !== undefined) {
        clearTimeout(timeoutId);
      }
    }
  }

  private async solveImpl(smtlib: string): Promise<string> {
    const config = this.z3.mk_config();
    const ctx = this.z3.mk_context(config);
    this.z3.del_config(config);

    try {
      // Strip get commands and execute
      const cleaned = this.stripGetCommands(smtlib);

      // Phase 1: check-sat
      const checkResult = await this.z3.eval_smtlib2_string(ctx, cleaned);
      const status = this.parseStatus(String(checkResult || ''));

      // Phase 2: get model or core
      let output = '';
      if (status === 'sat') {
        const model = await this.z3.eval_smtlib2_string(ctx, '(get-model)');
        output = String(model || '');
      } else if (status === 'unsat') {
        const core = await this.z3.eval_smtlib2_string(ctx, '(get-unsat-core)');
        output = String(core || '');
      }

      // Format response
      return output.trim() ? `; ${status}\n${output.trim()}` : `; ${status}`;

    } finally {
      this.z3.del_context(ctx);
    }
  }

  isLoaded(): boolean {
    return this.z3 !== null;
  }
}
