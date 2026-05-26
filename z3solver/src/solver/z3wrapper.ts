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
   * Strip output-producing commands so phase-1 eval yields only the check-sat status.
   *
   * We re-issue (get-model)/(get-unsat-core) ourselves in phase 2, and (get-value …)/
   * (get-objectives)/(get-assignment) would otherwise append text to the phase-1 output
   * and corrupt status parsing. The full model is returned via phase-2 (get-model), which
   * supersedes any caller-supplied (get-value …).
   *
   * Note: Uses simple regex replacement. May incorrectly match inside string literals,
   * but this is acceptable as SMT-LIB strings are rare and get-* commands in strings
   * would be unusual.
   */
  private stripGetCommands(smtlib: string): string {
    return smtlib
      .replace(/\(\s*get-model\s*\)/g, '')
      .replace(/\(\s*get-unsat-core\s*\)/g, '')
      .replace(/\(\s*get-objectives\s*\)/g, '')
      .replace(/\(\s*get-assignment\s*\)/g, '')
      .replace(/\(\s*get-value\s*\([^)]*\)\s*\)/g, '');
  }

  /**
   * Ensure an internal Z3 timeout is set so the JS race wall (timeoutMs) can't
   * pre-empt the solve and discard a recoverable answer.
   *
   * Z3's eval runs off the main thread, so the Promise.race in solve() genuinely
   * rejects mid-solve when timeoutMs fires — throwing away the status AND any
   * best-so-far optimize incumbent. If Z3's own `(set-option :timeout N)` fires
   * first, it instead returns `unknown` gracefully with the incumbent intact (for
   * OMT maximize/minimize; see solveImpl). We only inject when the caller hasn't
   * set their own timeout — if they have, that's their explicit choice.
   *
   * The internal bound is a fraction of timeoutMs, not timeoutMs minus a fixed
   * margin: Z3's `:timeout` is approximate and overshoots (~25% observed), so the
   * margin has to scale with the budget to keep the overshoot under the JS wall.
   */
  private ensureInternalTimeout(smtlib: string, timeoutMs: number): string {
    if (/\(\s*set-option\s+:timeout\b/.test(smtlib)) return smtlib;
    // Half the JS budget: leaves room for Z3's :timeout overshoot (~25%) plus the
    // phase-2 get-model, so Z3 finishes gracefully before the race wall fires.
    const safetyFactor = 0.5;
    const internal = Math.floor(timeoutMs * safetyFactor);
    return `(set-option :timeout ${internal})\n${smtlib}`;
  }

  /**
   * Parse the check-sat result.
   *
   * eval_smtlib2_string returns the concatenated output of every command it ran, so the
   * status can be one line among others (e.g. when the input also carries (get-value …)
   * or (get-objectives), or when set-option emits "success"). Scan for a bare status line
   * instead of exact-matching the whole output — exact matching reports `unknown` for any
   * input that produces output beyond `(check-sat)`.
   */
  private parseStatus(output: string): 'sat' | 'unsat' | 'unknown' {
    const lines = output.split(/\r?\n/).map((l) => l.trim());
    if (lines.includes('sat')) return 'sat';
    if (lines.includes('unsat')) return 'unsat';
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
        this.solveImpl(this.ensureInternalTimeout(smtlib, timeoutMs)),
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
      let incumbent = false;
      if (status === 'sat') {
        const model = await this.z3.eval_smtlib2_string(ctx, '(get-model)');
        output = String(model || '');
      } else if (status === 'unsat') {
        const core = await this.z3.eval_smtlib2_string(ctx, '(get-unsat-core)');
        output = String(core || '');
      } else if (status === 'unknown') {
        // Optimize (maximize/minimize) that timed out still holds a best-so-far
        // model — (get-model) returns it. A genuine "no model yet" (e.g. MaxSAT
        // assert-soft, or a plain timeout) returns an (error …) line instead, which
        // we exclude so callers don't get noise framed as a result.
        const model = String((await this.z3.eval_smtlib2_string(ctx, '(get-model)')) || '').trim();
        if (model && !/^\(error/m.test(model)) {
          output = model;
          incumbent = true;
        }
      }

      // Format response. An incumbent is feasible but not proven optimal — label it
      // so callers can accept it as "good enough" rather than treat the solve as failed.
      const body = output.trim();
      if (incumbent) {
        return `; unknown (incumbent - not proven optimal)\n${body}`;
      }
      return body ? `; ${status}\n${body}` : `; ${status}`;

    } finally {
      this.z3.del_context(ctx);
    }
  }

  isLoaded(): boolean {
    return this.z3 !== null;
  }
}
