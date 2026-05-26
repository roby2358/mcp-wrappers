# FIXES — yuwakisa-z3solver-mcp

_Last updated: 2026-05-26. Two issues are now documented: (1) the `(get-value …)`/`(get-objectives)` status-parse bug — **fixed** (below); (2) best-so-far model discarded on optimize timeout — **diagnosed, fix proposed** (see "Second issue: best-so-far …"). Both surfaced while using the server from another project (latest: MaxSAT arc-shaping in plotsolver); each made Z3 look broken when Z3 was in fact fine._

## TL;DR

`solve_smtlib` reported **`unknown`** for any SMT-LIB input that contained an
output-producing command other than `(check-sat)` — most commonly
`(get-value …)` or `(get-objectives)`. The status detection was the culprit, not
Z3. Fixed in `src/solver/z3wrapper.ts`; rebuilt; verified. **The published npm
package still has the bug until it is republished** (see "What's left").

## The bug

In `src/solver/z3wrapper.ts`, `solveImpl()` runs the input in two phases:

1. **Phase 1** — strip the get-commands it will re-issue, then
   `eval_smtlib2_string(ctx, cleaned)` and read the check-sat status.
2. **Phase 2** — separately issue `(get-model)` (sat) or `(get-unsat-core)` (unsat).

Two problems combined:

- `stripGetCommands()` removed only `(get-model)` and `(get-unsat-core)` — **not**
  `(get-value …)`, `(get-objectives)`, etc.
- `eval_smtlib2_string` returns the **concatenated output of every command** it
  ran. So with a surviving `(get-value …)`, the phase-1 output was e.g.
  `"sat\n((x 0) (y 1))"`.
- `parseStatus()` did an **exact match**: `output.trim() === 'sat'`. The
  concatenated string is not exactly `"sat"`, so it fell through to `unknown`.

### Why it was so confusing

- Queries ending in `(get-model)` worked — `get-model` was stripped, so phase-1
  output was exactly `"sat"`.
- Queries ending in `(get-value …)` / `(get-objectives)` always returned
  `unknown`, regardless of problem size or satisfiability.
- Calling the `z3-solver` package directly (Solver API, not `eval_smtlib2_string`)
  worked fine — confirming Z3 was healthy and the wrapper was at fault.
- It survived process restarts and a full machine reboot, because it was a code
  bug, not environment state.

## The fix

`src/solver/z3wrapper.ts`:

1. **`parseStatus()`** now scans output **lines** for a bare status token instead
   of exact-matching the whole blob:
   ```ts
   const lines = output.split(/\r?\n/).map((l) => l.trim());
   if (lines.includes('sat')) return 'sat';
   if (lines.includes('unsat')) return 'unsat';
   return 'unknown';
   ```
   This alone fixes the reported bug and is robust to any extra command output.

2. **`stripGetCommands()`** now also strips `(get-objectives)`, `(get-assignment)`,
   and `(get-value …)`, so phase 1 yields only the status (belt and suspenders).
   Note the `(get-value …)` regex handles one level of parens; deeply nested
   value expressions would slip through, but `parseStatus` covers that case.

Rebuilt with `npm run build` (tsc → `build/`).

## Verification

Ran the rebuilt `Z3Solver` against the exact shape that used to fail:

- Multi-var problem + `distinct` + `(get-value …)` → now `; sat` with the correct
  model (previously `; unknown`).
- An unsatisfiable problem → correctly `; unsat`.

## Second issue: best-so-far model discarded on optimize timeout (found 2026-05-26)

_Context: surfaced doing MaxSAT arc-shaping (`assert-soft`) from the plotsolver project. A hard-constraints-only (feasibility) solve returned `; sat` with a full model instantly; adding the soft objective made the **same** problem return a bare `; unknown` — even though Z3 had a perfectly usable ordering in hand._

### Symptom

Any optimization query — `assert-soft` (MaxSAT) or `maximize`/`minimize` (OMT) — that cannot *prove* its optimum within the time bound returns a bare `; unknown` with no model. The feasible, best-so-far solution Z3 found along the way is thrown away. This makes "good enough" optimization impossible through the wrapper: Z3's optimizer is **anytime** (it has a good incumbent within milliseconds and spends the rest of the budget on the optimality *proof*), but the wrapper discards that incumbent on timeout. Distinct from issue 1 — here the status genuinely *is* `unknown`; the loss is the model, not the status.

### Cause

In `solveImpl()` (`src/solver/z3wrapper.ts`), phase 2 fetches a model only on `sat`:

```ts
if (status === 'sat') {
  const model = await this.z3.eval_smtlib2_string(ctx, '(get-model)');
  output = String(model || '');
} else if (status === 'unsat') {
  /* (get-unsat-core) */
}
// status === 'unknown' → output stays '' → returns just `; unknown`
```

There is no `unknown` branch, so `(get-model)` is never attempted — even though, for an optimize problem that hit its internal timeout, Z3 still holds a feasible incumbent in `ctx`.

### Proposed fix

Add an `unknown` branch that still asks for the model and includes it only when Z3 actually has one:

```ts
} else if (status === 'unknown') {
  const model = await this.z3.eval_smtlib2_string(ctx, '(get-model)');
  const text = String(model || '').trim();
  // Optimize-timeout → Z3 returns the best-so-far model here.
  // A genuine "no model yet" returns an (error …) line — exclude that.
  if (text && !/^\(error/m.test(text)) output = text;
}
```

Label the result so callers can tell a *certified* model from a best-effort one — e.g. return `; unknown (incumbent — not proven optimal)` when a model is attached. Downstream can then accept the ordering as "good enough" instead of treating the whole solve as failed.

(If `eval_smtlib2_string('(get-model)')` turns out **not** to surface the incumbent after an SMT2-frontend optimize timeout, fall back to driving the `Optimize` API directly — `opt.check()` returning `unknown` still lets you call `opt.model()` for the incumbent. The string frontend is preferred if it works because it keeps the two-phase shape.)

### Critical interaction: there are TWO timeouts, and their order decides everything

1. **Z3-internal** — `(set-option :timeout N)` inside the SMT-LIB. When this fires, Z3 returns `unknown` *gracefully*, incumbent intact. This is what the fix reads.
2. **JS wrapper** — `solve(smtlib, timeoutMs)` races `solveImpl` against a `setTimeout` that **rejects**. If this fires first, the whole call throws "Z3 solver timed out" and **everything is lost** — no status, no incumbent.

So the incumbent is recoverable **only if the internal timeout fires first**. Today that's entirely on the caller (set `(set-option :timeout N)` with `N` safely below `timeoutMs`). Consider having the wrapper inject/clamp its own internal timeout derived from `timeoutMs` (e.g. internal ≈ `timeoutMs` − margin) so a caller who forgets can't hit the hard JS wall and lose an answer Z3 already had.

### Verify

Feed a MaxSAT instance too big to certify quickly (e.g. ~25+ integer position vars + `distinct` + many `assert-soft` terms — the plotsolver 27-beat encoding is a ready example) with `(set-option :timeout 2000)` and a larger `timeoutMs`. Expect `; unknown` **with** a model block (previously: bare `; unknown`). A 3-variable `assert-soft` must still return `; sat` with the proven optimum.

## What's left (next steps)

1. **Deploy the fix to the live server.** The running MCP server is the
   **npx-published** package (`npx -y yuwakisa-z3solver-mcp`), which still has the
   bug. Options:
   - Bump the version in `package.json` and `npm publish`, then clear the npx
     cache (`~/.npm/_npx/...`) so the new version is fetched; **or**
   - Point the MCP client config at the local build instead:
     `command: "node"`, `args: ["/work/mcp-wrappers/z3solver/build/index.js"]`.
   - **Until then, callers must use `(get-model)` and avoid `(get-value …)` /
     `(get-objectives)`** to get correct results from the live server.

2. **Pre-existing unsat-core bug.** For unsat inputs, phase 2 calls
   `(get-unsat-core)` even when the input never set
   `(set-option :produce-unsat-cores true)`, so the output carries a Z3 error line
   (`"unsat core construction is not enabled…"`). The status is still correct, but
   the body is noise. Fix by enabling `:produce-unsat-cores` before the core call,
   or by only attempting it when enabled.

3. **Add a regression test.** There is currently no real test runner
   (`npm test` is a stub; `test-*.js` are ad-hoc). Add a test that asserts a
   `(get-value …)` query returns `; sat` — this is exactly the case that
   regressed and would catch a recurrence.

4. **Optional hardening.** If callers may send nested `(get-value …)` expressions,
   replace the regex strip with a balanced-paren strip, or rely solely on the
   `parseStatus` line scan (which already handles it).

5. **Surface the best-so-far model on optimize timeout** (see "Second issue" above).
   Add the `unknown` → `(get-model)` branch, label incumbents distinctly, and clamp an
   internal timeout from `timeoutMs` so the JS wall can't pre-empt Z3. Ship in the same
   redeploy as item 1. Add a regression test: a MaxSAT instance + short internal timeout
   returns `; unknown` *with* a model.
