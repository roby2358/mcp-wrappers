#!/usr/bin/env node
/**
 * Quick local test of the Z3Solver
 */
import { Z3Solver } from './build/solver/z3wrapper.js';

const solver = new Z3Solver();

const testSMTLIB = `
(set-option :produce-unsat-cores true)
(declare-const x Int)
(declare-const y Int)
(assert (! (> x 0) :named x-positive))
(assert (! (> y 0) :named y-positive))
(assert (! (< (+ x y) 10) :named sum-less-than-10))
(check-sat)
`;

console.log('Testing Z3Solver...\n');
console.log('Input SMT-LIB:');
console.log(testSMTLIB);
console.log('\n--- Solving ---\n');

try {
  const result = await solver.solve(testSMTLIB);
  console.log('Result:');
  console.log(result);
  console.log('\n✓ Test passed!');
} catch (error) {
  console.error('✗ Test failed:', error.message);
  process.exit(1);
}
