#!/usr/bin/env node
/**
 * Test input validation corrections
 */
import { solve } from './build/tools/solve.js';

console.log('=== Validation Tests ===\n');

// Test: NaN timeout should be rejected
console.log('Test: NaN timeout rejection');
try {
  await solve({ smtlib: '(declare-const x Int)\n(assert (> x 0))\n(check-sat)', timeout_ms: NaN });
  console.log('✗ FAIL - should have rejected NaN\n');
} catch (error) {
  const msg = error.message;
  const hasNaN = msg.includes('NaN');
  console.log('Error:', msg);
  console.log(hasNaN ? '✓ PASS - NaN properly rejected\n' : '✗ FAIL - NaN not detected\n');
}

// Test: Infinity timeout should be rejected
console.log('Test: Infinity timeout rejection');
try {
  await solve({ smtlib: '(declare-const x Int)\n(assert (> x 0))\n(check-sat)', timeout_ms: Infinity });
  console.log('✗ FAIL - should have rejected Infinity\n');
} catch (error) {
  const msg = error.message;
  const hasInfinity = msg.includes('Infinity');
  console.log('Error:', msg);
  console.log(hasInfinity ? '✓ PASS - Infinity properly rejected\n' : '✗ FAIL - Infinity not detected\n');
}

// Test: Valid timeout should work
console.log('Test: Valid timeout works');
try {
  const result = await solve({ smtlib: '(declare-const x Int)\n(assert (> x 0))\n(check-sat)', timeout_ms: 5000 });
  console.log(result.startsWith('; sat') ? '✓ PASS\n' : '✗ FAIL\n');
} catch (error) {
  console.log('✗ FAIL - valid timeout rejected:', error.message, '\n');
}

console.log('=== Validation tests completed ===');
