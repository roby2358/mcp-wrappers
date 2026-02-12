import { describe, it, expect } from 'vitest';
import { countTokens } from '../../src/domain/token.js';

describe('countTokens', () => {
  it('returns 0 for empty string', () => {
    expect(countTokens('')).toBe(0);
  });

  it('rounds up for non-multiple-of-4', () => {
    expect(countTokens('hello')).toBe(2); // 5/4 = 1.25 -> 2
  });

  it('exact multiple of 4', () => {
    expect(countTokens('abcd')).toBe(1); // 4/4 = 1
  });

  it('handles long text', () => {
    expect(countTokens('a'.repeat(100))).toBe(25);
  });
});
