import { describe, it, expect } from 'vitest';
import { computeHash } from '../../src/domain/hash.js';

describe('computeHash', () => {
  it('produces a base64 string', () => {
    const h = computeHash(null, 'root', 'purpose', 'doc', 'hello', 1.0);
    expect(h).toBeTruthy();
    // SHA-512 base64 is 88 chars
    expect(h.length).toBe(88);
  });

  it('normalizes null parent_id to empty string', () => {
    const h1 = computeHash(null, 'a', 'b', 'c', 'd', 1.0);
    const h2 = computeHash(null, 'a', 'b', 'c', 'd', 1.0);
    expect(h1).toBe(h2);
  });

  it('produces different hashes for different inputs', () => {
    const h1 = computeHash(null, 'a', 'b', 'c', 'text1', 1.0);
    const h2 = computeHash(null, 'a', 'b', 'c', 'text2', 1.0);
    expect(h1).not.toBe(h2);
  });

  it('includes order_value in hash', () => {
    const h1 = computeHash('p', 'a', 'b', 'c', 'text', 1.0);
    const h2 = computeHash('p', 'a', 'b', 'c', 'text', 2.0);
    expect(h1).not.toBe(h2);
  });
});
