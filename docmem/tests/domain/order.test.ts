import { describe, it, expect } from 'vitest';
import { orderBefore, orderAfter } from '../../src/domain/order.js';

describe('orderBefore', () => {
  it('offsets by -1 when no previous sibling', () => {
    expect(orderBefore(5.0, null)).toBe(4.0);
  });

  it('uses 20/80 weighted interpolation', () => {
    // 20% toward target (5), 80% toward prev (3)
    // prev + (target - prev) * 0.2 = 3 + 2 * 0.2 = 3.4
    expect(orderBefore(5.0, 3.0)).toBeCloseTo(3.4);
  });
});

describe('orderAfter', () => {
  it('offsets by +1 when no next sibling', () => {
    expect(orderAfter(5.0, null)).toBe(6.0);
  });

  it('uses 20/80 weighted interpolation', () => {
    // target + (next - target) * 0.8 = 5 + (7 - 5) * 0.8 = 5 + 1.6 = 6.6
    expect(orderAfter(5.0, 7.0)).toBeCloseTo(6.6);
  });
});
