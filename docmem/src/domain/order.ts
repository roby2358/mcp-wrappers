/**
 * Calculate order value for inserting before a target node.
 * Uses 20% toward target, 80% toward the previous sibling.
 * If no previous sibling, offset by -1.0 from target.
 */
export function orderBefore(targetOrder: number, prevOrder: number | null): number {
  if (prevOrder === null) {
    return targetOrder - 1.0;
  }
  return prevOrder + (targetOrder - prevOrder) * 0.2;
}

/**
 * Calculate order value for inserting after a target node.
 * Uses 20% toward target, 80% toward the next sibling.
 * If no next sibling, offset by +1.0 from target.
 */
export function orderAfter(targetOrder: number, nextOrder: number | null): number {
  if (nextOrder === null) {
    return targetOrder + 1.0;
  }
  return targetOrder + (nextOrder - targetOrder) * 0.8;
}
