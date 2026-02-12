import { createHash } from 'node:crypto';

export function computeHash(
  parentId: string | null,
  contextType: string,
  contextName: string,
  contextValue: string,
  content: string,
  orderValue: number
): string {
  const parts = [
    parentId ?? '',
    contextType,
    contextName,
    contextValue,
    content,
    String(orderValue),
  ];
  const input = parts.join('|');
  return createHash('sha512').update(input).digest('base64');
}
