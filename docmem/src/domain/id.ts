import { randomBytes } from 'node:crypto';

const ALPHABET = 'abcdefghijklmnopqrstuvwxyz0123456789';

export function generateId(): string {
  const bytes = randomBytes(8);
  let result = '';
  for (let i = 0; i < 8; i++) {
    result += ALPHABET[bytes[i] % ALPHABET.length];
  }
  return result;
}
