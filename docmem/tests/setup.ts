import { initSchema } from '../src/db/schema.js';
import { run } from '../src/db/connection.js';

export async function setupTestDb() {
  await initSchema();
}

export async function clearTestDb() {
  await run('DELETE FROM nodes');
}
