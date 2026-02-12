import { run } from './connection.js';

export async function initSchema(): Promise<void> {
  await run(`
    CREATE TABLE IF NOT EXISTS nodes (
      id            VARCHAR NOT NULL PRIMARY KEY,
      parent_id     VARCHAR,
      content       VARCHAR NOT NULL DEFAULT '',
      order_value   DOUBLE NOT NULL,
      token_count   INTEGER NOT NULL,
      created_at    VARCHAR NOT NULL,
      updated_at    VARCHAR NOT NULL,
      context_type  VARCHAR NOT NULL,
      context_name  VARCHAR NOT NULL,
      context_value VARCHAR NOT NULL,
      readonly      INTEGER NOT NULL DEFAULT 0,
      hash          VARCHAR
    )
  `);
  await run(`CREATE INDEX IF NOT EXISTS idx_parent_id ON nodes (parent_id)`);
  await run(`CREATE INDEX IF NOT EXISTS idx_parent_order ON nodes (parent_id, order_value)`);
}
