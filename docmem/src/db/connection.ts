import duckdb from 'duckdb';

let db: duckdb.Database | null = null;
let conn: duckdb.Connection | null = null;

export function getConnection(): duckdb.Connection {
  if (!conn) {
    db = new duckdb.Database(':memory:');
    conn = new duckdb.Connection(db);
  }
  return conn;
}

/** Promise wrapper for conn.all() */
export function query(sql: string, ...params: unknown[]): Promise<Record<string, unknown>[]> {
  const c = getConnection();
  return new Promise((resolve, reject) => {
    c.all(sql, ...params, (err: Error | null, rows: Record<string, unknown>[]) => {
      if (err) reject(err);
      else resolve(rows ?? []);
    });
  });
}

/** Promise wrapper for conn.run() */
export function run(sql: string, ...params: unknown[]): Promise<void> {
  const c = getConnection();
  return new Promise((resolve, reject) => {
    c.run(sql, ...params, (err: Error | null) => {
      if (err) reject(err);
      else resolve();
    });
  });
}
