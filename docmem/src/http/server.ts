import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { listDocmems } from '../operations/docmem.js';
import { serialize, expandToLength, structure, nested } from '../operations/query.js';
import { importToml, exportToml } from '../operations/toml.js';
import { deleteNode } from '../operations/crud.js';
import { viewAdd, viewRemove, getActiveList } from '../operations/claudemd.js';

const PORT = 8182;

const MIME: Record<string, string> = {
  '.html': 'text/html',
  '.css': 'text/css',
  '.js': 'application/javascript',
};

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const publicDir = path.resolve(__dirname, '..', '..', 'public');

function serveStatic(req: http.IncomingMessage, res: http.ServerResponse): boolean {
  let urlPath = req.url?.split('?')[0] ?? '/';
  if (urlPath === '/') urlPath = '/index.html';

  const ext = path.extname(urlPath);
  const mime = MIME[ext];
  if (!mime) return false;

  const filePath = path.join(publicDir, urlPath);
  if (!filePath.startsWith(publicDir)) {
    res.writeHead(403);
    res.end();
    return true;
  }

  try {
    const content = fs.readFileSync(filePath, 'utf-8');
    res.writeHead(200, { 'Content-Type': mime });
    res.end(content);
    return true;
  } catch {
    return false;
  }
}

function json(res: http.ServerResponse, status: number, body: unknown): void {
  res.writeHead(status, { 'Content-Type': 'application/json' });
  res.end(JSON.stringify(body));
}

function readBody(req: http.IncomingMessage): Promise<string> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (c: Buffer) => chunks.push(c));
    req.on('end', () => resolve(Buffer.concat(chunks).toString()));
    req.on('error', reject);
  });
}

type ToolResult = { success: boolean; result: unknown; error: string };

async function handlePostOperation(
  req: http.IncomingMessage,
  operation: (body: Record<string, unknown>) => Promise<ToolResult>
): Promise<{ status: number; body: unknown }> {
  const body = JSON.parse(await readBody(req));
  const result = await operation(body);
  return result.success
    ? { status: 200, body: { success: true, data: result.result } }
    : { status: 404, body: { success: false, error: result.error } };
}

async function handleApi(req: http.IncomingMessage, res: http.ServerResponse): Promise<void> {
  const parsed = new URL(req.url ?? '/', `http://localhost:${PORT}`);
  const route = parsed.pathname;

  try {
    if (route === '/api/roots' && req.method === 'GET') {
      const result = await listDocmems();
      json(res, 200, { success: true, data: result.result });
      return;
    }

    if (route === '/api/view-active' && req.method === 'GET') {
      json(res, 200, { success: true, data: getActiveList() });
      return;
    }

    if (route === '/api/view' && req.method === 'GET') {
      const rootId = parsed.searchParams.get('root');
      const mode = parsed.searchParams.get('mode');
      if (!rootId || !mode) {
        json(res, 400, { success: false, error: 'Missing root or mode parameter.' });
        return;
      }
      let result;
      if (mode === 'serialize') result = await serialize(rootId);
      else if (mode === 'structure') result = await structure(rootId);
      else if (mode === 'nested') result = await nested(rootId);
      else if (mode === 'expand') result = await expandToLength(rootId, 100000);
      else {
        json(res, 400, { success: false, error: `Unknown mode '${mode}'. Use serialize, structure, nested, or expand.` });
        return;
      }
      if (result.success) {
        json(res, 200, { success: true, data: result.result });
      } else {
        json(res, 404, { success: false, error: result.error });
      }
      return;
    }

    if (route === '/api/export-toml' && req.method === 'POST') {
      const { status, body } = await handlePostOperation(req, (b) => exportToml(b.rootId as string));
      json(res, status, body);
      return;
    }

    if (route === '/api/load-toml' && req.method === 'POST') {
      const reqBody = JSON.parse(await readBody(req));
      const result = await importToml(reqBody.content);
      json(res, result.success ? 200 : 400, { success: result.success, data: result.result, error: result.error });
      return;
    }

    if (route === '/api/export-expanded' && req.method === 'POST') {
      const { status, body } = await handlePostOperation(req, (b) => expandToLength(b.rootId as string, 100000));
      json(res, status, body);
      return;
    }


    if (route === '/api/export-serialized' && req.method === 'POST') {
      const { status, body } = await handlePostOperation(req, (b) => serialize(b.rootId as string));
      json(res, status, body);
      return;
    }

    if (route === '/api/view-add' && req.method === 'POST') {
      const { status, body } = await handlePostOperation(req, (b) => viewAdd(b.rootId as string));
      json(res, status, body);
      return;
    }

    if (route === '/api/view-remove' && req.method === 'POST') {
      const { status, body } = await handlePostOperation(req, (b) => viewRemove(b.rootId as string));
      json(res, status, body);
      return;
    }

    if (route === '/api/delete' && req.method === 'POST') {
      const { status, body } = await handlePostOperation(req, (b) => deleteNode(b.rootId as string));
      json(res, status, body);
      return;
    }

    json(res, 404, { success: false, error: 'Not found.' });
  } catch (e: unknown) {
    const msg = e instanceof Error ? e.message : String(e);
    json(res, 500, { success: false, error: msg });
  }
}

export function startHttpServer(): void {
  const server = http.createServer((req, res) => {
    if (serveStatic(req, res)) return;
    handleApi(req, res);
  });

  server.listen(PORT, () => {
    console.error(`Docmem HTTP UI: http://localhost:${PORT}`);
  });
}
