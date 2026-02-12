export interface NodeRow {
  id: string;
  parent_id: string | null;
  content: string;
  order_value: number;
  token_count: number;
  created_at: string;
  updated_at: string;
  context_type: string;
  context_name: string;
  context_value: string;
  readonly: number;
  hash: string | null;
}

export interface ToolResponse {
  success: boolean;
  result: unknown;
  error: string;
}

export function ok(result: unknown): ToolResponse {
  return { success: true, result, error: '' };
}

export function fail(error: string): ToolResponse {
  return { success: false, result: '', error };
}
