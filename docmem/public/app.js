const state = {
  page: 'view',
  viewMode: 'structure',
  selectedRoot: null,
  roots: [],
};

const listPane = document.getElementById('list-pane');
const contentPane = document.getElementById('content-pane');
const optionBar = document.getElementById('option-bar');
const navBar = document.getElementById('nav-bar');
const fileInput = document.getElementById('file-input');

async function api(url, opts) {
  const res = await fetch(url, opts);
  return res.json();
}

function renderList() {
  listPane.innerHTML = '';
  for (const r of state.roots) {
    const div = document.createElement('div');
    div.className = 'item' + (r === state.selectedRoot ? ' selected' : '');
    div.textContent = r;
    div.onclick = () => {
      state.selectedRoot = r;
      renderList();
      renderContent();
    };
    listPane.appendChild(div);
  }
}

async function fetchRoots() {
  const data = await api('/api/roots');
  if (data.success) {
    const text = data.data;
    state.roots = text ? text.split('\n').map(line => line.split(' ')[0]) : [];
    if (state.roots.length > 0 && !state.roots.includes(state.selectedRoot)) {
      state.selectedRoot = state.roots[0];
    }
    if (state.roots.length === 0) {
      state.selectedRoot = null;
    }
  }
  renderList();
}

async function renderContent() {
  if (state.page === 'view') {
    if (!state.selectedRoot) {
      contentPane.textContent = '';
      return;
    }
    const data = await api(`/api/view?root=${encodeURIComponent(state.selectedRoot)}&mode=${state.viewMode}`);
    if (data.success) {
      contentPane.textContent = typeof data.data === 'string' ? data.data : JSON.stringify(data.data, null, 2);
    } else {
      contentPane.textContent = 'Error: ' + data.error;
    }
  } else {
    renderPersistPane();
  }
}

function renderPersistPane() {
  contentPane.innerHTML = '';
  const actions = [
    { label: 'load toml', action: loadToml },
    { label: 'save toml', action: saveToml },
    { label: 'save expanded', action: saveExpanded },
    { label: 'save serialized', action: saveSerialized },
    { label: 'delete', action: deleteDocmem },
  ];
  actions.forEach(({ label, action }) => {
    contentPane.appendChild(createLink(label, false, action));
  });
}

const VIEW_MODES = ['expand', 'structure', 'nested', 'serialize'];

function createLink(text, isActive, onClick) {
  const a = document.createElement('a');
  a.href = '#';
  a.textContent = text;
  a.className = isActive ? 'active' : '';
  a.onclick = (e) => { e.preventDefault(); onClick(); };
  return a;
}

function renderOptionBar() {
  optionBar.innerHTML = '';
  if (state.page === 'view') {
    VIEW_MODES.forEach(mode => {
      const link = createLink(mode, mode === state.viewMode, () => {
        state.viewMode = mode;
        renderOptionBar();
        renderContent();
      });
      optionBar.appendChild(link);
    });
  }
  optionBar.prepend(createLink('refresh', false, () => fetchRoots().then(() => renderContent())));
}

function triggerDownload(content, filename, mimeType) {
  const blob = new Blob([content], { type: mimeType });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  a.click();
  URL.revokeObjectURL(url);
}

function loadToml() {
  fileInput.onchange = async (e) => {
    const file = e.target.files[0];
    if (!file) return;
    const content = await file.text();
    const data = await api('/api/load-toml', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ content }),
    });
    if (data.success) {
      await fetchRoots();
      renderContent();
    } else {
      contentPane.textContent = 'Error: ' + data.error;
    }
    fileInput.value = '';
  };
  fileInput.click();
}

async function exportData(endpoint, filename, mimeType, formatData = (d) => d) {
  if (!state.selectedRoot) return;
  const data = await api(endpoint, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ rootId: state.selectedRoot }),
  });
  if (data.success) {
    triggerDownload(formatData(data.data), filename, mimeType);
  } else {
    contentPane.textContent = 'Error: ' + data.error;
  }
}

async function saveToml() {
  await exportData('/api/export-toml', state.selectedRoot + '.toml', 'application/toml');
}

async function saveExpanded() {
  await exportData('/api/export-expanded', state.selectedRoot + '-expanded.txt', 'text/plain');
}

async function saveSerialized() {
  await exportData('/api/export-serialized', state.selectedRoot + '-serialized.txt', 'text/plain');
}

async function deleteDocmem() {
  if (!state.selectedRoot) return;
  if (!confirm(`Delete docmem '${state.selectedRoot}' and all its children?`)) return;
  const data = await api('/api/delete', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ rootId: state.selectedRoot }),
  });
  if (data.success) {
    await fetchRoots();
    renderContent();
  } else {
    contentPane.textContent = 'Error: ' + data.error;
  }
}

// Nav clicks
navBar.addEventListener('click', (e) => {
  if (e.target.tagName !== 'A') return;
  e.preventDefault();
  const page = e.target.dataset.page;
  if (!page) return;
  state.page = page;
  navBar.querySelectorAll('a[data-page]').forEach(a => a.classList.toggle('active', a.dataset.page === page));
  renderOptionBar();
  renderContent();
});

// Init
fetchRoots().then(() => {
  renderOptionBar();
  renderContent();
});
