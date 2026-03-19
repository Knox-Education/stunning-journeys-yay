/**
 * app.js – Battlegrounds front‑end controller.
 * Handles screen navigation, socket events, and lobby UI.
 */

// ── Socket (deferred – won't block UI if connection fails) ───
let socket;
try {
  socket = io({
    transports: ['polling', 'websocket'],
    reconnection: true,
    reconnectionDelay: 1000,
    timeout: 10000,
  });
  socket.on('connect_error', (err) => console.warn('Socket connect error:', err.message));
} catch (e) {
  console.warn('Socket.io init failed:', e);
  socket = { on() {}, emit() {} }; // stub so UI still works
}

// ── State ────────────────────────────────────────────────────
let playerName = '';
let selectedMap = 0;
let currentLobbyCode = null;
let isHost = false;
let flowTarget = ''; // 'host' | 'join' | 'single'
let myColor = '#e94560';

const PLAYER_COLORS = ['#e94560', '#3498db', '#2ecc71', '#f5a623', '#9b59b6'];

// ── DOM helpers ──────────────────────────────────────────────
const $ = (sel) => document.querySelector(sel);
const $$ = (sel) => document.querySelectorAll(sel);

function showScreen(id) {
  $$('.screen').forEach((s) => s.classList.remove('active'));
  $(`#${id}`).classList.add('active');
}

// ── Screen: Start ────────────────────────────────────────────
$('#btn-singleplayer').addEventListener('click', () => {
  showScreen('screen-sp-mode');
});
$('#btn-sp-fight').addEventListener('click', () => {
  flowTarget = 'fight';
  showScreen('screen-name');
});
$('#btn-sp-training').addEventListener('click', () => {
  flowTarget = 'training';
  showScreen('screen-name');
});
$('#btn-sp-back').addEventListener('click', () => showScreen('screen-start'));
$('#btn-host').addEventListener('click', () => {
  flowTarget = 'host';
  showScreen('screen-name');
});
$('#btn-join').addEventListener('click', () => {
  flowTarget = 'join';
  showScreen('screen-name');
});
$('#btn-achievements').addEventListener('click', () => showScreen('screen-achievements'));
$('#btn-fighters-back').addEventListener('click', () => showScreen('screen-name'));
$('#btn-achievements-back').addEventListener('click', () => showScreen('screen-start'));

// ── Screen: Name input ───────────────────────────────────────
$('#btn-name-ok').addEventListener('click', submitName);
$('#input-name').addEventListener('keydown', (e) => { if (e.key === 'Enter') submitName(); });
$('#btn-name-back').addEventListener('click', () => showScreen('screen-start'));

function submitName() {
  const raw = $('#input-name').value.trim();
  if (raw.length < 1 || raw.length > 16) {
    $('#name-error').textContent = 'Name must be 1–16 characters.';
    return;
  }
  // Basic sanitisation: strip HTML-like tags
  playerName = raw.replace(/[<>]/g, '');
  $('#name-error').textContent = '';

  console.log('submitName:', flowTarget, playerName);

  // Route through fighter selection before continuing
  populateFighterScreen();
  showScreen('screen-fighters');
}

// ── Screen: Map select (host) ────────────────────────────────
function buildMapGrid() {
  const grid = $('#map-grid');
  grid.innerHTML = '';
  MAPS.forEach((map, i) => {
    const card = document.createElement('div');
    card.className = 'map-card' + (i === selectedMap ? ' selected' : '');
    const cvs = document.createElement('canvas');
    renderMapThumb(cvs, i);
    const label = document.createElement('div');
    label.className = 'map-label';
    label.textContent = map.name;
    card.appendChild(cvs);
    card.appendChild(label);
    card.addEventListener('click', () => {
      $$('.map-card').forEach((c) => c.classList.remove('selected'));
      card.classList.add('selected');
      selectedMap = i;
    });
    grid.appendChild(card);
  });
}

$('#btn-host-create').addEventListener('click', () => {
  socket.emit('host-game', { playerName, mapIndex: selectedMap });
});
$('#btn-host-map-back').addEventListener('click', () => showScreen('screen-name'));

// ── Screen: Join ─────────────────────────────────────────────
$('#btn-join-go').addEventListener('click', submitJoin);
$('#input-code').addEventListener('keydown', (e) => { if (e.key === 'Enter') submitJoin(); });
$('#btn-join-back').addEventListener('click', () => showScreen('screen-name'));

function submitJoin() {
  const code = $('#input-code').value.trim();
  if (code.length !== 6) {
    $('#join-error').textContent = 'Code must be 6 characters.';
    return;
  }
  $('#join-error').textContent = '';
  socket.emit('join-game', { playerName, code });
}

// ── Screen: Lobby ────────────────────────────────────────────
function openLobby(code, mapIndex, players, hosting, availableColors) {
  isHost = hosting;
  currentLobbyCode = code;
  selectedMap = mapIndex;

  // Find my color from the player list
  const me = players.find((p) => p.id === socket.id);
  if (me) myColor = me.color;

  $('#lobby-code').textContent = code;
  $('#lobby-title').textContent = isHost ? 'Your Lobby' : 'Lobby';
  renderMap($('#lobby-map-preview'), mapIndex, 16);
  $('#lobby-map-name').textContent = MAPS[mapIndex].name;

  if (isHost) {
    $('#host-map-controls').classList.remove('hidden');
    $('#btn-start-game').classList.remove('hidden');
  } else {
    $('#host-map-controls').classList.add('hidden');
    $('#btn-start-game').classList.add('hidden');
  }

  refreshPlayerList(players);
  buildColorPicker(availableColors || []);
  showScreen('screen-lobby');
}

$('#btn-copy-code').addEventListener('click', () => {
  if (currentLobbyCode) {
    navigator.clipboard.writeText(currentLobbyCode).catch(() => {});
  }
});

$('#btn-prev-map').addEventListener('click', () => cycleMap(-1));
$('#btn-next-map').addEventListener('click', () => cycleMap(1));

function cycleMap(dir) {
  selectedMap = (selectedMap + dir + MAPS.length) % MAPS.length;
  renderMap($('#lobby-map-preview'), selectedMap, 16);
  $('#lobby-map-name').textContent = MAPS[selectedMap].name;
  socket.emit('change-map', { mapIndex: selectedMap });
}

$('#btn-start-game').addEventListener('click', () => {
  socket.emit('start-game');
});

$('#btn-leave-lobby').addEventListener('click', () => {
  socket.emit('leave-lobby');
  currentLobbyCode = null;
  showScreen('screen-start');
});

function refreshPlayerList(players) {
  const list = $('#player-list');
  list.innerHTML = '';
  players.forEach((p) => {
    const div = document.createElement('div');
    div.className = 'player-item';
    div.innerHTML =
      `<span class="player-dot" style="background:${p.color}"></span>` +
      `<span>${escapeHtml(p.name)}</span>` +
      (p.isHost ? '<span class="host-badge">Host</span>' : '');
    list.appendChild(div);
  });
}

// ── Color picker ─────────────────────────────────────────────
function buildColorPicker(availableColors) {
  const picker = $('#color-picker');
  picker.innerHTML = '<span class="color-label">Pick your color:</span>';

  // Build the set of taken colors (not available AND not my color)
  const availSet = new Set(availableColors || []);

  PLAYER_COLORS.forEach((color) => {
    const swatch = document.createElement('button');
    swatch.className = 'color-swatch';
    swatch.style.background = color;

    const isMyColor = color === myColor;
    const isTaken = !availSet.has(color) && !isMyColor;

    if (isMyColor) swatch.classList.add('selected');
    if (isTaken) swatch.classList.add('taken');

    swatch.addEventListener('click', () => {
      if (isTaken) return;
      // Immediate visual feedback
      picker.querySelectorAll('.color-swatch').forEach((s) => s.classList.remove('selected'));
      swatch.classList.add('selected');
      myColor = color;
      // Tell server
      socket.emit('change-color', { color });
    });
    picker.appendChild(swatch);
  });
}

// ── Socket events ────────────────────────────────────────────
socket.on('game-hosted', ({ code, mapIndex, players, availableColors }) => {
  openLobby(code, mapIndex, players, true, availableColors);
});

socket.on('game-joined', ({ code, mapIndex, players, availableColors }) => {
  openLobby(code, mapIndex, players, false, availableColors);
});

socket.on('join-error', ({ message }) => {
  $('#join-error').textContent = message;
});

socket.on('player-joined', ({ players, availableColors }) => {
  refreshPlayerList(players);
  buildColorPicker(availableColors || []);
});

socket.on('player-left', ({ players, availableColors }) => {
  refreshPlayerList(players);
  buildColorPicker(availableColors || []);
});

socket.on('player-updated', ({ players, availableColors }) => {
  const me = players.find((p) => p.id === socket.id);
  if (me) myColor = me.color;
  refreshPlayerList(players);
  buildColorPicker(availableColors || []);
});

socket.on('map-changed', ({ mapIndex }) => {
  selectedMap = mapIndex;
  renderMap($('#lobby-map-preview'), mapIndex, 16);
  $('#lobby-map-name').textContent = MAPS[mapIndex].name;
});

socket.on('game-starting', ({ mapIndex, players }) => {
  enterGame(mapIndex, players);
});

// Multiplayer movement sync
socket.on('player-moved', ({ id, x, y, hp }) => {
  if (typeof onPlayerMove === 'function') {
    onPlayerMove(id, x, y, hp);
  }
});

// Multiplayer damage sync
socket.on('player-damaged', ({ targetId, amount }) => {
  if (typeof onRemoteDamage === 'function') {
    onRemoteDamage(targetId, amount);
  }
});

// Multiplayer knockback sync
socket.on('player-knockedback', ({ targetId, x, y }) => {
  if (typeof onRemoteKnockback === 'function') {
    onRemoteKnockback(targetId, x, y);
  }
});

// Zone timer sync from host
socket.on('zone-synced', ({ zoneInset: zi, zoneTimer: zt }) => {
  if (typeof onZoneSync === 'function') {
    onZoneSync(zi, zt);
  }
});

// Player died
socket.on('player-death', ({ playerId }) => {
  if (typeof onRemoteDeath === 'function') {
    onRemoteDeath(playerId);
  }
});

// Game over from server
socket.on('game-over', ({ winnerId, winnerName }) => {
  if (typeof onGameOver === 'function') {
    onGameOver(winnerId, winnerName);
  }
});

// Buff applied by another player
socket.on('player-buffed', ({ casterId, type, duration, cx, cy }) => {
  if (typeof onRemoteBuff === 'function') {
    onRemoteBuff(casterId, type, duration, cx, cy);
  }
});

// Debuff applied by another player
socket.on('player-debuffed', ({ casterId, targetId, type, duration }) => {
  if (typeof onRemoteDebuff === 'function') {
    onRemoteDebuff(casterId, targetId, type, duration);
  }
});

// Projectile spawned by another player (visual only)
socket.on('projectile-spawned', ({ ownerId, projectiles: projs }) => {
  if (typeof onRemoteProjectiles === 'function') {
    onRemoteProjectiles(ownerId, projs);
  }
});

// ── Enter the game screen ────────────────────────────────────
function enterGame(mapIndex, players, mode) {
  // Inject fighterId for local player
  players = players.map((p) => ({
    ...p,
    fighterId: (p.id === (socket.id || 'local')) ? selectedFighterId : (p.fighterId || 'fighter'),
  }));
  showScreen('screen-game');
  const myId = socket.id || 'local';
  startGame(mapIndex, players, myId, mode);
}

// ── Fighter screen ───────────────────────────────────────────
function populateFighterScreen() {
  // Build selection bar
  const bar = document.querySelector('#fighter-select-bar');
  bar.innerHTML = '';
  getAllFighterIds().forEach((fid) => {
    const f = getFighter(fid);
    const btn = document.createElement('button');
    btn.className = 'fighter-select-btn' + (fid === selectedFighterId ? ' active' : '');
    btn.textContent = f.name;
    btn.addEventListener('click', () => {
      selectedFighterId = fid;
      populateFighterScreen();
    });
    bar.appendChild(btn);
  });

  const f = getFighter(selectedFighterId);
  if (!f) return;

  const el = (sel) => document.querySelector(sel);
  el('#fc-name').textContent = f.name;
  el('#fc-hp').textContent = 'HP: ' + f.hp;
  el('#fc-desc').textContent = f.description;
  el('#fc-speed').textContent = f.speed;
  el('#fc-heal').textContent = f.healAmount + ' every ' + f.healTick + 's (after ' + f.healDelay + 's)';
  // Update button text
  el('#btn-select-fighter').textContent = 'Pick & Play';

  const list = el('#fc-abilities');
  list.innerHTML = '';
  f.abilities.forEach((a) => {
    const li = document.createElement('li');
    li.className = 'ability-item';
    li.innerHTML =
      `<span class="ability-key">${escapeHtml(a.key)}</span>` +
      `<div><strong>${escapeHtml(a.name)}</strong>` +
      `<br><small>${escapeHtml(a.description)}</small>` +
      `<br><small>DMG: ${a.damage || '—'}  CD: ${a.cooldown || '—'}s</small></div>`;
    list.appendChild(li);
  });
}

$('#btn-select-fighter').addEventListener('click', () => {
  if (typeof socket !== 'undefined' && socket.emit) {
    socket.emit('change-fighter', { fighterId: selectedFighterId });
  }
  if (flowTarget === 'host') {
    socket.emit('host-game', { playerName, mapIndex: selectedMap });
  } else if (flowTarget === 'training') {
    const randomMap = Math.floor(Math.random() * MAPS.length);
    const color = PLAYER_COLORS[Math.floor(Math.random() * PLAYER_COLORS.length)];
    enterGame(randomMap, [{ id: 'local', name: playerName, color, isHost: true, fighterId: selectedFighterId }], 'training');
  } else if (flowTarget === 'fight') {
    const randomMap = Math.floor(Math.random() * MAPS.length);
    const color = PLAYER_COLORS[Math.floor(Math.random() * PLAYER_COLORS.length)];
    enterGame(randomMap, [{ id: 'local', name: playerName, color, isHost: true, fighterId: selectedFighterId }], 'fight');
  } else if (flowTarget === 'join') {
    showScreen('screen-join');
  }
});

// ── Util ─────────────────────────────────────────────────────
function escapeHtml(str) {
  const div = document.createElement('div');
  div.appendChild(document.createTextNode(str));
  return div.innerHTML;
}
