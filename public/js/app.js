/**
 * app.js – Battlegrounds front‑end controller.
 * Handles screen navigation, socket events, and lobby UI.
 */

// ── Socket (deferred – won't block UI if connection fails) ───
let socket;
try {
  socket = io({
    transports: ['polling', 'websocket'],
    upgrade: true,
    reconnection: true,
    reconnectionDelay: 1000,
    reconnectionAttempts: 10,
    timeout: 20000,
  });
  socket.on('connect', () => console.log('Socket connected:', socket.id));
  socket.on('connect_error', (err) => console.warn('Socket connect error:', err.message));
  socket.on('disconnect', (reason) => console.warn('Socket disconnected:', reason));
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
let lobbyMode = 'ffa'; // 'ffa' | 'teams2' | 'teams3'

const PLAYER_COLORS = ['#e94560', '#3498db', '#2ecc71', '#f5a623', '#9b59b6', '#e67e22'];

// Shuffled fighter order (Fighter & Poker stay at front)
const _shuffledFighterIds = (() => {
  const all = getAllFighterIds();
  const fixed = all.filter(id => id === 'fighter' || id === 'poker');
  const rest = all.filter(id => id !== 'fighter' && id !== 'poker');
  for (let i = rest.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [rest[i], rest[j]] = [rest[j], rest[i]];
  }
  return [...fixed, ...rest];
})();

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
$('#btn-sp-fight-easy').addEventListener('click', () => {
  flowTarget = 'fight';
  showScreen('screen-name');
});
$('#btn-sp-fight-hard').addEventListener('click', () => {
  flowTarget = 'fight-hard';
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
$('#btn-fighters-back').addEventListener('click', () => showScreen('screen-name'));

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

  if (flowTarget === 'host') {
    // Multiplayer host: go to map select, then lobby (fighter select is in lobby)
    buildMapGrid();
    showScreen('screen-host-map');
  } else if (flowTarget === 'join') {
    // Multiplayer join: go to code entry, then lobby (fighter select is in lobby)
    showScreen('screen-join');
  } else {
    // Singleplayer: show fighter select screen
    populateFighterScreen();
    showScreen('screen-fighters');
  }
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
  socket.emit('host-game', { playerName, mapIndex: selectedMap, fighterId: selectedFighterId, lobbyMode });
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
  socket.emit('join-game', { playerName, code, fighterId: selectedFighterId });
}

// ── Screen: Lobby ────────────────────────────────────────────
function openLobby(code, mapIndex, players, hosting, availableColors, mode) {
  isHost = hosting;
  currentLobbyCode = code;
  selectedMap = mapIndex;
  lobbyMode = mode || 'ffa';

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
    $('#lobby-mode-toggle').classList.remove('hidden');
  } else {
    $('#host-map-controls').classList.add('hidden');
    $('#btn-start-game').classList.add('hidden');
    $('#lobby-mode-toggle').classList.add('hidden');
  }
  _updateModeLabel();

  refreshPlayerList(players);
  buildColorPicker(availableColors || []);
  populateLobbyFighters();
  showScreen('screen-lobby');
}

function _updateModeLabel() {
  const el = $('#lobby-mode-label');
  if (el) {
    if (lobbyMode === 'teams3') el.textContent = '3 Teams (max 6)';
    else if (lobbyMode === 'teams2') el.textContent = '2 Teams (max 6)';
    else el.textContent = 'FFA (max 4)';
  }
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
  const warn = $('#lobby-mode-warning');
  if (warn) { warn.style.display = 'none'; warn.textContent = ''; }
  socket.emit('start-game');
});

socket.on('start-error', ({ message }) => {
  const warn = $('#lobby-mode-warning');
  if (warn) {
    warn.textContent = message;
    warn.style.display = 'inline';
  }
});

$('#btn-toggle-mode').addEventListener('click', () => {
  if (lobbyMode === 'ffa') lobbyMode = 'teams2';
  else if (lobbyMode === 'teams2') lobbyMode = 'teams3';
  else lobbyMode = 'ffa';
  _updateModeLabel();
  socket.emit('change-mode', { lobbyMode });
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
    const fighterName = (typeof getFighter === 'function' && p.fighterId) ? getFighter(p.fighterId).name : '';
    div.innerHTML =
      `<span class="player-dot" style="background:${p.color}"></span>` +
      `<span>${escapeHtml(p.name)}</span>` +
      (fighterName ? `<span style="opacity:0.6;margin-left:6px;font-size:0.85em">(${escapeHtml(fighterName)})</span>` : '') +
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
socket.on('game-hosted', ({ code, mapIndex, players, availableColors, lobbyMode: lm }) => {
  openLobby(code, mapIndex, players, true, availableColors, lm);
});

socket.on('game-joined', ({ code, mapIndex, players, availableColors, lobbyMode: lm }) => {
  openLobby(code, mapIndex, players, false, availableColors, lm);
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

socket.on('mode-changed', ({ lobbyMode: lm }) => {
  lobbyMode = lm || 'ffa';
  _updateModeLabel();
});

socket.on('game-starting', ({ mapIndex, players, lobbyMode: lm }) => {
  if (lm) lobbyMode = lm;
  const mode = (lobbyMode === 'teams2' || lobbyMode === 'teams3') ? 'teams' : undefined;
  enterGame(mapIndex, players, mode);
});

// Multiplayer movement sync (legacy — skipped under host-authoritative)
socket.on('player-moved', ({ id, x, y, hp }) => {
  if (typeof isHostAuthority !== 'undefined' && typeof gameMode !== 'undefined' && gameMode === undefined) return;
  if (typeof onPlayerMove === 'function') {
    onPlayerMove(id, x, y, hp);
  }
});

// Multiplayer damage sync (legacy — skipped under host-authoritative)
socket.on('player-damaged', ({ targetId, amount }) => {
  if (typeof isHostAuthority !== 'undefined' && typeof gameMode !== 'undefined' && gameMode === undefined) return;
  if (typeof onRemoteDamage === 'function') {
    onRemoteDamage(targetId, amount);
  }
});

// Multiplayer knockback sync (legacy — skipped under host-authoritative)
socket.on('player-knockedback', ({ targetId, x, y }) => {
  if (typeof isHostAuthority !== 'undefined' && typeof gameMode !== 'undefined' && gameMode === undefined) return;
  if (typeof onRemoteKnockback === 'function') {
    onRemoteKnockback(targetId, x, y);
  }
});

// Zone timer sync (legacy — skipped under host-authoritative; zone comes in snapshot)
socket.on('zone-synced', ({ zoneInset: zi, zoneTimer: zt }) => {
  if (typeof isHostAuthority !== 'undefined' && typeof gameMode !== 'undefined' && gameMode === undefined) return;
  if (typeof onZoneSync === 'function') {
    onZoneSync(zi, zt);
  }
});

// Player died (legacy — skipped under host-authoritative; death state comes in snapshot)
socket.on('player-death', ({ playerId }) => {
  if (typeof isHostAuthority !== 'undefined' && typeof gameMode !== 'undefined' && gameMode === undefined) return;
  if (typeof onRemoteDeath === 'function') {
    onRemoteDeath(playerId);
  }
});

// Game over from server
socket.on('game-over', ({ winnerId, winnerName, winningTeam }) => {
  if (typeof onGameOver === 'function') {
    onGameOver(winnerId, winnerName, winningTeam);
  }
});

// Buff applied by another player (legacy — skipped under host-authoritative)
socket.on('player-buffed', ({ casterId, type, duration, cx, cy }) => {
  if (typeof isHostAuthority !== 'undefined' && typeof gameMode !== 'undefined' && gameMode === undefined) return;
  if (typeof onRemoteBuff === 'function') {
    onRemoteBuff(casterId, type, duration, cx, cy);
  }
});

// Debuff applied by another player (legacy — skipped under host-authoritative)
socket.on('player-debuffed', ({ casterId, targetId, type, duration }) => {
  if (typeof isHostAuthority !== 'undefined' && typeof gameMode !== 'undefined' && gameMode === undefined) return;
  if (typeof onRemoteDebuff === 'function') {
    onRemoteDebuff(casterId, targetId, type, duration);
  }
});

// Projectile spawned by another player (legacy — skipped under host-authoritative; projectiles come in snapshot)
socket.on('projectile-spawned', ({ ownerId, projectiles: projs }) => {
  if (typeof isHostAuthority !== 'undefined' && typeof gameMode !== 'undefined' && gameMode === undefined) return;
  if (typeof onRemoteProjectiles === 'function') {
    onRemoteProjectiles(ownerId, projs);
  }
});

// Host-authoritative: full game state snapshot received by non-host clients
socket.on('game-state', (snapshot) => {
  if (typeof onRemoteGameState === 'function') {
    onRemoteGameState(snapshot);
  }
});

// Host-authoritative: host receives input from a non-host client
socket.on('player-input', (input) => {
  if (typeof onRemoteInput === 'function') {
    onRemoteInput(input);
  }
});

// Position relay: all clients receive other players' positions
socket.on('player-position', (data) => {
  if (typeof onRemotePosition === 'function') {
    onRemotePosition(data);
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
function drawFighterIcon(canvas, fighterId, customSize) {
  const size = customSize || 72;
  canvas.width = size;
  canvas.height = size;
  const ctx = canvas.getContext('2d');
  const cx = size / 2, cy = size / 2, r = size * 0.38;

  if (fighterId === 'onexonexonex') {
    // Two crossed neon green swords
    ctx.lineCap = 'round';
    const sLen = r * 1.3;
    // Sword 1 (top-left to bottom-right)
    ctx.strokeStyle = '#00ff66'; ctx.lineWidth = 3; ctx.shadowColor = '#00ff66'; ctx.shadowBlur = 8;
    ctx.beginPath();
    ctx.moveTo(cx - sLen * 0.45, cy - sLen * 0.45);
    ctx.lineTo(cx + sLen * 0.45, cy + sLen * 0.45);
    ctx.stroke();
    // Blade highlight
    ctx.strokeStyle = '#88ffbb'; ctx.lineWidth = 1.2;
    ctx.beginPath();
    ctx.moveTo(cx - sLen * 0.42, cy - sLen * 0.42);
    ctx.lineTo(cx + sLen * 0.42, cy + sLen * 0.42);
    ctx.stroke();
    // Guard 1
    ctx.strokeStyle = '#00ff66'; ctx.lineWidth = 2.5;
    ctx.beginPath();
    ctx.moveTo(cx - sLen * 0.15, cy + sLen * 0.05);
    ctx.lineTo(cx + sLen * 0.05, cy - sLen * 0.15);
    ctx.stroke();
    // Sword 2 (top-right to bottom-left)
    ctx.strokeStyle = '#00ff66'; ctx.lineWidth = 3;
    ctx.beginPath();
    ctx.moveTo(cx + sLen * 0.45, cy - sLen * 0.45);
    ctx.lineTo(cx - sLen * 0.45, cy + sLen * 0.45);
    ctx.stroke();
    // Blade highlight
    ctx.strokeStyle = '#88ffbb'; ctx.lineWidth = 1.2;
    ctx.beginPath();
    ctx.moveTo(cx + sLen * 0.42, cy - sLen * 0.42);
    ctx.lineTo(cx - sLen * 0.42, cy + sLen * 0.42);
    ctx.stroke();
    // Guard 2
    ctx.strokeStyle = '#00ff66'; ctx.lineWidth = 2.5;
    ctx.beginPath();
    ctx.moveTo(cx - sLen * 0.05, cy - sLen * 0.15);
    ctx.lineTo(cx + sLen * 0.15, cy + sLen * 0.05);
    ctx.stroke();
    ctx.shadowBlur = 0;
  } else if (fighterId === 'poker') {
    // Chip icon
    ctx.fillStyle = '#1a1a2e'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#222'; ctx.beginPath(); ctx.arc(cx, cy, r * 0.75, 0, Math.PI * 2); ctx.fill();
    ctx.strokeStyle = '#f5a623'; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.arc(cx, cy, r * 0.75, 0, Math.PI * 2); ctx.stroke();
    ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.2;
    ctx.beginPath(); ctx.arc(cx, cy, r * 0.45, 0, Math.PI * 2); ctx.stroke();
    for (let n = 0; n < 4; n++) {
      const a = (n * Math.PI) / 2;
      ctx.strokeStyle = '#fff'; ctx.lineWidth = 2; ctx.beginPath();
      ctx.moveTo(cx + Math.cos(a) * r * 0.55, cy + Math.sin(a) * r * 0.55);
      ctx.lineTo(cx + Math.cos(a) * r * 0.72, cy + Math.sin(a) * r * 0.72);
      ctx.stroke();
    }
  } else if (fighterId === 'filbus') {
    // Chair icon
    ctx.fillStyle = '#1a1a2e'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    const cw = r * 0.9, ch = r * 0.5;
    ctx.fillStyle = '#a0522d';
    ctx.fillRect(cx - cw/2, cy - ch/2 + 2, cw, ch);
    ctx.fillStyle = '#8b4513';
    ctx.fillRect(cx - cw/2, cy - ch - 2, cw * 0.2, ch);
    ctx.fillRect(cx + cw/2 - cw * 0.2, cy - ch - 2, cw * 0.2, ch);
    ctx.strokeStyle = '#654321'; ctx.lineWidth = 1.5; ctx.beginPath();
    ctx.moveTo(cx - cw/2 + 2, cy + ch/2 + 2); ctx.lineTo(cx - cw/2 + 2, cy + ch + 2);
    ctx.moveTo(cx + cw/2 - 2, cy + ch/2 + 2); ctx.lineTo(cx + cw/2 - 2, cy + ch + 2);
    ctx.stroke();
  } else if (fighterId === 'cricket') {
    // Cricket bat icon
    ctx.fillStyle = '#1a1a2e'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    const batAngle = -Math.PI / 4, batLen = r * 1.5;
    const bx = cx - Math.cos(batAngle) * batLen * 0.15, by = cy - Math.sin(batAngle) * batLen * 0.15;
    ctx.strokeStyle = '#8b4513'; ctx.lineWidth = 3; ctx.beginPath();
    ctx.moveTo(bx, by);
    ctx.lineTo(bx + Math.cos(batAngle) * batLen * 0.4, by + Math.sin(batAngle) * batLen * 0.4);
    ctx.stroke();
    ctx.strokeStyle = '#c8a96e'; ctx.lineWidth = 6; ctx.beginPath();
    ctx.moveTo(bx + Math.cos(batAngle) * batLen * 0.4, by + Math.sin(batAngle) * batLen * 0.4);
    ctx.lineTo(bx + Math.cos(batAngle) * batLen, by + Math.sin(batAngle) * batLen);
    ctx.stroke();
  } else if (fighterId === 'deer') {
    // Deer antler icon — bold dual antlers
    ctx.fillStyle = '#1a1a2e'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    ctx.strokeStyle = '#c8a96e'; ctx.lineWidth = 3; ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    // Left antler — main trunk + 2 branches
    ctx.beginPath();
    ctx.moveTo(cx - 2, cy + 2);
    ctx.lineTo(cx - 6, cy - 8);
    ctx.lineTo(cx - 12, cy - 14);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(cx - 6, cy - 8);
    ctx.lineTo(cx - 14, cy - 6);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(cx - 9, cy - 11);
    ctx.lineTo(cx - 4, cy - 16);
    ctx.stroke();
    // Right antler — main trunk + 2 branches
    ctx.beginPath();
    ctx.moveTo(cx + 2, cy + 2);
    ctx.lineTo(cx + 6, cy - 8);
    ctx.lineTo(cx + 12, cy - 14);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(cx + 6, cy - 8);
    ctx.lineTo(cx + 14, cy - 6);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(cx + 9, cy - 11);
    ctx.lineTo(cx + 4, cy - 16);
    ctx.stroke();
    // Head
    ctx.fillStyle = '#8b6914'; ctx.beginPath(); ctx.arc(cx, cy + 8, 5, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#111'; ctx.beginPath(); ctx.arc(cx - 2, cy + 7, 1, 0, Math.PI * 2); ctx.fill();
    ctx.beginPath(); ctx.arc(cx + 2, cy + 7, 1, 0, Math.PI * 2); ctx.fill();
  } else if (fighterId === 'noli') {
    // 3 four-pointed stars, white filled, thin purple outline
    ctx.fillStyle = '#1a1a2e'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    function draw4Star(x, y, starR) {
      ctx.beginPath();
      for (let i = 0; i < 8; i++) {
        const a = (i * Math.PI) / 4 - Math.PI / 2;
        const sr = i % 2 === 0 ? starR : starR * 0.3;
        if (i === 0) ctx.moveTo(x + Math.cos(a) * sr, y + Math.sin(a) * sr);
        else ctx.lineTo(x + Math.cos(a) * sr, y + Math.sin(a) * sr);
      }
      ctx.closePath();
      ctx.fillStyle = '#ffffff';
      ctx.fill();
      ctx.strokeStyle = '#a020f0';
      ctx.lineWidth = 1;
      ctx.shadowColor = '#a020f0';
      ctx.shadowBlur = 4;
      ctx.stroke();
      ctx.shadowBlur = 0;
    }
    draw4Star(cx - 7, cy - 5, 7);
    draw4Star(cx + 8, cy - 2, 5);
    draw4Star(cx + 1, cy + 8, 4);
  } else if (fighterId === 'explodingcat') {
    // Cat face icon — ears, eyes, whiskers
    ctx.fillStyle = '#1a1a2e'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    // Cat head
    ctx.fillStyle = '#222';
    ctx.beginPath(); ctx.arc(cx, cy + 4, r * 0.55, 0, Math.PI * 2); ctx.fill();
    // Left ear
    ctx.beginPath();
    ctx.moveTo(cx - r * 0.45, cy + 2);
    ctx.lineTo(cx - r * 0.25, cy - r * 0.6);
    ctx.lineTo(cx - r * 0.05, cy);
    ctx.closePath(); ctx.fill();
    // Right ear
    ctx.beginPath();
    ctx.moveTo(cx + r * 0.45, cy + 2);
    ctx.lineTo(cx + r * 0.25, cy - r * 0.6);
    ctx.lineTo(cx + r * 0.05, cy);
    ctx.closePath(); ctx.fill();
    // Inner ears (orange)
    ctx.fillStyle = '#ff6600';
    ctx.beginPath();
    ctx.moveTo(cx - r * 0.35, cy + 1);
    ctx.lineTo(cx - r * 0.25, cy - r * 0.4);
    ctx.lineTo(cx - r * 0.1, cy);
    ctx.closePath(); ctx.fill();
    ctx.beginPath();
    ctx.moveTo(cx + r * 0.35, cy + 1);
    ctx.lineTo(cx + r * 0.25, cy - r * 0.4);
    ctx.lineTo(cx + r * 0.1, cy);
    ctx.closePath(); ctx.fill();
    // Eyes (angry slits)
    ctx.fillStyle = '#ff4400';
    ctx.beginPath(); ctx.ellipse(cx - 5, cy + 2, 3, 1.5, -0.2, 0, Math.PI * 2); ctx.fill();
    ctx.beginPath(); ctx.ellipse(cx + 5, cy + 2, 3, 1.5, 0.2, 0, Math.PI * 2); ctx.fill();
    // Nose
    ctx.fillStyle = '#ff69b4';
    ctx.beginPath(); ctx.arc(cx, cy + 6, 1.5, 0, Math.PI * 2); ctx.fill();
    // Whiskers
    ctx.strokeStyle = '#666'; ctx.lineWidth = 0.8;
    ctx.beginPath();
    ctx.moveTo(cx - 5, cy + 6); ctx.lineTo(cx - r * 0.7, cy + 4);
    ctx.moveTo(cx - 5, cy + 7); ctx.lineTo(cx - r * 0.7, cy + 8);
    ctx.moveTo(cx + 5, cy + 6); ctx.lineTo(cx + r * 0.7, cy + 4);
    ctx.moveTo(cx + 5, cy + 7); ctx.lineTo(cx + r * 0.7, cy + 8);
    ctx.stroke();
  } else if (fighterId === 'napoleon') {
    // Napoleon bicorne hat icon — detailed French general hat
    ctx.fillStyle = '#1a1a2e'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    // Hat body (bicorne) — dark navy/black felt
    ctx.fillStyle = '#1a1a2e';
    ctx.beginPath();
    // Left upswept brim
    ctx.moveTo(cx - r * 0.95, cy + r * 0.1);
    ctx.quadraticCurveTo(cx - r * 0.7, cy - r * 0.7, cx - r * 0.15, cy - r * 0.45);
    // Top crest
    ctx.quadraticCurveTo(cx, cy - r * 0.55, cx + r * 0.15, cy - r * 0.45);
    // Right upswept brim
    ctx.quadraticCurveTo(cx + r * 0.7, cy - r * 0.7, cx + r * 0.95, cy + r * 0.1);
    // Bottom band
    ctx.quadraticCurveTo(cx + r * 0.5, cy + r * 0.35, cx, cy + r * 0.25);
    ctx.quadraticCurveTo(cx - r * 0.5, cy + r * 0.35, cx - r * 0.95, cy + r * 0.1);
    ctx.closePath();
    ctx.fillStyle = '#111';
    ctx.fill();
    ctx.strokeStyle = '#333';
    ctx.lineWidth = 1;
    ctx.stroke();
    // Gold trim band along bottom
    ctx.strokeStyle = '#d4af37';
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(cx - r * 0.85, cy + r * 0.12);
    ctx.quadraticCurveTo(cx - r * 0.4, cy + r * 0.32, cx, cy + r * 0.22);
    ctx.quadraticCurveTo(cx + r * 0.4, cy + r * 0.32, cx + r * 0.85, cy + r * 0.12);
    ctx.stroke();
    // Cockade (rosette) — red/white/blue concentric circles
    const cockX = cx, cockY = cy + r * 0.05;
    ctx.fillStyle = '#003399'; ctx.beginPath(); ctx.arc(cockX, cockY, r * 0.2, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#ffffff'; ctx.beginPath(); ctx.arc(cockX, cockY, r * 0.14, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#cc0000'; ctx.beginPath(); ctx.arc(cockX, cockY, r * 0.08, 0, Math.PI * 2); ctx.fill();
    // Gold button at center of cockade
    ctx.fillStyle = '#d4af37'; ctx.beginPath(); ctx.arc(cockX, cockY, r * 0.04, 0, Math.PI * 2); ctx.fill();
    // Plume feather — white plume curving from left tip upward
    ctx.strokeStyle = '#fff';
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(cx - r * 0.6, cy - r * 0.5);
    ctx.quadraticCurveTo(cx - r * 0.9, cy - r * 1.1, cx - r * 0.4, cy - r * 0.9);
    ctx.stroke();
    ctx.strokeStyle = 'rgba(255,255,255,0.5)';
    ctx.lineWidth = 1.2;
    ctx.beginPath();
    ctx.moveTo(cx - r * 0.55, cy - r * 0.55);
    ctx.quadraticCurveTo(cx - r * 0.85, cy - r * 0.95, cx - r * 0.35, cy - r * 0.85);
    ctx.stroke();
  } else if (fighterId === 'moderator') {
    // Moderator: terminal/console icon
    ctx.fillStyle = '#1a1a2e'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    // Terminal window frame
    const tw = r * 1.5, th = r * 1.2;
    const tx = cx - tw / 2, ty = cy - th / 2;
    // Window background
    ctx.fillStyle = '#0c0c0c';
    ctx.beginPath();
    const cr = 3;
    ctx.moveTo(tx + cr, ty); ctx.lineTo(tx + tw - cr, ty);
    ctx.quadraticCurveTo(tx + tw, ty, tx + tw, ty + cr);
    ctx.lineTo(tx + tw, ty + th - cr);
    ctx.quadraticCurveTo(tx + tw, ty + th, tx + tw - cr, ty + th);
    ctx.lineTo(tx + cr, ty + th);
    ctx.quadraticCurveTo(tx, ty + th, tx, ty + th - cr);
    ctx.lineTo(tx, ty + cr);
    ctx.quadraticCurveTo(tx, ty, tx + cr, ty);
    ctx.closePath();
    ctx.fill();
    // Title bar
    ctx.fillStyle = '#2d2d2d';
    ctx.fillRect(tx, ty, tw, th * 0.18);
    // Title bar dots (red/yellow/green)
    const dotY = ty + th * 0.09;
    ctx.fillStyle = '#ff5f56'; ctx.beginPath(); ctx.arc(tx + 5, dotY, 2, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#ffbd2e'; ctx.beginPath(); ctx.arc(tx + 11, dotY, 2, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#27c93f'; ctx.beginPath(); ctx.arc(tx + 17, dotY, 2, 0, Math.PI * 2); ctx.fill();
    // Terminal text: "> mod_" with cursor blink
    ctx.fillStyle = '#00ff41';
    ctx.font = 'bold ' + Math.max(7, r * 0.35) + 'px monospace';
    ctx.textAlign = 'left';
    ctx.textBaseline = 'middle';
    ctx.fillText('> mod_', tx + 4, cy + th * 0.12);
    // Border glow
    ctx.strokeStyle = '#00ff41'; ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(tx + cr, ty); ctx.lineTo(tx + tw - cr, ty);
    ctx.quadraticCurveTo(tx + tw, ty, tx + tw, ty + cr);
    ctx.lineTo(tx + tw, ty + th - cr);
    ctx.quadraticCurveTo(tx + tw, ty + th, tx + tw - cr, ty + th);
    ctx.lineTo(tx + cr, ty + th);
    ctx.quadraticCurveTo(tx, ty + th, tx, ty + th - cr);
    ctx.lineTo(tx, ty + cr);
    ctx.quadraticCurveTo(tx, ty, tx + cr, ty);
    ctx.closePath();
    ctx.stroke();
  } else if (fighterId === 'dragon') {
    // Dragon of Icespire: icy dragon head silhouette
    ctx.fillStyle = '#0a1628'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    // Dragon head shape
    ctx.fillStyle = '#5b8fa8';
    ctx.beginPath();
    ctx.moveTo(cx - r * 0.5, cy + r * 0.4);
    ctx.lineTo(cx - r * 0.6, cy - r * 0.2);
    ctx.lineTo(cx - r * 0.3, cy - r * 0.6);
    ctx.lineTo(cx + r * 0.1, cy - r * 0.7);
    ctx.lineTo(cx + r * 0.5, cy - r * 0.4);
    ctx.lineTo(cx + r * 0.7, cy - r * 0.1);
    ctx.lineTo(cx + r * 0.5, cy + r * 0.2);
    ctx.lineTo(cx + r * 0.3, cy + r * 0.5);
    ctx.lineTo(cx, cy + r * 0.4);
    ctx.closePath();
    ctx.fill();
    // Icy eye
    ctx.fillStyle = '#00ddff';
    ctx.beginPath();
    ctx.arc(cx + r * 0.1, cy - r * 0.2, r * 0.15, 0, Math.PI * 2);
    ctx.fill();
    ctx.fillStyle = '#003';
    ctx.beginPath();
    ctx.arc(cx + r * 0.1, cy - r * 0.2, r * 0.07, 0, Math.PI * 2);
    ctx.fill();
    // Icy breath wisps from snout
    ctx.strokeStyle = 'rgba(200, 240, 255, 0.7)';
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    ctx.moveTo(cx + r * 0.7, cy - r * 0.1);
    ctx.quadraticCurveTo(cx + r * 1.0, cy + r * 0.1, cx + r * 0.8, cy + r * 0.3);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(cx + r * 0.7, cy - r * 0.1);
    ctx.quadraticCurveTo(cx + r * 1.1, cy - r * 0.3, cx + r * 0.9, cy - r * 0.5);
    ctx.stroke();
    // Horns
    ctx.strokeStyle = '#7fafc4';
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(cx - r * 0.3, cy - r * 0.6);
    ctx.lineTo(cx - r * 0.5, cy - r * 0.9);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(cx + r * 0.1, cy - r * 0.7);
    ctx.lineTo(cx + r * 0.0, cy - r * 1.0);
    ctx.stroke();
  } else if (fighterId === 'dnd') {
    // D&D Campaigner: Sword and Shield icon
    ctx.fillStyle = '#1a1a2e'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    // Shield (kite shield, left-center)
    const shX = cx - r * 0.2, shY = cy + r * 0.05;
    const shW = r * 0.8, shH = r * 1.1;
    ctx.fillStyle = '#2c3e80';
    ctx.beginPath();
    ctx.moveTo(shX - shW * 0.5, shY - shH * 0.45);
    ctx.lineTo(shX + shW * 0.5, shY - shH * 0.45);
    ctx.lineTo(shX + shW * 0.5, shY + shH * 0.1);
    ctx.lineTo(shX, shY + shH * 0.5);
    ctx.lineTo(shX - shW * 0.5, shY + shH * 0.1);
    ctx.closePath();
    ctx.fill();
    ctx.strokeStyle = '#1a2555'; ctx.lineWidth = 1.5; ctx.stroke();
    // Shield cross emblem
    ctx.strokeStyle = '#d4af37'; ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(shX, shY - shH * 0.3); ctx.lineTo(shX, shY + shH * 0.3);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(shX - shW * 0.3, shY - shH * 0.05); ctx.lineTo(shX + shW * 0.3, shY - shH * 0.05);
    ctx.stroke();
    // Sword (angled behind shield, upper-right)
    const swAngle = -Math.PI / 4;
    const swLen = r * 1.6;
    const swOx = cx + r * 0.1, swOy = cy + r * 0.2;
    const swTx = swOx + Math.cos(swAngle) * swLen;
    const swTy = swOy + Math.sin(swAngle) * swLen;
    // Blade
    ctx.strokeStyle = '#c0c0c0'; ctx.lineWidth = 3;
    ctx.beginPath(); ctx.moveTo(swOx, swOy); ctx.lineTo(swTx, swTy); ctx.stroke();
    // Blade highlight
    ctx.strokeStyle = '#eee'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(swOx + 1, swOy + 1); ctx.lineTo(swTx + 1, swTy + 1); ctx.stroke();
    // Tip
    ctx.fillStyle = '#e0e0e0';
    ctx.beginPath();
    ctx.moveTo(swTx, swTy);
    ctx.lineTo(swTx + Math.cos(swAngle) * r * 0.15 + Math.cos(swAngle + 0.4) * 3, swTy + Math.sin(swAngle) * r * 0.15 + Math.sin(swAngle + 0.4) * 3);
    ctx.lineTo(swTx + Math.cos(swAngle - 0.3) * 2, swTy + Math.sin(swAngle - 0.3) * 2);
    ctx.closePath(); ctx.fill();
    // Crossguard
    const gx = swOx + Math.cos(swAngle) * swLen * 0.3;
    const gy = swOy + Math.sin(swAngle) * swLen * 0.3;
    const gAngle = swAngle + Math.PI / 2;
    ctx.strokeStyle = '#d4af37'; ctx.lineWidth = 2.5;
    ctx.beginPath();
    ctx.moveTo(gx + Math.cos(gAngle) * 6, gy + Math.sin(gAngle) * 6);
    ctx.lineTo(gx - Math.cos(gAngle) * 6, gy - Math.sin(gAngle) * 6);
    ctx.stroke();
  } else {
    // Fighter: sword icon
    ctx.fillStyle = '#1a1a2e'; ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.fill();
    const sAngle = -Math.PI / 4, sLen = r * 1.4;
    const sx = cx - Math.cos(sAngle) * sLen * 0.15, sy = cy - Math.sin(sAngle) * sLen * 0.15;
    ctx.strokeStyle = '#ccc'; ctx.lineWidth = 3; ctx.beginPath();
    ctx.moveTo(sx, sy);
    ctx.lineTo(sx + Math.cos(sAngle) * sLen, sy + Math.sin(sAngle) * sLen);
    ctx.stroke();
    const hx = sx + Math.cos(sAngle) * sLen * 0.35, hy = sy + Math.sin(sAngle) * sLen * 0.35;
    const pAngle = sAngle + Math.PI / 2;
    ctx.strokeStyle = '#a0522d'; ctx.lineWidth = 2; ctx.beginPath();
    ctx.moveTo(hx + Math.cos(pAngle) * 5, hy + Math.sin(pAngle) * 5);
    ctx.lineTo(hx - Math.cos(pAngle) * 5, hy - Math.sin(pAngle) * 5);
    ctx.stroke();
  }
}

let fighterCardShown = null; // track which fighter's stats are showing

function populateFighterScreen() {
  const bar = document.querySelector('#fighter-select-bar');
  const card = document.querySelector('#fighter-card');
  bar.innerHTML = '';

  _shuffledFighterIds.forEach((fid) => {
    const f = getFighter(fid);
    const locked = !isFighterUnlocked(fid);
    const mpOnly = f.multiplayerOnly && (flowTarget === 'fight' || flowTarget === 'fight-hard' || flowTarget === 'training');
    const btn = document.createElement('button');
    btn.className = 'fighter-select-btn' + (fid === selectedFighterId ? ' active' : '') + ((locked || mpOnly) ? ' locked' : '');

    // Draw icon
    const canvas = document.createElement('canvas');
    drawFighterIcon(canvas, fid);
    btn.appendChild(canvas);

    // Name label
    const label = document.createElement('span');
    label.textContent = locked ? '???' : mpOnly ? f.name + ' (MP)' : f.name;
    btn.appendChild(label);

    btn.addEventListener('click', () => {
      if (locked || mpOnly) return;
      selectedFighterId = fid;
      if (fighterCardShown === fid) {
        // Clicking same fighter again hides stats
        card.classList.add('hidden');
        fighterCardShown = null;
      } else {
        showFighterStats(fid);
        fighterCardShown = fid;
      }
      // Update active state on all buttons
      bar.querySelectorAll('.fighter-select-btn').forEach((b, idx) => {
        const ids = _shuffledFighterIds;
        b.className = 'fighter-select-btn' + (ids[idx] === selectedFighterId ? ' active' : '') + (!isFighterUnlocked(ids[idx]) ? ' locked' : '');
      });
    });
    bar.appendChild(btn);
  });

  // Show stats for currently selected fighter
  if (fighterCardShown === selectedFighterId) {
    showFighterStats(selectedFighterId);
  }
}

function showFighterStats(fid) {
  const f = getFighter(fid);
  if (!f) return;

  const el = (sel) => document.querySelector(sel);
  const card = el('#fighter-card');
  card.classList.remove('hidden');

  el('#fc-name').textContent = f.name;
  el('#fc-hp').textContent = 'HP: ' + f.hp;
  el('#fc-desc').textContent = f.description;
  el('#fc-speed').textContent = f.speed;
  el('#fc-heal').textContent = f.healAmount + ' every ' + f.healTick + 's (after ' + f.healDelay + 's)';
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
  // Singleplayer only — pick fighter and start game
  if (!selectedFighterId) {
    return; // no fighter picked
  }
  if (typeof socket !== 'undefined' && socket.emit) {
    socket.emit('change-fighter', { fighterId: selectedFighterId });
  }
  if (flowTarget === 'training') {
    const randomMap = Math.floor(Math.random() * MAPS.length);
    const color = PLAYER_COLORS[Math.floor(Math.random() * PLAYER_COLORS.length)];
    enterGame(randomMap, [{ id: 'local', name: playerName, color, isHost: true, fighterId: selectedFighterId }], 'training');
  } else if (flowTarget === 'fight' || flowTarget === 'fight-hard') {
    const randomMap = Math.floor(Math.random() * MAPS.length);
    const color = PLAYER_COLORS[Math.floor(Math.random() * PLAYER_COLORS.length)];
    enterGame(randomMap, [{ id: 'local', name: playerName, color, isHost: true, fighterId: selectedFighterId }], flowTarget === 'fight-hard' ? 'fight-hard' : 'fight');
  }
});

// ── Lobby fighter selection ───────────────────────────────────
let lobbyFighterCardShown = null;

function populateLobbyFighters() {
  const bar = document.querySelector('#lobby-fighter-bar');
  const card = document.querySelector('#lobby-fighter-card');
  if (!bar) return;
  bar.innerHTML = '';

  _shuffledFighterIds.forEach((fid) => {
    const f = getFighter(fid);
    const locked = !isFighterUnlocked(fid);
    const btn = document.createElement('button');
    btn.className = 'lobby-fighter-btn' + (fid === selectedFighterId ? ' active' : '') + (locked ? ' locked' : '');

    const canvas = document.createElement('canvas');
    canvas.width = 40; canvas.height = 40;
    drawFighterIcon(canvas, fid, 40);
    btn.appendChild(canvas);

    const label = document.createElement('span');
    label.textContent = locked ? '???' : f.name;
    btn.appendChild(label);

    btn.addEventListener('click', () => {
      if (locked) return;
      selectedFighterId = fid;
      showLobbyFighterStats(fid);
      lobbyFighterCardShown = fid;
      bar.querySelectorAll('.lobby-fighter-btn').forEach((b, idx) => {
        const ids = _shuffledFighterIds;
        b.className = 'lobby-fighter-btn' + (ids[idx] === selectedFighterId ? ' active' : '') + (!isFighterUnlocked(ids[idx]) ? ' locked' : '');
      });
      // Tell server about fighter change
      if (typeof socket !== 'undefined' && socket.emit) {
        socket.emit('change-fighter', { fighterId: selectedFighterId });
      }
    });
    bar.appendChild(btn);
  });
}

function showLobbyFighterStats(fid) {
  const f = getFighter(fid);
  if (!f) return;

  const el = (sel) => document.querySelector(sel);
  const card = el('#lobby-fighter-card');
  card.classList.remove('hidden');

  el('#lfc-name').textContent = f.name;
  el('#lfc-hp').textContent = 'HP: ' + f.hp;
  el('#lfc-desc').textContent = f.description;
  el('#lfc-speed').textContent = f.speed;
  el('#lfc-heal').textContent = f.healAmount + ' every ' + f.healTick + 's (after ' + f.healDelay + 's)';

  const list = el('#lfc-abilities');
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

// ── Util ─────────────────────────────────────────────────────
function escapeHtml(str) {
  const div = document.createElement('div');
  div.appendChild(document.createTextNode(str));
  return div.innerHTML;
}

// ═══════════════════════════════════════════════════════════════
// ACHIEVEMENT / UNLOCK SYSTEM
// ═══════════════════════════════════════════════════════════════
/*
  Achievement state = completed set + progress counters.
  Encoded into an alphanumeric code the player can save/restore.
*/

// ── Encode / Decode achievement codes ────────────────────────
const _ACH_KEY = 'rbg_achievements'; // localStorage key

const _OLD_PROGRESS_KEYS = ['mpWins', 'spWins', 'winsAs1x', 'boiledOnePlays', 'summonKillMP', 'deerRestrictedWin'];
const _PROGRESS_KEYS = [
  'mpWins', 'spWins', 'winsAs1x', 'boiledOnePlays', 'summonKillMP', 'deerRestrictedWin',
  // Round 2 per-fighter progress
  'fighterSpecialAch', 'pokerNoSpecialAch', 'filbusBoiledKillAch',
  'onexKilledNoliMP', 'onexKilledCatSP', 'gearDmgAbsorbed',
  'deerWaterKill', 'noliVoidRushAch', 'catKittenAch',
  // Napoleon unlock
  'napoleonM1Kills', 'napoleonSummonWins',
  // Moderator
  'modWins',
  // D&D unlock
  'dndWinsPoker', 'dndWinsFighter', 'dndWinsCricket',
  // D&D F-move
  'dndElfWins', 'dndDwarfWins', 'dndHumanWins',
  // Dragon unlock
  'dragonWinsNapoleon', 'dragonWinsDnD',
  // Dragon F-move
  'dragonBeamAch',
];

function _defaultProgress() {
  const p = {};
  _PROGRESS_KEYS.forEach(k => { p[k] = 0; });
  return p;
}

function _achStateToBits(completed) {
  const ids = Object.keys(ACHIEVEMENTS);
  let bits = 0;
  ids.forEach((id, i) => { if (completed.has(id)) bits |= (1 << i); });
  return bits;
}

function _achBitsToState(bits) {
  const ids = Object.keys(ACHIEVEMENTS);
  const set = new Set();
  ids.forEach((id, i) => { if (bits & (1 << i)) set.add(id); });
  return set;
}

// Pack state into bytes: [achBitsLow, achBitsMid, achBitsHigh, ...progressKeys]
function _packState(completed, progress) {
  const bytes = [];
  const bits = _achStateToBits(completed);
  bytes.push(bits & 0xFF);
  bytes.push((bits >> 8) & 0xFF);
  bytes.push((bits >> 16) & 0xFF);
  _PROGRESS_KEYS.forEach(k => bytes.push(Math.min(255, Math.max(0, progress[k] || 0))));
  return bytes;
}

function _unpackState(bytes) {
  // Newest format: 3 ach bytes + full progress keys
  const newestLen = 3 + _PROGRESS_KEYS.length;
  if (bytes.length >= newestLen) {
    const bits = bytes[0] | (bytes[1] << 8) | (bytes[2] << 16);
    const completed = _achBitsToState(bits);
    const progress = _defaultProgress();
    _PROGRESS_KEYS.forEach((k, i) => { progress[k] = bytes[3 + i]; });
    return { completed, progress };
  }
  // Previous format: 2 ach bytes + 17 old progress keys
  const prevKeys = [
    'mpWins', 'spWins', 'winsAs1x', 'boiledOnePlays', 'summonKillMP', 'deerRestrictedWin',
    'fighterSpecialAch', 'pokerNoSpecialAch', 'filbusBoiledKillAch',
    'onexKilledNoliMP', 'onexKilledCatSP', 'gearDmgAbsorbed',
    'deerWaterKill', 'noliVoidRushAch', 'catKittenAch',
    'napoleonM1Kills', 'napoleonSummonWins',
  ];
  const prevLen = 2 + prevKeys.length;
  if (bytes.length >= prevLen) {
    const bits = bytes[0] | (bytes[1] << 8);
    const completed = _achBitsToState(bits);
    const progress = _defaultProgress();
    prevKeys.forEach((k, i) => { progress[k] = bytes[2 + i]; });
    return { completed, progress };
  }
  // Old format: 1 ach byte + 6 old progress keys
  const oldLen = 1 + _OLD_PROGRESS_KEYS.length;
  if (bytes.length >= oldLen) {
    const completed = _achBitsToState(bytes[0]);
    const progress = _defaultProgress();
    _OLD_PROGRESS_KEYS.forEach((k, i) => { progress[k] = bytes[1 + i]; });
    return { completed, progress };
  }
  return null;
}

// Code format: SALT-PAYLOAD  (SALT=4 chars derived from data, PAYLOAD=hex bytes XOR'd with salt)
function generateAchCode(completed, progress) {
  const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  const bytes = _packState(completed, progress);
  // Derive salt deterministically from data so same state = same code
  let hash = 0;
  for (let i = 0; i < bytes.length; i++) hash = ((hash * 31 + bytes[i] + 7) * 17) & 0xFFFFFFFF;
  let saltStr = '';
  let salt = 0;
  for (let i = 0; i < 4; i++) {
    const c = chars[((hash >>> (i * 8)) & 0xFF) % chars.length];
    saltStr += c;
    salt = (salt * 33 + c.charCodeAt(0)) & 0xFFFF;
  }
  const xorKey = salt & 0xFF;
  const hex = bytes.map(b => ((b ^ xorKey) & 0xFF).toString(16).padStart(2, '0')).join('');
  return saltStr + '-' + hex.toUpperCase();
}

function decodeAchCode(code) {
  if (!code || typeof code !== 'string') return null;
  code = code.trim().toUpperCase();
  if (code === 'NAPOLEON') {
    return { completed: new Set(Object.keys(ACHIEVEMENTS)), progress: _defaultProgress(), unlockAll: true };
  }
  const parts = code.split('-');
  if (parts.length !== 2 || parts[0].length !== 4) return null;
  const saltStr = parts[0];
  let salt = 0;
  for (let i = 0; i < 4; i++) {
    salt = (salt * 33 + saltStr.charCodeAt(i)) & 0xFFFF;
  }
  const hex = parts[1];
  if (hex.length % 2 !== 0) return null;
  const xorKey = salt & 0xFF;
  const bytes = [];
  for (let i = 0; i < hex.length; i += 2) {
    const b = parseInt(hex.substring(i, i + 2), 16);
    if (isNaN(b)) return null;
    bytes.push((b ^ xorKey) & 0xFF);
  }
  const state = _unpackState(bytes);
  if (!state) return null;
  return { completed: state.completed, progress: state.progress, unlockAll: false };
}

// ── Persistent state ─────────────────────────────────────────
let completedAchievements = new Set();
let achProgress = _defaultProgress();
let allFightersUnlocked = false;

function loadAchievements() {
  try {
    const saved = localStorage.getItem(_ACH_KEY);
    if (saved) {
      const decoded = decodeAchCode(saved);
      if (decoded) {
        if (decoded.unlockAll) allFightersUnlocked = true;
        completedAchievements = decoded.completed;
        achProgress = decoded.progress;
      }
    }
  } catch (e) { /* ignore */ }
}

function saveAchievements() {
  try {
    if (allFightersUnlocked) {
      localStorage.setItem(_ACH_KEY, 'NAPOLEON');
    } else {
      const code = generateAchCode(completedAchievements, achProgress);
      localStorage.setItem(_ACH_KEY, code);
    }
  } catch (e) { /* ignore */ }
}

// ── Achievement checking with reset logic ────────────────────
function _resetCategoriesFor(achId) {
  const cats = ACH_RESET_CATEGORIES[achId] || [];
  cats.forEach(cat => {
    const stats = PROGRESS_BY_CATEGORY[cat] || [];
    stats.forEach(s => { achProgress[s] = 0; });
  });
}

function _showMove4Toast(ach) {
  const fighter = getFighter(ach.forFighter);
  const fName = fighter ? fighter.name : ach.forFighter;
  const el = document.createElement('div');
  el.style.cssText = 'position:fixed;top:80px;left:50%;transform:translateX(-50%);z-index:9999;' +
    'background:linear-gradient(135deg,#1a1a2e,#16213e);color:#f5a623;padding:14px 28px;' +
    'border-radius:10px;font-family:monospace;font-size:16px;font-weight:bold;text-align:center;' +
    'border:2px solid #f5a623;box-shadow:0 0 20px rgba(245,166,35,0.4);' +
    'opacity:0;transition:opacity 0.4s;pointer-events:none;';
  el.innerHTML = '🔓 Move 4 Unlocked!<br><span style="font-size:13px;color:#ccc;">' +
    escapeHtml(fName) + ' — ' + escapeHtml(ach.name) + '</span>';
  document.body.appendChild(el);
  requestAnimationFrame(() => { el.style.opacity = '1'; });
  setTimeout(() => {
    el.style.opacity = '0';
    setTimeout(() => el.remove(), 500);
  }, 4000);
}

function checkAndUnlockAchievements() {
  let changed = false;
  const newlyCompleted = [];

  // firstWin: any SP win (tracked separately)
  if (!completedAchievements.has('firstWin') && achProgress.spWins >= 1) {
    completedAchievements.add('firstWin');
    _resetCategoriesFor('firstWin');
    changed = true;
  }
  // firstMPWin: any MP win
  if (!completedAchievements.has('firstMPWin') && achProgress.mpWins >= 1) {
    completedAchievements.add('firstMPWin');
    _resetCategoriesFor('firstMPWin');
    changed = true;
  }
  // cricketAch: 5 MP wins AND 3 SP wins
  if (!completedAchievements.has('cricketAch') && achProgress.mpWins >= 5 && achProgress.spWins >= 3) {
    completedAchievements.add('cricketAch');
    _resetCategoriesFor('cricketAch');
    changed = true;
  }
  // deerAch: kill with summon in MP
  if (!completedAchievements.has('deerAch') && achProgress.summonKillMP >= 1) {
    completedAchievements.add('deerAch');
    _resetCategoriesFor('deerAch');
    changed = true;
  }
  // noliAch: 5 wins as 1X AND 3 boiled one plays (requires 1X + Filbus unlocked)
  if (!completedAchievements.has('noliAch') && isAchievementAvailable('noliAch') && achProgress.winsAs1x >= 5 && achProgress.boiledOnePlays >= 3) {
    completedAchievements.add('noliAch');
    _resetCategoriesFor('noliAch');
    changed = true;
  }
  // catAch: deer restricted win (requires Deer unlocked)
  if (!completedAchievements.has('catAch') && isAchievementAvailable('catAch') && achProgress.deerRestrictedWin >= 1) {
    completedAchievements.add('catAch');
    _resetCategoriesFor('catAch');
    changed = true;
  }
  // napoleonAchUnlock: 2 summon wins + 5 M1 kills
  if (!completedAchievements.has('napoleonAchUnlock') && achProgress.napoleonSummonWins >= 2 && achProgress.napoleonM1Kills >= 5) {
    completedAchievements.add('napoleonAchUnlock');
    changed = true;
  }

  // ── Round 2 per-fighter achievements ──
  if (!completedAchievements.has('fighterAch') && achProgress.fighterSpecialAch >= 1) {
    completedAchievements.add('fighterAch');
    newlyCompleted.push('fighterAch');
    changed = true;
  }
  if (!completedAchievements.has('pokerAch') && achProgress.pokerNoSpecialAch >= 1) {
    completedAchievements.add('pokerAch');
    newlyCompleted.push('pokerAch');
    changed = true;
  }
  if (!completedAchievements.has('filbusAch') && isAchievementAvailable('filbusAch') && achProgress.filbusBoiledKillAch >= 1) {
    completedAchievements.add('filbusAch');
    newlyCompleted.push('filbusAch');
    changed = true;
  }
  if (!completedAchievements.has('onexAch') && isAchievementAvailable('onexAch') && achProgress.onexKilledNoliMP >= 1 && achProgress.onexKilledCatSP >= 1) {
    completedAchievements.add('onexAch');
    newlyCompleted.push('onexAch');
    changed = true;
  }
  if (!completedAchievements.has('cricketAch2') && isAchievementAvailable('cricketAch2') && achProgress.gearDmgAbsorbed >= 100) {
    completedAchievements.add('cricketAch2');
    newlyCompleted.push('cricketAch2');
    changed = true;
  }
  if (!completedAchievements.has('deerAch2') && isAchievementAvailable('deerAch2') && achProgress.deerWaterKill >= 1) {
    completedAchievements.add('deerAch2');
    newlyCompleted.push('deerAch2');
    changed = true;
  }
  if (!completedAchievements.has('noliAch2') && isAchievementAvailable('noliAch2') && achProgress.noliVoidRushAch >= 1) {
    completedAchievements.add('noliAch2');
    newlyCompleted.push('noliAch2');
    changed = true;
  }
  if (!completedAchievements.has('catAch2') && isAchievementAvailable('catAch2') && achProgress.catKittenAch >= 1) {
    completedAchievements.add('catAch2');
    newlyCompleted.push('catAch2');
    changed = true;
  }
  if (!completedAchievements.has('moderatorAch') && isAchievementAvailable('moderatorAch') && achProgress.modWins >= 1) {
    completedAchievements.add('moderatorAch');
    newlyCompleted.push('moderatorAch');
    changed = true;
  }
  // dndAchUnlock: 5 wins as Poker + 5 wins as Fighter + 5 wins as Cricket
  if (!completedAchievements.has('dndAchUnlock') && isAchievementAvailable('dndAchUnlock') && achProgress.dndWinsPoker >= 5 && achProgress.dndWinsFighter >= 5 && achProgress.dndWinsCricket >= 5) {
    completedAchievements.add('dndAchUnlock');
    changed = true;
  }
  // dndAch: D&D F-move — win as Elf 2, Dwarf 3, Human 4
  if (!completedAchievements.has('dndAch') && isAchievementAvailable('dndAch') && achProgress.dndElfWins >= 2 && achProgress.dndDwarfWins >= 3 && achProgress.dndHumanWins >= 4) {
    completedAchievements.add('dndAch');
    newlyCompleted.push('dndAch');
    changed = true;
  }
  // dragonAchUnlock: 3 wins as Napoleon + 3 wins as D&D Campaigner
  if (!completedAchievements.has('dragonAchUnlock') && isAchievementAvailable('dragonAchUnlock') && achProgress.dragonWinsNapoleon >= 3 && achProgress.dragonWinsDnD >= 3) {
    completedAchievements.add('dragonAchUnlock');
    changed = true;
  }
  // dragonAch: Dragon F-move — kill 2 opponents with Dragon Beam in a single game
  if (!completedAchievements.has('dragonAch') && isAchievementAvailable('dragonAch') && achProgress.dragonBeamAch >= 1) {
    completedAchievements.add('dragonAch');
    newlyCompleted.push('dragonAch');
    changed = true;
  }

  if (changed) {
    saveAchievements();
    // Show Move 4 unlock toast for newly completed Move 4 achievements
    for (const achId of newlyCompleted) {
      const ach = ACHIEVEMENTS[achId];
      if (ach && ach.unlocksMove4 && ach.forFighter) {
        _showMove4Toast(ach);
      }
    }
  }
  return changed;
}

// ── Public tracking API (called from game.js) ────────────────
function trackSPWin(fighterId) {
  achProgress.spWins++;
  if (fighterId === 'onexonexonex' && isAchievementAvailable('noliAch')) achProgress.winsAs1x++;
  if (fighterId === 'poker' || fighterId === 'fighter' || fighterId === 'cricket') trackDndFighterWin(fighterId);
  if (fighterId === 'napoleon' && isAchievementAvailable('dragonAchUnlock')) achProgress.dragonWinsNapoleon++;
  if (fighterId === 'dnd' && isAchievementAvailable('dragonAchUnlock')) achProgress.dragonWinsDnD++;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackMPWin(fighterId) {
  achProgress.mpWins++;
  if (fighterId === 'onexonexonex' && isAchievementAvailable('noliAch')) achProgress.winsAs1x++;
  if (fighterId === 'poker' || fighterId === 'fighter' || fighterId === 'cricket') trackDndFighterWin(fighterId);
  if (fighterId === 'napoleon' && isAchievementAvailable('dragonAchUnlock')) achProgress.dragonWinsNapoleon++;
  if (fighterId === 'dnd' && isAchievementAvailable('dragonAchUnlock')) achProgress.dragonWinsDnD++;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackSummonKillMP() {
  achProgress.summonKillMP = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackBoiledOnePlayed() {
  if (!isAchievementAvailable('noliAch')) return;
  achProgress.boiledOnePlays++;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackDeerRestrictedWin() {
  if (!isAchievementAvailable('catAch')) return;
  achProgress.deerRestrictedWin = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

// ── Round 2 tracking API (called from game.js) ───────────────
function trackFighterSpecialAch() {
  achProgress.fighterSpecialAch = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackPokerNoSpecialWin() {
  achProgress.pokerNoSpecialAch = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackFilbusOddityKill() {
  // Legacy function (no longer used for achievement)
}

function trackFilbusBoiledKill() {
  if (!isAchievementAvailable('filbusAch')) return;
  achProgress.filbusBoiledKillAch = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackOnexKilledNoliMP() {
  if (!isAchievementAvailable('onexAch')) return;
  achProgress.onexKilledNoliMP = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackOnexKilledCatSP() {
  if (!isAchievementAvailable('onexAch')) return;
  achProgress.onexKilledCatSP = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackGearDmgAbsorbed(amount) {
  if (!isAchievementAvailable('cricketAch2')) return;
  // Store in units of 10 (byte max 255 = 2550 damage)
  const toAdd = Math.floor(amount / 10);
  if (toAdd > 0) {
    achProgress.gearDmgAbsorbed = Math.min(255, achProgress.gearDmgAbsorbed + toAdd);
    checkAndUnlockAchievements();
    saveAchievements();
  }
}

function trackDeerWaterKill() {
  if (!isAchievementAvailable('deerAch2')) return;
  achProgress.deerWaterKill = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackNoliVoidRushAch() {
  if (!isAchievementAvailable('noliAch2')) return;
  achProgress.noliVoidRushAch = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackCatKittenAch() {
  if (!isAchievementAvailable('catAch2')) return;
  achProgress.catKittenAch = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

// Napoleon unlock tracking
function trackNapoleonM1Kill() {
  achProgress.napoleonM1Kills = (achProgress.napoleonM1Kills || 0) + 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackNapoleonSummonWin() {
  achProgress.napoleonSummonWins = (achProgress.napoleonSummonWins || 0) + 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

// Moderator achievement tracking
function trackModWin() {
  achProgress.modWins = (achProgress.modWins || 0) + 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

// D&D unlock tracking — per-fighter wins
function trackDndFighterWin(fighterId) {
  if (fighterId === 'poker') achProgress.dndWinsPoker = Math.min(255, (achProgress.dndWinsPoker || 0) + 1);
  else if (fighterId === 'fighter') achProgress.dndWinsFighter = Math.min(255, (achProgress.dndWinsFighter || 0) + 1);
  else if (fighterId === 'cricket') achProgress.dndWinsCricket = Math.min(255, (achProgress.dndWinsCricket || 0) + 1);
  checkAndUnlockAchievements();
  saveAchievements();
}

// D&D F-move tracking — per-race wins
function trackDndRaceWin(race) {
  if (!isAchievementAvailable('dndAch')) return;
  if (race === 'elf') achProgress.dndElfWins = Math.min(255, (achProgress.dndElfWins || 0) + 1);
  else if (race === 'dwarf') achProgress.dndDwarfWins = Math.min(255, (achProgress.dndDwarfWins || 0) + 1);
  else if (race === 'human') achProgress.dndHumanWins = Math.min(255, (achProgress.dndHumanWins || 0) + 1);
  checkAndUnlockAchievements();
  saveAchievements();
}

function trackDragonBeamAch() {
  if (!isAchievementAvailable('dragonAch')) return;
  achProgress.dragonBeamAch = 1;
  checkAndUnlockAchievements();
  saveAchievements();
}

function unlockAchievement(achId) {
  if (completedAchievements.has(achId)) return;
  completedAchievements.add(achId);
  _resetCategoriesFor(achId);
  saveAchievements();
}

function isFighterUnlocked(fid) {
  if (allFightersUnlocked) return true;
  if (isFighterFree(fid)) return true;
  for (const achId of completedAchievements) {
    const ach = ACHIEVEMENTS[achId];
    if (ach && ach.unlocks === fid) return true;
  }
  return false;
}

function isAchievementAvailable(achId) {
  const ach = ACHIEVEMENTS[achId];
  if (!ach || !ach.requiresFighters) return true;
  return ach.requiresFighters.every(fid => isFighterUnlocked(fid));
}

function isMove4Unlocked(fighterId) {
  if (allFightersUnlocked) return true;
  for (const achId of completedAchievements) {
    const ach = ACHIEVEMENTS[achId];
    if (ach && ach.unlocksMove4 && ach.forFighter === fighterId) return true;
  }
  return false;
}

// Load on startup
loadAchievements();

// If the currently selected fighter is locked, reset to 'fighter'
if (!isFighterUnlocked(selectedFighterId)) {
  selectedFighterId = 'fighter';
}

// ── Achievements screen ──────────────────────────────────────
$('#btn-achievements').addEventListener('click', () => {
  renderAchievementsScreen();
  showScreen('screen-achievements');
});
$('#btn-achv-back').addEventListener('click', () => showScreen('screen-start'));
$('#btn-achv-logout').addEventListener('click', () => {
  try { localStorage.removeItem(_ACH_KEY); } catch (e) { /* ignore */ }
  completedAchievements = new Set();
  achProgress = _defaultProgress();
  allFightersUnlocked = false;
  selectedFighterId = 'fighter';
  renderAchievementsScreen();
  const msg = $('#achv-msg');
  msg.textContent = 'Logged out. Save your code before leaving!';
  msg.className = 'achv-msg success';
});

$('#btn-achv-load').addEventListener('click', loadAchievementCode);
$('#achv-code-input').addEventListener('keydown', (e) => { if (e.key === 'Enter') loadAchievementCode(); });

function _getProgressText(achId) {
  const p = achProgress;
  switch (achId) {
    case 'firstWin': return p.spWins >= 1 ? '' : 'SP wins: ' + p.spWins + '/1';
    case 'firstMPWin': return p.mpWins >= 1 ? '' : 'MP wins: ' + p.mpWins + '/1';
    case 'cricketAch': return 'MP wins: ' + Math.min(p.mpWins, 5) + '/5 · SP wins: ' + Math.min(p.spWins, 3) + '/3';
    case 'deerAch': return p.summonKillMP ? '' : 'Summon kills: 0/1';
    case 'noliAch': return '1X wins: ' + Math.min(p.winsAs1x, 5) + '/5 · Boiled One: ' + Math.min(p.boiledOnePlays, 3) + '/3';
    case 'catAch': return p.deerRestrictedWin ? '' : 'Not yet completed';
    // Round 2
    case 'fighterAch': return p.fighterSpecialAch ? '' : 'Not yet completed';
    case 'pokerAch': return p.pokerNoSpecialAch ? '' : 'Not yet completed';
    case 'filbusAch': return p.filbusBoiledKillAch ? '' : 'Not yet completed';
    case 'onexAch': return 'Noli (MP): ' + (p.onexKilledNoliMP ? '✓' : '✗') + ' · Cat (SP): ' + (p.onexKilledCatSP ? '✓' : '✗');
    case 'cricketAch2': return 'Absorbed: ' + Math.min(p.gearDmgAbsorbed * 10, 1000) + '/1000';
    case 'deerAch2': return p.deerWaterKill ? '' : 'Not yet completed';
    case 'noliAch2': return p.noliVoidRushAch ? '' : 'Not yet completed';
    case 'catAch2': return p.catKittenAch ? '' : 'Not yet completed';
    default: return '';
  }
}

function loadAchievementCode() {
  const code = $('#achv-code-input').value.trim();
  const msg = $('#achv-msg');
  if (!code) {
    msg.textContent = 'Please enter a code.';
    msg.className = 'achv-msg error';
    return;
  }
  const decoded = decodeAchCode(code);
  if (!decoded) {
    msg.textContent = 'Invalid code. Check and try again.';
    msg.className = 'achv-msg error';
    return;
  }
  // Merge achievements and progress (take max of each counter)
  if (decoded.unlockAll) {
    allFightersUnlocked = true;
  }
  for (const id of decoded.completed) completedAchievements.add(id);
  _PROGRESS_KEYS.forEach(k => {
    achProgress[k] = Math.max(achProgress[k] || 0, decoded.progress[k] || 0);
  });
  saveAchievements();
  msg.textContent = 'Code loaded! Achievements restored.';
  msg.className = 'achv-msg success';
  renderAchievementsScreen();
}

function renderAchievementsScreen() {
  // Show the saved code (same one stored in localStorage)
  let displayCode;
  try { displayCode = localStorage.getItem(_ACH_KEY); } catch (e) { /* ignore */ }
  if (!displayCode) {
    saveAchievements();
    try { displayCode = localStorage.getItem(_ACH_KEY); } catch (e) { /* ignore */ }
  }
  $('#achv-code-display').textContent = displayCode || '------';

  // Achievement list
  const list = $('#achv-list');
  list.innerHTML = '';
  Object.values(ACHIEVEMENTS).forEach((ach) => {
    const done = completedAchievements.has(ach.id);
    // Move 4 achievements are completely hidden until completed (surprise reward)
    if (ach.unlocksMove4 && !done) return;
    const available = isAchievementAvailable(ach.id);
    const item = document.createElement('div');
    item.className = 'achv-item' + (done ? ' done' : '') + (!available ? ' unavailable' : '');
    if (!available) {
      // Show as hidden/unavailable — required fighters not unlocked
      const neededNames = (ach.requiresFighters || []).filter(f => !isFighterUnlocked(f)).map(f => getFighter(f).name);
      item.innerHTML =
        `<div class="achv-header">` +
          `<span class="achv-icon">❓</span>` +
          `<div class="achv-name">???</div>` +
          `<span class="achv-status locked">HIDDEN</span>` +
        `</div>` +
        `<div class="achv-details">` +
          `<div class="achv-desc">Unlock ${escapeHtml(neededNames.join(' & '))} first.</div>` +
        `</div>`;
    } else {
      let progressText = '';
      if (!done) progressText = _getProgressText(ach.id);
      item.innerHTML =
        `<div class="achv-header">` +
          `<span class="achv-icon">${done ? '✅' : '🔒'}</span>` +
          `<div class="achv-name">${escapeHtml(ach.name)}</div>` +
          `<span class="achv-status ${done ? 'done' : 'locked'}">${done ? 'DONE' : 'LOCKED'}</span>` +
        `</div>` +
        `<div class="achv-details">` +
          `<div class="achv-desc">${escapeHtml(ach.description)}</div>` +
          (progressText ? `<div class="achv-progress">${escapeHtml(progressText)}</div>` : '') +
        `</div>`;
    }
    // Collapsible: toggle details on header click
    const header = item.querySelector('.achv-header');
    header.style.cursor = 'pointer';
    header.addEventListener('click', () => {
      item.classList.toggle('expanded');
    });
    list.appendChild(item);
  });

  // Fighters grid
  const grid = $('#achv-fighter-grid');
  grid.innerHTML = '';
  _shuffledFighterIds.forEach((fid) => {
    if (isFighterFree(fid)) return; // skip free fighters
    const f = getFighter(fid);
    const unlocked = isFighterUnlocked(fid);
    const chip = document.createElement('div');
    chip.className = 'achv-fighter-chip ' + (unlocked ? 'unlocked' : 'locked');
    const canvas = document.createElement('canvas');
    drawFighterIcon(canvas, fid, 28);
    chip.appendChild(canvas);
    const name = document.createElement('span');
    name.textContent = unlocked ? f.name : 'Locked';
    chip.appendChild(name);
    grid.appendChild(chip);
  });
}
