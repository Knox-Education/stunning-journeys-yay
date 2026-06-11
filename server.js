const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');
const crypto = require('crypto');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: '*' },
  transports: ['websocket', 'polling'],
  allowEIO3: true,
  pingTimeout: 10000,
  pingInterval: 5000,
  maxHttpBufferSize: 1e6,
  perMessageDeflate: false,
  httpCompression: false,
});

app.use(express.static(path.join(__dirname, 'public'), {
  etag: false,
  maxAge: 0,
  setHeaders: (res) => {
    res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate');
    res.setHeader('Pragma', 'no-cache');
  }
}));

// ── Lobby state ─────────────────────────────────────────────
// lobbies Map:  code -> { host, mapIndex, players: Map<socketId, {name, color}> }
const lobbies = new Map();

const PLAYER_COLORS = ['#e94560', '#3498db', '#2ecc71', '#f5a623', '#9b59b6', '#e67e22', '#1abc9c', '#fd79a8'];

// Team color palettes: each set has [team1 shades, team2 shades, ...] 
// Each team has 4 shades (enough for up to 4 players per team)
const TEAM_COLOR_SETS = {
  'red-blue': {
    name: 'Red vs Blue',
    1: ['#e94560', '#ff6b81', '#c23152', '#ff4757'],
    2: ['#3498db', '#54a0ff', '#2e86c1', '#74b9ff'],
    3: ['#2ecc71', '#55efc4', '#27ae60', '#00b894'],
    4: ['#f5a623', '#fdcb6e', '#e67e22', '#feca57'],
  },
  'green-purple': {
    name: 'Green vs Purple',
    1: ['#2ecc71', '#55efc4', '#27ae60', '#00b894'],
    2: ['#9b59b6', '#a29bfe', '#8e44ad', '#6c5ce7'],
    3: ['#e94560', '#ff6b81', '#c23152', '#ff4757'],
    4: ['#f5a623', '#fdcb6e', '#e67e22', '#feca57'],
  },
  'orange-teal': {
    name: 'Orange vs Teal',
    1: ['#e67e22', '#f39c12', '#d35400', '#feca57'],
    2: ['#1abc9c', '#00cec9', '#16a085', '#55efc4'],
    3: ['#e94560', '#ff6b81', '#c23152', '#ff4757'],
    4: ['#9b59b6', '#a29bfe', '#8e44ad', '#6c5ce7'],
  },
  'pink-cyan': {
    name: 'Pink vs Cyan',
    1: ['#fd79a8', '#e84393', '#f368e0', '#ff6b81'],
    2: ['#00cec9', '#81ecec', '#00b5b8', '#7efadb'],
    3: ['#f5a623', '#fdcb6e', '#e67e22', '#feca57'],
    4: ['#2ecc71', '#55efc4', '#27ae60', '#00b894'],
  },
};
const TEAM_COLOR_SET_KEYS = Object.keys(TEAM_COLOR_SETS);

function generateCode() {
  // 6-char uppercase alphanumeric code
  let code;
  do {
    code = crypto.randomBytes(3).toString('hex').toUpperCase();
  } while (lobbies.has(code));
  return code;
}

// ── Socket.io events ────────────────────────────────────────
io.on('connection', (socket) => {
  console.log(`[${new Date().toISOString()}] Player connected: ${socket.id}`);

  // HOST a new game
  socket.on('host-game', ({ playerName, mapIndex, fighterId, lobbyMode }) => {
    const code = generateCode();
    const mode = (lobbyMode === 'teams2' || lobbyMode === 'teams4' || lobbyMode === 'teams2r') ? lobbyMode : 'ffa';
    const lobby = {
      host: socket.id,
      mapIndex: mapIndex ?? 0,
      mode,
      players: new Map(),
    };
    const color = PLAYER_COLORS[0];
    lobby.players.set(socket.id, { name: playerName, color, fighterId: fighterId || 'fighter' });
    lobbies.set(code, lobby);
    socket.join(code);
    socket.lobbyCode = code;
    socket.playerName = playerName;
    socket._lastFighterId = fighterId || 'fighter';

    socket.emit('game-hosted', {
      code,
      mapIndex: lobby.mapIndex,
      lobbyMode: mode,
      players: lobbyPlayerList(lobby),
      availableColors: getAvailableColors(lobby),
    });
    console.log(`Lobby ${code} created by ${playerName} (mode: ${mode})`);
  });

  // JOIN an existing game
  socket.on('join-game', ({ playerName, code, fighterId }) => {
    const upperCode = (code || '').toUpperCase().trim();
    const lobby = lobbies.get(upperCode);

    if (!lobby) {
      socket.emit('join-error', { message: 'Lobby not found. Check the code and try again.' });
      return;
    }
    const maxPlayers = 8;
    if (lobby.players.size >= maxPlayers) {
      socket.emit('join-error', { message: `Lobby is full (max ${maxPlayers} players).` });
      return;
    }

    const available = getAvailableColors(lobby);
    const color = available[0] || '#ffffff';
    lobby.players.set(socket.id, { name: playerName, color, fighterId: fighterId || 'fighter' });
    socket.join(upperCode);
    socket.lobbyCode = upperCode;
    socket.playerName = playerName;
    socket._lastFighterId = fighterId || 'fighter';

    // Tell the joiner
    socket.emit('game-joined', {
      code: upperCode,
      mapIndex: lobby.mapIndex,
      lobbyMode: lobby.mode,
      players: lobbyPlayerList(lobby),
      availableColors: getAvailableColors(lobby),
    });

    // Tell everyone else
    socket.to(upperCode).emit('player-joined', {
      players: lobbyPlayerList(lobby),
      availableColors: getAvailableColors(lobby),
    });
    console.log(`${playerName} joined lobby ${upperCode}`);
  });

  // Change color
  socket.on('change-color', ({ color }) => {
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby) return;
    const player = lobby.players.get(socket.id);
    if (!player) return;
    // Only allow if color is not taken by someone else
    const taken = new Set();
    for (const [id, p] of lobby.players) {
      if (id !== socket.id) taken.add(p.color);
    }
    if (!taken.has(color) && PLAYER_COLORS.includes(color)) {
      player.color = color;
      io.to(socket.lobbyCode).emit('player-updated', {
        players: lobbyPlayerList(lobby),
        availableColors: getAvailableColors(lobby),
      });
    }
  });

  // Change fighter selection
  socket.on('change-fighter', ({ fighterId }) => {
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby) return;
    const player = lobby.players.get(socket.id);
    if (!player) return;
    player.fighterId = fighterId;
    socket._lastFighterId = fighterId;
    io.to(socket.lobbyCode).emit('player-updated', {
      players: lobbyPlayerList(lobby),
      availableColors: getAvailableColors(lobby),
    });
  });

  // Change map (host only)
  socket.on('change-map', ({ mapIndex }) => {
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host !== socket.id) return;
    lobby.mapIndex = mapIndex;
    io.to(socket.lobbyCode).emit('map-changed', { mapIndex });
  });

  // Change lobby mode (host only)
  socket.on('change-mode', ({ lobbyMode }) => {
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host !== socket.id) return;
    const mode = (lobbyMode === 'teams2' || lobbyMode === 'teams4' || lobbyMode === 'teams2r') ? lobbyMode : 'ffa';
    lobby.mode = mode;
    io.to(socket.lobbyCode).emit('mode-changed', { lobbyMode: mode });
  });

  // Change team color set (host only)
  socket.on('change-team-colors', ({ colorSet }) => {
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host !== socket.id) return;
    if (TEAM_COLOR_SETS[colorSet]) {
      lobby.teamColorSet = colorSet;
      io.to(socket.lobbyCode).emit('team-colors-changed', { colorSet, colorSetName: TEAM_COLOR_SETS[colorSet].name });
    }
  });

  // Randomize team color set (host only)
  socket.on('random-team-colors', () => {
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host !== socket.id) return;
    const key = TEAM_COLOR_SET_KEYS[Math.floor(Math.random() * TEAM_COLOR_SET_KEYS.length)];
    lobby.teamColorSet = key;
    io.to(socket.lobbyCode).emit('team-colors-changed', { colorSet: key, colorSetName: TEAM_COLOR_SETS[key].name });
  });

  // Start game (host only)
  socket.on('start-game', () => {
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host !== socket.id) return;

    // Team mode requires minimum 2 players
    if ((lobby.mode === 'teams2' || lobby.mode === 'teams2r') && lobby.players.size < 2) {
      socket.emit('start-error', { message: 'Need at least 2 players for 2 Teams.' });
      return;
    }
    // 4 Teams requires at least 4 players
    if (lobby.mode === 'teams4' && lobby.players.size < 4) {
      socket.emit('start-error', { message: 'Need at least 4 players for 4 Teams.' });
      return;
    }

    lobby.deadPlayers = new Set();
    lobby.killCounts = new Map(); // for respawn mode
    const playerList = lobbyPlayerList(lobby);
    // Assign teams for team modes
    if (lobby.mode === 'teams2' || lobby.mode === 'teams2r') {
      lobby.teamMap = new Map();
      playerList.forEach((p, i) => {
        p.team = (i % 2) + 1;
        lobby.teamMap.set(p.id, p.team);
      });
      // Init kill counters for respawn mode
      if (lobby.mode === 'teams2r') {
        lobby.killCounts.set(1, 0);
        lobby.killCounts.set(2, 0);
        lobby.respawnGameTimer = 180; // 3 minute game
      }
    } else if (lobby.mode === 'teams4') {
      lobby.teamMap = new Map();
      playerList.forEach((p, i) => {
        p.team = (i % 4) + 1;
        lobby.teamMap.set(p.id, p.team);
      });
    }
    // Assign team colors to players in team modes
    if (lobby.teamMap && lobby.teamMap.size > 0) {
      const setKey = lobby.teamColorSet || TEAM_COLOR_SET_KEYS[0];
      const colorSet = TEAM_COLOR_SETS[setKey];
      // Count how many players are on each team to assign shade index
      const teamCounters = {};
      playerList.forEach(p => {
        if (!p.team) return;
        if (!teamCounters[p.team]) teamCounters[p.team] = 0;
        const shades = colorSet[p.team] || colorSet[1];
        p.color = shades[teamCounters[p.team] % shades.length];
        // Also update the lobby's stored color
        const lobbyPlayer = lobby.players.get(p.id);
        if (lobbyPlayer) lobbyPlayer.color = p.color;
        teamCounters[p.team]++;
      });
    }
    io.to(socket.lobbyCode).emit('game-starting', {
      mapIndex: lobby.mapIndex,
      players: playerList,
      lobbyMode: lobby.mode,
    });
  });

  // In-game movement + HP broadcast (with validation)
  socket.on('player-move', ({ x, y, hp }) => {
    if (!socket.lobbyCode) return;
    // Validate types: must be finite numbers
    if (typeof x !== 'number' || typeof y !== 'number' || typeof hp !== 'number') return;
    if (!isFinite(x) || !isFinite(y) || !isFinite(hp)) return;
    // Clamp position to reasonable bounds (50 cols * 48 tile = 2400, generous margin)
    const maxCoord = 5000;
    const cx = Math.max(0, Math.min(x, maxCoord));
    const cy = Math.max(0, Math.min(y, maxCoord));
    // Clamp HP: 0 to 5000 (generous cap for any fighter)
    const chp = Math.max(0, Math.min(hp, 5000));
    // Rate-limit: max ~60 updates/sec per socket
    const now = Date.now();
    if (!socket._lastMove) socket._lastMove = 0;
    if (now - socket._lastMove < 16) return; // drop if too fast
    socket._lastMove = now;
    socket.to(socket.lobbyCode).emit('player-moved', {
      id: socket.id,
      x: cx,
      y: cy,
      hp: chp,
    });
  });

  // Relay damage events from attacker to all clients (with validation)
  socket.on('player-damage', ({ targetId, amount, attackerId }) => {
    if (!socket.lobbyCode) return;
    // Validate damage: must be a positive number, cap at 1000 per hit
    if (typeof amount !== 'number' || amount <= 0 || !isFinite(amount)) return;
    const clampedAmount = Math.min(amount, 1000);
    socket.to(socket.lobbyCode).emit('player-damaged', {
      targetId,
      amount: clampedAmount,
      attackerId: socket.id,
    });
  });

  // Relay knockback (with position validation)
  socket.on('player-knockback', ({ targetId, x, y }) => {
    if (!socket.lobbyCode) return;
    if (typeof x !== 'number' || typeof y !== 'number' || !isFinite(x) || !isFinite(y)) return;
    const maxCoord = 5000;
    socket.to(socket.lobbyCode).emit('player-knockedback', {
      targetId,
      x: Math.max(0, Math.min(x, maxCoord)),
      y: Math.max(0, Math.min(y, maxCoord)),
    });
  });

  // Host broadcasts zone timer to keep everyone in sync
  socket.on('zone-sync', ({ zoneInset, zoneTimer }) => {
    if (socket.lobbyCode) {
      socket.to(socket.lobbyCode).emit('zone-synced', {
        zoneInset,
        zoneTimer,
      });
    }
  });

  // ── HOST-AUTHORITATIVE STATE BROADCAST ──────────────────────
  // Host sends full game state snapshot; relay to all non-host clients with volatile flag for speed
  socket.on('game-state', (snapshot) => {
    if (!socket.lobbyCode) return;
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host !== socket.id) return; // only host can broadcast state
    // Use volatile emit — dropped snapshots are fine since the next one replaces it
    socket.to(socket.lobbyCode).volatile.emit('game-state', snapshot);
  });

  // Non-host clients send their input state to host each frame
  socket.on('player-input', (input) => {
    if (!socket.lobbyCode) return;
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host === socket.id) return; // only non-hosts send input
    // Relay input to host only — volatile since stale inputs are replaced by newer ones
    const hostSocket = io.sockets.sockets.get(lobby.host);
    if (hostSocket) {
      hostSocket.volatile.emit('player-input', { playerId: socket.id, ...input });
    }
  });

  // All clients relay their position for smooth movement sync — volatile for performance
  socket.on('player-position', ({ x, y }) => {
    if (!socket.lobbyCode) return;
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby) return;
    // Validate position
    if (typeof x !== 'number' || typeof y !== 'number' || !isFinite(x) || !isFinite(y)) return;
    const maxCoord = 5000;
    socket.to(socket.lobbyCode).volatile.emit('player-position', {
      id: socket.id,
      x: Math.max(0, Math.min(x, maxCoord)),
      y: Math.max(0, Math.min(y, maxCoord)),
    });
  });

  // Player died — relay to all
  socket.on('player-died', ({ playerId, killerId }) => {
    if (!socket.lobbyCode) return;
    const code = socket.lobbyCode;
    io.to(code).emit('player-death', { playerId });

    // Check win condition server-side
    const lobby = lobbies.get(code);
    if (!lobby) return;

    // Respawn mode: track kills and respawn, don't eliminate
    if (lobby.mode === 'teams2r') {
      if (killerId && lobby.teamMap) {
        const killerTeam = lobby.teamMap.get(killerId);
        if (killerTeam && lobby.killCounts) {
          lobby.killCounts.set(killerTeam, (lobby.killCounts.get(killerTeam) || 0) + 1);
          io.to(code).emit('respawn-kill-update', {
            team1Kills: lobby.killCounts.get(1) || 0,
            team2Kills: lobby.killCounts.get(2) || 0,
          });
        }
      }
      // Tell all clients to respawn this player in 3 seconds
      io.to(code).emit('player-respawn', { playerId, delay: 3 });
      return;
    }

    // Knockout modes: track dead players
    if (!lobby.deadPlayers) lobby.deadPlayers = new Set();
    lobby.deadPlayers.add(playerId);
    const totalPlayers = lobby.players.size;
    const alive = [];
    for (const [id] of lobby.players) {
      if (!lobby.deadPlayers.has(id)) alive.push(id);
    }

    if (lobby.mode === 'teams2' || lobby.mode === 'teams4') {
      // Team win: check if all alive players are on the same team
      if (!lobby.teamMap) return;
      const aliveTeams = new Set();
      for (const id of alive) {
        const t = lobby.teamMap.get(id);
        if (t) aliveTeams.add(t);
      }
      if (aliveTeams.size <= 1 && alive.length > 0) {
        const winningTeam = aliveTeams.values().next().value;
        io.to(code).emit('game-over', {
          winnerId: null,
          winnerName: null,
          winningTeam,
        });
      } else if (alive.length === 0) {
        io.to(code).emit('game-over', { winnerId: null, winnerName: null, winningTeam: null });
      }
    } else {
      // FFA: last player standing
      if (alive.length <= 1 && totalPlayers > 1) {
        const winnerId = alive.length === 1 ? alive[0] : null;
        const winnerData = winnerId ? lobby.players.get(winnerId) : null;
        io.to(code).emit('game-over', {
          winnerId,
          winnerName: winnerData ? winnerData.name : null,
        });
      }
    }
  });

  // Respawn mode: game timer ended — determine winner by kills
  socket.on('respawn-timer-end', () => {
    if (!socket.lobbyCode) return;
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.mode !== 'teams2r') return;
    if (lobby.host !== socket.id) return; // only host triggers
    const t1 = (lobby.killCounts && lobby.killCounts.get(1)) || 0;
    const t2 = (lobby.killCounts && lobby.killCounts.get(2)) || 0;
    const winningTeam = t1 > t2 ? 1 : t2 > t1 ? 2 : null;
    io.to(socket.lobbyCode).emit('game-over', {
      winnerId: null,
      winnerName: null,
      winningTeam,
      respawnMode: true,
      team1Kills: t1,
      team2Kills: t2,
    });
  });

  // Relay buff/debuff events
  socket.on('player-buff', ({ type, duration, cx, cy }) => {
    if (socket.lobbyCode) {
      io.to(socket.lobbyCode).emit('player-buffed', {
        casterId: socket.id,
        type,
        duration,
        cx,
        cy,
      });
    }
  });

  socket.on('projectile-spawn', (data) => {
    if (!socket.lobbyCode) return;
    // Validate: must be an array, cap at 10 projectiles per message
    if (!Array.isArray(data.projectiles)) return;
    // Rate-limit: max ~10 projectile-spawn messages per second per socket
    const now = Date.now();
    if (!socket._lastProjSpawn) socket._lastProjSpawn = 0;
    if (now - socket._lastProjSpawn < 100) return; // drop if too fast
    socket._lastProjSpawn = now;
    const clamped = data.projectiles.slice(0, 10);
    socket.to(socket.lobbyCode).emit('projectile-spawned', {
      ownerId: socket.id,
      projectiles: clamped,
    });
  });

  socket.on('player-debuff', ({ targetId, type, duration }) => {
    if (socket.lobbyCode) {
      io.to(socket.lobbyCode).emit('player-debuffed', {
        casterId: socket.id,
        targetId,
        type,
        duration,
      });
    }
  });

  // ── PLAY AGAIN: create a new lobby from the old one ────────
  // First person to click creates the lobby; everyone else joins the same one.
  // Priority: original host becomes host of new lobby IF they click in time.
  socket.on('request-play-again', () => {
    const oldCode = socket.lobbyCode;
    if (!oldCode) return;
    const oldLobby = lobbies.get(oldCode);
    if (!oldLobby) return;

    // If a play-again lobby already exists for this game, auto-join it
    if (oldLobby._playAgainCode) {
      const remaining = Math.max(0, Math.ceil((oldLobby._playAgainDeadline - Date.now()) / 1000));
      if (remaining > 0) {
        // Auto-join the existing play-again lobby
        _joinPlayAgainLobby(socket, oldLobby._playAgainCode, oldCode, oldLobby);
      } else {
        socket.emit('play-again-expired');
      }
      return;
    }

    // Create a new lobby with same settings
    const newCode = generateCode();
    const wasHost = oldLobby.host === socket.id;
    const newLobby = {
      host: socket.id,
      mapIndex: oldLobby.mapIndex,
      mode: oldLobby.mode || 'ffa',
      players: new Map(),
      _fromPlayAgain: true,
      _originalHost: oldLobby.host,  // track original host for priority
    };
    // Add the requester as first player
    const pName = socket.playerName || 'Player';
    const pColor = PLAYER_COLORS[0];
    const pFighter = (oldLobby.players.get(socket.id) || {}).fighterId || socket._lastFighterId || 'fighter';
    newLobby.players.set(socket.id, { name: pName, color: pColor, fighterId: pFighter });
    socket._lastFighterId = pFighter; // persist fighter across play-again transitions
    lobbies.set(newCode, newLobby);

    // Mark old lobby so others can find the play-again code
    oldLobby._playAgainCode = newCode;
    oldLobby._playAgainDeadline = Date.now() + 5000;

    // Move requester to new lobby room
    socket.leave(oldCode);
    socket.join(newCode);
    socket.lobbyCode = newCode;
    oldLobby.players.delete(socket.id);

    // Tell the requester they're hosting the new lobby
    socket.emit('play-again-hosted', {
      code: newCode,
      mapIndex: newLobby.mapIndex,
      players: lobbyPlayerList(newLobby),
      availableColors: getAvailableColors(newLobby),
      lobbyMode: newLobby.mode,
    });

    // Tell all remaining players in old lobby about the play-again opportunity
    io.to(oldCode).emit('play-again-offered', { code: newCode, countdown: 5 });

    // After 5 seconds, clean up old lobby reference and finalize host
    setTimeout(() => {
      delete oldLobby._playAgainCode;
      delete oldLobby._playAgainDeadline;
      // Clean up old lobby if empty
      if (oldLobby.players.size === 0) {
        lobbies.delete(oldCode);
      }
    }, 5500);

    console.log(`Play-again: ${pName} created new lobby ${newCode} from ${oldCode}`);
  });

  // Helper: join an existing play-again lobby
  function _joinPlayAgainLobby(sock, newCode, oldCode, oldLobby) {
    const newLobby = lobbies.get(newCode);
    if (!newLobby) {
      sock.emit('play-again-expired');
      return;
    }
    // Already in the new lobby?
    if (sock.lobbyCode === newCode) return;

    const maxPlayers = 8;
    if (newLobby.players.size >= maxPlayers) {
      sock.emit('join-error', { message: 'New lobby is full.' });
      return;
    }

    // Add to new lobby — read fighter data BEFORE deletion from old lobby
    const pName = sock.playerName || 'Player';
    const available = getAvailableColors(newLobby);
    const pColor = available[0] || '#ffffff';
    const pFighter = (oldLobby && oldLobby.players.get(sock.id) || {}).fighterId || sock._lastFighterId || 'fighter';

    // Leave old lobby
    if (oldLobby) {
      oldLobby.players.delete(sock.id);
      sock.leave(oldCode);
      if (oldLobby.players.size === 0 && !oldLobby._playAgainCode) {
        lobbies.delete(oldCode);
      } else if (oldLobby.host === sock.id) {
        const nextHost = oldLobby.players.keys().next().value;
        if (nextHost) oldLobby.host = nextHost;
      }
    }

    // Add to new lobby
    newLobby.players.set(sock.id, { name: pName, color: pColor, fighterId: pFighter });
    sock._lastFighterId = pFighter; // persist fighter selection across play-again transitions
    sock.join(newCode);
    sock.lobbyCode = newCode;

    // If this player was the original host, promote them to host of the new lobby
    if (newLobby._originalHost === sock.id) {
      newLobby.host = sock.id;
      // Tell this player they're the host
      sock.emit('play-again-hosted', {
        code: newCode,
        mapIndex: newLobby.mapIndex,
        players: lobbyPlayerList(newLobby),
        availableColors: getAvailableColors(newLobby),
        lobbyMode: newLobby.mode,
      });
    } else {
      // Tell this player they've joined
      sock.emit('play-again-joined', {
        code: newCode,
        mapIndex: newLobby.mapIndex,
        players: lobbyPlayerList(newLobby),
        availableColors: getAvailableColors(newLobby),
        lobbyMode: newLobby.mode,
      });
    }

    // Tell everyone else in new lobby about the new player
    sock.to(newCode).emit('player-joined', {
      players: lobbyPlayerList(newLobby),
      availableColors: getAvailableColors(newLobby),
    });

    console.log(`${pName} joined play-again lobby ${newCode}`);
  }

  socket.on('join-play-again', ({ code, fighterId }) => {
    if (!code) return;
    const oldCode = socket.lobbyCode;
    const oldLobby = oldCode ? lobbies.get(oldCode) : null;
    // Store fighterId before joining
    if (fighterId && oldLobby) {
      const pData = oldLobby.players.get(socket.id);
      if (pData) pData.fighterId = fighterId;
    }
    _joinPlayAgainLobby(socket, code, oldCode, oldLobby);
  });

  // Leave / disconnect
  socket.on('leave-lobby', () => leaveLobby(socket));
  socket.on('disconnect', () => {
    leaveCardsLobby(socket);
    leaveLobby(socket);
    console.log(`[${new Date().toISOString()}] Player disconnected: ${socket.id}`);
  });

  // ── CARD GAME LOBBY EVENTS ─────────────────────────────────
  socket.on('cards-host-game', ({ playerName, gameType }) => {
    const code = generateCode();
    const lobby = {
      host: socket.id,
      gameType: gameType || 'exploding_kittens',
      players: new Map(),
      inGame: false,
    };
    lobby.players.set(socket.id, { name: playerName });
    cardsLobbies.set(code, lobby);
    socket.join('cards-' + code);
    socket.cardsLobbyCode = code;
    socket.playerName = playerName;

    socket.emit('cards-game-hosted', {
      code,
      gameType: lobby.gameType,
      players: cardsLobbyPlayerList(lobby),
    });
    console.log(`Cards lobby ${code} created by ${playerName}`);
  });

  socket.on('cards-join-game', ({ playerName, code }) => {
    const upperCode = (code || '').toUpperCase().trim();
    const lobby = cardsLobbies.get(upperCode);
    if (!lobby) {
      socket.emit('cards-join-error', { message: 'Lobby not found.' });
      return;
    }
    if (lobby.players.size >= 5) {
      socket.emit('cards-join-error', { message: 'Lobby is full (max 5 players).' });
      return;
    }
    if (lobby.inGame) {
      socket.emit('cards-join-error', { message: 'Game already in progress.' });
      return;
    }

    lobby.players.set(socket.id, { name: playerName });
    socket.join('cards-' + upperCode);
    socket.cardsLobbyCode = upperCode;
    socket.playerName = playerName;

    socket.emit('cards-game-joined', {
      code: upperCode,
      gameType: lobby.gameType,
      players: cardsLobbyPlayerList(lobby),
    });
    socket.to('cards-' + upperCode).emit('cards-player-joined', {
      code: upperCode,
      players: cardsLobbyPlayerList(lobby),
    });
    console.log(`${playerName} joined cards lobby ${upperCode}`);
  });

  socket.on('cards-start-game', () => {
    const code = socket.cardsLobbyCode;
    if (!code) return;
    const lobby = cardsLobbies.get(code);
    if (!lobby || lobby.host !== socket.id) return;
    if (lobby.players.size < 2) {
      socket.emit('cards-start-error', { message: 'Need at least 2 players.' });
      return;
    }
    lobby.inGame = true;

    // Create game state on server
    const players = cardsLobbyPlayerList(lobby).map(p => ({ id: p.id, name: p.name, isCPU: false }));
    const game = new ServerEKGame(players);
    game.setup();
    cardsGames.set(code, game);

    // Send initial state to each player (they only see their own hand)
    for (const [pid] of lobby.players) {
      const sock = io.sockets.sockets.get(pid);
      if (sock) {
        sock.emit('cards-game-starting', {
          gameType: lobby.gameType,
          players: players,
          initialState: game.serializeForPlayer(pid),
        });
      }
    }
    console.log(`Cards game started in lobby ${code}`);
  });

  socket.on('cards-game-action', ({ actionType, data }) => {
    const code = socket.cardsLobbyCode;
    if (!code) return;
    const game = cardsGames.get(code);
    if (!game || game.winner) return;

    let result;
    switch (actionType) {
      case 'play_card':
        result = game.playCard(socket.id, data.cardIndex);
        break;
      case 'nope':
        result = game.playNope(socket.id);
        if (result && result.success) {
          // Cancel the nope timer
          if (game._nopeTimer) { clearTimeout(game._nopeTimer); game._nopeTimer = null; }
        }
        break;
      case 'draw':
        result = game.drawCard(socket.id);
        break;
      case 'place_kitten':
        result = game.placeKitten(data.position);
        break;
      case 'steal_target':
        result = game.resolveSteal(data.targetId);
        break;
      case 'favor_target':
        result = game.pickFavorTarget(data.targetId);
        break;
      case 'favor_give':
        result = game.resolveFavor(socket.id, data.cardIndex);
        break;
      default:
        return;
    }

    // If nope window started, set a 2-second timer to resolve
    if (result && result.action === 'nope_window') {
      if (game._nopeTimer) clearTimeout(game._nopeTimer);
      game._nopeTimer = setTimeout(() => {
        game._nopeTimer = null;
        const resolved = game.resolveNopeWindow();
        if (resolved && resolved.action === 'see_future' && resolved.cards) {
          const s = io.sockets.sockets.get(socket.id);
          if (s) s.emit('cards-see-future', { cards: resolved.cards });
        }
        if (resolved && resolved.action === 'reveal_future' && resolved.cards) {
          const lobby2 = cardsLobbies.get(code);
          if (lobby2) {
            for (const [pid] of lobby2.players) {
              const s = io.sockets.sockets.get(pid);
              if (s) s.emit('cards-see-future', { cards: resolved.cards });
            }
          }
        }
        // Broadcast state after resolution
        const lobby2 = cardsLobbies.get(code);
        if (lobby2) {
          for (const [pid] of lobby2.players) {
            const s = io.sockets.sockets.get(pid);
            if (s) s.emit('cards-game-state', game.serializeForPlayer(pid));
          }
        }
      }, 2000);
    }

    // Send See the Future result only to the requesting player
    if (result && result.action === 'see_future' && result.cards) {
      socket.emit('cards-see-future', { cards: result.cards });
    }

    // Send Reveal the Future to ALL players in the lobby
    if (result && result.action === 'reveal_future' && result.cards) {
      const revealLobby = cardsLobbies.get(code);
      if (revealLobby) {
        for (const [pid] of revealLobby.players) {
          const s = io.sockets.sockets.get(pid);
          if (s) s.emit('cards-see-future', { cards: result.cards });
        }
      }
    }

    // Broadcast updated state to all players
    const lobby = cardsLobbies.get(code);
    if (lobby) {
      for (const [pid] of lobby.players) {
        const sock = io.sockets.sockets.get(pid);
        if (sock) {
          sock.emit('cards-game-state', game.serializeForPlayer(pid));
        }
      }
    }
  });

  socket.on('cards-leave-lobby', () => leaveCardsLobby(socket));
});

function leaveLobby(socket) {
  const code = socket.lobbyCode;
  if (!code) return;
  const lobby = lobbies.get(code);
  if (!lobby) return;

  lobby.players.delete(socket.id);
  socket.leave(code);
  socket.lobbyCode = null;

  if (lobby.players.size === 0) {
    lobbies.delete(code);
    console.log(`Lobby ${code} closed (empty)`);
  } else {
    // If host left, assign new host
    if (lobby.host === socket.id) {
      lobby.host = lobby.players.keys().next().value;
    }
    io.to(code).emit('player-left', {
      players: lobbyPlayerList(lobby),
      availableColors: getAvailableColors(lobby),
      host: lobby.host,
    });
  }
}

function lobbyPlayerList(lobby) {
  return Array.from(lobby.players.entries()).map(([id, data]) => ({
    id,
    name: data.name,
    color: data.color,
    fighterId: data.fighterId || 'fighter',
    isHost: id === lobby.host,
  }));
}

function getAvailableColors(lobby) {
  const taken = new Set();
  for (const [, p] of lobby.players) taken.add(p.color);
  return PLAYER_COLORS.filter((c) => !taken.has(c));
}

// ── Card Game Lobby State ────────────────────────────────────
const cardsLobbies = new Map(); // code -> { host, gameType, players: Map<socketId, {name}>, inGame }
const cardsGames = new Map();   // code -> ServerEKGame

function cardsLobbyPlayerList(lobby) {
  return Array.from(lobby.players.entries()).map(([id, data]) => ({
    id,
    name: data.name,
    isHost: id === lobby.host,
  }));
}

function leaveCardsLobby(socket) {
  const code = socket.cardsLobbyCode;
  if (!code) return;
  const lobby = cardsLobbies.get(code);
  if (!lobby) return;

  // If game is in progress, eliminate the disconnecting player
  const game = cardsGames.get(code);
  if (game && !game.winner && game.alive.has(socket.id)) {
    game.alive.delete(socket.id);
    if (game.hands[socket.id]) {
      game.discardPile.push(...game.hands[socket.id]);
      game.hands[socket.id] = [];
    }
    game.addLog(`${game.getPlayerName(socket.id)} disconnected and was eliminated!`);
    // If it was their turn, advance
    if (game.currentPlayer && game.currentPlayer.id === socket.id) {
      game.turnsRemaining = 0;
      game.advanceTurn();
    }
    game.checkWin();
    // Broadcast updated state to remaining players
    for (const [pid] of lobby.players) {
      if (pid === socket.id) continue;
      const s = io.sockets.sockets.get(pid);
      if (s) s.emit('cards-game-state', game.serializeForPlayer(pid));
    }
  }

  lobby.players.delete(socket.id);
  socket.leave('cards-' + code);
  socket.cardsLobbyCode = null;

  if (lobby.players.size === 0) {
    cardsLobbies.delete(code);
    cardsGames.delete(code);
    console.log(`Cards lobby ${code} closed (empty)`);
  } else {
    if (lobby.host === socket.id) {
      lobby.host = lobby.players.keys().next().value;
    }
    io.to('cards-' + code).emit('cards-player-left', {
      code,
      players: cardsLobbyPlayerList(lobby),
    });
  }
}

// ── Server-side Exploding Kittens Game ──────────────────────
class ServerEKGame {
  constructor(players) {
    this.players = players;
    this.hands = {};
    this.drawPile = [];
    this.discardPile = [];
    this.alive = new Set(players.map(p => p.id));
    this.currentPlayerIdx = 0;
    this.turnsRemaining = 1;
    this.winner = null;
    this.pendingAction = null;
    this.pendingCardAction = null;
    this._nopeTimer = null;
    this.log = [];
  }

  setup() {
    const playerCount = this.players.length;
    let deck = [];
    // 4 of each action card
    const actionTypes = ['attack', 'skip', 'see_the_future', 'shuffle', 'favor'];
    actionTypes.forEach(t => { for (let i = 0; i < 4; i++) deck.push({ type: t }); });
    // 5 Nope
    for (let i = 0; i < 5; i++) deck.push({ type: 'nope' });
    // 3 Reveal the Future
    for (let i = 0; i < 3; i++) deck.push({ type: 'reveal_the_future' });
    // 4 Draw from Bottom, 4 Self Attack
    for (let i = 0; i < 4; i++) deck.push({ type: 'draw_from_bottom' });
    for (let i = 0; i < 4; i++) deck.push({ type: 'self_attack' });
    // 4 of each cat type
    const catTypes = ['cat_taco', 'cat_melon', 'cat_potato', 'cat_beard', 'cat_rainbow'];
    catTypes.forEach(t => { for (let i = 0; i < 4; i++) deck.push({ type: t }); });
    // Extra defuses
    const extraDefuses = Math.max(0, 6 - playerCount);
    for (let i = 0; i < extraDefuses; i++) deck.push({ type: 'defuse' });
    // Exploding kittens
    const ekCount = playerCount - 1;
    const ekCards = [];
    for (let i = 0; i < ekCount; i++) ekCards.push({ type: 'exploding_kitten' });

    this.shuffle(deck);

    // Deal 6 + 1 Defuse to each player (7 total)
    this.players.forEach(p => {
      this.hands[p.id] = [{ type: 'defuse' }];
      for (let i = 0; i < 6; i++) {
        if (deck.length > 0) this.hands[p.id].push(deck.pop());
      }
    });

    // Shuffle remaining + EKs into draw pile
    this.drawPile = [...deck, ...ekCards];
    this.shuffle(this.drawPile);
    this.addLog('Game started!');
  }

  shuffle(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
  }

  get currentPlayer() { return this.players[this.currentPlayerIdx]; }

  getAlivePlayers() { return this.players.filter(p => this.alive.has(p.id)); }

  addLog(msg) { this.log.push(msg); if (this.log.length > 50) this.log.shift(); }

  getPlayerName(id) { const p = this.players.find(p => p.id === id); return p ? p.name : '?'; }

  playCard(playerId, cardIndex) {
    if (this.winner) return { success: false };
    if (this.pendingCardAction) return { success: false, reason: 'Nope window active' };
    if (this.currentPlayer.id !== playerId && !this.pendingAction) return { success: false, reason: 'Not your turn' };
    const hand = this.hands[playerId];
    if (!hand || cardIndex < 0 || cardIndex >= hand.length) return { success: false };
    const card = hand[cardIndex];
    if (card.type === 'exploding_kitten') return { success: false };
    if (card.type === 'defuse' && !this.pendingAction) return { success: false };
    if (card.type === 'nope') return { success: false, reason: 'Use nope action type' };

    // Cat pairs
    if (card.type.startsWith('cat_')) {
      const pairIdx = hand.findIndex((c, i) => i !== cardIndex && c.type === card.type);
      if (pairIdx === -1) return { success: false };
      const removed = [cardIndex, pairIdx].sort((a, b) => b - a);
      removed.forEach(i => hand.splice(i, 1));
      this.discardPile.push(card, { type: card.type });
      this.addLog(`${this.getPlayerName(playerId)} played a cat pair!`);
      this.pendingCardAction = { playerId, card, action: 'steal_pick_target' };
      return { success: true, action: 'nope_window', card };
    }

    hand.splice(cardIndex, 1);
    this.discardPile.push(card);

    const nopeableTypes = ['attack', 'skip', 'see_the_future', 'reveal_the_future', 'shuffle', 'favor', 'draw_from_bottom', 'self_attack'];
    if (nopeableTypes.includes(card.type)) {
      this.addLog(`${this.getPlayerName(playerId)} played ${card.type.replace(/_/g, ' ')}!`);
      this.pendingCardAction = { playerId, card };
      return { success: true, action: 'nope_window', card };
    }

    return this.resolveCard(playerId, card);
  }

  playNope(playerId) {
    if (!this.pendingCardAction) return { success: false };
    if (playerId === this.pendingCardAction.playerId) return { success: false };
    const hand = this.hands[playerId];
    if (!hand) return { success: false };
    const nopeIdx = hand.findIndex(c => c.type === 'nope');
    if (nopeIdx === -1) return { success: false };
    hand.splice(nopeIdx, 1);
    this.discardPile.push({ type: 'nope' });
    this.addLog(`${this.getPlayerName(playerId)} played Nope!`);
    this.pendingCardAction = null;
    return { success: true, action: 'noped' };
  }

  resolveNopeWindow() {
    if (!this.pendingCardAction) return null;
    const { playerId, card, action } = this.pendingCardAction;
    this.pendingCardAction = null;
    if (action === 'steal_pick_target') {
      this.pendingAction = { type: 'steal', playerId };
      return { success: true, action: 'steal_pick_target' };
    }
    return this.resolveCard(playerId, card);
  }

  resolveCard(playerId, card) {
    switch (card.type) {
      case 'attack':
        this.addLog(`${this.getPlayerName(playerId)} played Attack!`);
        this.turnsRemaining = 0;
        this.advanceTurn();
        this.turnsRemaining = 2;
        return { success: true, action: 'attack' };
      case 'skip':
        this.addLog(`${this.getPlayerName(playerId)} played Skip!`);
        this.turnsRemaining--;
        if (this.turnsRemaining <= 0) this.advanceTurn();
        return { success: true, action: 'skip' };
      case 'see_the_future':
        this.addLog(`${this.getPlayerName(playerId)} played See the Future!`);
        return { success: true, action: 'see_future', cards: this.drawPile.slice(-2).reverse() };
      case 'reveal_the_future':
        this.addLog(`${this.getPlayerName(playerId)} played Reveal the Future!`);
        return { success: true, action: 'reveal_future', cards: this.drawPile.slice(-3).reverse() };
      case 'shuffle':
        this.addLog(`${this.getPlayerName(playerId)} shuffled the deck!`);
        this.shuffle(this.drawPile);
        return { success: true, action: 'shuffle' };
      case 'favor':
        this.addLog(`${this.getPlayerName(playerId)} played Favor!`);
        this.pendingAction = { type: 'favor_pick_target', playerId };
        return { success: true, action: 'favor_pick_target' };
      case 'draw_from_bottom':
        this.addLog(`${this.getPlayerName(playerId)} drew from the bottom!`);
        return this.drawFromBottom(playerId);
      case 'self_attack':
        this.addLog(`${this.getPlayerName(playerId)} played Self Attack! (+2 turns)`);
        this.turnsRemaining += 2;
        return { success: true, action: 'self_attack' };
      case 'nope':
        this.addLog(`${this.getPlayerName(playerId)} played Nope!`);
        return { success: true, action: 'nope' };
      default:
        return { success: true };
    }
  }

  drawCard(playerId) {
    if (this.winner) return { success: false };
    if (this.currentPlayer.id !== playerId) return { success: false };
    if (this.pendingAction) return { success: false };
    if (this.pendingCardAction) return { success: false };
    if (this.drawPile.length === 0) return { success: false };

    const card = this.drawPile.pop();
    if (card.type === 'exploding_kitten') {
      const defIdx = this.hands[playerId].findIndex(c => c.type === 'defuse');
      if (defIdx !== -1) {
        this.hands[playerId].splice(defIdx, 1);
        this.discardPile.push({ type: 'defuse' });
        this.addLog(`${this.getPlayerName(playerId)} defused an Exploding Kitten!`);
        this.pendingAction = { type: 'place_kitten', playerId, card };
        return { success: true, action: 'defused' };
      } else {
        this.addLog(`💥 ${this.getPlayerName(playerId)} EXPLODED!`);
        this.alive.delete(playerId);
        this.discardPile.push(card, ...this.hands[playerId]);
        this.hands[playerId] = [];
        this.turnsRemaining = 0;
        this.advanceTurn();
        this.checkWin();
        return { success: true, action: 'exploded' };
      }
    }

    this.hands[playerId].push(card);
    this.turnsRemaining--;
    if (this.turnsRemaining <= 0) this.advanceTurn();
    return { success: true, action: 'drew' };
  }

  drawFromBottom(playerId) {
    if (this.drawPile.length === 0) return { success: true, action: 'draw_bottom_empty' };
    const card = this.drawPile.shift(); // bottom = index 0

    if (card.type === 'exploding_kitten') {
      const defIdx = this.hands[playerId].findIndex(c => c.type === 'defuse');
      if (defIdx !== -1) {
        this.hands[playerId].splice(defIdx, 1);
        this.discardPile.push({ type: 'defuse' });
        this.addLog(`${this.getPlayerName(playerId)} defused an Exploding Kitten from the bottom!`);
        this.pendingAction = { type: 'place_kitten', playerId, card };
        return { success: true, action: 'defused' };
      } else {
        this.addLog(`\ud83d\udca5 ${this.getPlayerName(playerId)} drew from the bottom and EXPLODED!`);
        this.alive.delete(playerId);
        this.discardPile.push(card, ...this.hands[playerId]);
        this.hands[playerId] = [];
        this.turnsRemaining = 0;
        this.advanceTurn();
        this.checkWin();
        return { success: true, action: 'exploded' };
      }
    }

    this.hands[playerId].push(card);
    this.turnsRemaining--;
    if (this.turnsRemaining <= 0) this.advanceTurn();
    return { success: true, action: 'drew_bottom' };
  }

  placeKitten(position) {
    if (!this.pendingAction || this.pendingAction.type !== 'place_kitten') return { success: false };
    const { card } = this.pendingAction;
    const pos = Math.max(0, Math.min(position, this.drawPile.length));
    const insertIdx = this.drawPile.length - pos;
    this.drawPile.splice(Math.max(0, insertIdx), 0, card);
    this.pendingAction = null;
    this.turnsRemaining--;
    if (this.turnsRemaining <= 0) this.advanceTurn();
    return { success: true };
  }

  resolveSteal(targetId) {
    if (!this.pendingAction || this.pendingAction.type !== 'steal') return { success: false };
    const targetHand = this.hands[targetId];
    if (!targetHand || targetHand.length === 0) { this.pendingAction = null; return { success: true }; }
    const rIdx = Math.floor(Math.random() * targetHand.length);
    const stolen = targetHand.splice(rIdx, 1)[0];
    this.hands[this.pendingAction.playerId].push(stolen);
    this.addLog(`${this.getPlayerName(this.pendingAction.playerId)} stole from ${this.getPlayerName(targetId)}!`);
    this.pendingAction = null;
    return { success: true };
  }

  pickFavorTarget(targetId) {
    if (!this.pendingAction || this.pendingAction.type !== 'favor_pick_target') return { success: false };
    if (!this.alive.has(targetId) || targetId === this.pendingAction.playerId) return { success: false };
    this.pendingAction = { type: 'favor_give', playerId: this.pendingAction.playerId, targetId };
    return { success: true };
  }

  resolveFavor(targetId, cardIndex) {
    if (!this.pendingAction || this.pendingAction.type !== 'favor_give') return { success: false };
    const hand = this.hands[targetId];
    if (!hand || cardIndex < 0 || cardIndex >= hand.length) return { success: false };
    const card = hand.splice(cardIndex, 1)[0];
    this.hands[this.pendingAction.playerId].push(card);
    this.addLog(`${this.getPlayerName(targetId)} gave a card`);
    this.pendingAction = null;
    return { success: true };
  }

  advanceTurn() {
    const alive = this.getAlivePlayers();
    if (alive.length <= 1) return;
    let idx = this.currentPlayerIdx;
    do { idx = (idx + 1) % this.players.length; } while (!this.alive.has(this.players[idx].id));
    this.currentPlayerIdx = idx;
    this.turnsRemaining = Math.max(this.turnsRemaining, 1);
  }

  checkWin() {
    const alive = this.getAlivePlayers();
    if (alive.length === 1) {
      this.winner = alive[0];
      this.addLog(`🎉 ${this.winner.name} wins!`);
    }
  }

  serializeForPlayer(playerId) {
    return {
      players: this.players.map(p => ({
        id: p.id,
        name: p.name,
        alive: this.alive.has(p.id),
        handSize: (this.hands[p.id] || []).length,
        isCPU: false,
      })),
      hands: { [playerId]: this.hands[playerId] || [] },
      drawPileSize: this.drawPile.length,
      discardPile: this.discardPile,
      alive: Array.from(this.alive),
      currentPlayerIdx: this.currentPlayerIdx,
      turnsRemaining: this.turnsRemaining,
      pendingAction: this.pendingAction,
      pendingCardAction: this.pendingCardAction ? { playerId: this.pendingCardAction.playerId, card: this.pendingCardAction.card } : null,
      winner: this.winner,
      log: this.log.slice(-8),
    };
  }
}

// ── Start server ────────────────────────────────────────────
const PORT = process.env.PORT || 3000;

server.listen(PORT, '0.0.0.0', () => {
  console.log(`Server running on port ${PORT}`);
});
