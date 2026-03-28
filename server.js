const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');
const crypto = require('crypto');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: '*' },
  transports: ['polling', 'websocket'],
  allowEIO3: true,
  pingTimeout: 30000,
  pingInterval: 10000,
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

const PLAYER_COLORS = ['#e94560', '#3498db', '#2ecc71', '#f5a623', '#9b59b6', '#e67e22'];

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
  console.log(`Player connected: ${socket.id}`);

  // HOST a new game
  socket.on('host-game', ({ playerName, mapIndex, fighterId, lobbyMode }) => {
    const code = generateCode();
    const mode = (lobbyMode === 'teams2' || lobbyMode === 'teams3') ? lobbyMode : 'ffa';
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
    const maxPlayers = (lobby.mode === 'teams2' || lobby.mode === 'teams3') ? 6 : 4;
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
    const mode = (lobbyMode === 'teams2' || lobbyMode === 'teams3') ? lobbyMode : 'ffa';
    lobby.mode = mode;
    io.to(socket.lobbyCode).emit('mode-changed', { lobbyMode: mode });
  });

  // Start game (host only)
  socket.on('start-game', () => {
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host !== socket.id) return;

    // 3 Teams requires exactly 6 players
    if (lobby.mode === 'teams3' && lobby.players.size < 6) {
      socket.emit('start-error', { message: 'Not enough people — 3 Teams requires 6 players.' });
      return;
    }

    lobby.deadPlayers = new Set();
    const playerList = lobbyPlayerList(lobby);
    // Assign teams for team modes
    if (lobby.mode === 'teams2') {
      lobby.teamMap = new Map();
      playerList.forEach((p, i) => {
        p.team = (i % 2) + 1;
        lobby.teamMap.set(p.id, p.team);
      });
    } else if (lobby.mode === 'teams3') {
      lobby.teamMap = new Map();
      playerList.forEach((p, i) => {
        p.team = (i % 3) + 1;
        lobby.teamMap.set(p.id, p.team);
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
    // Rate-limit: max ~30 updates/sec per socket
    const now = Date.now();
    if (!socket._lastMove) socket._lastMove = 0;
    if (now - socket._lastMove < 30) return; // drop if too fast
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
  // Host sends full game state snapshot every ~50ms; relay to all non-host clients
  socket.on('game-state', (snapshot) => {
    if (!socket.lobbyCode) return;
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host !== socket.id) return; // only host can broadcast state
    // Relay snapshot to all NON-host players in the lobby
    socket.to(socket.lobbyCode).emit('game-state', snapshot);
  });

  // Non-host clients send their input state to host each frame
  socket.on('player-input', (input) => {
    if (!socket.lobbyCode) return;
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host === socket.id) return; // only non-hosts send input
    // Relay input to host only
    const hostSocket = io.sockets.sockets.get(lobby.host);
    if (hostSocket) {
      hostSocket.emit('player-input', { playerId: socket.id, ...input });
    }
  });

  // All clients relay their position for smooth movement sync
  socket.on('player-position', ({ x, y }) => {
    if (!socket.lobbyCode) return;
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby) return;
    // Relay to every other client in the lobby (including host)
    socket.to(socket.lobbyCode).emit('player-position', { id: socket.id, x, y });
  });

  // Player died — relay to all
  socket.on('player-died', ({ playerId }) => {
    if (!socket.lobbyCode) return;
    const code = socket.lobbyCode;
    io.to(code).emit('player-death', { playerId });

    // Check win condition server-side
    const lobby = lobbies.get(code);
    if (!lobby) return;
    // Count alive: everyone who hasn't sent a death event
    // Track deaths on the lobby
    if (!lobby.deadPlayers) lobby.deadPlayers = new Set();
    lobby.deadPlayers.add(playerId);
    const totalPlayers = lobby.players.size;
    const alive = [];
    for (const [id] of lobby.players) {
      if (!lobby.deadPlayers.has(id)) alive.push(id);
    }

    if (lobby.mode === 'teams2' || lobby.mode === 'teams3') {
      // Team win: check if all alive players are on the same team
      // Retrieve team assignments from the last start-game emission
      if (!lobby.teamMap) return; // should have been set at start
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
    const pFighter = (oldLobby.players.get(socket.id) || {}).fighterId || 'fighter';
    newLobby.players.set(socket.id, { name: pName, color: pColor, fighterId: pFighter });
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

    const maxPlayers = (newLobby.mode === 'teams2' || newLobby.mode === 'teams3') ? 6 : 4;
    if (newLobby.players.size >= maxPlayers) {
      sock.emit('join-error', { message: 'New lobby is full.' });
      return;
    }

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
    const pName = sock.playerName || 'Player';
    const available = getAvailableColors(newLobby);
    const pColor = available[0] || '#ffffff';
    const pFighter = (oldLobby && oldLobby.players.get(sock.id) || {}).fighterId || 'fighter';
    newLobby.players.set(sock.id, { name: pName, color: pColor, fighterId: pFighter });
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
    leaveLobby(socket);
    console.log(`Player disconnected: ${socket.id}`);
  });
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

// ── Start server ────────────────────────────────────────────
const PORT = process.env.PORT || 3000;

server.listen(PORT, '0.0.0.0', () => {
  console.log(`Server running on port ${PORT}`);
});
