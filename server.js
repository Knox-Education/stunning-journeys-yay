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
});

app.use(express.static(path.join(__dirname, 'public')));

// ── Lobby state ─────────────────────────────────────────────
// lobbies Map:  code -> { host, mapIndex, players: Map<socketId, {name, color}> }
const lobbies = new Map();

const PLAYER_COLORS = ['#e94560', '#3498db', '#2ecc71', '#f5a623', '#9b59b6'];

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
  socket.on('host-game', ({ playerName, mapIndex }) => {
    const code = generateCode();
    const lobby = {
      host: socket.id,
      mapIndex: mapIndex ?? 0,
      players: new Map(),
    };
    const color = PLAYER_COLORS[0];
    lobby.players.set(socket.id, { name: playerName, color, fighterId: 'fighter' });
    lobbies.set(code, lobby);
    socket.join(code);
    socket.lobbyCode = code;

    socket.emit('game-hosted', {
      code,
      mapIndex: lobby.mapIndex,
      players: lobbyPlayerList(lobby),
      availableColors: getAvailableColors(lobby),
    });
    console.log(`Lobby ${code} created by ${playerName}`);
  });

  // JOIN an existing game
  socket.on('join-game', ({ playerName, code }) => {
    const upperCode = (code || '').toUpperCase().trim();
    const lobby = lobbies.get(upperCode);

    if (!lobby) {
      socket.emit('join-error', { message: 'Lobby not found. Check the code and try again.' });
      return;
    }
    if (lobby.players.size >= 5) {
      socket.emit('join-error', { message: 'Lobby is full (max 5 players).' });
      return;
    }

    const available = getAvailableColors(lobby);
    const color = available[0] || '#ffffff';
    lobby.players.set(socket.id, { name: playerName, color, fighterId: 'fighter' });
    socket.join(upperCode);
    socket.lobbyCode = upperCode;

    // Tell the joiner
    socket.emit('game-joined', {
      code: upperCode,
      mapIndex: lobby.mapIndex,
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

  // Start game (host only)
  socket.on('start-game', () => {
    const lobby = lobbies.get(socket.lobbyCode);
    if (!lobby || lobby.host !== socket.id) return;
    lobby.deadPlayers = new Set();
    io.to(socket.lobbyCode).emit('game-starting', {
      mapIndex: lobby.mapIndex,
      players: lobbyPlayerList(lobby),
    });
  });

  // In-game movement + HP broadcast
  socket.on('player-move', ({ x, y, hp }) => {
    if (socket.lobbyCode) {
      socket.to(socket.lobbyCode).emit('player-moved', {
        id: socket.id,
        x,
        y,
        hp,
      });
    }
  });

  // Relay damage events from attacker to all clients
  socket.on('player-damage', ({ targetId, amount, attackerId }) => {
    if (socket.lobbyCode) {
      socket.to(socket.lobbyCode).emit('player-damaged', {
        targetId,
        amount,
        attackerId: socket.id,
      });
    }
  });

  // Relay knockback
  socket.on('player-knockback', ({ targetId, x, y }) => {
    if (socket.lobbyCode) {
      socket.to(socket.lobbyCode).emit('player-knockedback', {
        targetId,
        x,
        y,
      });
    }
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
    const deadCount = lobby.deadPlayers.size;
    const alive = [];
    for (const [id] of lobby.players) {
      if (!lobby.deadPlayers.has(id)) alive.push(id);
    }
    if (alive.length <= 1 && totalPlayers > 1) {
      const winnerId = alive.length === 1 ? alive[0] : null;
      const winnerData = winnerId ? lobby.players.get(winnerId) : null;
      io.to(code).emit('game-over', {
        winnerId,
        winnerName: winnerData ? winnerData.name : null,
      });
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
    if (socket.lobbyCode) {
      socket.to(socket.lobbyCode).emit('projectile-spawned', {
        ownerId: socket.id,
        projectiles: data.projectiles, // [{x,y,vx,vy,timer,type}]
      });
    }
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
server.listen(PORT, () => {
  console.log(`Battlegrounds server running on http://localhost:${PORT}`);
});
