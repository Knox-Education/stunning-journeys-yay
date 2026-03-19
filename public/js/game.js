/**
 * game.js – In-game engine: camera, rendering, movement, combat, abilities.
 *
 * The game canvas fills the entire viewport.
 * Camera is centred on the local player with a 5-tile visible range.
 * Map edges beyond bounds render as water.
 * Players are coloured dots slightly smaller than one tile.
 * Movement is smooth (pixel-level), using WASD or arrow keys.
 * Combat uses M1/E/R/T/Space bindings.
 */

const GAME_TILE = 48;
const CAMERA_RANGE = 3;
const PLAYER_RADIUS_RATIO = 0.38;
const BASE_MOVE_SPEED = 3.2;

let gameRunning = false;
let gameCanvas, gameCtx;
let gameMap;
let gamePlayers = [];    // [{id, name, color, x, y, hp, maxHp, fighter, ...}]
let localPlayerId = null;
let localPlayer = null;
let lastTime = 0;

// Zone shrink state
let zoneInset = 0;        // tiles shrunk from each edge
let zoneTimer = 40;       // seconds until next shrink
let zonePhaseStart = 0;   // wall-clock ms when current zone phase started
const ZONE_INTERVAL = 40; // seconds between shrinks
const ZONE_DPS = 50;      // damage per second outside zone

// Input state
const keys = {};
let mouseX = 0, mouseY = 0;
let mouseDown = false;
let lastWallClock = 0;  // wall-clock ms for background-tab-safe dt

// Projectile system
let projectiles = [];  // [{x, y, vx, vy, ownerId, damage, speed, timer, type}]
let combatLog = [];    // [{text, timer, color}]

// Spectator / dead-camera state
let spectateIndex = -1;   // index into gamePlayers, -1 = free camera
let freeCamX = 0, freeCamY = 0;

// Training dummy respawn timer
let dummyRespawnTimer = 0;

// Game mode: 'training' | 'fight' | undefined (multiplayer)
let gameMode = undefined;

// CPU names
const CPU_NAMES = ['Alpha', 'Bravo', 'Charlie', 'Delta', 'Echo', 'Foxtrot', 'Ghost', 'Havoc'];
const CPU_COLORS = ['#e67e22', '#1abc9c', '#9b59b6', '#e74c3c', '#3498db', '#f1c40f'];

// ═══════════════════════════════════════════════════════════════
// START GAME
// ═══════════════════════════════════════════════════════════════
function startGame(mapIndex, players, myId, mode) {
  gameCanvas = document.querySelector('#game-canvas');
  gameCtx = gameCanvas.getContext('2d');
  gameMap = MAPS[mapIndex];
  localPlayerId = myId;
  gameMode = mode;

  // Find walkable spawn positions
  const walkable = [];
  for (let r = 0; r < gameMap.rows; r++) {
    for (let c = 0; c < gameMap.cols; c++) {
      const t = gameMap.tiles[r][c];
      if (t === TILE.GROUND || t === TILE.GRASS) {
        walkable.push({ r, c });
      }
    }
  }

  // Pick spawn points at opposite corners/edges of the map
  const spawnCandidates = [
    { r: 1, c: 1 },
    { r: 1, c: gameMap.cols - 2 },
    { r: gameMap.rows - 2, c: 1 },
    { r: gameMap.rows - 2, c: gameMap.cols - 2 },
    { r: Math.floor(gameMap.rows / 2), c: 1 },
    { r: 1, c: Math.floor(gameMap.cols / 2) },
    { r: gameMap.rows - 2, c: Math.floor(gameMap.cols / 2) },
    { r: Math.floor(gameMap.rows / 2), c: gameMap.cols - 2 },
  ];
  // Filter to walkable and pick unique positions
  const validSpawns = spawnCandidates.filter((s) => {
    if (s.r < 0 || s.r >= gameMap.rows || s.c < 0 || s.c >= gameMap.cols) return false;
    const t = gameMap.tiles[s.r][s.c];
    return t === TILE.GROUND || t === TILE.GRASS;
  });
  // Fallback: if not enough valid spawns, add shuffled walkable tiles
  if (validSpawns.length < players.length) {
    shuffleArray(walkable);
    for (const w of walkable) {
      if (!validSpawns.some((s) => s.r === w.r && s.c === w.c)) {
        validSpawns.push(w);
        if (validSpawns.length >= players.length) break;
      }
    }
  }

  // Reset zone
  zoneInset = 0;
  zoneTimer = ZONE_INTERVAL;
  zonePhaseStart = Date.now();

  // Reset projectiles
  projectiles = [];
  combatLog = [];
  spectateIndex = -1;
  freeCamX = 0;
  freeCamY = 0;

  gamePlayers = players.map((p, i) => {
    const spawn = validSpawns[i % validSpawns.length];
    const fighter = getFighter(p.fighterId || 'fighter');
    return createPlayerState(p, spawn, fighter);
  });

  localPlayer = gamePlayers.find((p) => p.id === localPlayerId);
  if (!localPlayer && gamePlayers.length > 0) {
    localPlayer = gamePlayers[0];
    localPlayerId = localPlayer.id;
  }

  // Singleplayer mode setup
  if (gameMode === 'training') {
    // Training: dummy in center of map, 2000 HP, respawns
    const centerR = Math.floor(gameMap.rows / 2);
    const centerC = Math.floor(gameMap.cols / 2);
    const dummySpawn = { r: centerR, c: centerC };
    const dummyFighter = getFighter('fighter');
    const dummy = createPlayerState(
      { id: 'dummy', name: 'Training Dummy', color: '#555' },
      dummySpawn,
      dummyFighter
    );
    dummy.hp = 2000;
    dummy.maxHp = 2000;
    gamePlayers.push(dummy);
    dummyRespawnTimer = 0;
  } else if (gameMode === 'fight') {
    // Fight: 4 CPU opponents — 1 easy, 2 medium, 1 hard
    const allFighters = getAllFighterIds();
    const difficulties = ['easy', 'medium', 'medium', 'hard'];
    const shuffledNames = CPU_NAMES.slice().sort(() => Math.random() - 0.5);
    const shuffledColors = CPU_COLORS.slice().sort(() => Math.random() - 0.5);
    for (let i = 0; i < 4; i++) {
      const cpuFighterId = allFighters[Math.floor(Math.random() * allFighters.length)];
      const cpuFighter = getFighter(cpuFighterId);
      const cpuSpawn = validSpawns[(i + 1) % validSpawns.length];
      const cpu = createPlayerState(
        { id: 'cpu-' + i, name: shuffledNames[i], color: shuffledColors[i % shuffledColors.length], fighterId: cpuFighterId },
        cpuSpawn,
        cpuFighter
      );
      cpu.isCPU = true;
      cpu.difficulty = difficulties[i];
      cpu.aiState = {
        moveTarget: null,
        attackTarget: null,
        thinkTimer: 0,
        abilityTimer: 0,
        lastSeenPositions: {}, // id -> {x, y, time}
        strafeDir: Math.random() < 0.5 ? 1 : -1,
        retreating: false,
      };
      gamePlayers.push(cpu);
    }
  }

  // Resize canvas
  resizeCanvas();
  window.addEventListener('resize', resizeCanvas);

  // Input listeners
  window.addEventListener('keydown', onKeyDown);
  window.addEventListener('keyup', (e) => { keys[e.key] = false; });
  gameCanvas.addEventListener('mousedown', (e) => { if (e.button === 0) mouseDown = true; });
  gameCanvas.addEventListener('mouseup', (e) => { if (e.button === 0) mouseDown = false; });
  gameCanvas.addEventListener('mousemove', (e) => { mouseX = e.clientX; mouseY = e.clientY; });

  // Build HUD
  buildHUD();

  gameRunning = true;
  lastTime = performance.now();
  lastWallClock = Date.now();
  requestAnimationFrame(gameLoop);
}

function createPlayerState(p, spawn, fighter) {
  return {
    id: p.id,
    name: p.name,
    color: p.color,
    x: (spawn.c + 0.5) * GAME_TILE,
    y: (spawn.r + 0.5) * GAME_TILE,
    // Combat
    hp: fighter.hp,
    maxHp: fighter.hp,
    fighter: fighter,
    alive: true,
    // Cooldowns (seconds remaining)
    cdM1: 0,
    cdE: 0,
    cdR: 0,
    cdT: 0,
    // Ability state
    totalDamageTaken: 0,
    specialUnlocked: false,
    specialUsed: false,
    // Buffs / debuffs
    supportBuff: 0,        // seconds remaining of 50% dmg boost
    intimidated: 0,        // seconds remaining of intimidation debuff
    intimidatedBy: null,   // id of the fighter who intimidated
    stunned: 0,            // seconds of stun remaining
    // Auto-heal state
    noDamageTimer: 0,      // time since last damage taken
    healTickTimer: 0,      // countdown to next heal tick
    isHealing: false,      // whether heal ticks are active
    // Special state
    specialJumping: false,
    specialAiming: false,
    specialAimX: 0,
    specialAimY: 0,
    specialAimTimer: 0,   // seconds left before forced landing
    // Visual effects
    effects: [],           // [{type, timer, ...}]
    // Poker-specific state
    blindBuff: null,       // 'small' | 'big' | 'dealer' | null
    blindTimer: 0,         // seconds remaining for big blind
    chipChangeDmg: -1,     // -1 = normal, else 0/100/200/300/400
    chipChangeTimer: 0,    // seconds remaining
    // Filbus-specific state
    chairCharges: 0,       // number of crafted chairs
    isCraftingChair: false,// currently channeling Filbism (1)
    craftTimer: 0,         // seconds remaining on craft channel
    isEatingChair: false,  // currently channeling Filbism (2)
    eatTimer: 0,           // seconds remaining on eat channel
    eatHealPool: 0,        // HP left to heal during eat
    summonId: null,        // id of active companion entity
    boiledOneActive: false,// whether Boiled One is active
    boiledOneTimer: 0,     // seconds remaining until first stunned can move
    // 1X1X1X1-specific state
    poisonTimers: [],       // [{sourceId, dps, remaining}]
    unstableEyeTimer: 0,    // seconds remaining of Unstable Eye
    zombieIds: [],           // array of zombie summon ids
  };
}

function resizeCanvas() {
  gameCanvas.width = window.innerWidth;
  gameCanvas.height = window.innerHeight;
}

// ═══════════════════════════════════════════════════════════════
// INPUT
// ═══════════════════════════════════════════════════════════════
function onKeyDown(e) {
  keys[e.key] = true;
  if (['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', ' '].includes(e.key)) {
    e.preventDefault();
  }

  if (!localPlayer) return;

  // Spectator: Tab to cycle through alive players when dead
  if (!localPlayer.alive) {
    if (e.key === 'Tab') {
      e.preventDefault();
      const alivePlayers = gamePlayers.filter(p => p.alive && p.id !== localPlayerId);
      if (alivePlayers.length > 0) {
        // Find current spectate target in alive list
        let curIdx = -1;
        if (spectateIndex >= 0 && spectateIndex < gamePlayers.length) {
          curIdx = alivePlayers.indexOf(gamePlayers[spectateIndex]);
        }
        curIdx = (curIdx + 1) % alivePlayers.length;
        spectateIndex = gamePlayers.indexOf(alivePlayers[curIdx]);
      }
    }
    // Escape returns to free camera
    if (e.key === 'Escape') {
      spectateIndex = -1;
    }
    return;
  }

  // Ability presses (single-fire, not held)
  if (e.key === 'e' || e.key === 'E') useAbility('E');
  if (e.key === 'r' || e.key === 'R') useAbility('R');
  if (e.key === 't' || e.key === 'T') useAbility('T');
  if (e.key === ' ') useAbility('SPACE');
}

// ═══════════════════════════════════════════════════════════════
// GAME LOOP
// ═══════════════════════════════════════════════════════════════
function gameLoop(now) {
  if (!gameRunning) return;

  const dt = Math.min((now - lastTime) / 1000, 0.1); // delta in seconds, capped
  lastTime = now;

  updateGame(dt);
  renderGame();

  // Check win condition: last player standing in multiplayer
  checkWinCondition();

  // Broadcast position + HP
  if (typeof socket !== 'undefined' && socket.emit && localPlayer) {
    socket.emit('player-move', { x: localPlayer.x, y: localPlayer.y, hp: localPlayer.hp });
    // Host syncs zone timer every frame
    if (isHost) {
      socket.emit('zone-sync', { zoneInset, zoneTimer });
    }
  }

  requestAnimationFrame(gameLoop);
}

// ═══════════════════════════════════════════════════════════════
// UPDATE
// ═══════════════════════════════════════════════════════════════
function updateGame(dt) {
  if (!localPlayer) return;

  // Use wall-clock delta for timers, capped to prevent huge jumps on tab-switch
  const wallNow = Date.now();
  const wallDt = Math.min((wallNow - lastWallClock) / 1000, 0.1); // cap same as dt to prevent burst damage/cooldowns
  lastWallClock = wallNow;

  // Dead: free camera movement
  if (!localPlayer.alive) {
    // Free camera movement with WASD
    if (spectateIndex < 0 || !gamePlayers[spectateIndex] || !gamePlayers[spectateIndex].alive) {
      let dx = 0, dy = 0;
      if (keys['ArrowUp']    || keys['w'] || keys['W']) dy -= 1;
      if (keys['ArrowDown']  || keys['s'] || keys['S']) dy += 1;
      if (keys['ArrowLeft']  || keys['a'] || keys['A']) dx -= 1;
      if (keys['ArrowRight'] || keys['d'] || keys['D']) dx += 1;
      const camSpeed = 6 * GAME_TILE * dt;
      freeCamX += dx * camSpeed;
      freeCamY += dy * camSpeed;
      // If spectate target died, reset to free cam
      if (spectateIndex >= 0) spectateIndex = -1;
    }
  }

  // === World simulation (always runs, even when dead) ===

  // Tick cooldowns for local player (only if alive)
  if (localPlayer.alive) tickCooldowns(localPlayer, wallDt);

  // Tick buffs/debuffs for all players
  for (const p of gamePlayers) {
    if (p.supportBuff > 0) p.supportBuff = Math.max(0, p.supportBuff - wallDt);
    if (p.intimidated > 0) {
      p.intimidated = Math.max(0, p.intimidated - wallDt);
      if (p.intimidated <= 0) p.intimidatedBy = null;
    }
    if (p.stunned > 0) p.stunned = Math.max(0, p.stunned - wallDt);

    // Auto-heal: if not damaged for healDelay seconds, heal healAmount every healTick
    if (p.alive && p.hp < p.maxHp) {
      p.noDamageTimer += wallDt;
      if (!p.isHealing && p.noDamageTimer >= p.fighter.healDelay) {
        p.isHealing = true;
        p.healTickTimer = 0; // first tick starts immediately
      }
      if (p.isHealing) {
        p.healTickTimer -= wallDt;
        if (p.healTickTimer <= 0) {
          p.hp = Math.min(p.maxHp, p.hp + p.fighter.healAmount);
          p.healTickTimer = p.fighter.healTick;
        }
      }
    }

    // Zone damage: hurt players outside the safe zone
    if (p.alive && zoneInset > 0) {
      const pCol = Math.floor(p.x / GAME_TILE);
      const pRow = Math.floor(p.y / GAME_TILE);
      if (pCol < zoneInset || pCol >= gameMap.cols - zoneInset ||
          pRow < zoneInset || pRow >= gameMap.rows - zoneInset) {
        p.hp -= ZONE_DPS * wallDt;
        p.noDamageTimer = 0;
        p.isHealing = false;
        p.healTickTimer = 0;
        if (p.hp <= 0) {
          p.hp = 0;
          p.alive = false;
          p.effects.push({ type: 'death', timer: 2 });
          if (p.id === localPlayerId) { freeCamX = p.x; freeCamY = p.y; spectateIndex = -1; }
        }
      }
    }

    // Tick effects
    p.effects = p.effects.filter((fx) => {
      fx.timer -= wallDt;
      return fx.timer > 0;
    });

    // Tick Poker-specific timers
    if (p.blindBuff === 'dealer') {
      p.blindTimer += wallDt;
      if (p.blindTimer >= 3) { p.blindBuff = null; p.blindTimer = 0; }
    } else if (p.blindTimer > 0) {
      p.blindTimer = Math.max(0, p.blindTimer - wallDt);
      if (p.blindTimer <= 0 && p.blindBuff === 'big') p.blindBuff = null;
    }
    if (p.chipChangeTimer > 0) {
      p.chipChangeTimer = Math.max(0, p.chipChangeTimer - wallDt);
      if (p.chipChangeTimer <= 0) p.chipChangeDmg = -1;
    }

    // Tick Filbus-specific timers
    if (p.isCraftingChair) {
      p.craftTimer -= wallDt;
      if (p.craftTimer <= 0) {
        p.isCraftingChair = false;
        p.craftTimer = 0;
        p.chairCharges++;
        if (p.id === localPlayerId) {
          combatLog.push({ text: '🪑 Chair crafted! (' + p.chairCharges + ' chairs)', timer: 3, color: '#2ecc71' });
          showPopup('🪑 Chair crafted!');
        }
      }
    }
    if (p.isEatingChair) {
      p.eatTimer -= wallDt;
      // Heal gradually over the channel time
      const channelTime = p.fighter.abilities && p.fighter.abilities[2] ? (p.fighter.abilities[2].channelTime || 3) : 3;
      const healPerSec = (p.eatHealPool > 0 ? p.eatHealPool : 100) / channelTime;
      if (p.alive) {
        p.hp = Math.min(p.maxHp, p.hp + healPerSec * wallDt);
      }
      if (p.eatTimer <= 0) {
        p.isEatingChair = false;
        p.eatTimer = 0;
        p.eatHealPool = 0;
        if (p.id === localPlayerId) {
          combatLog.push({ text: '🪑 Chair consumed!', timer: 2, color: '#2ecc71' });
        }
      }
    }
    // Boiled One timer
    if (p.boiledOneActive) {
      p.boiledOneTimer -= wallDt;
      // While active, anyone who can see the dark-red dot gets stunned
      for (const target of gamePlayers) {
        if (target.id === p.id || !target.alive || target.isSummon) continue;
        // Check if target can "see" p (within camera range and not hidden in grass)
        const dx = target.x - p.x; const dy = target.y - p.y;
        const viewRange = CAMERA_RANGE * GAME_TILE * 2;
        if (Math.sqrt(dx * dx + dy * dy) <= viewRange) {
          if (target.stunned < 1) {
            target.stunned = 1;
            target.effects.push({ type: 'stun', timer: 1 });
          }
        }
      }
      if (p.boiledOneTimer <= 0) {
        p.boiledOneActive = false;
        p.boiledOneTimer = 0;
      }
    }

    // Tick poison timers
    if (p.poisonTimers && p.poisonTimers.length > 0 && p.alive) {
      for (let pi = p.poisonTimers.length - 1; pi >= 0; pi--) {
        const pt = p.poisonTimers[pi];
        const poisonDmg = pt.dps * wallDt;
        p.hp -= poisonDmg;
        p.noDamageTimer = 0;
        p.isHealing = false;
        p.healTickTimer = 0;
        pt.remaining -= wallDt;
        if (pt.remaining <= 0) p.poisonTimers.splice(pi, 1);
      }
      if (p.hp <= 0 && p.alive) {
        p.hp = 0;
        p.alive = false;
        p.effects.push({ type: 'death', timer: 2 });
        if (p.id === localPlayerId) { freeCamX = p.x; freeCamY = p.y; spectateIndex = -1; }
      }
    }

    // Tick Unstable Eye timer
    if (p.unstableEyeTimer > 0) {
      p.unstableEyeTimer = Math.max(0, p.unstableEyeTimer - wallDt);
    }
  }

  // Update summon AI
  updateSummons(wallDt);

  // Zone shrink timer — use wall-clock so tab-switching doesn't pause it
  const zoneElapsed = (Date.now() - zonePhaseStart) / 1000;
  zoneTimer = Math.max(0, ZONE_INTERVAL - zoneElapsed);
  if (zoneTimer <= 0) {
    const maxInset = Math.floor(Math.min(gameMap.cols, gameMap.rows) / 2) - 2;
    if (zoneInset < maxInset) {
      zoneInset += (zoneInset < 3) ? 2 : 1;
      zoneInset = Math.min(zoneInset, maxInset);
      showPopup('⚠ ZONE CLOSING ⚠');
    }
    zonePhaseStart = Date.now();
    zoneTimer = ZONE_INTERVAL;
  }

  // Handle special aiming (only if alive)
  if (localPlayer.alive && localPlayer.specialAiming) {
    const cw = gameCanvas.width;
    const ch = gameCanvas.height;
    const camX = localPlayer.x - cw / 2;
    const camY = localPlayer.y - ch / 2;
    localPlayer.specialAimX = mouseX + camX;
    localPlayer.specialAimY = mouseY + camY;
    // Count down aim timer
    localPlayer.specialAimTimer -= dt;
    if (localPlayer.specialAimTimer <= 0 || mouseDown) {
      executeSpecialLanding();
    }
    // Skip normal movement while aiming, but continue world sim below
  }

  // Movement (only if alive and not stunned/aiming/channeling)
  if (localPlayer.alive && !localPlayer.specialAiming && localPlayer.stunned <= 0
      && !localPlayer.isCraftingChair && !localPlayer.isEatingChair) {
    updateMovement(dt);
  }

  // Update projectiles
  updateProjectiles(dt);

  // Tick combat log
  for (let i = combatLog.length - 1; i >= 0; i--) {
    combatLog[i].timer -= dt;
    if (combatLog[i].timer <= 0) combatLog.splice(i, 1);
  }

  // M1 – auto-fire while mouse held (only if alive)
  if (localPlayer.alive && mouseDown && localPlayer.cdM1 <= 0) {
    useAbility('M1');
  }

  // CPU AI update
  if (gameMode === 'fight') {
    updateCPUs(dt);
  }

  // Training dummy respawn
  if (gameMode === 'training' && dummyRespawnTimer > 0) {
    dummyRespawnTimer -= dt;
    if (dummyRespawnTimer <= 0) {
      dummyRespawnTimer = 0;
      // Remove old dummy
      const oldIdx = gamePlayers.findIndex(p => p.id === 'dummy');
      if (oldIdx >= 0) gamePlayers.splice(oldIdx, 1);
      // Spawn new dummy in center
      const centerR = Math.floor(gameMap.rows / 2);
      const centerC = Math.floor(gameMap.cols / 2);
      const dummyFighter = getFighter('fighter');
      const dummy = createPlayerState(
        { id: 'dummy', name: 'Training Dummy', color: '#555' },
        { r: centerR, c: centerC },
        dummyFighter
      );
      dummy.hp = 2000;
      dummy.maxHp = 2000;
      gamePlayers.push(dummy);
    }
  }
}

function tickCooldowns(p, dt) {
  if (p.cdM1 > 0) p.cdM1 = Math.max(0, p.cdM1 - dt);
  if (p.cdE > 0) p.cdE = Math.max(0, p.cdE - dt);
  if (p.cdR > 0) p.cdR = Math.max(0, p.cdR - dt);
  if (p.cdT > 0) p.cdT = Math.max(0, p.cdT - dt);
}

// ═══════════════════════════════════════════════════════════════
// MOVEMENT
// ═══════════════════════════════════════════════════════════════
function updateMovement(dt) {
  if (!localPlayer) return;

  let dx = 0, dy = 0;
  if (keys['ArrowUp']    || keys['w'] || keys['W']) dy -= 1;
  if (keys['ArrowDown']  || keys['s'] || keys['S']) dy += 1;
  if (keys['ArrowLeft']  || keys['a'] || keys['A']) dx -= 1;
  if (keys['ArrowRight'] || keys['d'] || keys['D']) dx += 1;

  if (dx !== 0 && dy !== 0) {
    const len = Math.sqrt(dx * dx + dy * dy);
    dx /= len;
    dy /= len;
  }

  let speed = localPlayer.fighter.speed;
  // Unstable Eye: 30% speed boost
  if (localPlayer.unstableEyeTimer > 0) speed *= 1.3;
  // Intimidation: move 1.5× faster when moving AWAY from intimidator
  if (localPlayer.intimidated > 0 && localPlayer.intimidatedBy) {
    const src = gamePlayers.find((p) => p.id === localPlayer.intimidatedBy);
    if (src) {
      const awayX = localPlayer.x - src.x;
      const awayY = localPlayer.y - src.y;
      const dot = dx * awayX + dy * awayY;
      if (dot > 0) speed *= 1.5; // moving away
    }
  }

  const newX = localPlayer.x + dx * speed;
  const newY = localPlayer.y + dy * speed;
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;

  if (canMoveTo(newX, localPlayer.y, radius)) localPlayer.x = newX;
  if (canMoveTo(localPlayer.x, newY, radius)) localPlayer.y = newY;
}

function canMoveTo(px, py, radius) {
  const offsets = [
    { x: -radius, y: -radius }, { x: radius, y: -radius },
    { x: -radius, y: radius },  { x: radius, y: radius },
  ];
  for (const off of offsets) {
    const col = Math.floor((px + off.x) / GAME_TILE);
    const row = Math.floor((py + off.y) / GAME_TILE);
    if (col < 0 || col >= gameMap.cols || row < 0 || row >= gameMap.rows) return false;
    const tile = gameMap.tiles[row][col];
    if (tile === TILE.ROCK || tile === TILE.WATER) return false;
  }
  return true;
}

// ═══════════════════════════════════════════════════════════════
// PROJECTILES
// ═══════════════════════════════════════════════════════════════
function updateProjectiles(dt) {
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;
  for (let i = projectiles.length - 1; i >= 0; i--) {
    const p = projectiles[i];
    p.timer -= dt;
    if (p.timer <= 0) { projectiles.splice(i, 1); continue; }

    // Move
    p.x += p.vx * dt;
    p.y += p.vy * dt;

    // Wall collision (rock blocks, out of bounds = sea destroys)
    const col = Math.floor(p.x / GAME_TILE);
    const row = Math.floor(p.y / GAME_TILE);
    if (col < 0 || col >= gameMap.cols || row < 0 || row >= gameMap.rows) {
      projectiles.splice(i, 1); continue;
    }
    const tile = gameMap.tiles[row][col];
    if (tile === TILE.ROCK) {
      projectiles.splice(i, 1); continue;
    }

    // Hit detection against players (owner's client resolves, or CPU projectiles resolve locally)
    const isCpuProj = p.ownerId && p.ownerId.startsWith('cpu-');
    if (p.ownerId === localPlayerId || isCpuProj) {
      const owner = isCpuProj ? gamePlayers.find(pl => pl.id === p.ownerId) : localPlayer;
      for (const target of gamePlayers) {
        if (target.id === p.ownerId || !target.alive) continue;
        const dx = target.x - p.x;
        const dy = target.y - p.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist < radius + 4) {
          dealDamage(owner, target, p.damage);
          // Log gamble card hits
          if (p.type === 'card') {
            combatLog.push({ text: '🎲 Gamble hit ' + target.name + ' for ' + p.damage + '!', timer: 4, color: '#f5a623' });
          }
          // Entanglement: stun + drag toward owner
          if (p.type === 'entangle' && owner) {
            const stunDur = p.stunDuration || 1.5;
            target.stunned = stunDur;
            target.effects.push({ type: 'stun', timer: stunDur });
            // Drag target toward the owner
            const dragDist = (p.dragDistance || 3) * GAME_TILE;
            const ddx = owner.x - target.x; const ddy = owner.y - target.y;
            const dDist = Math.sqrt(ddx * ddx + ddy * ddy) || 1;
            const dragNx = ddx / dDist; const dragNy = ddy / dDist;
            const actualDrag = Math.min(dragDist, dDist - GAME_TILE * PLAYER_RADIUS_RATIO * 2);
            if (actualDrag > 0) {
              const r = GAME_TILE * PLAYER_RADIUS_RATIO;
              for (let s = 10; s >= 1; s--) {
                const tryX = target.x + dragNx * actualDrag * (s / 10);
                const tryY = target.y + dragNy * actualDrag * (s / 10);
                if (canMoveTo(tryX, tryY, r)) { target.x = tryX; target.y = tryY; break; }
              }
            }
            if (typeof socket !== 'undefined' && socket.emit) {
              socket.emit('player-knockback', { targetId: target.id, x: target.x, y: target.y });
              socket.emit('player-debuff', { targetId: target.id, type: 'stun', duration: stunDur });
            }
            combatLog.push({ text: '⚔ Entangled ' + target.name + '!', timer: 3, color: '#00ff66' });
          }
          projectiles.splice(i, 1);
          break;
        }
      }
    }
  }
}

// ═══════════════════════════════════════════════════════════════
// SUMMON AI
// ═══════════════════════════════════════════════════════════════
function updateSummons(dt) {
  for (const s of gamePlayers) {
    if (!s.isSummon || !s.alive) continue;
    if (s.stunned > 0) continue;

    const owner = gamePlayers.find(p => p.id === s.summonOwner);
    const radius = GAME_TILE * PLAYER_RADIUS_RATIO;

    // Find nearest enemy (not owner, not fellow summons of same owner)
    let bestTarget = null;
    let bestDist = Infinity;
    for (const p of gamePlayers) {
      if (p.id === s.id || p.id === s.summonOwner || !p.alive) continue;
      if (p.isSummon && p.summonOwner === s.summonOwner) continue;
      const dx = p.x - s.x; const dy = p.y - s.y;
      const dist = Math.sqrt(dx * dx + dy * dy);
      if (dist < bestDist) { bestDist = dist; bestTarget = p; }
    }

    s.summonAttackTimer = Math.max(0, s.summonAttackTimer - dt);

    if (s.summonType === 'obelisk') {
      // Obelisk: stationary, touch = instant kill (except owner)
      for (const p of gamePlayers) {
        if (p.id === s.id || p.id === s.summonOwner || !p.alive) continue;
        if (p.isSummon && p.summonOwner === s.summonOwner) continue;
        const dx = p.x - s.x; const dy = p.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist < radius * 2.5) {
          dealDamage(owner || s, p, p.hp); // instant kill
          combatLog.push({ text: '⚱️ ' + p.name + ' touched the Obelisk!', timer: 4, color: '#d4af37' });
        }
      }
    } else if (s.summonType === 'macrocosms') {
      // Headless Macrocosms: very slow movement, melee attack with cooldown
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const speed = s.summonSpeed;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * speed;
        const newY = s.y + ny * speed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Attack when in range and off cooldown
        if (bestDist < radius * 2.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage);
          bestTarget.stunned = s.summonStunDur;
          bestTarget.effects.push({ type: 'stun', timer: s.summonStunDur });
          s.summonAttackTimer = s.summonAttackCD;
          combatLog.push({ text: '👁 Headless Macrocosms struck ' + bestTarget.name + '!', timer: 3, color: '#4a0080' });
        }
      }
    } else if (s.summonType === 'fleshbed') {
      // Fleshbed: medium speed, attack with stun on cooldown
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const speed = s.summonSpeed;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * speed;
        const newY = s.y + ny * speed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Attack within melee range
        if (bestDist < GAME_TILE * 1.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage);
          bestTarget.stunned = s.summonStunDur;
          bestTarget.effects.push({ type: 'stun', timer: s.summonStunDur });
          s.summonAttackTimer = s.summonAttackCD;
          s.effects.push({ type: 'chair-swing', timer: 0.2, aimNx: nx, aimNy: ny });
        }
      }
    } else if (s.summonType === 'zombie') {
      // Zombie: medium speed, melee slash only
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const speed = s.summonSpeed;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * speed;
        const newY = s.y + ny * speed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Slash attack within melee range
        if (bestDist < GAME_TILE * 1.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage);
          s.summonAttackTimer = s.summonAttackCD;
          s.effects.push({ type: 'zombie-slash', timer: 0.2, aimNx: nx, aimNy: ny });
        }
      }
    }

    // Clean up summon if owner died
    if (owner && !owner.alive) {
      s.alive = false;
      s.hp = 0;
      s.effects.push({ type: 'death', timer: 2 });
    }
  }
}

// ═══════════════════════════════════════════════════════════════
// CPU AI
// ═══════════════════════════════════════════════════════════════

// Difficulty tuning
const AI_PARAMS = {
  easy:   { thinkDelay: 1.2, aimError: 0.35, abilityDelay: 3.0, aggroRange: 7, retreatHp: 0.15, reactionTime: 0.8 },
  medium: { thinkDelay: 0.6, aimError: 0.18, abilityDelay: 1.5, aggroRange: 10, retreatHp: 0.25, reactionTime: 0.4 },
  hard:   { thinkDelay: 0.25, aimError: 0.06, abilityDelay: 0.7, aggroRange: 14, retreatHp: 0.35, reactionTime: 0.15 },
};

function updateCPUs(dt) {
  for (const cpu of gamePlayers) {
    if (!cpu.isCPU || !cpu.alive || cpu.stunned > 0) continue;
    const ai = cpu.aiState;
    const params = AI_PARAMS[cpu.difficulty] || AI_PARAMS.medium;

    // Tick cooldowns for CPU
    tickCooldowns(cpu, dt);

    // Tick CPU-specific buff/debuff timers
    if (cpu.blindBuff === 'dealer') {
      cpu.blindTimer += dt;
      if (cpu.blindTimer >= 3) { cpu.blindBuff = null; cpu.blindTimer = 0; }
    } else if (cpu.blindTimer > 0) {
      cpu.blindTimer = Math.max(0, cpu.blindTimer - dt);
      if (cpu.blindTimer <= 0 && cpu.blindBuff === 'big') cpu.blindBuff = null;
    }
    if (cpu.chipChangeTimer > 0) {
      cpu.chipChangeTimer = Math.max(0, cpu.chipChangeTimer - dt);
      if (cpu.chipChangeTimer <= 0) cpu.chipChangeDmg = -1;
    }

    // Think timer — re-evaluate target periodically
    ai.thinkTimer -= dt;
    if (ai.thinkTimer <= 0) {
      ai.thinkTimer = params.thinkDelay * (0.8 + Math.random() * 0.4);
      cpuChooseTarget(cpu, params);
    }

    // Update vision — track "last seen" positions of visible enemies
    cpuUpdateVision(cpu, params);

    // Movement (skip if channeling)
    if (!cpu.isCraftingChair && !cpu.isEatingChair) {
      cpuMove(cpu, dt, params);
    }

    // Combat
    ai.abilityTimer -= dt;
    if (ai.abilityTimer <= 0 && ai.attackTarget) {
      cpuAttack(cpu, params);
      ai.abilityTimer = params.abilityDelay * (0.7 + Math.random() * 0.6);
    }
  }
}

function cpuChooseTarget(cpu, params) {
  const ai = cpu.aiState;
  const aggroRange = params.aggroRange * GAME_TILE;

  // Find closest alive enemy within aggro range
  let bestTarget = null;
  let bestDist = Infinity;
  for (const p of gamePlayers) {
    if (p.id === cpu.id || !p.alive) continue;
    if (p.isSummon && p.summonOwner === cpu.id) continue; // skip own summons
    // Check if CPU can see the player (not hidden in grass)
    if (cpuIsHidden(p, cpu)) continue;
    const dx = p.x - cpu.x; const dy = p.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist < bestDist) {
      bestDist = dist;
      bestTarget = p;
    }
  }

  // If no visible target, check last-seen positions
  if (!bestTarget) {
    let newestTime = 0;
    for (const id in ai.lastSeenPositions) {
      const seen = ai.lastSeenPositions[id];
      const target = gamePlayers.find(p => p.id === id);
      if (!target || !target.alive) { delete ai.lastSeenPositions[id]; continue; }
      if (seen.time > newestTime) {
        newestTime = seen.time;
        ai.moveTarget = { x: seen.x, y: seen.y };
      }
    }
    ai.attackTarget = null;
    return;
  }

  ai.attackTarget = bestTarget;
  ai.moveTarget = null; // will chase attackTarget directly
}

function cpuIsHidden(target, observer) {
  // Check if target is hidden in grass from observer's perspective
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;
  const samplePoints = [
    { x: target.x, y: target.y },
    { x: target.x - radius, y: target.y }, { x: target.x + radius, y: target.y },
    { x: target.x, y: target.y - radius }, { x: target.x, y: target.y + radius },
  ];
  let grassCount = 0;
  for (const pt of samplePoints) {
    const col = Math.floor(pt.x / GAME_TILE);
    const row = Math.floor(pt.y / GAME_TILE);
    if (row >= 0 && row < gameMap.rows && col >= 0 && col < gameMap.cols
        && gameMap.tiles[row][col] === TILE.GRASS) grassCount++;
  }
  const grassFraction = grassCount / samplePoints.length;
  if (grassFraction <= 0.5) return false; // not hidden

  // Hidden, BUT check if observer saw them enter (last seen recently)
  const ai = observer.aiState;
  const seen = ai.lastSeenPositions[target.id];
  if (seen) {
    const dx = target.x - seen.x; const dy = target.y - seen.y;
    // If target is still near where we last saw them and it was recent
    if (Math.sqrt(dx * dx + dy * dy) < GAME_TILE * 2 && (Date.now() - seen.time) < 3000) {
      return false; // still "tracked"
    }
  }
  return true;
}

function cpuUpdateVision(cpu, params) {
  const ai = cpu.aiState;
  for (const p of gamePlayers) {
    if (p.id === cpu.id || !p.alive) continue;
    if (!cpuIsHidden(p, cpu)) {
      ai.lastSeenPositions[p.id] = { x: p.x, y: p.y, time: Date.now() };
    }
  }
}

function cpuMove(cpu, dt, params) {
  const ai = cpu.aiState;
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;
  let speed = cpu.fighter.speed;
  // Unstable Eye: 30% speed boost
  if (cpu.unstableEyeTimer > 0) speed *= 1.3;

  // Retreat if low HP
  ai.retreating = cpu.hp / cpu.maxHp < params.retreatHp;

  let goalX, goalY;

  if (ai.attackTarget && ai.attackTarget.alive) {
    const target = ai.attackTarget;
    const dx = target.x - cpu.x; const dy = target.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);

    if (ai.retreating) {
      // Run away from target
      goalX = cpu.x - dx / (dist || 1) * GAME_TILE * 3;
      goalY = cpu.y - dy / (dist || 1) * GAME_TILE * 3;
    } else {
      // Approach to ideal range based on fighter type
      const idealRange = cpu.fighter.id === 'poker' ? 5 * GAME_TILE : cpu.fighter.id === 'filbus' ? 1.5 * GAME_TILE : 1.2 * GAME_TILE;
      if (dist > idealRange + GAME_TILE) {
        // Move toward target
        goalX = target.x;
        goalY = target.y;
      } else if (dist < idealRange - GAME_TILE * 0.5) {
        // Too close, back off slightly
        goalX = cpu.x - dx / (dist || 1) * GAME_TILE;
        goalY = cpu.y - dy / (dist || 1) * GAME_TILE;
      } else {
        // At ideal range — strafe
        const perpX = -dy / (dist || 1);
        const perpY = dx / (dist || 1);
        goalX = cpu.x + perpX * ai.strafeDir * GAME_TILE * 2;
        goalY = cpu.y + perpY * ai.strafeDir * GAME_TILE * 2;
        // Randomly switch strafe direction
        if (Math.random() < 0.01) ai.strafeDir *= -1;
      }
    }
  } else if (ai.moveTarget) {
    goalX = ai.moveTarget.x;
    goalY = ai.moveTarget.y;
    // Clear move target if reached
    const dx = goalX - cpu.x; const dy = goalY - cpu.y;
    if (Math.sqrt(dx * dx + dy * dy) < GAME_TILE) {
      ai.moveTarget = null;
    }
  } else {
    // Wander toward zone center
    const centerX = (gameMap.cols / 2) * GAME_TILE;
    const centerY = (gameMap.rows / 2) * GAME_TILE;
    goalX = centerX + (Math.random() - 0.5) * GAME_TILE * 4;
    goalY = centerY + (Math.random() - 0.5) * GAME_TILE * 4;
  }

  if (goalX === undefined) return;

  let moveX = goalX - cpu.x;
  let moveY = goalY - cpu.y;
  const moveDist = Math.sqrt(moveX * moveX + moveY * moveY);
  if (moveDist < 2) return;
  moveX /= moveDist;
  moveY /= moveDist;

  // Stay in zone — strongly prefer moving toward zone center if out of bounds
  if (zoneInset > 0) {
    const pCol = Math.floor(cpu.x / GAME_TILE);
    const pRow = Math.floor(cpu.y / GAME_TILE);
    if (pCol < zoneInset + 1 || pCol >= gameMap.cols - zoneInset - 1 ||
        pRow < zoneInset + 1 || pRow >= gameMap.rows - zoneInset - 1) {
      const centerX = (gameMap.cols / 2) * GAME_TILE;
      const centerY = (gameMap.rows / 2) * GAME_TILE;
      const toCenter = Math.sqrt((centerX - cpu.x) ** 2 + (centerY - cpu.y) ** 2) || 1;
      moveX = (centerX - cpu.x) / toCenter;
      moveY = (centerY - cpu.y) / toCenter;
    }
  }

  // Use cover: prefer moving through grass if nearby
  const grassBias = 0.3;
  for (let angle = -1; angle <= 1; angle += 2) {
    const testX = cpu.x + (moveX * Math.cos(angle * 0.5) - moveY * Math.sin(angle * 0.5)) * GAME_TILE;
    const testY = cpu.y + (moveX * Math.sin(angle * 0.5) + moveY * Math.cos(angle * 0.5)) * GAME_TILE;
    const testCol = Math.floor(testX / GAME_TILE);
    const testRow = Math.floor(testY / GAME_TILE);
    if (testRow >= 0 && testRow < gameMap.rows && testCol >= 0 && testCol < gameMap.cols) {
      if (gameMap.tiles[testRow][testCol] === TILE.GRASS && !ai.attackTarget) {
        const toGrassX = testX - cpu.x;
        const toGrassY = testY - cpu.y;
        const toGrassDist = Math.sqrt(toGrassX * toGrassX + toGrassY * toGrassY) || 1;
        moveX = moveX * (1 - grassBias) + (toGrassX / toGrassDist) * grassBias;
        moveY = moveY * (1 - grassBias) + (toGrassY / toGrassDist) * grassBias;
        break;
      }
    }
  }

  const newX = cpu.x + moveX * speed;
  const newY = cpu.y + moveY * speed;
  if (canMoveTo(newX, cpu.y, radius)) cpu.x = newX;
  if (canMoveTo(cpu.x, newY, radius)) cpu.y = newY;
}

function cpuAttack(cpu, params) {
  const ai = cpu.aiState;
  const target = ai.attackTarget;
  if (!target || !target.alive) return;

  const dx = target.x - cpu.x; const dy = target.y - cpu.y;
  const dist = Math.sqrt(dx * dx + dy * dy);
  const fighter = cpu.fighter;
  const isPoker = fighter.id === 'poker';
  const isFilbus = fighter.id === 'filbus';
  const is1x = fighter.id === 'onexonexonex';

  // Add aim error based on difficulty
  const errorAngle = (Math.random() - 0.5) * params.aimError * 2;
  const baseAngle = Math.atan2(dy, dx);
  const aimAngle = baseAngle + errorAngle;
  const aimNx = Math.cos(aimAngle);
  const aimNy = Math.sin(aimAngle);

  // Try to use abilities in priority order: Special > R > E > T > M1
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;

  // Special
  if (cpu.specialUnlocked && !cpu.specialUsed) {
    if (isPoker) {
      const closeRange = 3 * GAME_TILE;
      const mediumRange = 10 * GAME_TILE;
      if (dist < mediumRange) {
        cpuUseSpecialPoker(cpu, params);
        return;
      }
    } else if (isFilbus) {
      // Boiled One: use when enemies nearby
      cpuUseSpecialFilbus(cpu);
      return;
    } else if (is1x) {
      cpuUseSpecial1x(cpu);
      return;
    } else {
      if (dist < 10 * GAME_TILE) {
        cpuUseSpecialFighter(cpu, target);
        return;
      }
    }
  }

  // E ability
  if (cpu.cdE <= 0) {
    if (isPoker) {
      if (dist < 12 * GAME_TILE) {
        cpuFireProjectile(cpu, target, 'card', aimAngle);
        return;
      }
    } else if (isFilbus) {
      // Filbism (1): craft chair when not in combat range and no chairs
      if (dist > 4 * GAME_TILE && cpu.chairCharges <= 0 && !cpu.isCraftingChair) {
        cpu.isCraftingChair = true;
        cpu.craftTimer = fighter.abilities[1].channelTime || 10;
        return;
      }
    } else if (is1x) {
      // Entanglement: throw swords if in range
      if (dist < 8 * GAME_TILE) {
        cpu1xEntangle(cpu, target, aimAngle);
        return;
      }
    } else {
      cpu.cdE = fighter.abilities[1].cooldown;
      cpu.supportBuff = fighter.abilities[1].duration;
      cpu.effects.push({ type: 'support', timer: 1.5 });
      return;
    }
  }

  // R ability
  if (cpu.cdR <= 0) {
    if (isPoker) {
      cpu.cdR = fighter.abilities[2].cooldown;
      const roll = Math.random();
      if (roll < 0.70) { cpu.blindBuff = 'small'; cpu.blindTimer = 0; }
      else if (roll < 0.90) { cpu.blindBuff = 'big'; cpu.blindTimer = 60; }
      else { cpu.blindBuff = 'dealer'; cpu.blindTimer = 0; cpu.cdE = 0; }
      cpu.effects.push({ type: 'blind-small', timer: 1.0 });
      return;
    } else if (isFilbus) {
      // Filbism (2): eat chair to heal when hurt
      if (cpu.chairCharges > 0 && cpu.hp < cpu.maxHp * 0.6 && !cpu.isEatingChair) {
        cpu.isEatingChair = true;
        cpu.eatTimer = fighter.abilities[2].channelTime || 3;
        cpu.eatHealPool = fighter.abilities[2].healAmount || 100;
        cpu.chairCharges--;
        return;
      }
    } else if (is1x) {
      // Mass Infection: wide attack when enemies nearby
      if (dist < (fighter.abilities[2].range || 4) * GAME_TILE) {
        cpu1xMassInfection(cpu, target, aimNx, aimNy);
        return;
      }
    } else {
      if (dist < fighter.abilities[2].range * GAME_TILE) {
        cpuPowerSwing(cpu, target, aimNx, aimNy);
        return;
      }
    }
  }

  // T ability
  if (cpu.cdT <= 0 && Math.random() < 0.3) {
    if (isPoker) {
      cpu.cdT = fighter.abilities[3].cooldown;
      const options = [50, 100, 200, 300, 400];
      cpu.chipChangeDmg = options[Math.floor(Math.random() * options.length)];
      cpu.chipChangeTimer = fighter.abilities[3].duration || 30;
      return;
    } else if (isFilbus) {
      // Oddity Overthrow: summon a companion
      if (!cpu.summonId) {
        cpu.cdT = fighter.abilities[3].cooldown;
        const abil = fighter.abilities[3];
        const companionKeys = Object.keys(abil.companions);
        const pick = companionKeys[Math.floor(Math.random() * companionKeys.length)];
        const compDef = abil.companions[pick];
        const summonId = 'summon-' + cpu.id + '-' + Date.now();
        const summon = {
          id: summonId,
          name: compDef.name,
          color: pick === 'fleshbed' ? '#8b4513' : pick === 'macrocosms' ? '#4a0080' : '#d4af37',
          x: cpu.x + (Math.random() - 0.5) * GAME_TILE * 2,
          y: cpu.y + (Math.random() - 0.5) * GAME_TILE * 2,
          hp: compDef.hp, maxHp: compDef.hp,
          fighter: fighter, alive: true,
          cdM1: 0, cdE: 0, cdR: 0, cdT: 0,
          totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
          supportBuff: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
          noDamageTimer: 0, healTickTimer: 0, isHealing: false,
          specialJumping: false, specialAiming: false,
          specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
          effects: [],
          blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
          chairCharges: 0, isCraftingChair: false, craftTimer: 0,
          isEatingChair: false, eatTimer: 0, eatHealPool: 0,
          summonId: null, boiledOneActive: false, boiledOneTimer: 0,
          poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
          isSummon: true, summonOwner: cpu.id, summonType: pick,
          summonSpeed: compDef.speed, summonDamage: compDef.damage,
          summonStunDur: compDef.stunDuration, summonAttackCD: compDef.attackCooldown,
          summonAttackTimer: 0,
        };
        if (pick === 'obelisk') {
          summon.x = cpu.x;
          summon.y = cpu.y;
        }
        gamePlayers.push(summon);
        cpu.summonId = summonId;
        cpu.effects.push({ type: 'summon', timer: 1.5 });
        return;
      }
    } else if (is1x) {
      // Unstable Eye: use when enemy is nearby
      if (cpu.unstableEyeTimer <= 0 && dist < 6 * GAME_TILE) {
        cpu.cdT = fighter.abilities[3].cooldown;
        cpu.unstableEyeTimer = fighter.abilities[3].duration || 6;
        cpu.effects.push({ type: 'unstable-eye', timer: fighter.abilities[3].duration || 6 });
        return;
      }
    } else {
      const sightRange = CAMERA_RANGE * GAME_TILE * 2;
      if (dist <= sightRange) {
        cpu.cdT = fighter.abilities[3].cooldown;
        for (const t of gamePlayers) {
          if (t.id === cpu.id || !t.alive) continue;
          const d = Math.sqrt((t.x - cpu.x) ** 2 + (t.y - cpu.y) ** 2);
          if (d <= sightRange) {
            t.intimidated = fighter.abilities[3].duration;
            t.intimidatedBy = cpu.id;
          }
        }
        cpu.effects.push({ type: 'intimidation', timer: 1.0 });
        return;
      }
    }
  }

  // M1 — primary attack
  if (cpu.cdM1 <= 0) {
    if (isPoker) {
      if (dist < 8 * GAME_TILE) {
        cpuFireChips(cpu, target, aimAngle);
      }
    } else if (isFilbus) {
      // Chair swing
      if (dist < (fighter.abilities[0].range || 1.8) * GAME_TILE) {
        cpuChairSwing(cpu, target, aimNx, aimNy);
      }
    } else if (is1x) {
      // 1x Slash
      if (dist < (fighter.abilities[0].range || 1.5) * GAME_TILE) {
        cpu1xSlash(cpu, target, aimNx, aimNy);
      }
    } else {
      if (dist < fighter.abilities[0].range * GAME_TILE) {
        cpuSwordSwing(cpu, target, aimNx, aimNy);
      }
    }
  }
}

function cpuFireProjectile(cpu, target, type, aimAngle) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[1]; // E = Gamble
  cpu.cdE = abil.cooldown;
  // Weighted damage
  const roll = Math.random();
  let dmg;
  if (roll < 0.60) dmg = 100 + Math.floor(Math.random() * 4) * 100;
  else if (roll < 0.85) dmg = 500 + Math.floor(Math.random() * 3) * 100;
  else if (roll < 0.95) dmg = 800 + Math.floor(Math.random() * 2) * 100;
  else dmg = 1000;
  if (cpu.supportBuff > 0) dmg *= 1.5;
  if (cpu.intimidated > 0) dmg *= 0.5;
  const spd = (abil.projectileSpeed || 18) * GAME_TILE / 10;
  projectiles.push({
    x: cpu.x, y: cpu.y,
    vx: Math.cos(aimAngle) * spd, vy: Math.sin(aimAngle) * spd,
    ownerId: cpu.id, damage: Math.round(dmg), timer: 999, type: 'card',
  });
  if (cpu.blindBuff === 'small') cpu.blindBuff = null;
  cpu.effects.push({ type: 'gamble', timer: 0.5 });
}

function cpuFireChips(cpu, target, aimAngle) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[0]; // M1
  cpu.cdM1 = abil.cooldown;
  const count = abil.projectileCount || 3;
  const spread = abil.projectileSpread || 0.15;
  let dmg = abil.damage;
  if (cpu.chipChangeDmg >= 0) dmg = cpu.chipChangeDmg;
  if (cpu.supportBuff > 0) dmg *= 1.5;
  if (cpu.intimidated > 0) dmg *= 0.5;
  for (let i = 0; i < count; i++) {
    const angle = aimAngle + (i - (count - 1) / 2) * spread;
    const spd = (abil.projectileSpeed || 8) * GAME_TILE / 10;
    projectiles.push({
      x: cpu.x, y: cpu.y,
      vx: Math.cos(angle) * spd, vy: Math.sin(angle) * spd,
      ownerId: cpu.id, damage: dmg, timer: 0.8, type: 'chip',
    });
  }
  if (cpu.blindBuff === 'small') cpu.blindBuff = null;
  cpu.effects.push({ type: 'chip-throw', timer: 0.2 });
}

function cpuSwordSwing(cpu, target, aimNx, aimNy) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[0];
  cpu.cdM1 = abil.cooldown;
  const range = abil.range * GAME_TILE;
  let baseDmg = abil.damage;
  if (cpu.supportBuff > 0) baseDmg *= 1.5;
  if (cpu.intimidated > 0) baseDmg *= 0.5;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    const dx = t.x - cpu.x; const dy = t.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > range) continue;
    const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
    if (dot < 0) continue;
    dealDamage(cpu, t, baseDmg);
  }
  cpu.effects.push({ type: 'sword', timer: 0.2, aimNx, aimNy });
}

function cpuPowerSwing(cpu, target, aimNx, aimNy) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[2];
  cpu.cdR = abil.cooldown;
  const range = abil.range * GAME_TILE;
  let baseDmg = abil.damage;
  if (cpu.supportBuff > 0) baseDmg *= 1.5;
  if (cpu.intimidated > 0) baseDmg *= 0.5;
  const r = GAME_TILE * PLAYER_RADIUS_RATIO;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    const dx = t.x - cpu.x; const dy = t.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > range) continue;
    dealDamage(cpu, t, baseDmg);
    const kbDist = (abil.knockback || 3) * GAME_TILE;
    const kbNx = dx / (dist || 1); const kbNy = dy / (dist || 1);
    for (let s = 10; s >= 1; s--) {
      const tryX = t.x + kbNx * kbDist * (s / 10);
      const tryY = t.y + kbNy * kbDist * (s / 10);
      if (canMoveTo(tryX, tryY, r)) { t.x = tryX; t.y = tryY; break; }
      if (s === 1) { /* stay */ }
    }
  }
  cpu.effects.push({ type: 'power-arc', timer: 0.3 });
}

function cpuUseSpecialPoker(cpu, params) {
  const fighter = cpu.fighter;
  cpu.specialUsed = true;
  cpu.hp = cpu.maxHp;
  const stunDur = fighter.abilities[4].stunDuration || 3;
  const execThresh = fighter.abilities[4].executeThreshold || 500;
  const closeRange = 3 * GAME_TILE;
  const mediumRange = (fighter.abilities[4].range || 10) * GAME_TILE;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    const dx = t.x - cpu.x; const dy = t.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > mediumRange) continue;
    if (dist <= closeRange) {
      if (t.hp <= execThresh) { dealDamage(cpu, t, t.hp); }
      else { t.stunned = stunDur; t.effects.push({ type: 'stun', timer: stunDur }); }
    }
    t.cdM1 = t.fighter.abilities[0].cooldown;
    t.cdE = t.fighter.abilities[1].cooldown;
    t.cdR = t.fighter.abilities[2].cooldown;
    t.cdT = t.fighter.abilities[3].cooldown;
    t.specialUnlocked = false; t.totalDamageTaken = 0;
    t.supportBuff = 0; t.chipChangeDmg = -1; t.chipChangeTimer = 0;
    t.blindBuff = null; t.blindTimer = 0;
  }
  cpu.effects.push({ type: 'royal-flush', timer: 2.0 });
}

function cpuUseSpecialFighter(cpu, target) {
  // CPU does a simpler instant jump toward target (no aiming phase)
  const fighter = cpu.fighter;
  const abil = fighter.abilities[4];
  cpu.specialUsed = true;
  const landX = target.x;
  const landY = target.y;
  const hitRange = GAME_TILE * 1.2;
  let hitSomeone = false;
  let baseDmg = abil.damage;
  if (cpu.supportBuff > 0) baseDmg *= 1.5;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    const dx = t.x - landX; const dy = t.y - landY;
    if (Math.sqrt(dx * dx + dy * dy) < hitRange) {
      dealDamage(cpu, t, baseDmg);
      hitSomeone = true;
    }
  }
  const r = GAME_TILE * PLAYER_RADIUS_RATIO;
  if (canMoveTo(landX, landY, r)) { cpu.x = landX; cpu.y = landY; }
  if (!hitSomeone) {
    cpu.stunned = abil.missStun;
    cpu.hp = Math.max(0, cpu.hp - abil.missDamage);
    if (cpu.hp <= 0) { cpu.alive = false; cpu.hp = 0; cpu.effects.push({ type: 'death', timer: 2 }); }
    cpu.effects.push({ type: 'stun', timer: abil.missStun });
  }
  cpu.effects.push({ type: 'land', timer: 0.5 });
}

function cpuChairSwing(cpu, target, aimNx, aimNy) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[0];
  cpu.cdM1 = abil.cooldown;
  // Cancel channels
  cpu.isCraftingChair = false;
  cpu.craftTimer = 0;
  cpu.isEatingChair = false;
  cpu.eatTimer = 0;

  const isTable = Math.random() < (abil.tableChance || 0.05);
  const range = (isTable ? (abil.tableRange || 2.5) : (abil.range || 1.8)) * GAME_TILE;
  let baseDmg = isTable ? (abil.tableDamage || 400) : (abil.damage || 250);
  if (cpu.supportBuff > 0) baseDmg *= 1.5;
  if (cpu.intimidated > 0) baseDmg *= 0.5;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    if (t.isSummon && t.summonOwner === cpu.id) continue;
    const dx = t.x - cpu.x; const dy = t.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > range) continue;
    const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
    if (dot < 0) continue;
    dealDamage(cpu, t, baseDmg);
  }
  cpu.effects.push({ type: isTable ? 'table-swing' : 'chair-swing', timer: 0.2, aimNx, aimNy });
}

function cpuUseSpecialFilbus(cpu) {
  const fighter = cpu.fighter;
  cpu.specialUsed = true;
  cpu.boiledOneActive = true;
  const stunDur = fighter.abilities[4].stunDuration || 10;
  cpu.boiledOneTimer = stunDur;
  for (const t of gamePlayers) {
    if (!t.alive || t.isSummon) continue;
    if (t.id === cpu.id) continue; // Filbus is immune
    t.stunned = stunDur;
    t.effects.push({ type: 'stun', timer: stunDur });
  }
  cpu.effects.push({ type: 'boiled-one', timer: stunDur + 1 });
}

function cpu1xSlash(cpu, target, aimNx, aimNy) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[0];
  cpu.cdM1 = abil.cooldown;
  const range = (abil.range || 1.5) * GAME_TILE;
  let baseDmg = abil.damage;
  if (cpu.supportBuff > 0) baseDmg *= 1.5;
  if (cpu.intimidated > 0) baseDmg *= 0.5;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    if (t.isSummon && t.summonOwner === cpu.id) continue;
    const dx = t.x - cpu.x; const dy = t.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > range) continue;
    const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
    if (dot < 0) continue;
    dealDamage(cpu, t, baseDmg);
    if (!t.poisonTimers) t.poisonTimers = [];
    t.poisonTimers.push({ sourceId: cpu.id, dps: abil.poisonDPS || 50, remaining: abil.poisonDuration || 3 });
    t.effects.push({ type: 'poison', timer: abil.poisonDuration || 3 });
  }
  cpu.effects.push({ type: 'slash-1x', timer: 0.2, aimNx, aimNy });
}

function cpu1xEntangle(cpu, target, aimAngle) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[1];
  cpu.cdE = abil.cooldown;
  const spd = (abil.projectileSpeed || 25) * GAME_TILE / 10;
  const evx = Math.cos(aimAngle) * spd;
  const evy = Math.sin(aimAngle) * spd;
  projectiles.push({
    x: cpu.x, y: cpu.y, vx: evx, vy: evy,
    ownerId: cpu.id, damage: abil.damage,
    timer: 1.5, type: 'entangle',
    stunDuration: abil.stunDuration || 1.5,
    dragDistance: abil.dragDistance || 3,
  });
  cpu.effects.push({ type: 'entangle-cast', timer: 0.5 });
}

function cpu1xMassInfection(cpu, target, aimNx, aimNy) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[2];
  cpu.cdR = abil.cooldown;
  const range = (abil.range || 4) * GAME_TILE;
  let baseDmg = abil.damage;
  if (cpu.supportBuff > 0) baseDmg *= 1.5;
  if (cpu.intimidated > 0) baseDmg *= 0.5;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    if (t.isSummon && t.summonOwner === cpu.id) continue;
    const dx = t.x - cpu.x; const dy = t.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > range) continue;
    const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
    if (dot < -0.1) continue;
    dealDamage(cpu, t, baseDmg);
    if (!t.poisonTimers) t.poisonTimers = [];
    t.poisonTimers.push({ sourceId: cpu.id, dps: abil.poisonDPS || 50, remaining: abil.poisonDuration || 3 });
    t.effects.push({ type: 'poison', timer: abil.poisonDuration || 3 });
  }
  cpu.effects.push({ type: 'mass-infection', timer: 0.6, aimNx, aimNy });
}

function cpuUseSpecial1x(cpu) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[4];
  cpu.specialUsed = true;
  let deadCount = 0;
  for (const p of gamePlayers) {
    if (!p.alive && !p.isSummon) deadCount++;
  }
  const zombieCount = (abil.baseZombies || 5) + deadCount;
  // Clear old zombies
  for (let zi = gamePlayers.length - 1; zi >= 0; zi--) {
    if (gamePlayers[zi].isSummon && gamePlayers[zi].summonType === 'zombie' && gamePlayers[zi].summonOwner === cpu.id) {
      gamePlayers.splice(zi, 1);
    }
  }
  cpu.zombieIds = [];
  for (let z = 0; z < zombieCount; z++) {
    const zombieId = 'zombie-' + cpu.id + '-' + Date.now() + '-' + z;
    let zx, zy;
    for (let attempts = 0; attempts < 50; attempts++) {
      zx = (Math.floor(Math.random() * gameMap.cols) + 0.5) * GAME_TILE;
      zy = (Math.floor(Math.random() * gameMap.rows) + 0.5) * GAME_TILE;
      if (canMoveTo(zx, zy, GAME_TILE * PLAYER_RADIUS_RATIO)) break;
    }
    const zombie = {
      id: zombieId, name: 'Zombie', color: '#1a5c1a',
      x: zx, y: zy,
      hp: abil.zombieHp || 500, maxHp: abil.zombieHp || 500,
      fighter: fighter, alive: true,
      cdM1: 0, cdE: 0, cdR: 0, cdT: 0,
      totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
      supportBuff: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
      noDamageTimer: 0, healTickTimer: 0, isHealing: false,
      specialJumping: false, specialAiming: false,
      specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
      effects: [],
      blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
      chairCharges: 0, isCraftingChair: false, craftTimer: 0,
      isEatingChair: false, eatTimer: 0, eatHealPool: 0,
      summonId: null, boiledOneActive: false, boiledOneTimer: 0,
      poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
      isSummon: true, summonOwner: cpu.id, summonType: 'zombie',
      summonSpeed: abil.zombieSpeed || 2.0,
      summonDamage: abil.zombieDamage || 100,
      summonStunDur: 0, summonAttackCD: 4.0, summonAttackTimer: 0,
    };
    gamePlayers.push(zombie);
    cpu.zombieIds.push(zombieId);
  }
  cpu.effects.push({ type: 'rejuvenate', timer: 2.0 });
}

// ═══════════════════════════════════════════════════════════════
// ABILITIES
// ═══════════════════════════════════════════════════════════════
function useAbility(key) {
  const lp = localPlayer;
  if (!lp || !lp.alive || lp.stunned > 0) return;

  const fighter = lp.fighter;
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;
  const isPoker = fighter.id === 'poker';
  const isFilbus = fighter.id === 'filbus';
  const is1x = fighter.id === 'onexonexonex';

  // Filbus: channeling interrupts
  if (isFilbus && (key !== 'E' && key !== 'R')) {
    lp.isCraftingChair = false;
    lp.craftTimer = 0;
    lp.isEatingChair = false;
    lp.eatTimer = 0;
    lp.eatHealPool = 0;
  }

  if (key === 'M1') {
    if (lp.cdM1 > 0) return;
    const abil = fighter.abilities[0];
    lp.cdM1 = abil.cooldown;

    if (isPoker) {
      // Chip Throw: fire 3 projectiles toward mouse
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const baseAngle = Math.atan2(aimDy, aimDx);
      const count = abil.projectileCount || 3;
      const spread = abil.projectileSpread || 0.15;
      let dmg = abil.damage;
      if (lp.chipChangeDmg >= 0) dmg = lp.chipChangeDmg;
      if (lp.supportBuff > 0) dmg *= 1.5;
      if (lp.intimidated > 0) dmg *= 0.5;
      const spawnedChips = [];
      for (let i = 0; i < count; i++) {
        const angle = baseAngle + (i - (count - 1) / 2) * spread;
        const vx = Math.cos(angle) * (abil.projectileSpeed || 8) * GAME_TILE / 10;
        const vy = Math.sin(angle) * (abil.projectileSpeed || 8) * GAME_TILE / 10;
        const proj = { x: lp.x, y: lp.y, vx, vy, ownerId: lp.id, damage: dmg, timer: 0.8, type: 'chip' };
        projectiles.push(proj);
        spawnedChips.push({ x: proj.x, y: proj.y, vx, vy, timer: 0.8, type: 'chip' });
      }
      // Visual sync to other clients
      if (typeof socket !== 'undefined' && socket.emit) {
        socket.emit('projectile-spawn', { projectiles: spawnedChips });
      }
      // Clear small blind when using another move
      if (lp.blindBuff === 'small') lp.blindBuff = null;
      lp.effects.push({ type: 'chip-throw', timer: 0.2 });
    } else if (isFilbus) {
      // Filbus: Swing Chair (rare table chance)
      const isTable = Math.random() < (abil.tableChance || 0.05);
      const range = (isTable ? (abil.tableRange || 2.5) : (abil.range || 1.8)) * GAME_TILE;
      let baseDmg = isTable ? (abil.tableDamage || 400) : (abil.damage || 250);
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        dealDamage(lp, target, baseDmg);
      }
      if (isTable) {
        combatLog.push({ text: '🪑 TABLE SWING! 400 dmg!', timer: 3, color: '#ff6600' });
        lp.effects.push({ type: 'table-swing', timer: 0.3, aimNx, aimNy });
      } else {
        lp.effects.push({ type: 'chair-swing', timer: 0.2, aimNx, aimNy });
      }
    } else if (is1x) {
      // 1X1X1X1: Slash — melee + poison
      const range = (abil.range || 1.5) * GAME_TILE;
      let baseDmg = abil.damage;
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        dealDamage(lp, target, baseDmg);
        // Apply poison
        if (!target.poisonTimers) target.poisonTimers = [];
        target.poisonTimers.push({ sourceId: lp.id, dps: abil.poisonDPS || 50, remaining: abil.poisonDuration || 3 });
        target.effects.push({ type: 'poison', timer: abil.poisonDuration || 3 });
      }
      lp.effects.push({ type: 'slash-1x', timer: 0.2, aimNx, aimNy });
    } else {
      // Fighter: Sword (original M1)
      const range = abil.range * GAME_TILE;
      let baseDmg = abil.damage;
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        dealDamage(lp, target, baseDmg);
      }
      lp.effects.push({ type: 'sword', timer: 0.2, aimNx, aimNy });
    }
  }

  else if (key === 'E') {
    if (lp.cdE > 0) return;
    const abil = fighter.abilities[1];
    lp.cdE = abil.cooldown;

    if (isPoker) {
      // Gamble: throw a card with weighted random damage
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const angle = Math.atan2(aimDy, aimDx);
      // Weighted: 100-400 common, 500-1000 rare
      const roll = Math.random();
      let dmg;
      if (roll < 0.60) dmg = 100 + Math.floor(Math.random() * 4) * 100; // 100-400
      else if (roll < 0.85) dmg = 500 + Math.floor(Math.random() * 3) * 100; // 500-700
      else if (roll < 0.95) dmg = 800 + Math.floor(Math.random() * 2) * 100; // 800-900
      else dmg = 1000; // 5% chance
      if (lp.supportBuff > 0) dmg *= 1.5;
      if (lp.intimidated > 0) dmg *= 0.5;
      const cvx = Math.cos(angle) * (abil.projectileSpeed || 18) * GAME_TILE / 10;
      const cvy = Math.sin(angle) * (abil.projectileSpeed || 18) * GAME_TILE / 10;
      projectiles.push({
        x: lp.x, y: lp.y, vx: cvx, vy: cvy,
        ownerId: lp.id, damage: Math.round(dmg),
        timer: 999, type: 'card',
      });
      // Visual sync
      if (typeof socket !== 'undefined' && socket.emit) {
        socket.emit('projectile-spawn', { projectiles: [{ x: lp.x, y: lp.y, vx: cvx, vy: cvy, timer: 999, type: 'card' }] });
      }
      // Clear small blind when using another move
      if (lp.blindBuff === 'small') lp.blindBuff = null;
      lp.effects.push({ type: 'gamble', timer: 0.5 });
    } else if (isFilbus) {
      // Filbus E: Filbism (1) — start crafting a chair (10s channel)
      // No cooldown needed; channeling is the gate
      lp.cdE = 0; // refund the cooldown we set above
      if (lp.isCraftingChair) {
        // Cancel crafting
        lp.isCraftingChair = false;
        lp.craftTimer = 0;
        combatLog.push({ text: '🪑 Chair crafting cancelled', timer: 2, color: '#999' });
      } else {
        lp.isCraftingChair = true;
        lp.craftTimer = abil.channelTime || 10;
        lp.isEatingChair = false;
        lp.eatTimer = 0;
        combatLog.push({ text: '🪑 Crafting a chair...', timer: 2, color: '#c8a96e' });
        lp.effects.push({ type: 'crafting', timer: (abil.channelTime || 10) + 0.5 });
      }
    } else if (is1x) {
      // 1X1X1X1 E: Entanglement — throw swords in a line, stun + drag target
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const angle = Math.atan2(aimDy, aimDx);
      const spd = (abil.projectileSpeed || 25) * GAME_TILE / 10;
      const evx = Math.cos(angle) * spd;
      const evy = Math.sin(angle) * spd;
      projectiles.push({
        x: lp.x, y: lp.y, vx: evx, vy: evy,
        ownerId: lp.id, damage: abil.damage,
        timer: 1.5, type: 'entangle',
        stunDuration: abil.stunDuration || 1.5,
        dragDistance: abil.dragDistance || 3,
      });
      if (typeof socket !== 'undefined' && socket.emit) {
        socket.emit('projectile-spawn', { projectiles: [{ x: lp.x, y: lp.y, vx: evx, vy: evy, timer: 1.5, type: 'entangle' }] });
      }
      lp.effects.push({ type: 'entangle-cast', timer: 0.5 });
      combatLog.push({ text: '⚔ Entanglement!', timer: 2, color: '#00ff66' });
    } else {
      // Fighter: Support buff
      lp.supportBuff = abil.duration;
      lp.effects.push({ type: 'support', timer: 1.5 });
      if (typeof socket !== 'undefined' && socket.emit) {
        socket.emit('player-buff', { type: 'support', duration: abil.duration });
      }
    }
  }

  else if (key === 'R') {
    if (lp.cdR > 0) return;
    const abil = fighter.abilities[2];
    lp.cdR = abil.cooldown;

    if (isPoker) {
      // Blinds: random outcome
      const roll = Math.random();
      if (roll < 0.70) {
        // Small blind: half damage taken until another move is used
        lp.blindBuff = 'small';
        lp.blindTimer = 0;
        showPopup('🛡 Small Blind — ½ damage taken!');
        lp.effects.push({ type: 'blind-small', timer: 2.0 });
      } else if (roll < 0.90) {
        // Big blind: 1.5× damage taken for 60 seconds
        lp.blindBuff = 'big';
        lp.blindTimer = 60;
        showPopup('⚠ Big Blind — 1.5× damage for 60s!');
        lp.effects.push({ type: 'blind-big', timer: 2.0 });
      } else {
        // Dealer: reset Gamble cooldown, no blind buff
        lp.blindBuff = 'dealer';
        lp.blindTimer = 0;
        lp.cdE = 0; // reset Gamble cooldown
        showPopup('🎰 Dealer! Gamble reset!');
        lp.effects.push({ type: 'blind-dealer', timer: 2.0 });
      }
      // Broadcast blind to other clients
      if (typeof socket !== 'undefined' && socket.emit) {
        socket.emit('player-buff', { type: 'blind', duration: lp.blindBuff === 'big' ? 60 : 0 });
      }
    } else if (isFilbus) {
      // Filbus R: Filbism (2) — eat a chair to heal 100 HP over 3s
      lp.cdR = 0; // refund cooldown
      if (lp.isEatingChair) {
        // Cancel eating
        lp.isEatingChair = false;
        lp.eatTimer = 0;
        lp.eatHealPool = 0;
        combatLog.push({ text: '🪑 Stopped eating chair', timer: 2, color: '#999' });
      } else if (lp.chairCharges <= 0) {
        combatLog.push({ text: '🪑 No chairs to eat!', timer: 2, color: '#e94560' });
      } else {
        lp.isEatingChair = true;
        lp.eatTimer = abil.channelTime || 3;
        lp.eatHealPool = abil.healAmount || 100;
        lp.isCraftingChair = false;
        lp.craftTimer = 0;
        lp.chairCharges--;
        combatLog.push({ text: '🪑 Eating a chair... (' + lp.chairCharges + ' left)', timer: 2, color: '#2ecc71' });
        lp.effects.push({ type: 'eating', timer: (abil.channelTime || 3) + 0.5 });
      }
    } else if (is1x) {
      // 1X1X1X1 R: Mass Infection — wide horizontal shockwave + poison
      const range = (abil.range || 4) * GAME_TILE;
      let baseDmg = abil.damage;
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        // Wide angle — 180 degrees (dot product >= -0.1)
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < -0.1) continue;
        dealDamage(lp, target, baseDmg);
        // Apply poison
        if (!target.poisonTimers) target.poisonTimers = [];
        target.poisonTimers.push({ sourceId: lp.id, dps: abil.poisonDPS || 50, remaining: abil.poisonDuration || 3 });
        target.effects.push({ type: 'poison', timer: abil.poisonDuration || 3 });
      }
      lp.effects.push({ type: 'mass-infection', timer: 0.6, aimNx, aimNy });
      combatLog.push({ text: '☣ Mass Infection!', timer: 3, color: '#00ff66' });
    } else {
      // Fighter: Power Swing
      const range = abil.range * GAME_TILE;
      let baseDmgR = abil.damage;
      if (lp.supportBuff > 0) baseDmgR *= 1.5;
      if (lp.intimidated > 0) baseDmgR *= 0.5;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        dealDamage(lp, target, baseDmgR);
        const kbDist = (abil.knockback || 3) * GAME_TILE;
        const kbNx = dx / (dist || 1);
        const kbNy = dy / (dist || 1);
        let newTX = target.x + kbNx * kbDist;
        let newTY = target.y + kbNy * kbDist;
        const steps = 10;
        for (let s = steps; s >= 1; s--) {
          const tryX = target.x + kbNx * kbDist * (s / steps);
          const tryY = target.y + kbNy * kbDist * (s / steps);
          if (canMoveTo(tryX, tryY, GAME_TILE * PLAYER_RADIUS_RATIO)) {
            newTX = tryX; newTY = tryY; break;
          }
          if (s === 1) { newTX = target.x; newTY = target.y; }
        }
        target.x = newTX; target.y = newTY;
        if (typeof socket !== 'undefined' && socket.emit) {
          socket.emit('player-knockback', { targetId: target.id, x: newTX, y: newTY });
        }
      }
      lp.effects.push({ type: 'power-arc', timer: 0.3 });
    }
  }

  else if (key === 'T') {
    if (lp.cdT > 0) return;
    const abil = fighter.abilities[3];
    lp.cdT = abil.cooldown;

    if (isPoker) {
      // Chip Change: randomize M1 damage for 30 seconds
      const options = [50, 100, 200, 300, 400];
      lp.chipChangeDmg = options[Math.floor(Math.random() * options.length)];
      lp.chipChangeTimer = abil.duration || 30;
      // Clear small blind when using another move
      if (lp.blindBuff === 'small') lp.blindBuff = null;
      lp.effects.push({ type: 'chip-change', timer: 1.5 });
    } else if (isFilbus) {
      // Filbus T: Oddity Overthrow — summon or dismiss companion
      if (lp.summonId) {
        // Dismiss existing summon
        const sIdx = gamePlayers.findIndex(p => p.id === lp.summonId);
        if (sIdx >= 0) {
          gamePlayers[sIdx].alive = false;
          gamePlayers[sIdx].hp = 0;
          gamePlayers[sIdx].effects.push({ type: 'death', timer: 2 });
          gamePlayers.splice(sIdx, 1);
        }
        lp.summonId = null;
        lp.cdT = 5; // short cooldown on dismiss
        combatLog.push({ text: '👋 Companion dismissed', timer: 2, color: '#999' });
      } else {
        // Summon a random companion
        const companionKeys = Object.keys(abil.companions);
        const pick = companionKeys[Math.floor(Math.random() * companionKeys.length)];
        const compDef = abil.companions[pick];
        const summonId = 'summon-' + lp.id + '-' + Date.now();
        const summon = {
          id: summonId,
          name: compDef.name,
          color: pick === 'fleshbed' ? '#8b4513' : pick === 'macrocosms' ? '#4a0080' : '#d4af37',
          x: lp.x + (Math.random() - 0.5) * GAME_TILE * 2,
          y: lp.y + (Math.random() - 0.5) * GAME_TILE * 2,
          hp: compDef.hp,
          maxHp: compDef.hp,
          fighter: fighter,
          alive: true,
          cdM1: 0, cdE: 0, cdR: 0, cdT: 0,
          totalDamageTaken: 0,
          specialUnlocked: false, specialUsed: false,
          supportBuff: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
          noDamageTimer: 0, healTickTimer: 0, isHealing: false,
          specialJumping: false, specialAiming: false,
          specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
          effects: [],
          blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
          chairCharges: 0, isCraftingChair: false, craftTimer: 0,
          isEatingChair: false, eatTimer: 0, eatHealPool: 0,
          summonId: null, boiledOneActive: false, boiledOneTimer: 0,
          poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
          // Summon-specific
          isSummon: true,
          summonOwner: lp.id,
          summonType: pick,
          summonSpeed: compDef.speed,
          summonDamage: compDef.damage,
          summonStunDur: compDef.stunDuration,
          summonAttackCD: compDef.attackCooldown,
          summonAttackTimer: 0,
        };
        // Obelisk spawns at Filbus's position
        if (pick === 'obelisk') {
          summon.x = lp.x;
          summon.y = lp.y;
        }
        gamePlayers.push(summon);
        lp.summonId = summonId;
        combatLog.push({ text: '🔮 Summoned ' + compDef.name + '!', timer: 3, color: '#d4af37' });
        lp.effects.push({ type: 'summon', timer: 1.5 });
      }
    } else if (is1x) {
      // 1X1X1X1 T: Unstable Eye — speed boost + reveal all enemies + blur
      lp.unstableEyeTimer = abil.duration || 6;
      lp.effects.push({ type: 'unstable-eye', timer: abil.duration || 6 });
      combatLog.push({ text: '👁 Unstable Eye activated!', timer: 3, color: '#00ff66' });
      showPopup('👁 UNSTABLE EYE');
    } else {
      // Fighter: Intimidation
      const sightRange = CAMERA_RANGE * GAME_TILE * 2;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        const dist = Math.sqrt((target.x - lp.x) ** 2 + (target.y - lp.y) ** 2);
        if (dist <= sightRange) {
          target.intimidated = abil.duration;
          target.intimidatedBy = lp.id;
          if (typeof socket !== 'undefined' && socket.emit) {
            socket.emit('player-debuff', { targetId: target.id, type: 'intimidation', duration: abil.duration });
          }
        }
      }
      lp.effects.push({ type: 'intimidation', timer: 1.0 });
    }
  }

  else if (key === 'SPACE') {
    if (!lp.specialUnlocked || lp.specialUsed) return;

    if (isPoker) {
      // Royal Flush — distance-tiered:
      //   Self: heal to full HP automatically
      //   Close (≤3 tiles): stun + execute <500hp + reset CDs/charges
      //   Medium (3–10 tiles): reset CDs/charges only
      lp.specialUsed = true;
      lp.hp = lp.maxHp;  // Self-heal
      const stunDur = fighter.abilities[4].stunDuration || 3;
      const execThresh = fighter.abilities[4].executeThreshold || 500;
      const closeRange = 3 * GAME_TILE;
      const mediumRange = (fighter.abilities[4].range || 10) * GAME_TILE;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > mediumRange) continue; // out of range entirely
        if (dist <= closeRange) {
          // Close range: stun + execute + reset
          if (target.hp <= execThresh) {
            dealDamage(lp, target, target.hp);
          } else {
            target.stunned = stunDur;
            target.effects.push({ type: 'stun', timer: stunDur });
          }
        }
        // Both close and medium: reset cooldowns/charges
        target.cdM1 = target.fighter.abilities[0].cooldown;
        target.cdE = target.fighter.abilities[1].cooldown;
        target.cdR = target.fighter.abilities[2].cooldown;
        target.cdT = target.fighter.abilities[3].cooldown;
        // Reset their special / charges
        target.specialUnlocked = false;
        target.totalDamageTaken = 0;
        target.supportBuff = 0;
        target.chipChangeDmg = -1;
        target.chipChangeTimer = 0;
        target.blindBuff = null;
        target.blindTimer = 0;
      }
      showPopup('👑 ROYAL FLUSH!');
      lp.effects.push({ type: 'royal-flush', timer: 2.0 });
      // Broadcast to other clients with position for distance calc
      if (typeof socket !== 'undefined' && socket.emit) {
        socket.emit('player-buff', { type: 'royal-flush', duration: stunDur, cx: lp.x, cy: lp.y });
      }
    } else if (isFilbus) {
      // Filbus SPACE: The Boiled One Phenomenon
      // Phen 228 enters — stun ALL fighters for 10s, dot turns dark red
      // Anyone who sees the dark red dot gets stunned
      // Lasts until first stunned player can move
      lp.specialUsed = true;
      lp.boiledOneActive = true;
      const stunDur = fighter.abilities[4].stunDuration || 10;
      lp.boiledOneTimer = stunDur;
      // Stun everyone except Filbus
      for (const target of gamePlayers) {
        if (!target.alive) continue;
        if (target.isSummon) continue;
        if (target.id === lp.id) continue; // Filbus is immune
        target.stunned = stunDur;
        target.effects.push({ type: 'stun', timer: stunDur });
      }
      showPopup('🩸 THE BOILED ONE PHENOMENON');
      lp.effects.push({ type: 'boiled-one', timer: stunDur + 1 });
      combatLog.push({ text: '🩸 Phen 228 has entered...', timer: 5, color: '#8b0000' });
    } else if (is1x) {
      // 1X1X1X1 SPACE: Rejuvenate the Rotten — summon zombies
      lp.specialUsed = true;
      const abil = fighter.abilities[4];
      // Count dead players
      let deadCount = 0;
      for (const p of gamePlayers) {
        if (!p.alive && !p.isSummon) deadCount++;
      }
      const zombieCount = (abil.baseZombies || 5) + deadCount;
      // Clear old zombies
      for (let zi = gamePlayers.length - 1; zi >= 0; zi--) {
        if (gamePlayers[zi].isSummon && gamePlayers[zi].summonType === 'zombie' && gamePlayers[zi].summonOwner === lp.id) {
          gamePlayers.splice(zi, 1);
        }
      }
      lp.zombieIds = [];
      // Spawn zombies at random positions on the map
      for (let z = 0; z < zombieCount; z++) {
        const zombieId = 'zombie-' + lp.id + '-' + Date.now() + '-' + z;
        // Random walkable position
        let zx, zy;
        for (let attempts = 0; attempts < 50; attempts++) {
          zx = (Math.floor(Math.random() * gameMap.cols) + 0.5) * GAME_TILE;
          zy = (Math.floor(Math.random() * gameMap.rows) + 0.5) * GAME_TILE;
          if (canMoveTo(zx, zy, GAME_TILE * PLAYER_RADIUS_RATIO)) break;
        }
        const zombie = {
          id: zombieId, name: 'Zombie', color: '#1a5c1a',
          x: zx, y: zy,
          hp: abil.zombieHp || 500, maxHp: abil.zombieHp || 500,
          fighter: fighter, alive: true,
          cdM1: 0, cdE: 0, cdR: 0, cdT: 0,
          totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
          supportBuff: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
          noDamageTimer: 0, healTickTimer: 0, isHealing: false,
          specialJumping: false, specialAiming: false,
          specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
          effects: [],
          blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
          chairCharges: 0, isCraftingChair: false, craftTimer: 0,
          isEatingChair: false, eatTimer: 0, eatHealPool: 0,
          summonId: null, boiledOneActive: false, boiledOneTimer: 0,
          poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
          // Summon-specific
          isSummon: true, summonOwner: lp.id, summonType: 'zombie',
          summonSpeed: abil.zombieSpeed || 2.0,
          summonDamage: abil.zombieDamage || 100,
          summonStunDur: 0, summonAttackCD: 4.0, summonAttackTimer: 0,
        };
        gamePlayers.push(zombie);
        lp.zombieIds.push(zombieId);
      }
      showPopup('🧟 REJUVENATE THE ROTTEN!');
      lp.effects.push({ type: 'rejuvenate', timer: 2.0 });
      combatLog.push({ text: '🧟 Summoned ' + zombieCount + ' zombies!', timer: 4, color: '#1a5c1a' });
    } else {
      // Fighter: Special jump
      lp.specialJumping = true;
      lp.specialAiming = true;
      lp.specialAimX = lp.x;
      lp.specialAimY = lp.y;
      const aimTime = lp.fighter.abilities[4].aimTime || 5;
      lp.specialAimTimer = aimTime;
      lp.effects.push({ type: 'jump', timer: aimTime + 2 });
    }
  }
}

function executeSpecialLanding() {
  const lp = localPlayer;
  const abil = lp.fighter.abilities[4]; // Special
  lp.specialAiming = false;
  lp.specialJumping = false;
  lp.specialUsed = true;
  lp.effects = lp.effects.filter((fx) => fx.type !== 'jump');

  // Check if hit any enemy within 1 tile of landing
  const landX = lp.specialAimX;
  const landY = lp.specialAimY;
  const hitRange = GAME_TILE * 1.2;
  let hitSomeone = false;

  for (const target of gamePlayers) {
    if (target.id === lp.id || !target.alive) continue;
    const dist = Math.sqrt((target.x - landX) ** 2 + (target.y - landY) ** 2);
    if (dist <= hitRange) {
      dealDamage(lp, target, abil.damage);
      hitSomeone = true;
    }
  }

  // Move player to landing position
  lp.x = landX;
  lp.y = landY;

  if (!hitSomeone) {
    // Miss: stun self + self damage
    lp.stunned = abil.missStun;
    lp.hp = Math.max(0, lp.hp - abil.missDamage);
    if (lp.hp <= 0) {
      lp.alive = false; lp.hp = 0;
      lp.effects.push({ type: 'death', timer: 2 });
      freeCamX = lp.x; freeCamY = lp.y; spectateIndex = -1;
    }
    lp.effects.push({ type: 'stun', timer: abil.missStun });
  }

  lp.effects.push({ type: 'land', timer: 0.5 });
}

function dealDamage(attacker, target, amount) {
  if (!target.alive) return;
  // Obelisk is invincible
  if (target.isSummon && target.summonType === 'obelisk') return;
  // Blinds modifier (Poker)
  if (target.blindBuff === 'small') amount = Math.round(amount * 0.5);
  else if (target.blindBuff === 'big') amount = Math.round(amount * 1.5);
  target.hp -= amount;
  // Reset heal state on damage
  target.noDamageTimer = 0;
  target.isHealing = false;
  target.healTickTimer = 0;
  target.effects.push({ type: 'hit', timer: 0.3 });

  // Filbus: interrupt channeling on damage
  if (target.isCraftingChair) {
    target.isCraftingChair = false;
    target.craftTimer = 0;
    if (target.id === localPlayerId) {
      combatLog.push({ text: '🪑 Chair crafting interrupted!', timer: 2, color: '#e94560' });
    }
  }
  if (target.isEatingChair) {
    target.isEatingChair = false;
    target.eatTimer = 0;
    target.eatHealPool = 0;
    if (target.id === localPlayerId) {
      combatLog.push({ text: '🪑 Chair eating interrupted!', timer: 2, color: '#e94560' });
    }
  }

  // Track damage taken for special unlock (target's counter)
  target.totalDamageTaken += amount;
  if (!target.specialUnlocked && target.totalDamageTaken >= target.maxHp * 2) {
    target.specialUnlocked = true;
    if (target.id === localPlayerId) {
      showPopup('⚡ SPECIAL UNLOCKED! [SPACE]');
    }
  }

  // Track damage dealt for attacker's special unlock too
  if (attacker && attacker.alive) {
    attacker.totalDamageTaken += amount;
    if (!attacker.specialUnlocked && attacker.totalDamageTaken >= attacker.maxHp * 2) {
      attacker.specialUnlocked = true;
      if (attacker.id === localPlayerId) {
        showPopup('⚡ SPECIAL UNLOCKED! [SPACE]');
      }
    }
  }

  // Broadcast damage to other clients
  if (typeof socket !== 'undefined' && socket.emit && attacker && attacker.id === localPlayerId) {
    socket.emit('player-damage', { targetId: target.id, amount, attackerId: attacker.id });
  }

  if (target.hp <= 0) {
    target.hp = 0;
    target.alive = false;
    target.effects.push({ type: 'death', timer: 2 });
    // Init spectator camera if local player died
    if (target.id === localPlayerId) {
      freeCamX = target.x;
      freeCamY = target.y;
      spectateIndex = -1;
    }
    // Training dummy respawn after 3 seconds
    if (target.id === 'dummy' && gameMode === 'training') {
      dummyRespawnTimer = 3;
    }
    // Summon death: clear owner's summonId
    if (target.isSummon) {
      const owner = gamePlayers.find(p => p.id === target.summonOwner);
      if (owner && owner.summonId === target.id) {
        owner.summonId = null;
      }
    }
    // Owner death: clear summon reference (summon cleanup in updateSummons)
    if (target.summonId) {
      const summon = gamePlayers.find(p => p.id === target.summonId);
      if (summon && summon.alive) {
        summon.alive = false;
        summon.hp = 0;
        summon.effects.push({ type: 'death', timer: 2 });
      }
      target.summonId = null;
    }
    // Tell server this player died
    if (typeof socket !== 'undefined' && socket.emit) {
      socket.emit('player-died', { playerId: target.id });
    }
  }
}

// Apply damage received from another client
function onRemoteDamage(targetId, amount) {
  const target = gamePlayers.find((p) => p.id === targetId);
  if (!target || !target.alive) return;
  target.hp -= amount;
  target.noDamageTimer = 0;
  target.isHealing = false;
  target.healTickTimer = 0;
  target.effects.push({ type: 'hit', timer: 0.3 });
  target.totalDamageTaken += amount;
  if (!target.specialUnlocked && target.totalDamageTaken >= target.maxHp * 2) {
    target.specialUnlocked = true;
    if (target.id === localPlayerId) {
      showPopup('⚡ SPECIAL UNLOCKED! [SPACE]');
    }
  }
  if (target.hp <= 0) {
    target.hp = 0;
    target.alive = false;
    target.effects.push({ type: 'death', timer: 2 });
    // Init spectator camera if local player died
    if (target.id === localPlayerId) {
      freeCamX = target.x;
      freeCamY = target.y;
      spectateIndex = -1;
    }
  }
}

function onRemoteKnockback(targetId, x, y) {
  const target = gamePlayers.find((p) => p.id === targetId);
  if (target) { target.x = x; target.y = y; }
}

function onZoneSync(newInset, newTimer) {
  zoneInset = newInset;
  zoneTimer = newTimer;
  // Back-calculate what zonePhaseStart would be for this timer value
  zonePhaseStart = Date.now() - (ZONE_INTERVAL - newTimer) * 1000;
}

function onGameOver(winnerId, winnerName) {
  gameRunning = false;
  const cw = gameCanvas.width;
  const ch = gameCanvas.height;
  gameCtx.fillStyle = 'rgba(0, 0, 0, 0.7)';
  gameCtx.fillRect(0, 0, cw, ch);
  if (winnerId) {
    const isMe = winnerId === localPlayerId;
    gameCtx.fillStyle = isMe ? '#2ecc71' : '#e94560';
    gameCtx.font = 'bold 36px "Press Start 2P", monospace';
    gameCtx.textAlign = 'center';
    gameCtx.fillText(isMe ? 'VICTORY!' : 'DEFEATED', cw / 2, ch / 2 - 20);
    gameCtx.fillStyle = '#fff';
    gameCtx.font = 'bold 16px "Press Start 2P", monospace';
    gameCtx.fillText((winnerName || 'Someone') + ' wins!', cw / 2, ch / 2 + 30);
  } else {
    gameCtx.fillStyle = '#f5a623';
    gameCtx.font = 'bold 36px "Press Start 2P", monospace';
    gameCtx.textAlign = 'center';
    gameCtx.fillText('DRAW', cw / 2, ch / 2);
  }
}

function onRemoteDeath(playerId) {
  const p = gamePlayers.find((pl) => pl.id === playerId);
  if (p) {
    p.alive = false;
    p.hp = 0;
    p.effects.push({ type: 'death', timer: 2 });
  }
}

// ═══════════════════════════════════════════════════════════════
// RENDER
// ═══════════════════════════════════════════════════════════════
function renderGame() {
  const cw = gameCanvas.width;
  const ch = gameCanvas.height;
  gameCtx.clearRect(0, 0, cw, ch);

  if (!localPlayer) return;

  // Camera: follow alive player, or spectator target, or free cam
  let camX, camY;
  if (localPlayer.alive) {
    camX = localPlayer.x - cw / 2;
    camY = localPlayer.y - ch / 2;
  } else if (spectateIndex >= 0 && gamePlayers[spectateIndex] && gamePlayers[spectateIndex].alive) {
    camX = gamePlayers[spectateIndex].x - cw / 2;
    camY = gamePlayers[spectateIndex].y - ch / 2;
  } else {
    camX = freeCamX - cw / 2;
    camY = freeCamY - ch / 2;
  }

  // Tiles
  const startCol = Math.floor(camX / GAME_TILE) - 1;
  const endCol   = Math.ceil((camX + cw) / GAME_TILE) + 1;
  const startRow = Math.floor(camY / GAME_TILE) - 1;
  const endRow   = Math.ceil((camY + ch) / GAME_TILE) + 1;

  for (let r = startRow; r <= endRow; r++) {
    for (let c = startCol; c <= endCol; c++) {
      const screenX = c * GAME_TILE - camX;
      const screenY = r * GAME_TILE - camY;

      if (r < 0 || r >= gameMap.rows || c < 0 || c >= gameMap.cols) {
        drawWater(gameCtx, screenX, screenY, GAME_TILE, Math.abs(r), Math.abs(c));
      } else {
        const tile = gameMap.tiles[r][c];
        drawGround(gameCtx, screenX, screenY, GAME_TILE);
        if (tile === TILE.GRASS) drawGrass(gameCtx, screenX, screenY, GAME_TILE, r, c);
        else if (tile === TILE.ROCK) drawRock(gameCtx, screenX, screenY, GAME_TILE);
        else if (tile === TILE.WATER) drawWater(gameCtx, screenX, screenY, GAME_TILE, r, c);
      }
    }
  }

  // Special aim reticle
  if (localPlayer.specialAiming) {
    const aimSX = localPlayer.specialAimX - camX;
    const aimSY = localPlayer.specialAimY - camY;
    gameCtx.strokeStyle = '#f5a623';
    gameCtx.lineWidth = 3;
    gameCtx.beginPath();
    gameCtx.arc(aimSX, aimSY, GAME_TILE * 1.2, 0, Math.PI * 2);
    gameCtx.stroke();
    gameCtx.beginPath();
    gameCtx.moveTo(aimSX - 10, aimSY);
    gameCtx.lineTo(aimSX + 10, aimSY);
    gameCtx.moveTo(aimSX, aimSY - 10);
    gameCtx.lineTo(aimSX, aimSY + 10);
    gameCtx.stroke();
    // Aim timer text
    gameCtx.fillStyle = '#f5a623';
    gameCtx.font = 'bold 14px "Press Start 2P", monospace';
    gameCtx.textAlign = 'center';
    gameCtx.fillText(Math.ceil(localPlayer.specialAimTimer) + 's', aimSX, aimSY - GAME_TILE * 1.5);
  }

  // Draw players
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;
  for (const p of gamePlayers) {
    if (!p.alive && !p.effects.some((fx) => fx.type === 'death')) continue;
    if (p.specialJumping && p.id === localPlayerId) continue; // in the air

    const sx = p.x - camX;
    const sy = p.y - camY;

    if (sx < -GAME_TILE * 2 || sx > cw + GAME_TILE * 2 || sy < -GAME_TILE * 2 || sy > ch + GAME_TILE * 2) continue;

    // Dead player: dark red for 2s then hidden
    const isDying = !p.alive && p.effects.some((fx) => fx.type === 'death');

    // Grass hiding logic
    const samplePoints = [
      { x: p.x, y: p.y },
      { x: p.x - radius, y: p.y }, { x: p.x + radius, y: p.y },
      { x: p.x, y: p.y - radius }, { x: p.x, y: p.y + radius },
      { x: p.x - radius * 0.7, y: p.y - radius * 0.7 },
      { x: p.x + radius * 0.7, y: p.y - radius * 0.7 },
      { x: p.x - radius * 0.7, y: p.y + radius * 0.7 },
      { x: p.x + radius * 0.7, y: p.y + radius * 0.7 },
    ];
    let grassCount = 0;
    for (const pt of samplePoints) {
      const col = Math.floor(pt.x / GAME_TILE);
      const row = Math.floor(pt.y / GAME_TILE);
      if (row >= 0 && row < gameMap.rows && col >= 0 && col < gameMap.cols
          && gameMap.tiles[row][col] === TILE.GRASS) grassCount++;
    }
    const grassFraction = grassCount / samplePoints.length;
    const isHidden = grassFraction > 0.5;
    const isLocal = p.id === localPlayerId;

    if (isHidden && !isLocal) continue;

    const inAnyGrass = grassFraction > 0;
    const dotAlpha = isDying ? 0.7 : (isLocal && inAnyGrass) ? 0.4 : (p.alive ? 1.0 : 0.3);

    gameCtx.save();
    gameCtx.globalAlpha = dotAlpha;

    // Stunned visual
    if (p.stunned > 0 && !isDying) {
      gameCtx.fillStyle = 'rgba(255,255,0,0.2)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 4, 0, Math.PI * 2);
      gameCtx.fill();
    }

    // Dot — dark red if dying or Boiled One active
    if (p.isSummon) {
      // ── Custom summon shapes ──
      if (p.summonType === 'fleshbed') {
        // Grey square
        const sz = radius * 1.6;
        gameCtx.fillStyle = isDying ? '#8b0000' : '#888';
        gameCtx.fillRect(sx - sz / 2, sy - sz / 2, sz, sz);
        gameCtx.strokeStyle = '#555';
        gameCtx.lineWidth = 2;
        gameCtx.strokeRect(sx - sz / 2, sy - sz / 2, sz, sz);
        // Dark inner lines for texture
        gameCtx.strokeStyle = '#666';
        gameCtx.lineWidth = 1;
        gameCtx.beginPath();
        gameCtx.moveTo(sx - sz / 4, sy - sz / 2);
        gameCtx.lineTo(sx - sz / 4, sy + sz / 2);
        gameCtx.moveTo(sx + sz / 4, sy - sz / 2);
        gameCtx.lineTo(sx + sz / 4, sy + sz / 2);
        gameCtx.stroke();
      } else if (p.summonType === 'macrocosms') {
        // Grey circle
        gameCtx.fillStyle = isDying ? '#8b0000' : '#999';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 1.1, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = '#555';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 1.1, 0, Math.PI * 2);
        gameCtx.stroke();
        // No head — just a dark void at top
        gameCtx.fillStyle = '#333';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - radius * 0.4, radius * 0.35, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'obelisk') {
        // Black triangle with red streaks
        const h = radius * 2.2;
        const base = radius * 1.6;
        gameCtx.fillStyle = isDying ? '#8b0000' : '#111';
        gameCtx.beginPath();
        gameCtx.moveTo(sx, sy - h / 2);           // top
        gameCtx.lineTo(sx - base / 2, sy + h / 2); // bottom-left
        gameCtx.lineTo(sx + base / 2, sy + h / 2); // bottom-right
        gameCtx.closePath();
        gameCtx.fill();
        // Outline
        gameCtx.strokeStyle = '#333';
        gameCtx.lineWidth = 2;
        gameCtx.stroke();
        // Red streaks
        gameCtx.strokeStyle = '#8b0000';
        gameCtx.lineWidth = 1.5;
        gameCtx.beginPath();
        gameCtx.moveTo(sx - 2, sy - h * 0.3);
        gameCtx.lineTo(sx - 4, sy + h * 0.2);
        gameCtx.moveTo(sx + 3, sy - h * 0.25);
        gameCtx.lineTo(sx + 1, sy + h * 0.3);
        gameCtx.moveTo(sx, sy - h * 0.1);
        gameCtx.lineTo(sx - 2, sy + h * 0.35);
        gameCtx.stroke();
        // Glowing red eye near top
        gameCtx.fillStyle = '#ff2200';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - h * 0.15, 2.5, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.fillStyle = 'rgba(255, 34, 0, 0.3)';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - h * 0.15, 5, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'zombie') {
        // Dark green circle for zombie
        gameCtx.fillStyle = isDying ? '#8b0000' : '#1a5c1a';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 0.9, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = '#0a3a0a';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 0.9, 0, Math.PI * 2);
        gameCtx.stroke();
        // Zombie eyes — two small dots
        gameCtx.fillStyle = '#88ff44';
        gameCtx.beginPath();
        gameCtx.arc(sx - 3, sy - 2, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + 3, sy - 2, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
      }
    } else if (p.fighter && p.fighter.id === 'onexonexonex' && !p.isSummon) {
      // ── 1X1X1X1: Fully custom dot — dark base with neon green glitches + red eye ──
      // Base: dark circle
      gameCtx.fillStyle = isDying ? '#8b0000' : '#111';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
      gameCtx.fill();
      // Glitchy neon green edge fragments (irregular outline instead of smooth)
      gameCtx.strokeStyle = '#00ff66';
      gameCtx.lineWidth = 2;
      const segments = 8;
      for (let i = 0; i < segments; i++) {
        const a1 = (i / segments) * Math.PI * 2;
        const a2 = ((i + 0.6) / segments) * Math.PI * 2;
        // Offset each segment slightly for glitch effect
        const jitter = ((i * 7 + 3) % 5) * 0.5 - 1;
        const r = radius + jitter;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, r, a1, a2);
        gameCtx.stroke();
      }
      // Neon green glitch streaks across the dot surface
      gameCtx.strokeStyle = '#00ff66';
      gameCtx.lineWidth = 1.2;
      gameCtx.globalAlpha = 0.7;
      gameCtx.beginPath();
      gameCtx.moveTo(sx - radius * 0.6, sy - radius * 0.3);
      gameCtx.lineTo(sx - radius * 0.2, sy - radius * 0.1);
      gameCtx.moveTo(sx + radius * 0.1, sy + radius * 0.2);
      gameCtx.lineTo(sx + radius * 0.6, sy + radius * 0.1);
      gameCtx.moveTo(sx - radius * 0.3, sy + radius * 0.4);
      gameCtx.lineTo(sx + radius * 0.1, sy + radius * 0.55);
      gameCtx.moveTo(sx + radius * 0.3, sy - radius * 0.5);
      gameCtx.lineTo(sx + radius * 0.5, sy - radius * 0.2);
      gameCtx.stroke();
      gameCtx.globalAlpha = 1.0;
      // Subtle green inner glow
      gameCtx.fillStyle = 'rgba(0, 255, 102, 0.08)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius * 0.8, 0, Math.PI * 2);
      gameCtx.fill();
      // Red eye — glowing, slightly above center (like obelisk but rounder)
      // Outer glow
      gameCtx.fillStyle = 'rgba(255, 34, 0, 0.25)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy - radius * 0.15, 6, 0, Math.PI * 2);
      gameCtx.fill();
      // Eye white (dark)
      gameCtx.fillStyle = '#220000';
      gameCtx.beginPath();
      // Almond/eye shape
      gameCtx.ellipse(sx, sy - radius * 0.15, 5, 3, 0, 0, Math.PI * 2);
      gameCtx.fill();
      // Iris
      gameCtx.fillStyle = '#ff2200';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy - radius * 0.15, 2.5, 0, Math.PI * 2);
      gameCtx.fill();
      // Pupil
      gameCtx.fillStyle = '#000';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy - radius * 0.15, 1, 0, Math.PI * 2);
      gameCtx.fill();
      // Bright red glint
      gameCtx.fillStyle = 'rgba(255, 100, 80, 0.8)';
      gameCtx.beginPath();
      gameCtx.arc(sx + 1, sy - radius * 0.15 - 1, 0.7, 0, Math.PI * 2);
      gameCtx.fill();
      // Zombie indicator if zombies active
      if (p.zombieIds && p.zombieIds.length > 0) {
        gameCtx.fillStyle = '#1a5c1a';
        gameCtx.beginPath();
        gameCtx.arc(sx + radius + 3, sy - radius - 3, 3, 0, Math.PI * 2);
        gameCtx.fill();
      }
    } else {
      // Normal player dot
      gameCtx.fillStyle = isDying ? '#8b0000' : (p.boiledOneActive ? '#8b0000' : p.color);
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
      gameCtx.fill();

    // Outline
    gameCtx.strokeStyle = 'rgba(0,0,0,0.4)';
    gameCtx.lineWidth = 2;
    gameCtx.stroke();

    // Fighter icon on the dot
    if (p.fighter && p.fighter.id === 'poker') {
      // Poker: chip icon sticking out from the dot (like the sword does for Fighter)
      const chipR = radius * 0.5;
      const chipAngle = -Math.PI / 4; // upper-right, same as sword
      const chipX = sx + Math.cos(chipAngle) * (radius + chipR * 0.3);
      const chipY = sy + Math.sin(chipAngle) * (radius + chipR * 0.3);
      // Chip body
      gameCtx.fillStyle = '#222';
      gameCtx.beginPath();
      gameCtx.arc(chipX, chipY, chipR, 0, Math.PI * 2);
      gameCtx.fill();
      // Outer ring
      gameCtx.strokeStyle = '#555';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.arc(chipX, chipY, chipR, 0, Math.PI * 2);
      gameCtx.stroke();
      // Inner circle
      gameCtx.strokeStyle = '#fff';
      gameCtx.lineWidth = 1.5;
      gameCtx.beginPath();
      gameCtx.arc(chipX, chipY, chipR * 0.55, 0, Math.PI * 2);
      gameCtx.stroke();
      // Edge notches (4 dashes around the chip)
      for (let n = 0; n < 4; n++) {
        const a = (n * Math.PI) / 2;
        const nx1 = chipX + Math.cos(a) * chipR * 0.7;
        const ny1 = chipY + Math.sin(a) * chipR * 0.7;
        const nx2 = chipX + Math.cos(a) * chipR * 0.95;
        const ny2 = chipY + Math.sin(a) * chipR * 0.95;
        gameCtx.strokeStyle = '#fff';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.moveTo(nx1, ny1);
        gameCtx.lineTo(nx2, ny2);
        gameCtx.stroke();
      }
    } else if (p.fighter && p.fighter.id === 'filbus') {
      // Filbus: chair icon on the dot
      const chairAngle = -Math.PI / 4;
      const chairX = sx + Math.cos(chairAngle) * (radius + 2);
      const chairY = sy + Math.sin(chairAngle) * (radius + 2);
      const chairW = radius * 0.7;
      const chairH = radius * 0.5;
      // Seat
      gameCtx.fillStyle = '#a0522d';
      gameCtx.fillRect(chairX - chairW / 2, chairY - chairH / 2, chairW, chairH);
      // Back
      gameCtx.fillStyle = '#8b4513';
      gameCtx.fillRect(chairX - chairW / 2, chairY - chairH, chairW * 0.25, chairH);
      gameCtx.fillRect(chairX + chairW / 4, chairY - chairH, chairW * 0.25, chairH);
      // Legs
      gameCtx.strokeStyle = '#654321';
      gameCtx.lineWidth = 1.5;
      gameCtx.beginPath();
      gameCtx.moveTo(chairX - chairW / 2 + 1, chairY + chairH / 2);
      gameCtx.lineTo(chairX - chairW / 2 + 1, chairY + chairH);
      gameCtx.moveTo(chairX + chairW / 2 - 1, chairY + chairH / 2);
      gameCtx.lineTo(chairX + chairW / 2 - 1, chairY + chairH);
      gameCtx.stroke();
      // Summon indicator dot if summon active
      if (p.summonId) {
        gameCtx.fillStyle = '#d4af37';
        gameCtx.beginPath();
        gameCtx.arc(sx + radius + 3, sy - radius - 3, 3, 0, Math.PI * 2);
        gameCtx.fill();
      }
    } else {
      // Fighter: Sword indicator on the dot
      const swordLen = radius * 1.3;
      const swordAngle = -Math.PI / 4;
      const sBaseX = sx + Math.cos(swordAngle) * radius * 0.4;
      const sBaseY = sy + Math.sin(swordAngle) * radius * 0.4;
      const sTipX = sBaseX + Math.cos(swordAngle) * swordLen;
      const sTipY = sBaseY + Math.sin(swordAngle) * swordLen;
      gameCtx.strokeStyle = '#ccc';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.moveTo(sBaseX, sBaseY);
      gameCtx.lineTo(sTipX, sTipY);
      gameCtx.stroke();
      const hiltX = sBaseX + Math.cos(swordAngle) * swordLen * 0.3;
      const hiltY = sBaseY + Math.sin(swordAngle) * swordLen * 0.3;
      const perpAngle = swordAngle + Math.PI / 2;
      gameCtx.strokeStyle = '#a0522d';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.moveTo(hiltX + Math.cos(perpAngle) * 4, hiltY + Math.sin(perpAngle) * 4);
      gameCtx.lineTo(hiltX - Math.cos(perpAngle) * 4, hiltY - Math.sin(perpAngle) * 4);
      gameCtx.stroke();
    }
    } // end normal player dot

    // Support buff ring (visible to all players)
    if (p.supportBuff > 0) {
      gameCtx.strokeStyle = '#2ecc71';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 6, 0, Math.PI * 2);
      gameCtx.stroke();
      // Pulsing glow
      gameCtx.strokeStyle = 'rgba(46, 204, 113, 0.3)';
      gameCtx.lineWidth = 6;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 10, 0, Math.PI * 2);
      gameCtx.stroke();
      // Buff timer text below the dot
      gameCtx.fillStyle = '#2ecc71';
      gameCtx.font = 'bold 12px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('BUFF ' + Math.ceil(p.supportBuff) + 's', sx, sy + radius + 18);
    }

    // Intimidation debuff ring drawn on any intimidated player
    if (p.intimidated > 0) {
      gameCtx.strokeStyle = 'rgba(155, 89, 182, 0.6)';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 6, 0, Math.PI * 2);
      gameCtx.stroke();
      // Timer text
      gameCtx.fillStyle = 'rgba(155, 89, 182, 0.9)';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText(Math.ceil(p.intimidated) + 's', sx, sy - radius - 22);
    }

    // Name + HP above
    gameCtx.globalAlpha = 1;
    gameCtx.fillStyle = isDying ? '#8b0000' : '#fff';
    gameCtx.font = 'bold 11px sans-serif';
    gameCtx.textAlign = 'center';
    gameCtx.fillText(p.name, sx, sy - radius - 14);

    // HP bar above dot
    if (p.alive) {
      const barW = radius * 2.2;
      const barH = 4;
      const barX = sx - barW / 2;
      const barY = sy - radius - 10;
      gameCtx.fillStyle = '#333';
      gameCtx.fillRect(barX, barY, barW, barH);
      const hpFrac = Math.max(0, p.hp / p.maxHp);
      gameCtx.fillStyle = hpFrac >= 0.7 ? '#2ecc71' : hpFrac >= 0.4 ? '#f5a623' : '#e94560';
      gameCtx.fillRect(barX, barY, barW * hpFrac, barH);
    }

    // Sword swing effect
    const swordFx = p.effects.find((fx) => fx.type === 'sword');
    if (swordFx) {
      const swLen = GAME_TILE * 1.3;
      gameCtx.strokeStyle = '#ccc';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      const aRad = Math.atan2(swordFx.aimNy, swordFx.aimNx);
      gameCtx.arc(sx, sy, swLen, aRad - 0.5, aRad + 0.5);
      gameCtx.stroke();
    }

    // Power Swing red circle effect
    const powerFx = p.effects.find((fx) => fx.type === 'power-arc');
    if (powerFx) {
      const swLen = GAME_TILE * 1.3;
      gameCtx.strokeStyle = '#e94560';
      gameCtx.lineWidth = 4;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, swLen, 0, Math.PI * 2);
      gameCtx.stroke();
      // Faint fill
      gameCtx.fillStyle = 'rgba(233, 69, 96, 0.15)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, swLen, 0, Math.PI * 2);
      gameCtx.fill();
    }

    // Hit flash
    if (p.effects.some((fx) => fx.type === 'hit')) {
      gameCtx.fillStyle = 'rgba(255,0,0,0.3)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 2, 0, Math.PI * 2);
      gameCtx.fill();
    }

    // Blind ring (Poker)
    if (p.blindBuff === 'small') {
      gameCtx.strokeStyle = 'rgba(100, 200, 255, 0.7)';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 7, 0, Math.PI * 2);
      gameCtx.stroke();
    } else if (p.blindBuff === 'big') {
      gameCtx.strokeStyle = 'rgba(255, 80, 80, 0.7)';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 7, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.fillStyle = 'rgba(255, 80, 80, 0.8)';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('BIG ' + Math.ceil(p.blindTimer) + 's', sx, sy + radius + 18);
    }

    // Chip change indicator
    if (p.chipChangeDmg >= 0 && p.chipChangeTimer > 0) {
      gameCtx.fillStyle = '#f5a623';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('♠' + p.chipChangeDmg + ' ' + Math.ceil(p.chipChangeTimer) + 's', sx, sy + radius + (p.blindBuff === 'big' ? 28 : 18));
    }

    // Royal Flush explosion effect
    if (p.effects.some((fx) => fx.type === 'royal-flush')) {
      gameCtx.strokeStyle = '#f5a623';
      gameCtx.lineWidth = 4;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 20, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.fillStyle = 'rgba(245, 166, 35, 0.2)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 20, 0, Math.PI * 2);
      gameCtx.fill();
    }

    // Filbus: Chair swing arc effect
    const chairFx = p.effects.find((fx) => fx.type === 'chair-swing');
    if (chairFx) {
      const swLen = GAME_TILE * 1.5;
      gameCtx.strokeStyle = '#a0522d';
      gameCtx.lineWidth = 4;
      gameCtx.beginPath();
      const aRad = Math.atan2(chairFx.aimNy, chairFx.aimNx);
      gameCtx.arc(sx, sy, swLen, aRad - 0.6, aRad + 0.6);
      gameCtx.stroke();
    }

    // Filbus: Table swing effect (bigger, orange)
    const tableFx = p.effects.find((fx) => fx.type === 'table-swing');
    if (tableFx) {
      const swLen = GAME_TILE * 2.2;
      gameCtx.strokeStyle = '#ff6600';
      gameCtx.lineWidth = 5;
      gameCtx.beginPath();
      const aRad = Math.atan2(tableFx.aimNy, tableFx.aimNx);
      gameCtx.arc(sx, sy, swLen, aRad - 0.7, aRad + 0.7);
      gameCtx.stroke();
      gameCtx.fillStyle = 'rgba(255, 102, 0, 0.15)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, swLen, aRad - 0.7, aRad + 0.7);
      gameCtx.fill();
    }

    // Filbus: Crafting channel indicator
    if (p.isCraftingChair) {
      const pct = 1 - (p.craftTimer / ((p.fighter.abilities && p.fighter.abilities[1] ? p.fighter.abilities[1].channelTime : 10) || 10));
      gameCtx.strokeStyle = '#c8a96e';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 10, -Math.PI / 2, -Math.PI / 2 + pct * Math.PI * 2);
      gameCtx.stroke();
      gameCtx.fillStyle = '#c8a96e';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('🪑 ' + Math.ceil(p.craftTimer) + 's', sx, sy + radius + 20);
    }

    // Filbus: Eating channel indicator
    if (p.isEatingChair) {
      const pct = 1 - (p.eatTimer / ((p.fighter.abilities && p.fighter.abilities[2] ? p.fighter.abilities[2].channelTime : 3) || 3));
      gameCtx.strokeStyle = '#2ecc71';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 10, -Math.PI / 2, -Math.PI / 2 + pct * Math.PI * 2);
      gameCtx.stroke();
      gameCtx.fillStyle = '#2ecc71';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('🍽 ' + Math.ceil(p.eatTimer) + 's', sx, sy + radius + 20);
    }

    // Filbus: Chair charges display
    if (p.fighter && p.fighter.id === 'filbus' && p.chairCharges > 0 && p.alive) {
      gameCtx.fillStyle = '#c8a96e';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('🪑×' + p.chairCharges, sx, sy + radius + (p.isCraftingChair || p.isEatingChair ? 32 : 18));
    }

    // Filbus: Boiled One dark aura
    if (p.boiledOneActive) {
      gameCtx.strokeStyle = '#8b0000';
      gameCtx.lineWidth = 4;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 16, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.fillStyle = 'rgba(139, 0, 0, 0.2)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 16, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.fillStyle = '#8b0000';
      gameCtx.font = 'bold 10px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('🩸BOILED ' + Math.ceil(p.boiledOneTimer) + 's', sx, sy - radius - 26);
    }

    // 1X1X1X1: Slash arc effect (neon green)
    const slashFx = p.effects.find((fx) => fx.type === 'slash-1x');
    if (slashFx) {
      const swLen = GAME_TILE * 1.3;
      gameCtx.strokeStyle = '#00ff66';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      const aRad = Math.atan2(slashFx.aimNy, slashFx.aimNx);
      gameCtx.arc(sx, sy, swLen, aRad - 0.5, aRad + 0.5);
      gameCtx.stroke();
    }

    // 1X1X1X1: Mass Infection green shockwave
    const miFx = p.effects.find((fx) => fx.type === 'mass-infection');
    if (miFx) {
      const waveR = GAME_TILE * 4;
      gameCtx.strokeStyle = '#00ff66';
      gameCtx.lineWidth = 5;
      const aRad = Math.atan2(miFx.aimNy, miFx.aimNx);
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, waveR, aRad - Math.PI / 2, aRad + Math.PI / 2);
      gameCtx.stroke();
      gameCtx.fillStyle = 'rgba(0, 255, 102, 0.12)';
      gameCtx.beginPath();
      gameCtx.moveTo(sx, sy);
      gameCtx.arc(sx, sy, waveR, aRad - Math.PI / 2, aRad + Math.PI / 2);
      gameCtx.closePath();
      gameCtx.fill();
    }

    // 1X1X1X1: Zombie slash effect (dark green arc)
    const zombieSlashFx = p.effects.find((fx) => fx.type === 'zombie-slash');
    if (zombieSlashFx) {
      const swLen = GAME_TILE * 1.2;
      gameCtx.strokeStyle = '#1a5c1a';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      const aRad = Math.atan2(zombieSlashFx.aimNy, zombieSlashFx.aimNx);
      gameCtx.arc(sx, sy, swLen, aRad - 0.4, aRad + 0.4);
      gameCtx.stroke();
    }

    // Poison visual: green ring when poisoned
    if (p.poisonTimers && p.poisonTimers.length > 0 && p.alive) {
      gameCtx.strokeStyle = 'rgba(0, 255, 102, 0.7)';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 4, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.fillStyle = '#00ff66';
      gameCtx.font = 'bold 8px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('☣ POISON', sx, sy - radius - 8);
    }

    // Unstable Eye: speed indicator
    if (p.unstableEyeTimer > 0) {
      gameCtx.strokeStyle = '#00ff66';
      gameCtx.lineWidth = 3;
      gameCtx.setLineDash([4, 4]);
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 12, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.setLineDash([]);
      gameCtx.fillStyle = '#00ff66';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('👁 EYE ' + Math.ceil(p.unstableEyeTimer) + 's', sx, sy - radius - 18);
    }

    // Summon-specific rendering
    if (p.isSummon) {
      // Tether line to owner
      const owner2 = gamePlayers.find(pl => pl.id === p.summonOwner);
      if (owner2 && owner2.alive) {
        const ownSx = owner2.x - camX;
        const ownSy = owner2.y - camY;
        gameCtx.strokeStyle = 'rgba(212, 175, 55, 0.3)';
        gameCtx.lineWidth = 1;
        gameCtx.beginPath();
        gameCtx.moveTo(sx, sy);
        gameCtx.lineTo(ownSx, ownSy);
        gameCtx.stroke();
      }
    }

    gameCtx.restore();
  }

  // Draw projectiles
  for (const proj of projectiles) {
    const px = proj.x - camX;
    const py = proj.y - camY;
    if (px < -50 || px > cw + 50 || py < -50 || py > ch + 50) continue;
    if (proj.type === 'chip') {
      gameCtx.fillStyle = '#f5a623';
      gameCtx.beginPath();
      gameCtx.arc(px, py, 5, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.strokeStyle = '#333';
      gameCtx.lineWidth = 1;
      gameCtx.stroke();
    } else if (proj.type === 'card') {
      gameCtx.save();
      const angle = Math.atan2(proj.vy, proj.vx);
      gameCtx.translate(px, py);
      gameCtx.rotate(angle);
      // Large card shape
      gameCtx.fillStyle = '#fff';
      gameCtx.fillRect(-14, -9, 28, 18);
      gameCtx.strokeStyle = '#e94560';
      gameCtx.lineWidth = 2;
      gameCtx.strokeRect(-14, -9, 28, 18);
      gameCtx.fillStyle = '#e94560';
      gameCtx.font = 'bold 12px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.textBaseline = 'middle';
      gameCtx.fillText('♠', 0, 0);
      gameCtx.restore();
    } else if (proj.type === 'entangle') {
      // Neon green spinning swords
      gameCtx.save();
      const angle = Math.atan2(proj.vy, proj.vx) + (Date.now() / 100);
      gameCtx.translate(px, py);
      gameCtx.rotate(angle);
      gameCtx.strokeStyle = '#00ff66';
      gameCtx.lineWidth = 2.5;
      gameCtx.beginPath();
      gameCtx.moveTo(-10, 0);
      gameCtx.lineTo(10, 0);
      gameCtx.moveTo(0, -10);
      gameCtx.lineTo(0, 10);
      gameCtx.stroke();
      // Glow
      gameCtx.fillStyle = 'rgba(0, 255, 102, 0.3)';
      gameCtx.beginPath();
      gameCtx.arc(0, 0, 8, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.restore();
    }
  }

  // Boiled One horror overlay — dark reddish tint + random dark patches
  const anyBoiledOne = gamePlayers.some(p => p.boiledOneActive);
  if (anyBoiledOne) {
    gameCtx.fillStyle = 'rgba(60, 0, 0, 0.5)';
    gameCtx.fillRect(0, 0, cw, ch);
    // Random dark splotches scattered across the screen (seeded by frame-stable positions)
    const t = Math.floor(Date.now() / 200); // shift slowly
    for (let i = 0; i < 18; i++) {
      const seed = i * 7919 + 1301;
      const px = ((seed * 31 + t * 3) % cw + cw) % cw;
      const py = ((seed * 47 + t * 5) % ch + ch) % ch;
      const r = 30 + (seed % 60);
      const alpha = 0.08 + (seed % 12) * 0.015;
      gameCtx.fillStyle = 'rgba(0, 0, 0, ' + alpha + ')';
      gameCtx.beginPath();
      gameCtx.arc(px, py, r, 0, Math.PI * 2);
      gameCtx.fill();
    }
  }

  // Unstable Eye overlay: blur + green outlines (only visible to the 1x player, overridden by Boiled One)
  if (localPlayer && localPlayer.unstableEyeTimer > 0 && localPlayer.fighter.id === 'onexonexonex' && !anyBoiledOne) {
    // 60% blur overlay
    gameCtx.fillStyle = 'rgba(0, 40, 0, 0.15)';
    gameCtx.fillRect(0, 0, cw, ch);
    // Green outlines on all enemy players (reveal effect)
    for (const p of gamePlayers) {
      if (p.id === localPlayerId || !p.alive) continue;
      if (p.isSummon && p.summonOwner === localPlayerId) continue;
      const ex = p.x - camX;
      const ey = p.y - camY;
      if (ex < -100 || ex > cw + 100 || ey < -100 || ey > ch + 100) continue;
      const r = GAME_TILE * PLAYER_RADIUS_RATIO;
      gameCtx.strokeStyle = '#00ff66';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(ex, ey, r + 8, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.fillStyle = 'rgba(0, 255, 102, 0.15)';
      gameCtx.beginPath();
      gameCtx.arc(ex, ey, r + 8, 0, Math.PI * 2);
      gameCtx.fill();
    }
  }

  // Draw zone overlay
  if (zoneInset > 0) {
    gameCtx.fillStyle = 'rgba(200, 30, 30, 0.25)';
    for (let r = startRow; r <= endRow; r++) {
      for (let c = startCol; c <= endCol; c++) {
        if (r < zoneInset || r >= gameMap.rows - zoneInset ||
            c < zoneInset || c >= gameMap.cols - zoneInset) {
          if (r >= 0 && r < gameMap.rows && c >= 0 && c < gameMap.cols) {
            const ox = c * GAME_TILE - camX;
            const oy = r * GAME_TILE - camY;
            gameCtx.fillRect(ox, oy, GAME_TILE, GAME_TILE);
          }
        }
      }
    }
    // Zone border line
    const zx = zoneInset * GAME_TILE - camX;
    const zy = zoneInset * GAME_TILE - camY;
    const zw = (gameMap.cols - zoneInset * 2) * GAME_TILE;
    const zh = (gameMap.rows - zoneInset * 2) * GAME_TILE;
    gameCtx.strokeStyle = 'rgba(255, 60, 60, 0.7)';
    gameCtx.lineWidth = 3;
    gameCtx.strokeRect(zx, zy, zw, zh);
  }

  // Zone timer countdown
  gameCtx.save();
  gameCtx.font = 'bold 16px "Press Start 2P", monospace';
  gameCtx.textAlign = 'center';
  gameCtx.fillStyle = '#000';
  gameCtx.fillText('Zone: ' + Math.ceil(zoneTimer) + 's', cw / 2 + 1, 33);
  gameCtx.fillStyle = zoneTimer <= 10 ? '#e94560' : '#fff';
  gameCtx.fillText('Zone: ' + Math.ceil(zoneTimer) + 's', cw / 2, 32);
  gameCtx.restore();

  // Spectator overlay when dead
  if (localPlayer && !localPlayer.alive) {
    gameCtx.save();
    // Slight dark overlay
    gameCtx.fillStyle = 'rgba(0,0,0,0.15)';
    gameCtx.fillRect(0, 0, cw, ch);
    // "YOU DIED" text
    gameCtx.font = 'bold 36px "Press Start 2P", monospace';
    gameCtx.textAlign = 'center';
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('YOU DIED', cw / 2 + 2, ch / 2 - 40 + 2);
    gameCtx.fillStyle = '#8b0000';
    gameCtx.fillText('YOU DIED', cw / 2, ch / 2 - 40);
    // Spectator hint
    gameCtx.font = 'bold 12px "Press Start 2P", monospace';
    gameCtx.fillStyle = '#ccc';
    if (spectateIndex >= 0 && gamePlayers[spectateIndex]) {
      gameCtx.fillText('Spectating: ' + gamePlayers[spectateIndex].name, cw / 2, ch / 2);
    }
    gameCtx.fillText('TAB = cycle players | WASD = free cam | ESC = free cam', cw / 2, ch / 2 + 24);
    gameCtx.restore();
  }

  // Draw HP in top-left corner
  drawTopRightHP();

  // Draw active effects log at center top
  drawEffectLog();

  // Update HUD
  updateHUD();
}

// ═══════════════════════════════════════════════════════════════
// HUD
// ═══════════════════════════════════════════════════════════════
function drawTopRightHP() {
  if (!localPlayer) return;
  const lp = localPlayer;
  const hpFrac = Math.max(0, lp.hp / lp.maxHp);
  const hpColor = hpFrac >= 0.7 ? '#2ecc71' : hpFrac >= 0.4 ? '#f5a623' : '#e94560';
  const text = Math.ceil(lp.hp) + '/' + lp.maxHp;

  gameCtx.save();
  gameCtx.font = 'bold 22px "Press Start 2P", monospace';
  gameCtx.textAlign = 'left';
  gameCtx.fillStyle = '#000';
  gameCtx.fillText(text, 22, 38);
  gameCtx.fillStyle = hpColor;
  gameCtx.fillText(text, 20, 36);
  gameCtx.restore();
}

function drawEffectLog() {
  if (!localPlayer) return;
  const lp = localPlayer;
  const cw = gameCanvas.width;

  // Draw centered at top, below zone timer
  gameCtx.save();
  gameCtx.font = 'bold 13px "Press Start 2P", monospace';
  gameCtx.textAlign = 'center';
  let logY = 56;
  if (lp.blindBuff === 'small') {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('🛡 Small Blind (½ dmg taken)', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#64c8ff';
    gameCtx.fillText('🛡 Small Blind (½ dmg taken)', cw / 2, logY);
    logY += 20;
  } else if (lp.blindBuff === 'big' && lp.blindTimer > 0) {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('⚠ Big Blind: take 1.5× dmg ' + Math.ceil(lp.blindTimer) + 's', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#ff5050';
    gameCtx.fillText('⚠ Big Blind: take 1.5× dmg ' + Math.ceil(lp.blindTimer) + 's', cw / 2, logY);
    logY += 20;
  } else if (lp.blindBuff === 'dealer') {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('🎰 Dealer — Gamble reset!', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#f5a623';
    gameCtx.fillText('🎰 Dealer — Gamble reset!', cw / 2, logY);
    logY += 20;
  }
  if (lp.chipChangeDmg >= 0 && lp.chipChangeTimer > 0) {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('♠ Chips→' + lp.chipChangeDmg + ' ' + Math.ceil(lp.chipChangeTimer) + 's', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#f5a623';
    gameCtx.fillText('♠ Chips→' + lp.chipChangeDmg + ' ' + Math.ceil(lp.chipChangeTimer) + 's', cw / 2, logY);
    logY += 20;
  }
  if (lp.supportBuff > 0) {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('💪 Support ' + Math.ceil(lp.supportBuff) + 's', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#2ecc71';
    gameCtx.fillText('💪 Support ' + Math.ceil(lp.supportBuff) + 's', cw / 2, logY);
    logY += 20;
  }
  if (lp.intimidated > 0) {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('😨 Intimidated ' + Math.ceil(lp.intimidated) + 's', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#9b59b6';
    gameCtx.fillText('😨 Intimidated ' + Math.ceil(lp.intimidated) + 's', cw / 2, logY);
    logY += 20;
  }
  // Filbus status
  if (lp.isCraftingChair) {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('🪑 Crafting... ' + Math.ceil(lp.craftTimer) + 's', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#c8a96e';
    gameCtx.fillText('🪑 Crafting... ' + Math.ceil(lp.craftTimer) + 's', cw / 2, logY);
    logY += 20;
  }
  if (lp.isEatingChair) {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('🍽 Eating chair... ' + Math.ceil(lp.eatTimer) + 's', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#2ecc71';
    gameCtx.fillText('🍽 Eating chair... ' + Math.ceil(lp.eatTimer) + 's', cw / 2, logY);
    logY += 20;
  }
  if (lp.chairCharges > 0) {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('🪑 Chairs: ' + lp.chairCharges, cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#c8a96e';
    gameCtx.fillText('🪑 Chairs: ' + lp.chairCharges, cw / 2, logY);
    logY += 20;
  }
  if (lp.boiledOneActive) {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('🩸 BOILED ONE ' + Math.ceil(lp.boiledOneTimer) + 's', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#8b0000';
    gameCtx.fillText('🩸 BOILED ONE ' + Math.ceil(lp.boiledOneTimer) + 's', cw / 2, logY);
    logY += 20;
  }
  for (let i = 0; i < combatLog.length; i++) {
    const entry = combatLog[i];
    gameCtx.fillStyle = '#000';
    gameCtx.fillText(entry.text, cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = entry.color;
    gameCtx.fillText(entry.text, cw / 2, logY);
    logY += 20;
  }
  gameCtx.restore();
}

function buildHUD() {
  const abils = document.querySelector('#hud-abilities');
  abils.innerHTML = '';
  const fighter = localPlayer.fighter;
  const keys = ['M1', 'E', 'R', 'T', 'SPC'];
  const names = fighter.abilities.map((a) => {
    const n = a.name;
    return n.length > 7 ? n.substring(0, 6) + '.' : n;
  });
  keys.forEach((k, i) => {
    const div = document.createElement('div');
    div.className = 'hud-ability ready';
    div.id = 'hud-ab-' + k;
    div.innerHTML = `<span class="key-label">${k}</span>`;
    div.title = names[i] || '';
    abils.appendChild(div);
  });
  // Show special bar
  document.querySelector('#hud-special-bar').classList.remove('hidden');
}

function updateHUD() {
  if (!localPlayer) return;
  const lp = localPlayer;

  // HP bar (bottom HUD)
  const hpFrac = Math.max(0, lp.hp / lp.maxHp);
  const hpFill = document.querySelector('#hud-hp-fill');
  hpFill.style.width = (hpFrac * 100) + '%';
  // Match HP bar colour to thresholds
  hpFill.style.background = hpFrac >= 0.7 ? '#2ecc71' : hpFrac >= 0.4 ? '#f5a623' : '#e94560';
  document.querySelector('#hud-hp-text').textContent = Math.ceil(lp.hp) + '/' + lp.maxHp;

  // Special meter
  const specThresh = lp.maxHp * 2;
  const specFrac = Math.min(1, lp.totalDamageTaken / specThresh);
  document.querySelector('#hud-special-fill').style.width = (specFrac * 100) + '%';

  // Ability cooldowns
  const cds = [
    { id: 'M1', cd: lp.cdM1, max: lp.fighter.abilities[0].cooldown },
    { id: 'E', cd: lp.cdE, max: lp.fighter.abilities[1].cooldown },
    { id: 'R', cd: lp.cdR, max: lp.fighter.abilities[2].cooldown },
    { id: 'T', cd: lp.cdT, max: lp.fighter.abilities[3].cooldown },
    { id: 'SPC', cd: lp.specialUsed ? 999 : (lp.specialUnlocked ? 0 : 999), max: 1 },
  ];

  cds.forEach((c) => {
    const el = document.querySelector('#hud-ab-' + c.id);
    if (!el) return;
    const existing = el.querySelector('.cd-overlay');
    if (c.cd > 0.05) {
      el.className = 'hud-ability on-cd';
      if (!existing) {
        const ov = document.createElement('div');
        ov.className = 'cd-overlay';
        el.appendChild(ov);
      }
      const ov = el.querySelector('.cd-overlay');
      if (c.id === 'SPC') {
        ov.textContent = lp.specialUsed ? '✓' : '🔒';
      } else {
        ov.textContent = Math.ceil(c.cd) + 's';
      }
    } else {
      if (c.id === 'SPC' && lp.specialUnlocked && !lp.specialUsed) {
        el.className = 'hud-ability special-ready';
      } else {
        el.className = 'hud-ability ready';
      }
      if (existing) existing.remove();
    }
  });
}

function showPopup(text) {
  const popup = document.querySelector('#hud-popup');
  popup.textContent = text;
  popup.classList.remove('hidden');
  setTimeout(() => popup.classList.add('hidden'), 2500);
}

function checkWinCondition() {
  if (gameMode === 'fight') {
    const alive = gamePlayers.filter(p => p.alive && !p.isSummon);
    // When local player dies, show placement immediately
    if (!localPlayer.alive && gameRunning) {
      const place = alive.length + 1; // they were eliminated, so their place = alive count + 1
      gameRunning = false;
      const cw = gameCanvas.width;
      const ch = gameCanvas.height;
      gameCtx.fillStyle = 'rgba(0, 0, 0, 0.7)';
      gameCtx.fillRect(0, 0, cw, ch);
      gameCtx.font = 'bold 36px "Press Start 2P", monospace';
      gameCtx.textAlign = 'center';
      gameCtx.fillStyle = '#e94560';
      const suffix = place === 2 ? 'nd' : place === 3 ? 'rd' : 'th';
      gameCtx.fillText(place + suffix + ' PLACE', cw / 2, ch / 2);
      gameCtx.font = 'bold 14px "Press Start 2P", monospace';
      gameCtx.fillStyle = '#ccc';
      gameCtx.fillText('Refresh to play again', cw / 2, ch / 2 + 50);
      return;
    }
    // Victory if last alive
    if (alive.length <= 1) {
      gameRunning = false;
      const cw = gameCanvas.width;
      const ch = gameCanvas.height;
      gameCtx.fillStyle = 'rgba(0, 0, 0, 0.7)';
      gameCtx.fillRect(0, 0, cw, ch);
      gameCtx.font = 'bold 36px "Press Start 2P", monospace';
      gameCtx.textAlign = 'center';
      if (alive.length === 1 && alive[0].id === localPlayerId) {
        gameCtx.fillStyle = '#2ecc71';
        gameCtx.fillText('VICTORY!', cw / 2, ch / 2);
        gameCtx.font = 'bold 20px "Press Start 2P", monospace';
        gameCtx.fillStyle = '#fff';
        gameCtx.fillText('1st PLACE', cw / 2, ch / 2 + 50);
      } else {
        gameCtx.fillStyle = '#e94560';
        const winnerName = alive.length === 1 ? alive[0].name : 'Nobody';
        gameCtx.fillText(winnerName + ' WINS', cw / 2, ch / 2);
      }
      gameCtx.font = 'bold 14px "Press Start 2P", monospace';
      gameCtx.fillStyle = '#ccc';
      gameCtx.fillText('Refresh to play again', cw / 2, ch / 2 + 80);
    }
    return;
  }
  // Multiplayer: server handles this
  const realPlayers = gamePlayers.filter((p) => p.id !== 'dummy');
  if (realPlayers.length > 1) return;
}

// ═══════════════════════════════════════════════════════════════
// MULTIPLAYER SYNC
// ═══════════════════════════════════════════════════════════════
function onRemoteBuff(casterId, type, duration, cx, cy) {
  // Apply buff to the caster only
  if (type === 'support') {
    const caster = gamePlayers.find((p) => p.id === casterId);
    if (caster && caster.alive) caster.supportBuff = duration;
  } else if (type === 'blind') {
    const caster = gamePlayers.find((p) => p.id === casterId);
    if (caster && caster.alive) {
      // Visual only — damage modifiers are resolved locally by the attacker
      caster.blindBuff = duration > 0 ? 'big' : 'small';
      caster.blindTimer = duration;
    }
  } else if (type === 'royal-flush') {
    // Royal Flush: distance-tiered effects
    const caster = gamePlayers.find((p) => p.id === casterId);
    const casterX = cx || (caster ? caster.x : 0);
    const casterY = cy || (caster ? caster.y : 0);
    const closeRange = 3 * GAME_TILE;
    const mediumRange = 10 * GAME_TILE;
    for (const target of gamePlayers) {
      if (target.id === casterId || !target.alive) continue;
      const ddx = target.x - casterX; const ddy = target.y - casterY;
      const dist = Math.sqrt(ddx * ddx + ddy * ddy);
      if (dist > mediumRange) continue;
      if (dist <= closeRange) {
        target.stunned = duration;
        target.effects.push({ type: 'stun', timer: duration });
      }
      target.cdM1 = target.fighter.abilities[0].cooldown;
      target.cdE = target.fighter.abilities[1].cooldown;
      target.cdR = target.fighter.abilities[2].cooldown;
      target.cdT = target.fighter.abilities[3].cooldown;
      target.specialUnlocked = false;
      target.totalDamageTaken = 0;
    }
    if (caster) caster.effects.push({ type: 'royal-flush', timer: 2.0 });
  }
}

function onRemoteDebuff(casterId, targetId, type, duration) {
  if (type === 'intimidation') {
    const target = gamePlayers.find((p) => p.id === targetId);
    if (target) {
      target.intimidated = duration;
      target.intimidatedBy = casterId;
    }
  }
}

function onRemoteProjectiles(ownerId, projs) {
  // Add visual-only projectiles (no damage — owner's client resolves hits)
  for (const p of projs) {
    projectiles.push({
      x: p.x, y: p.y, vx: p.vx, vy: p.vy,
      ownerId: ownerId, damage: 0, // 0 damage — visual only
      timer: p.timer, type: p.type,
    });
  }
}

function onPlayerMove(id, x, y, hp) {
  const p = gamePlayers.find((pl) => pl.id === id);
  if (p && p.id !== localPlayerId) {
    p.x = x;
    p.y = y;
    if (hp !== undefined) p.hp = hp;
  }
}

// ═══════════════════════════════════════════════════════════════
// UTIL
// ═══════════════════════════════════════════════════════════════
function shuffleArray(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
}
