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

// ═══════════════════════════════════════════════════════════════
// START GAME
// ═══════════════════════════════════════════════════════════════
function startGame(mapIndex, players, myId) {
  gameCanvas = document.querySelector('#game-canvas');
  gameCtx = gameCanvas.getContext('2d');
  gameMap = MAPS[mapIndex];
  localPlayerId = myId;

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

  // In singleplayer, add a training dummy so the player can deal damage and unlock special
  if (gamePlayers.length === 1) {
    const dummySpawn = validSpawns[1] || validSpawns[0];
    const dummyFighter = getFighter('fighter');
    const dummy = createPlayerState(
      { id: 'dummy', name: 'Training Dummy', color: '#555' },
      dummySpawn,
      dummyFighter
    );
    dummy.hp = 99999;
    dummy.maxHp = 99999;
    gamePlayers.push(dummy);
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

  if (!localPlayer || !localPlayer.alive) return;

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
  if (!localPlayer || !localPlayer.alive) return;

  // Use wall-clock delta for timers so they keep running in background tabs
  const wallNow = Date.now();
  const wallDt = Math.min((wallNow - lastWallClock) / 1000, 2); // cap at 2s to avoid huge jumps
  lastWallClock = wallNow;

  // Tick cooldowns
  tickCooldowns(localPlayer, wallDt);

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
        if (p.hp <= 0) { p.hp = 0; p.alive = false; }
      }
    }

    // Tick effects
    p.effects = p.effects.filter((fx) => {
      fx.timer -= wallDt;
      return fx.timer > 0;
    });

    // Tick Poker-specific timers
    if (p.blindTimer > 0) {
      p.blindTimer = Math.max(0, p.blindTimer - wallDt);
      if (p.blindTimer <= 0 && p.blindBuff === 'big') p.blindBuff = null;
    }
    if (p.chipChangeTimer > 0) {
      p.chipChangeTimer = Math.max(0, p.chipChangeTimer - wallDt);
      if (p.chipChangeTimer <= 0) p.chipChangeDmg = -1;
    }
  }

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

  // Handle special aiming
  if (localPlayer.specialAiming) {
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
    return; // Skip normal movement while aiming
  }

  // Movement
  if (localPlayer.stunned > 0) return;
  updateMovement(dt);

  // Update projectiles
  updateProjectiles(dt);

  // M1 – auto-fire while mouse held
  if (mouseDown && localPlayer.cdM1 <= 0) {
    useAbility('M1');
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

    // Wall collision (rock/water/out of bounds)
    const col = Math.floor(p.x / GAME_TILE);
    const row = Math.floor(p.y / GAME_TILE);
    if (col < 0 || col >= gameMap.cols || row < 0 || row >= gameMap.rows) {
      projectiles.splice(i, 1); continue;
    }
    const tile = gameMap.tiles[row][col];
    if (tile === TILE.ROCK || tile === TILE.WATER) {
      projectiles.splice(i, 1); continue;
    }

    // Hit detection against players (only owner's client resolves damage)
    if (p.ownerId === localPlayerId) {
      for (const target of gamePlayers) {
        if (target.id === p.ownerId || !target.alive) continue;
        const dx = target.x - p.x;
        const dy = target.y - p.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist < radius + 4) {
          dealDamage(localPlayer, target, p.damage);
          projectiles.splice(i, 1);
          break;
        }
      }
    }
  }
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
        const proj = { x: lp.x, y: lp.y, vx, vy, ownerId: lp.id, damage: dmg, timer: 1.5, type: 'chip' };
        projectiles.push(proj);
        spawnedChips.push({ x: proj.x, y: proj.y, vx, vy, timer: 1.5, type: 'chip' });
      }
      // Visual sync to other clients
      if (typeof socket !== 'undefined' && socket.emit) {
        socket.emit('projectile-spawn', { projectiles: spawnedChips });
      }
      // Clear small blind when using another move
      if (lp.blindBuff === 'small') lp.blindBuff = null;
      lp.effects.push({ type: 'chip-throw', timer: 0.2 });
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
      const cvx = Math.cos(angle) * (abil.projectileSpeed || 10) * GAME_TILE / 10;
      const cvy = Math.sin(angle) * (abil.projectileSpeed || 10) * GAME_TILE / 10;
      projectiles.push({
        x: lp.x, y: lp.y, vx: cvx, vy: cvy,
        ownerId: lp.id, damage: Math.round(dmg),
        timer: 2.0, type: 'card',
      });
      // Visual sync
      if (typeof socket !== 'undefined' && socket.emit) {
        socket.emit('projectile-spawn', { projectiles: [{ x: lp.x, y: lp.y, vx: cvx, vy: cvy, timer: 2.0, type: 'card' }] });
      }
      showPopup('🎲 Gamble: ' + Math.round(dmg) + ' DMG!');
      // Clear small blind when using another move
      if (lp.blindBuff === 'small') lp.blindBuff = null;
      lp.effects.push({ type: 'gamble', timer: 0.5 });
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
      const options = [0, 100, 200, 300, 400];
      lp.chipChangeDmg = options[Math.floor(Math.random() * options.length)];
      lp.chipChangeTimer = abil.duration || 30;
      showPopup('♠ Chip Change: M1 → ' + lp.chipChangeDmg + ' DMG!');
      // Clear small blind when using another move
      if (lp.blindBuff === 'small') lp.blindBuff = null;
      lp.effects.push({ type: 'chip-change', timer: 1.5 });
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
      // Royal Flush: heal to full, stun enemies, reset their CDs, execute <500hp
      lp.specialUsed = true;
      lp.hp = lp.maxHp;
      const stunDur = fighter.abilities[4].stunDuration || 3;
      const execThresh = fighter.abilities[4].executeThreshold || 500;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        // Auto-kill if below threshold
        if (target.hp <= execThresh) {
          dealDamage(lp, target, target.hp);
        } else {
          // Stun
          target.stunned = stunDur;
          target.effects.push({ type: 'stun', timer: stunDur });
        }
        // Reset all their cooldowns (simulating debt)
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
      // Broadcast stun + reset to other clients
      if (typeof socket !== 'undefined' && socket.emit) {
        socket.emit('player-buff', { type: 'royal-flush', duration: stunDur });
      }
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
    if (lp.hp <= 0) { lp.alive = false; lp.hp = 0; }
    lp.effects.push({ type: 'stun', timer: abil.missStun });
  }

  lp.effects.push({ type: 'land', timer: 0.5 });
}

function dealDamage(attacker, target, amount) {
  if (!target.alive) return;
  // Blinds modifier (Poker)
  if (target.blindBuff === 'small') amount = Math.round(amount * 0.5);
  else if (target.blindBuff === 'big') amount = Math.round(amount * 1.5);
  target.hp -= amount;
  // Reset heal state on damage
  target.noDamageTimer = 0;
  target.isHealing = false;
  target.healTickTimer = 0;
  target.effects.push({ type: 'hit', timer: 0.3 });

  // Track damage taken for special unlock
  target.totalDamageTaken += amount;
  if (!target.specialUnlocked && target.totalDamageTaken >= target.maxHp * 2) {
    target.specialUnlocked = true;
    if (target.id === localPlayerId) {
      showPopup('⚡ SPECIAL UNLOCKED! [SPACE]');
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

  const camX = localPlayer.x - cw / 2;
  const camY = localPlayer.y - ch / 2;

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
    const dotAlpha = (isLocal && inAnyGrass) ? 0.4 : (p.alive ? 1.0 : 0.3);

    gameCtx.save();
    gameCtx.globalAlpha = dotAlpha;

    // Stunned visual
    if (p.stunned > 0) {
      gameCtx.fillStyle = 'rgba(255,255,0,0.2)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 4, 0, Math.PI * 2);
      gameCtx.fill();
    }

    // Dot
    gameCtx.fillStyle = p.color;
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
      gameCtx.fillStyle = '#f5a623';
      gameCtx.beginPath();
      gameCtx.arc(chipX, chipY, chipR, 0, Math.PI * 2);
      gameCtx.fill();
      // Outer ring
      gameCtx.strokeStyle = '#d4891a';
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
    gameCtx.fillStyle = '#fff';
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
      gameCtx.fillStyle = '#fff';
      gameCtx.fillRect(-8, -5, 16, 10);
      gameCtx.strokeStyle = '#e94560';
      gameCtx.lineWidth = 1;
      gameCtx.strokeRect(-8, -5, 16, 10);
      gameCtx.fillStyle = '#e94560';
      gameCtx.font = 'bold 8px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.textBaseline = 'middle';
      gameCtx.fillText('♠', 0, 0);
      gameCtx.restore();
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

  // Draw HP in top-left corner
  drawTopRightHP();

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
  // In singleplayer only — multiplayer uses server-side win detection
  const realPlayers = gamePlayers.filter((p) => p.id !== 'dummy');
  if (realPlayers.length > 1) return; // multiplayer: server handles this
  // Singleplayer: no win/loss to check
}

// ═══════════════════════════════════════════════════════════════
// MULTIPLAYER SYNC
// ═══════════════════════════════════════════════════════════════
function onRemoteBuff(casterId, type, duration) {
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
    // Royal Flush: stun all non-casters, handled by caster's client for damage
    const stunDur = duration;
    for (const target of gamePlayers) {
      if (target.id === casterId || !target.alive) continue;
      target.stunned = stunDur;
      target.effects.push({ type: 'stun', timer: stunDur });
      target.cdM1 = target.fighter.abilities[0].cooldown;
      target.cdE = target.fighter.abilities[1].cooldown;
      target.cdR = target.fighter.abilities[2].cooldown;
      target.cdT = target.fighter.abilities[3].cooldown;
      target.specialUnlocked = false;
      target.totalDamageTaken = 0;
    }
    const caster = gamePlayers.find((p) => p.id === casterId);
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
