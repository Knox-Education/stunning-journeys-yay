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
const TEAM_HEAL_RANGE = 3; // tiles — range for team heal/buff sharing

let gameRunning = false;
let gameCanvas, gameCtx;
let gameMap;
let gamePlayers = [];    // [{id, name, color, x, y, hp, maxHp, fighter, ...}]
let localPlayerId = null;
let localPlayer = null;
let lastTime = 0;

// Host-authoritative multiplayer
// remoteInputs: map of playerId -> {keys:{}, mouseX, mouseY, mouseDown, pendingAbilities:[]}
let remoteInputs = {};
let isHostAuthority = false; // true if we are the host in a multiplayer game

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
let deathOverlayTimer = 0; // seconds since local player died — used to fade out "YOU DIED"
let diedInOtherWorld = false; // true if local player died while in backrooms or with alternate
let screenShakeTimer = 0; // screen shake effect timer

// Training dummy respawn timer
let dummyRespawnTimer = 0;

// Apple tree state
let appleTree = null; // {col, row, hp, maxHp, alive, regrowTimer, appleTimer, apples:[{col,row}]}

// Game mode: 'training' | 'fight' | 'teams' | undefined (multiplayer FFA)
let gameMode = undefined;
let respawnMode = false; // true for 2-team respawn mode
let respawnGameTimer = 180; // 3 minute game timer for respawn mode
let respawnTeam1Kills = 0;
let respawnTeam2Kills = 0;

// Animation frame ID for cancellation
let _gameLoopFrameId = null;

// Deferred removal IDs (avoids splice inside for..of)
const _deferredRemoveIds = [];

// Achievement: track which ability keys the local player used this game
let usedAbilityKeys = new Set();

// Achievement (round 2): per-game kill counters
let _fighterSpecialKillsThisGame = 0;
let _noliVoidRushKillsThisGame = 0;
let _catKittenKillsThisGame = 0;
let _gearDmgAbsorbedRemainder = 0; // fractional damage not yet added to progress
let _filbusBoiledKillsThisGame = 0;
let _hadSummonKillThisGame = false;
let _lastDealDamageWasM1 = false;

// CPU names
const CPU_NAMES = ['Alpha', 'Bravo', 'Charlie', 'Delta', 'Echo', 'Foxtrot', 'Ghost', 'Havoc'];
const CPU_COLORS = ['#e67e22', '#1abc9c', '#9b59b6', '#e74c3c', '#3498db', '#f1c40f'];

// Power Special threshold: 3× max HP if fighter has achievement unlocked, 2× otherwise
// CPUs always use 2× (they cannot use Power Specials)
function getSpecialThreshold(p) {
  if (p.isCPU) return p.maxHp * 2;
  const hasPower = typeof isMove4Unlocked === 'function' && isMove4Unlocked(p.fighter.id);
  return p.maxHp * (hasPower ? 3 : 2);
}

// ═══════════════════════════════════════════════════════════════
// START GAME
// ═══════════════════════════════════════════════════════════════
function startGame(mapIndex, players, myId, mode) {
  gameCanvas = document.querySelector('#game-canvas');
  gameCtx = gameCanvas.getContext('2d');
  // Deep-copy the map so apple tree tile overrides don't permanently mutate MAPS
  const srcMap = MAPS[mapIndex];
  gameMap = {
    ...srcMap,
    tiles: srcMap.tiles.map(row => row.slice()),
  };
  localPlayerId = myId;
  if (mode === 'teams-respawn') {
    gameMode = 'teams';
    respawnMode = true;
    respawnGameTimer = 180;
    respawnTeam1Kills = 0;
    respawnTeam2Kills = 0;
  } else {
    gameMode = mode;
    respawnMode = false;
  }
  usedAbilityKeys = new Set();
  _fighterSpecialKillsThisGame = 0;
  _noliVoidRushKillsThisGame = 0;
  _catKittenKillsThisGame = 0;
  _gearDmgAbsorbedRemainder = 0;
  _filbusBoiledKillsThisGame = 0;
  _hadSummonKillThisGame = false;
  _dragonBeamKillsThisGame = 0;
  _lastDealDamageWasM1 = false;
  window._spikeEntities = [];

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

  // Pick spawn points spread around corners and edges — need 7 unique for up to 6 CPUs + 1 player
  const spawnCandidates = [
    { r: 1, c: 1 },                                                          // top-left
    { r: 1, c: gameMap.cols - 2 },                                            // top-right
    { r: gameMap.rows - 2, c: 1 },                                            // bottom-left
    { r: gameMap.rows - 2, c: gameMap.cols - 2 },                              // bottom-right
    { r: 1, c: Math.floor(gameMap.cols / 2) },                                 // top-center
    { r: gameMap.rows - 2, c: Math.floor(gameMap.cols / 2) },                   // bottom-center
    { r: Math.floor(gameMap.rows / 2), c: 1 },                                 // mid-left
    { r: Math.floor(gameMap.rows / 2), c: gameMap.cols - 2 },                   // mid-right
  ];
  // Filter to walkable and pick unique positions
  const validSpawns = spawnCandidates.filter((s) => {
    if (s.r < 0 || s.r >= gameMap.rows || s.c < 0 || s.c >= gameMap.cols) return false;
    const t = gameMap.tiles[s.r][s.c];
    return t === TILE.GROUND || t === TILE.GRASS;
  });
  // Ensure at least 7 spawns (1 player + up to 6 CPUs) — add shuffled walkable tiles as fallback
  const requiredSpawns = 7;
  if (validSpawns.length < requiredSpawns) {
    shuffleArray(walkable);
    for (const w of walkable) {
      if (!validSpawns.some((s) => s.r === w.r && s.c === w.c)) {
        // Ensure minimum distance from existing spawns (at least 4 tiles)
        const tooClose = validSpawns.some(s => Math.abs(s.r - w.r) + Math.abs(s.c - w.c) < 4);
        if (tooClose) continue;
        validSpawns.push(w);
        if (validSpawns.length >= requiredSpawns) break;
      }
    }
    // If still not enough, add without distance constraint
    if (validSpawns.length < requiredSpawns) {
      for (const w of walkable) {
        if (!validSpawns.some((s) => s.r === w.r && s.c === w.c)) {
          validSpawns.push(w);
          if (validSpawns.length >= requiredSpawns) break;
        }
      }
    }
  }
  // Shuffle spawns so each game has varied placement
  shuffleArray(validSpawns);

  // Reset zone
  zoneInset = 0;
  zoneTimer = ZONE_INTERVAL;
  zonePhaseStart = Date.now();

  // Reset projectiles and network state
  projectiles = [];
  combatLog = [];
  _respawnQueue = [];
  spectateIndex = -1;
  freeCamX = 0;
  freeCamY = 0;
  remoteInputs = {};

  gamePlayers = players.map((p, i) => {
    const spawn = validSpawns[i % validSpawns.length];
    const fighter = getFighter(p.fighterId || 'fighter');
    return createPlayerState(p, spawn, fighter);
  });

  // F moves start with full cooldown
  for (const gp of gamePlayers) {
    if (gp.fighter && gp.fighter.abilities && gp.fighter.abilities.length > 5) {
      const fAbil = gp.fighter.abilities[5];
      if (fAbil.cooldown > 0) gp.cdF = fAbil.cooldown;
    }
    // Unstable: assign random speed for the whole game
    if (gp.fighter && gp.fighter.id === 'unstable') {
      gp.unstableRandomSpeed = 1.5 + Math.random() * 3.5; // 1.5 to 5.0
      gp.unstableOriginalFighter = gp.fighter;
    }
  }

  localPlayer = gamePlayers.find((p) => p.id === localPlayerId);
  if (!localPlayer && gamePlayers.length > 0) {
    localPlayer = gamePlayers[0];
    localPlayerId = localPlayer.id;
  }

  // Determine if we are the host in multiplayer
  // mode is undefined or 'teams' for multiplayer, 'training'/'fight' for singleplayer
  if (gameMode === undefined || gameMode === 'teams') {
    // Check if OUR player entry has isHost flag (not just players[0])
    const myEntry = players.find(p => p.id === myId);
    isHostAuthority = !!(myEntry && myEntry.isHost);
  } else {
    isHostAuthority = false; // singleplayer: no network authority needed
  }

  // Singleplayer mode setup
  if (gameMode === 'training') {
    // Training: dummy in center + a practice bot that fights back
    const centerR = Math.floor(gameMap.rows / 2);
    const centerC = Math.floor(gameMap.cols / 2);
    const dummySpawn = { r: centerR, c: centerC };
    const dummyFighter = getFighter('fighter');
    const dummy = createPlayerState(
      { id: 'dummy', name: 'Training Dummy', color: '#555' },
      dummySpawn,
      dummyFighter
    );
    dummy.hp = 3000;
    dummy.maxHp = 3000;
    gamePlayers.push(dummy);
    dummyRespawnTimer = 0;
    // Spawn a practice bot that fights back (easy difficulty)
    const botFighters = getAllFighterIds().filter(f => f !== localPlayer.fighter.id && f !== 'moderator' && f !== 'unstable' && f !== 'omori');
    const botFighterId = botFighters[Math.floor(Math.random() * botFighters.length)];
    const botFighter = getFighter(botFighterId);
    const botSpawn = validSpawns[1] || { r: centerR + 3, c: centerC + 3 };
    const bot = createPlayerState(
      { id: 'training-bot', name: 'Sparring Partner', color: '#4a90d9', fighterId: botFighterId },
      botSpawn,
      botFighter
    );
    bot.isCPU = true;
    bot.difficulty = 'easy';
    bot.aiState = {
      moveTarget: null, attackTarget: null, thinkTimer: 0, abilityTimer: 0,
      lastSeenPositions: {}, strafeDir: Math.random() < 0.5 ? 1 : -1, retreating: false,
    };
    gamePlayers.push(bot);
  } else if (gameMode === 'fight' || gameMode === 'fight-hard') {
    // Fight: CPU opponents
    const allFighters = getAllFighterIds().filter(f => f !== 'moderator' && f !== 'dogtooth' && f !== 'explodingcat' && f !== 'unstable' && f !== 'omori');
    const difficulties = gameMode === 'fight-hard'
      ? ['expert', 'expert', 'expert', 'expert', 'expert', 'expert']
      : ['easy', 'medium', 'hard', 'hard'];
    const shuffledNames = CPU_NAMES.slice().sort(() => Math.random() - 0.5);
    const shuffledColors = CPU_COLORS.slice().sort(() => Math.random() - 0.5);
    for (let i = 0; i < difficulties.length; i++) {
      const cpuFighterId = allFighters[Math.floor(Math.random() * allFighters.length)];
      const cpuFighter = getFighter(cpuFighterId);
      // Use spawn index i+1 (index 0 is the local player) — all unique due to 7+ valid spawns
      const cpuSpawn = validSpawns[(i + 1) < validSpawns.length ? (i + 1) : i % validSpawns.length];
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

  // ── Apple Tree: spawn a 2×2 tree in the center of the map ──
  {
    // Find center tiles (pre-scaled map)
    let treeCol = Math.floor(gameMap.cols / 2) - 1;
    let treeRow = Math.floor(gameMap.rows / 2) - 1;
    // River Crossing: place on bridge (walkable gap in the water)
    if (gameMap.name === 'River Crossing') {
      // Find the bridge: look for ground tiles in the water column area around center
      for (let r = 0; r < gameMap.rows; r++) {
        for (let c = 0; c < gameMap.cols; c++) {
          const t = gameMap.tiles[r][c];
          if (t === TILE.GROUND || t === TILE.GRASS) {
            // Check if this is near the horizontal center and in the bridge area
            if (Math.abs(c - gameMap.cols / 2) < 3 && Math.abs(r - gameMap.rows / 2) < 3) {
              // Verify 2x2 area is walkable
              if (r + 1 < gameMap.rows && c + 1 < gameMap.cols) {
                const t01 = gameMap.tiles[r][c + 1];
                const t10 = gameMap.tiles[r + 1][c];
                const t11 = gameMap.tiles[r + 1][c + 1];
                if ((t01 === TILE.GROUND || t01 === TILE.GRASS) &&
                    (t10 === TILE.GROUND || t10 === TILE.GRASS) &&
                    (t11 === TILE.GROUND || t11 === TILE.GRASS)) {
                  treeCol = c;
                  treeRow = r;
                  break;
                }
              }
            }
          }
        }
        if (treeCol !== Math.floor(gameMap.cols / 2) - 1) break;
      }
    }
    // Ensure 2x2 area is within bounds
    treeCol = Math.max(0, Math.min(treeCol, gameMap.cols - 2));
    treeRow = Math.max(0, Math.min(treeRow, gameMap.rows - 2));
    // Replace tiles under the tree with GROUND (remove any obstacles)
    for (let dr = 0; dr < 2; dr++) {
      for (let dc = 0; dc < 2; dc++) {
        const t = gameMap.tiles[treeRow + dr][treeCol + dc];
        if (t === TILE.ROCK || t === TILE.WATER) {
          gameMap.tiles[treeRow + dr][treeCol + dc] = TILE.GROUND;
        }
      }
    }
    appleTree = {
      col: treeCol, row: treeRow,
      hp: 2000, maxHp: 2000,
      alive: true,
      regrowTimer: 0,
      appleTimer: 15,   // seconds until next apple
      apples: [],        // [{col, row}]
    };
  }

  // Resize canvas
  resizeCanvas();
  window.addEventListener('resize', resizeCanvas);

  // Input listeners (named so they can be removed in cleanupGame)
  window.addEventListener('keydown', onKeyDown);
  window.addEventListener('keyup', _onKeyUp);
  gameCanvas.addEventListener('mousedown', _onMouseDown);
  gameCanvas.addEventListener('mouseup', _onMouseUp);
  gameCanvas.addEventListener('mousemove', _onMouseMove);

  // Build HUD
  buildHUD();

  // Hide play-again overlay from any previous game
  const _paOverlay = document.querySelector('#play-again-overlay');
  if (_paOverlay) _paOverlay.classList.add('hidden');
  _gameEnded = false;

  gameRunning = true;
  lastTime = performance.now();
  lastWallClock = Date.now();
  deathOverlayTimer = 0;
  diedInOtherWorld = false;
  if (_gameLoopFrameId) cancelAnimationFrame(_gameLoopFrameId);
  _gameLoopFrameId = requestAnimationFrame(gameLoop);
}

// Named input handlers (so cleanupGame can remove them)
function _onKeyUp(e) { keys[e.key] = false; }
function _onMouseDown(e) { if (e.button === 0) mouseDown = true; }
function _onMouseUp(e) { if (e.button === 0) mouseDown = false; }
function _onMouseMove(e) { mouseX = e.clientX; mouseY = e.clientY; }

// Game-ended state (set by onGameOver / checkWinCondition)
let _gameEnded = false;

// ── CLEANUP: tear down in-game state so we can start fresh ──
function cleanupGame() {
  gameRunning = false;
  _gameEnded = false;

  // Cancel pending animation frame
  if (_gameLoopFrameId) {
    cancelAnimationFrame(_gameLoopFrameId);
    _gameLoopFrameId = null;
  }

  // Remove input listeners
  window.removeEventListener('keydown', onKeyDown);
  window.removeEventListener('keyup', _onKeyUp);
  window.removeEventListener('resize', resizeCanvas);
  if (gameCanvas) {
    gameCanvas.removeEventListener('mousedown', _onMouseDown);
    gameCanvas.removeEventListener('mouseup', _onMouseUp);
    gameCanvas.removeEventListener('mousemove', _onMouseMove);
  }

  // Reset input state
  for (const k in keys) delete keys[k];
  mouseDown = false;

  // Reset game state
  gamePlayers = [];
  projectiles = [];
  combatLog = [];
  _respawnQueue = [];
  localPlayer = null;
  localPlayerId = null;
  gameMode = undefined;
  respawnMode = false;
  isHostAuthority = false;
  remoteInputs = {};
  zoneInset = 0;
  zoneTimer = ZONE_INTERVAL;
  spectateIndex = -1;
  freeCamX = 0;
  freeCamY = 0;
  deathOverlayTimer = 0;
  diedInOtherWorld = false;
  appleTree = null;
  window._spikeEntities = [];

  // Hide play-again overlay and reset button state
  const paOverlay = document.querySelector('#play-again-overlay');
  if (paOverlay) paOverlay.classList.add('hidden');
  const paBtn = document.querySelector('#btn-play-again');
  if (paBtn) { paBtn.disabled = false; paBtn.textContent = 'Play Again'; }
  const paTimer = document.querySelector('#play-again-timer');
  if (paTimer) paTimer.textContent = '';

  // Clear gameLoop scheduled frames
  if (gameLoop._lastBroadcast) gameLoop._lastBroadcast = 0;
  if (gameLoop._lastInputSend) gameLoop._lastInputSend = 0;
  if (gameLoop._lastPosSend) gameLoop._lastPosSend = 0;
}

// Show play-again overlay (called after game ends)
function _showPlayAgainOverlay() {
  const overlay = document.querySelector('#play-again-overlay');
  if (overlay) overlay.classList.remove('hidden');
  // Reset play-again button state so it's clickable for every game
  const btn = document.querySelector('#btn-play-again');
  if (btn) { btn.disabled = false; btn.textContent = 'Play Again'; }
  const timerEl = document.querySelector('#play-again-timer');
  if (timerEl) timerEl.textContent = '';
}

function createPlayerState(p, spawn, fighter) {
  return {
    id: p.id,
    name: p.name,
    color: p.color,
    x: (spawn.c + 0.5) * GAME_TILE,
    y: (spawn.r + 0.5) * GAME_TILE,
    spawnX: (spawn.c + 0.5) * GAME_TILE,
    spawnY: (spawn.r + 0.5) * GAME_TILE,
    // Team (multiplayer teams mode)
    team: p.team || null,
    // Combat
    hp: fighter.hp,
    maxHp: fighter.hp,
    fighter: fighter,
    alive: true,
    // Trait (always active if fighter has one)
    traitActive: !!fighter.trait,
    // Cooldowns (seconds remaining)
    cdM1: 0,
    cdE: 0,
    cdR: 0,
    cdT: 0,
    cdF: 0,
    move4Uses: 0,
    // Ability state
    totalDamageTaken: 0,
    specialUnlocked: false,
    specialUsed: false,
    specialGraceTimer: 0,  // 3s grace period after unlocking before decay starts
    specialDecayTimer: 0,  // 5s decay period — bar drains to 0
    // Buffs / debuffs
    supportBuff: 0,        // seconds remaining of 50% dmg boost
    buffSlowed: 0,         // seconds remaining of Buff slow debuff
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
    pokerDiceUsed: false,  // Poker trait: one-time revive used
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
    // Cricket-specific state
    gearUpTimer: 0,         // seconds remaining of Gear Up
    wicketIds: [],           // array of wicket summon ids [near, far]
    driveReflectTimer: 0,   // seconds remaining of Drive reflect window
    // Deer-specific state
    deerFearTimer: 0,       // seconds remaining of Deer's Fear
    deerFearTargetX: 0,     // x of closest enemy when Fear was used
    deerFearTargetY: 0,     // y of closest enemy when Fear was used
    deerSeerTimer: 0,       // seconds remaining of Deer's Seer
    deerRobotId: null,      // id of deer robot summon
    deerBuildSlowTimer: 0,  // seconds of build-slowness remaining
    iglooX: 0,              // igloo center x
    iglooY: 0,              // igloo center y
    iglooTimer: 0,          // igloo active timer
    // Noli-specific state
    noliVoidRushActive: false,  // currently dashing
    noliVoidRushVx: 0,
    noliVoidRushVy: 0,
    noliVoidRushTimer: 0,
    noliVoidRushChain: 0,       // 0=none, increments each hit (unlimited)
    noliVoidRushChainTimer: 0,  // seconds left to use chain
    noliVoidRushLastHitId: null, // can't hit same target consecutively
    noliVoidStarAiming: false,
    noliVoidStarAimX: 0,
    noliVoidStarAimY: 0,
    noliVoidStarTimer: 0,
    noliObservantUses: 0,       // uses this game (max 3)
    noliCloneId: null,          // id of hallucination clone
    // Exploding Cat-specific state
    catCards: 0,                // saved cat cards
    catStolenAbil: null,        // {fighterId, abilIndex} saved stolen ability
    catStolenReady: false,      // true = next R fires the stolen move
    catAttackBuff: 0,           // seconds remaining of scratch buff
    catSeerTimer: 0,            // reveal the future timer
    catNopeTimer: 0,            // global nope timer (blocks a random ability)
    catNopeAbility: null,       // which ability key is noped ('E','R','T')
    catKittenIds: [],            // ids of exploding kitten summons
    catUnicornId: null,          // id of Cat's unicorn summon (F ability)
    // Move 4 (F ability) state
    pokerFullHouseActive: false, // Poker F buff
    potionHealPool: 0,           // Fighter F heal remaining
    potionHealTimer: 0,          // Fighter F heal timer
    coolkiddId: null,            // 1X F summon
    bowlerId: null,              // Cricket F summon
    crabIds: [],                 // Deer F summons
    johnDoeId: null,             // Noli F summon
    // Filbus Analogus state
    inBackrooms: false,          // is player trapped in backrooms?
    backroomsDoorX: 0,           // door position X
    backroomsDoorY: 0,           // door position Y
    backroomsChaserId: null,     // id of backrooms chaser entity
    backroomsTimer: 0,           // seconds remaining (max 30s, auto-escape)
    hasAlternate: false,         // is an alternate copy hunting this player?
    alternateId: null,           // id of alternate entity
    // Napoleon-specific state
    napoleonCavalry: false,      // currently mounted (Cavalry toggle)
    napoleonCannonId: null,      // id of cannon summon
    napoleonWallId: null,        // id of defensive wall entity
    napoleonInfantryIds: [],     // ids of infantry summons
    // Moderator-specific state
    modBugFixedTargets: [],      // [{targetId, abilityIndex}] — disabled moves
    modDisabledAbilities: [],    // ability slots disabled by Bug Fixing
    modServerResetUses: 0,       // uses of Server Reset (max 3)
    modFirewallTimer: 0,         // seconds remaining of Firewall
    modServerUpdateTimer: 0,     // buff timer for Server Update
    modScaredId: null,           // id of Scare target (for Fear effect)
    modFearTimer: 0,             // Fear duration on this player
    modFearSourceId: null,       // who scared this player
    // D&D Campaigner state
    dndGP: 0,                    // gold pieces earned from questing
    dndRace: 'human',            // current race: 'human', 'elf', 'dwarf'
    dndWeaponBonus: 0,           // permanent M1 bonus from better weapon purchases
    dndCharm: false,             // charm purchased (doubled autoheal)
    dndD20Active: false,         // D20 buff active (M1 = 1000 dmg)
    dndBlurTimer: 0,             // blur debuff timer (from D&D spell)
    dndHealPool: 0,              // remaining HP to heal from potion
    dndHealTimer: 0,             // potion heal tick timer
    dndOrcIds: [],               // ids of active quest orcs
    dndSidekickId: null,         // id of active sidekick summon
    // Dragon of Icespire state
    dragonBreathFuel: 5,         // current breath fuel (seconds)
    dragonBreathActive: false,   // currently breathing
    dragonBreathAimNx: 0,       // aim direction
    dragonBreathAimNy: 0,
    dragonBreathWindup: 0,       // 0.2s windup before damage starts
    dragonBreathRegenDelay: 0,   // 3s delay before fuel regen if fuel hit <=0.5
    dragonFlyTimer: 0,           // dragon ride remaining time
    dragonFlying: false,         // currently flying
    dragonBeamCharging: false,   // beam charging
    dragonBeamChargeTimer: 0,    // beam charge timer (3s)
    dragonBeamFiring: false,     // beam active (firing frame)
    dragonBeamRecovery: 0,       // recovery timer (can't move)
    dragonBeamAimNx: 0,         // beam aim direction
    dragonBeamAimNy: 0,
    dragonRoarActive: false,     // roar speed buff active
    dragonSummonId: null,        // id of active summon (ochre or lich)
    // Dog Tooth-specific state
    dogtoothBleedTimers: [],     // [{targetId, dps, remaining}] on victims
    dogtoothOurielId: null,      // id of Ouriel summon
    dogtoothOurielHp: null,       // stored HP when Ouriel is recalled
    dogtoothOurielHitsLeft: null, // stored hits left when recalled
    dogtoothSmileTimer: 0,       // seconds remaining of Smile Tapes
    dogtoothSmileDmg: 0,         // boosted M1 damage during Smile
    dogtoothPuppetGod: false,    // Kill The Puppet God chosen (revive on death)
    dogtoothPuppetUsed: false,   // already revived once
    dogtoothReviveDmgMult: 1,    // 1.5× after revive
    dogtoothMoonUsed: false,     // The Moon Woke Up used
    dogtoothSpecialChoice: null, // 'puppet' or 'moon' or null
    dogtoothChoiceTimer: 0,      // auto-confirm timer for special
    dogtoothMoonX: 0,            // moon impact X
    dogtoothMoonY: 0,            // moon impact Y
    dogtoothMoonTimer: 0,        // moon delay timer
    dogtoothMoonRadius: 0,       // moon impact radius
    dogtoothMoonDmg: 0,          // moon damage
    dogtoothInComplex: false,    // in The Complex (F ability arena)
    dogtoothComplexRoomId: null, // id of the Room in The Complex
    dogtoothFUsed: false,        // F already used this game
    dogtoothCPRUsed: false,      // Self CPR trait: one-time revive used
    _roomDmgTaken: 0,            // Self CPR trait: Room damage cap tracker
    // Omori-specific state
    omoriPartyIds: [],           // ids of party member summons (Kel/Aubrey/Hero)
    omoriKelBuffTimer: 0,       // seconds remaining of Kel 50% ATK buff
    omoriAubreyBuffTimer: 0,    // seconds remaining of Aubrey 10% chance 600 dmg
    omoriHeroHealPool: 0,       // HP left to heal from Hero skill
    omoriHeroHealTimer: 0,      // seconds remaining of Hero heal channel
    omoriSadPoemPause: 0,       // seconds of pause before Sad Poem activates
    omoriHeadspaceActive: false, // Headspace (FARAWAY TOWN) toggled on
    omoriPlotArmourAvailable: true,  // Plot Armour trait: can revive
    omoriPlotArmourCooldown: 0,      // 30s timer after revive — if die during = dead
    omoriPlotArmourImmunity: 0,      // 5s immunity after revive
    omoriSpecialPartyIds: [],   // ids of special-spawned party (Release Energy)
    omoriSpecialTimer: 0,       // seconds remaining of Release Energy
    omoriSadTimer: 0,           // global: seconds remaining of Sad Poem debuff
    // Illusion-specific state
    illusionInvisTimer: 0,       // seconds remaining of invisibility
    illusionCopyId: null,        // id of illusion copy summon (E ability)
    illusionDodgeTargetId: null, // id of the player whose attacks to dodge
    illusionDodgeTimer: 0,       // seconds remaining of dodge from Teleattack
    illusionTimeFreezeTimer: 0,  // seconds remaining of time freeze (T ability)
    illusionSpecialInvis: false, // special-granted invisibility (SPACE)
    illusionSpecialCopyIds: [],  // ids of 3 illusion copies from special
    illusionSeeGrassTimer: 0,   // seconds remaining of grass-see-through (F)
    illusionBushInvisTimer: 0,  // seconds remaining of bush invis after leaving (trait)
    illusionPositionHistory: [], // position history for rewind [{x,y,t}]
    // Unstable-specific state
    unstableOriginalFighter: null, // saved original fighter object
    unstableRandomSpeed: 0,       // random speed assigned at game start
    unstableInfantryIds: [],      // ids of unstable infantry summons
    unstableSummonId: null,       // id of unstable random summon
    // Power Special state
    pokerDebtTarget: null,        // id of poker who put this player in debt
    pokerDebtHits: 0,             // hits remaining to clear debt (5)
    cricketTrophyId: null,        // id of cricket trophy entity
    cricketTrophyShield: false,   // untouchable while trophy alive
    filbusDinoIds: [],            // ids of Prehistoric Emergence dinosaurs
    onexSlasherId: null,          // id of Slasher summon
    bleedTimers: [],              // [{dps, remaining}] generic bleeding
    noliGuest666Id: null,         // id of Guest666 summon
    catImplodingKittenId: null,   // id of Imploding Kitten summon
    bhSlow: 0,                    // black hole outer-zone movement slow timer
    bhZone: null,                 // 'inner'|'mid'|'outer' — current black hole zone
    bhZoneTimer: 0,               // how long zone tag lasts (refreshed by AI)
    bhSourceX: null,              // x of the black hole affecting this player
    bhSourceY: null,              // y of the black hole affecting this player
    bhTrapped: false,             // true when spinning in the black hole center
    napoleonPowerCannonIds: [],   // ids of Full Power cannons
    napoleonCavalryIds: [],       // ids of Full Power cavalry
    dragonSummonId2: null,        // 2nd dragon summon (Double Trouble)
    dndD20DeathsRemaining: 0,    // Super Lucky deaths remaining
    dogtoothForceMoon: false,    // Dogtooth power: next special forced to Moon
    // Pyromaniac-specific state
    pyroFlameActive: false,       // flamethrower currently firing
    pyroFlameFuel: fighter.abilities && fighter.abilities[0] ? (fighter.abilities[0].maxFuel || 5) : 5,
    pyroFlameWindup: 0,           // windup before damage starts
    pyroFlameRegenDelay: 0,       // delay before fuel starts regenerating
    pyroFlameDmgAccum: {},        // accumulated damage per target for rounding fix
    pyroGasolineTimer: 0,         // seconds remaining of gasoline pour
    pyroGasolineTrail: [],        // [{x, y}] positions of gasoline puddles
    pyroFireZones: [],            // [{x, y, timer, radius, ownerId}] active fire zones
    pyroMolotovAiming: false,     // aiming molotov
    pyroMolotovAimX: 0,
    pyroMolotovAimY: 0,
    pyroMolotovTimer: 0,
    pyroMolotovShadows: [],       // [{x, y, timer, radius, dmg, burnDPS, burnDur, fireDur}] pending molotov impacts
    pyroRainTimer: 0,             // fire rain active timer
    pyroRainX: 0,                 // fire rain center X
    pyroRainY: 0,                 // fire rain center Y
    pyroFireBuffTimer: 0,         // double damage/range buff remaining
    pyroBurnImmuneTimer: 0,       // immune to own burn (from special)
    pyroRoarTimer: 0,             // roar animation timer
    pyroSpecialRainTimer: 0,      // map-wide special rain timer
    pyroSpecialRoarCharging: false, // charging roar before special rain
    pyroBurnTimers: [],           // [{dps, remaining}] burn DOT on this player
    // Heavy Rope-specific state
    ropeSwingActive: false,       // currently swinging rope (shield)
    ropeSwingNx: 0,               // shield aim direction X
    ropeSwingNy: 0,               // shield aim direction Y
    ropeGripActive: false,        // Rope Grip toggle (half range, more damage)
    ropeGrabActive: false,        // rope projectile in flight
    ropeGrabX: 0,                 // rope grab projectile X
    ropeGrabY: 0,                 // rope grab projectile Y
    ropeGrabNx: 0,                // rope grab direction X
    ropeGrabNy: 0,                // rope grab direction Y
    ropePowerTimer: 0,            // ROPE POWER spinning timer
    ropePowerHit: {},             // track who was hit by rope power
    ropeSecondGripTimer: 0,       // Second Grip buff timer
    ropeTraitTimer: 30,           // Hard Worker Breaks - heal timer
    // Filbus chair linger zone
    chairSwingTimer: 0,           // lingering hitbox timer
    chairSwingAimNx: 0,           // swing aim direction X
    chairSwingAimNy: 0,           // swing aim direction Y
    chairSwingRange: 0,           // swing range in world units
    chairSwingDmg: 0,             // linger damage per check
    chairSwingHitIds: [],         // IDs already hit this swing
    // Hitman-specific state
    hitmanWeapon: 'pistol',       // current weapon: 'pistol'|'akm'|'sniper'
    hitmanAmmo: 20,               // current ammo
    hitmanReloading: false,       // currently reloading
    hitmanReloadTimer: 0,         // seconds remaining on reload
    hitmanEquipping: false,       // weapon switch equip animation
    hitmanEquipTimer: 0,          // seconds remaining of equip
    hitmanSenseTimer: 0,          // Heightened Senses timer
    hitmanConcealTimer: 0,        // Conceal invisibility timer
    hitmanConcealUses: 0,         // uses so far (max 3)
    hitmanBackupIds: [],          // ids of backup summons
    hitmanLockingIn: false,       // Locking In active
    hitmanLockingInTimer: 0,      // seconds remaining for Locking In
    hitmanLockingFireTimer: 0,    // fire rate timer for locking in auto-fire
    hitmanBountyTargetId: null,   // Bounty trait: id of current bounty target
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
  const _mpNonHost = (gameMode === undefined || gameMode === 'teams') && !isHostAuthority;
  if (e.key === 'e' || e.key === 'E') {
    if (_mpNonHost) { if (!localPlayer._pendingAbilities) localPlayer._pendingAbilities = []; localPlayer._pendingAbilities.push('E'); }
    else useAbility('E');
  }
  if (e.key === 'r' || e.key === 'R') {
    if (_mpNonHost) { if (!localPlayer._pendingAbilities) localPlayer._pendingAbilities = []; localPlayer._pendingAbilities.push('R'); }
    else useAbility('R');
  }
  if (e.key === 't' || e.key === 'T') {
    if (_mpNonHost) { if (!localPlayer._pendingAbilities) localPlayer._pendingAbilities = []; localPlayer._pendingAbilities.push('T'); }
    else useAbility('T');
  }
  if (e.key === 'f' || e.key === 'F') {
    if (_mpNonHost) { if (!localPlayer._pendingAbilities) localPlayer._pendingAbilities = []; localPlayer._pendingAbilities.push('F'); }
    else useAbility('F');
  }
  if (e.key === ' ') {
    if (_mpNonHost) {
      if (!localPlayer._pendingAbilities) localPlayer._pendingAbilities = [];
      localPlayer._pendingAbilities.push('SPACE');
      // Also trigger local aiming mode for visual feedback (not for Noli — instant special)
      if (localPlayer.specialUnlocked && !localPlayer.specialUsed && localPlayer.alive && localPlayer.stunned <= 0
          && localPlayer.fighter.id !== 'noli'
          && localPlayer.fighter.id !== 'explodingcat'
          && localPlayer.fighter.id !== 'heavyrope'
          && localPlayer.fighter.id !== 'pyromaniac'
          && localPlayer.fighter.id !== 'dragon'
          && localPlayer.fighter.id !== 'napoleon'
          && localPlayer.fighter.id !== 'moderator'
          && localPlayer.fighter.id !== 'illusion') {
        localPlayer.specialAiming = true;
        localPlayer.specialAimX = localPlayer.x;
        localPlayer.specialAimY = localPlayer.y;
        const aimTime = localPlayer.fighter.abilities[4].aimTime || 5;
        localPlayer.specialAimTimer = aimTime;
        localPlayer.effects.push({ type: localPlayer.fighter.id === 'deer' ? 'igloo-aim' : 'sixer-aim', timer: aimTime + 2 });
      }
    }
    else useAbility('SPACE');
  }
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

  if (typeof socket !== 'undefined' && socket.emit && localPlayer) {
    // NON-HOST clients broadcast own position every 20ms for host to use
    // Host doesn't need to broadcast position (it's in the snapshot)
    if ((gameMode === undefined || gameMode === 'teams') && !isHostAuthority) {
      if (!gameLoop._lastPosSend || now - gameLoop._lastPosSend > 16) {
        gameLoop._lastPosSend = now;
        socket.emit('player-position', { x: localPlayer.x, y: localPlayer.y });
      }
    }
    if (isHostAuthority) {
      // HOST: broadcast full game state snapshot every ~33ms (30 Hz) to reduce bandwidth
      if (!gameLoop._lastBroadcast || now - gameLoop._lastBroadcast > 33) {
        gameLoop._lastBroadcast = now;
        const snapshot = buildGameStateSnapshot();
        socket.emit('game-state', snapshot);
      }
    } else if (gameMode === undefined || gameMode === 'teams') {
      // NON-HOST: send ability inputs throttled to ~30 Hz (every 33ms)
      if (!gameLoop._lastInputSend || now - gameLoop._lastInputSend > 33) {
        gameLoop._lastInputSend = now;
        // Send world-space aim coordinates so host canvas size doesn't matter
        const cw = gameCanvas.width, ch = gameCanvas.height;
        const camX = localPlayer.x - cw / 2, camY = localPlayer.y - ch / 2;
        const pending = localPlayer._pendingAbilities || [];
        // Only send if there's meaningful input (mouse state changed or abilities pending)
        const input = {
          aimWorldX: mouseX + camX, aimWorldY: mouseY + camY, mouseDown,
          pendingAbilities: pending,
          keys: { w: !!keys['w'] || !!keys['W'], a: !!keys['a'] || !!keys['A'], s: !!keys['s'] || !!keys['S'], d: !!keys['d'] || !!keys['D'],
                  up: !!keys['ArrowUp'], down: !!keys['ArrowDown'], left: !!keys['ArrowLeft'], right: !!keys['ArrowRight'] },
        };
        localPlayer._pendingAbilities = [];
        socket.emit('player-input', input);
      } else {
        // Between sends, still accumulate abilities but don't emit yet
      }
    }
  }

  _gameLoopFrameId = requestAnimationFrame(gameLoop);
}

// ═══════════════════════════════════════════════════════════════
// UPDATE
// ═══════════════════════════════════════════════════════════════
function updateGame(dt) {
  if (!localPlayer) return;

  // NON-HOST CLIENT in multiplayer: predict local movement, render visuals, but host runs all combat
  if ((gameMode === undefined || gameMode === 'teams') && !isHostAuthority) {
    lastWallClock = Date.now();
    // Local aiming prediction for specials (visual feedback while host processes)
    if (localPlayer.alive && localPlayer.specialAiming) {
      const cw = gameCanvas.width, ch = gameCanvas.height;
      const camX = localPlayer.x - cw / 2, camY = localPlayer.y - ch / 2;
      localPlayer.specialAimX = mouseX + camX;
      localPlayer.specialAimY = mouseY + camY;
      localPlayer.specialAimTimer -= dt;
      if (localPlayer.specialAimTimer <= 0 || mouseDown) {
        localPlayer.specialAiming = false;
      }
    }
    // Local movement prediction so our own character feels responsive
    if (localPlayer.alive && !localPlayer.specialAiming && localPlayer.stunned <= 0
        && !localPlayer.isCraftingChair && !localPlayer.isEatingChair
        && !localPlayer.noliVoidRushActive && !localPlayer.noliVoidStarAiming
        && !(localPlayer.dogtoothSmileTimer > 0) && !localPlayer.dogtoothInComplex) {
      updateMovement(dt);
    }
    // Tick effect timers locally so visual effects render smoothly (host still sends authoritative effects)
    for (const p of gamePlayers) {
      p.effects = p.effects.filter(fx => { fx.timer -= dt; return fx.timer > 0; });
    }
    // Move projectiles locally for smooth visuals (host sends authoritative projectiles in snapshot)
    for (let i = projectiles.length - 1; i >= 0; i--) {
      const pr = projectiles[i];
      pr.timer -= dt;
      if (pr.timer <= 0) { projectiles.splice(i, 1); continue; }
      pr.x += pr.vx * dt;
      pr.y += pr.vy * dt;
      const col = Math.floor(pr.x / GAME_TILE);
      const row = Math.floor(pr.y / GAME_TILE);
      if (col < 0 || col >= gameMap.cols || row < 0 || row >= gameMap.rows) {
        projectiles.splice(i, 1); continue;
      }
      if (gameMap.tiles[row][col] === TILE.ROCK || isStumpTile(col, row)) {
        projectiles.splice(i, 1); continue;
      }
    }
    // Tick combat log
    for (let i = combatLog.length - 1; i >= 0; i--) {
      combatLog[i].timer -= dt;
      if (combatLog[i].timer <= 0) combatLog.splice(i, 1);
    }
    // Interpolate remote players toward their target positions (set by snapshots)
    for (const p of gamePlayers) {
      if (p.id === localPlayerId) continue;
      if (p._targetX !== undefined) {
        // Adaptive interpolation: faster lerp when further away for snappier tracking
        const dx = p._targetX - p.x, dy = p._targetY - p.y;
        const distSq = dx * dx + dy * dy;
        const lerpFactor = distSq > (GAME_TILE * 2) * (GAME_TILE * 2) ? 0.5 : 0.3;
        p.x += dx * lerpFactor;
        p.y += dy * lerpFactor;
      }
    }
    // Dead: free camera movement and death overlay timer
    if (!localPlayer.alive) {
      deathOverlayTimer += dt;
      if (spectateIndex < 0 || !gamePlayers[spectateIndex] || !gamePlayers[spectateIndex].alive) {
        let dx = 0, dy = 0;
        if (keys['ArrowUp']    || keys['w'] || keys['W']) dy -= 1;
        if (keys['ArrowDown']  || keys['s'] || keys['S']) dy += 1;
        if (keys['ArrowLeft']  || keys['a'] || keys['A']) dx -= 1;
        if (keys['ArrowRight'] || keys['d'] || keys['D']) dx += 1;
        const camSpeed = 6 * GAME_TILE * dt;
        freeCamX += dx * camSpeed;
        freeCamY += dy * camSpeed;
        if (spectateIndex >= 0) spectateIndex = -1;
      }
    }
    // Non-host: tick respawn queue timers for countdown display (host handles actual respawn via snapshot)
    for (const r of _respawnQueue) { r.timer -= dt; }
    _respawnQueue = _respawnQueue.filter(r => r.timer > -1);
    return;
  }

  // Use wall-clock delta for timers, capped to prevent huge jumps on tab-switch
  const wallNow = Date.now();
  const wallDt = Math.min((wallNow - lastWallClock) / 1000, 0.1); // cap same as dt to prevent burst damage/cooldowns
  lastWallClock = wallNow;

  // Dead: free camera movement and death overlay timer
  if (!localPlayer.alive) {
    deathOverlayTimer += dt;
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

  // Respawn mode: process respawn queue and game timer
  processRespawnQueue(dt);
  if (respawnMode && gameRunning) {
    respawnGameTimer -= dt;
    if (respawnGameTimer <= 0 && isHostAuthority) {
      respawnGameTimer = 0;
      socket.emit('respawn-timer-end');
    }
  }

  // Tick cooldowns for ALL alive players (host must tick remote players too)
  for (const p of gamePlayers) {
    if (p.alive) tickCooldowns(p, wallDt);
  }

  // Tick buffs/debuffs for all players
  for (const p of gamePlayers) {
    if (p.supportBuff > 0) p.supportBuff = Math.max(0, p.supportBuff - wallDt);
    if (p.buffSlowed > 0) p.buffSlowed = Math.max(0, p.buffSlowed - wallDt);
    if (p.intimidated > 0) {
      p.intimidated = Math.max(0, p.intimidated - wallDt);
      if (p.intimidated <= 0) p.intimidatedBy = null;
    }
    if (p.stunned > 0) p.stunned = Math.max(0, p.stunned - wallDt);

    // Auto-heal: if not damaged for healDelay seconds, heal healAmount every healTick
    if (p.alive && p.hp < p.maxHp && !p.noCloneHeal && !p.inBackrooms && !p.hasAlternate) {
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
          // Team heal sharing: nearby allies get half the heal
          if (gameMode === 'teams' && p.team && !p.isSummon && p.fighter.id !== 'filbus') {
            const healRange = TEAM_HEAL_RANGE * GAME_TILE;
            const allyHeal = Math.round(p.fighter.healAmount * 0.5);
            for (const ally of gamePlayers) {
              if (ally.id === p.id || !ally.alive || ally.isSummon || ally.team !== p.team) continue;
              const adx = ally.x - p.x; const ady = ally.y - p.y;
              if (Math.sqrt(adx * adx + ady * ady) <= healRange && ally.hp < ally.maxHp) {
                ally.hp = Math.min(ally.maxHp, ally.hp + allyHeal);
                ally.effects.push({ type: 'team-heal', timer: 0.3 });
              }
            }
          }
        }
      }
    }

    // Special bar decay timer: 3s grace → 5s drain → reset if unused
    if (p.alive && p.specialUnlocked && !p.specialUsed) {
      if (p.specialGraceTimer > 0) {
        // Grace period: bar stays full
        p.specialGraceTimer -= wallDt;
      } else if (p.specialDecayTimer < 5) {
        // Decay period: bar drains over 5 seconds
        p.specialDecayTimer += wallDt;
        if (p.specialDecayTimer >= 5) {
          // Time's up: reset special
          p.specialUnlocked = false;
          p.totalDamageTaken = 0;
          p.specialGraceTimer = 0;
          p.specialDecayTimer = 0;
          if (p.id === localPlayerId) {
            showPopup('💨 Special expired!');
          }
        }
      }
    }

    // Zone damage: hurt players outside the safe zone
    if (p.alive && zoneInset > 0 && !p.isSummon) {
      // Skip backrooms/Complex players — they're in another dimension
      if (p.inBackrooms || p.dogtoothInComplex) continue;
      const pCol = Math.floor(p.x / GAME_TILE);
      const pRow = Math.floor(p.y / GAME_TILE);
      if (pCol < zoneInset || pCol >= gameMap.cols - zoneInset ||
          pRow < zoneInset || pRow >= gameMap.rows - zoneInset) {
        const zoneDmg = Math.round(ZONE_DPS * wallDt);
        if (zoneDmg > 0) {
          dealDamage(null, p, zoneDmg);
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
    // Tick Filbus chair linger zone (host or local only)
    if (p.chairSwingTimer > 0 && (p.id === localPlayerId || isHostAuthority || p.isCPU)) {
      p.chairSwingTimer -= wallDt;
      if (p.chairSwingTimer > 0) {
        // Check every frame for new targets entering the arc
        for (const t of gamePlayers) {
          if (!t.alive || p.chairSwingHitIds.includes(t.id)) continue;
          if (t.isSummon && t.summonOwner === p.id) continue;
          if (gameMode === 'teams' && p.team && t.team === p.team) continue;
          const dx = t.x - p.x; const dy = t.y - p.y;
          const dist = Math.sqrt(dx * dx + dy * dy);
          if (dist > p.chairSwingRange) continue;
          const dot = (dx * p.chairSwingAimNx + dy * p.chairSwingAimNy) / (dist || 1);
          if (dot < 0) continue;
          dealDamage(p, t, p.chairSwingDmg);
          p.chairSwingHitIds.push(t.id);
        }
      } else {
        p.chairSwingTimer = 0;
        p.chairSwingHitIds = [];
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
    // Boiled One timer (only the Filbus player's client drives the stun loop)
    if (p.boiledOneActive) {
      p.boiledOneTimer -= wallDt;
      // Only the local Filbus client applies ongoing stuns to prevent duplicate stun application
      if (p.id === localPlayerId) {
        for (const target of gamePlayers) {
          if (target.id === p.id || !target.alive || target.isSummon) continue;
          if (target.inBackrooms || target.dogtoothInComplex) continue; // backrooms/complex players immune
          const dx = target.x - p.x; const dy = target.y - p.y;
          const viewRange = CAMERA_RANGE * GAME_TILE * 2;
          if (Math.sqrt(dx * dx + dy * dy) <= viewRange) {
            if (target.stunned < 1) {
              target.stunned = 1;
              target.effects.push({ type: 'stun', timer: 1 });
            }
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
      if (p.hp <= 0 && p.alive) _handleDeath(p);
    }

    // Tick bleeding timers (Power Special bleeding)
    if (p.bleedTimers && p.bleedTimers.length > 0 && p.alive) {
      for (let bi = p.bleedTimers.length - 1; bi >= 0; bi--) {
        const bt = p.bleedTimers[bi];
        const bleedDmg = bt.dps * wallDt;
        p.hp -= bleedDmg;
        p.noDamageTimer = 0;
        p.isHealing = false;
        p.healTickTimer = 0;
        bt.remaining -= wallDt;
        if (bt.remaining <= 0) p.bleedTimers.splice(bi, 1);
      }
      if (p.hp <= 0 && p.alive) _handleDeath(p);
    }

    // Tick Pyromaniac burn timers
    if (p.pyroBurnTimers && p.pyroBurnTimers.length > 0 && p.alive) {
      {
        for (let bi = p.pyroBurnTimers.length - 1; bi >= 0; bi--) {
          const bt = p.pyroBurnTimers[bi];
          p.hp -= bt.dps * wallDt;
          p.noDamageTimer = 0; p.isHealing = false; p.healTickTimer = 0;
          bt.remaining -= wallDt;
          if (bt.remaining <= 0) p.pyroBurnTimers.splice(bi, 1);
        }
        if (p.hp <= 0 && p.alive) _handleDeath(p);
      }
    }

    // Tick Pyromaniac gasoline pour
    if (p.pyroGasolineTimer > 0 && p.alive) {
      p.pyroGasolineTimer -= wallDt;
      // Drop a gasoline puddle at player's position every 0.2s
      if (!p._pyroGasDrop) p._pyroGasDrop = 0;
      p._pyroGasDrop -= wallDt;
      if (p._pyroGasDrop <= 0) {
        p._pyroGasDrop = 0.2;
        if (!p.pyroGasolineTrail) p.pyroGasolineTrail = [];
        p.pyroGasolineTrail.push({ x: p.x, y: p.y, lit: false });
      }
      if (p.pyroGasolineTimer <= 0) p.pyroGasolineTimer = 0;
    }

    // Tick Pyromaniac molotov shadows (falling delay)
    if (p.pyroMolotovShadows && p.pyroMolotovShadows.length > 0) {
      for (let mi = p.pyroMolotovShadows.length - 1; mi >= 0; mi--) {
        const ms = p.pyroMolotovShadows[mi];
        ms.timer -= wallDt;
        if (ms.timer <= 0) {
          // IMPACT — create fire zone + deal damage + ignite gasoline
          if (!p.pyroFireZones) p.pyroFireZones = [];
          p.pyroFireZones.push({ x: ms.x, y: ms.y, timer: ms.fireDur || 5, radius: ms.radius || 3 });
          const impactR = (ms.radius || 3) * GAME_TILE;
          for (const t of gamePlayers) {
            if (!t.alive) continue;
            if (t.id === p.id && !(p.fighter && p.fighter.id === 'pyromaniac')) continue;
            if (t.id !== p.id && gameMode === 'teams' && p.team && t.team === p.team) continue;
            const dx = t.x - ms.x, dy = t.y - ms.y;
            if (Math.sqrt(dx * dx + dy * dy) < impactR) {
              dealDamage(p, t, ms.dmg || 200);
              _applyPyroBurn(t, ms.burnDPS || 100, ms.burnDur || 3);
              t.effects.push({ type: 'hit', timer: 0.5 });
            }
          }
          // Ignite nearby gasoline
          for (const op of gamePlayers) {
            if (!op.pyroGasolineTrail) continue;
            for (const g of op.pyroGasolineTrail) {
              if (g.lit) continue;
              const gx = g.x - ms.x, gy = g.y - ms.y;
              if (Math.sqrt(gx * gx + gy * gy) < impactR * 1.5) {
                g.lit = true;
                if (!p.pyroFireZones) p.pyroFireZones = [];
                p.pyroFireZones.push({ x: g.x, y: g.y, timer: 10, radius: 1.5 });
              }
            }
          }
          p.pyroMolotovShadows.splice(mi, 1);
        }
      }
    }

    // Tick Pyromaniac fire zones (molotov, rain, ignited gasoline)
    if (p.pyroFireZones && p.pyroFireZones.length > 0) {
      for (let fi = p.pyroFireZones.length - 1; fi >= 0; fi--) {
        const fz = p.pyroFireZones[fi];
        fz.timer -= wallDt;
        if (fz.timer <= 0) { p.pyroFireZones.splice(fi, 1); continue; }
        // Burn enemies standing in the fire zone (Pyro can burn himself)
        const fzR = (fz.radius || 1.5) * GAME_TILE;
        for (const t of gamePlayers) {
          if (!t.alive) continue;
          if (t.id === p.id && !(p.fighter && p.fighter.id === 'pyromaniac')) continue;
          if (t.id !== p.id && gameMode === 'teams' && p.team && t.team === p.team) continue;
          const dx = t.x - fz.x, dy = t.y - fz.y;
          if (Math.sqrt(dx * dx + dy * dy) < fzR) {
            if (fz.isGrassFire) {
              // Grass fire: only burn after burnDelay seconds in the zone
              if (!fz._inZoneTimers) fz._inZoneTimers = {};
              fz._inZoneTimers[t.id] = (fz._inZoneTimers[t.id] || 0) + wallDt;
              if (fz._inZoneTimers[t.id] >= (fz.burnDelay || 3)) {
                _applyPyroBurn(t, 100, fz.burnDuration || 5);
              }
            } else {
              _applyPyroBurn(t, 100, 3, !!fz.isRain);
            }
          } else if (fz.isGrassFire && fz._inZoneTimers && fz._inZoneTimers[t.id]) {
            // Left the zone, reset timer
            fz._inZoneTimers[t.id] = 0;
          }
        }
        // Ignite any gasoline puddles overlapping this fire zone
        for (const op of gamePlayers) {
          if (!op.pyroGasolineTrail) continue;
          for (const g of op.pyroGasolineTrail) {
            if (g.lit) continue;
            const gx = g.x - fz.x, gy = g.y - fz.y;
            if (Math.sqrt(gx * gx + gy * gy) < fzR + GAME_TILE) {
              g.lit = true;
              if (!p.pyroFireZones) p.pyroFireZones = [];
              p.pyroFireZones.push({ x: g.x, y: g.y, timer: 10, radius: 1.5 });
            }
          }
        }
      }
    }

    // Tick Pyromaniac fire rain
    if (p.pyroRainTimer > 0 && p.alive) {
      p.pyroRainTimer -= wallDt;
      // Rain arrows every 0.3s
      if (!p._pyroRainTick) p._pyroRainTick = 0;
      p._pyroRainTick -= wallDt;
      if (p._pyroRainTick <= 0) {
        p._pyroRainTick = 0.3;
        const rainR = (p.fighter.abilities[3].fireRadius || 5) * GAME_TILE;
        for (const t of gamePlayers) {
          if (!t.alive || t.isSummon) continue;
          if (t.id !== p.id && gameMode === 'teams' && p.team && t.team === p.team) continue;
          const dx = t.x - p.pyroRainX, dy = t.y - p.pyroRainY;
          if (Math.sqrt(dx * dx + dy * dy) < rainR) {
            let dmg = p.fighter.abilities[3].damage || 10;
            if (p.pyroFireBuffTimer > 0) dmg *= 2;
            if (t.id === p.id) {
              // Self-burn from rain (blocked by T-move burn immunity)
              _applyPyroBurn(t, p.fighter.abilities[3].burnDPS || 100, p.fighter.abilities[3].burnDuration || 3, true);
            } else {
              dealDamage(p, t, dmg);
              t.effects.push({ type: 'hit', timer: 0.3 });
            }
          }
        }
      }
      // When rain ends, leave ground fire
      if (p.pyroRainTimer <= 0) {
        p.pyroRainTimer = 0;
        const fireDur = p.fighter.abilities[3].fireDuration || 10;
        const fireR = p.fighter.abilities[3].fireRadius || 5;
        if (!p.pyroFireZones) p.pyroFireZones = [];
        p.pyroFireZones.push({ x: p.pyroRainX, y: p.pyroRainY, timer: fireDur, radius: fireR, isRain: true });
      }
    }

    // Pyromaniac flamethrower continuous DPS (like Dragon Breath)
    if (p.fighter && p.fighter.id === 'pyromaniac') {
      // Fuel regen when not firing
      if (!p.pyroFlameActive && p.pyroFlameRegenDelay <= 0) {
        const regen = (p.fighter.abilities[0].fuelRegen || 1) * wallDt;
        p.pyroFlameFuel = Math.min(p.pyroFlameFuel + regen, p.fighter.abilities[0].maxFuel || 5);
      }
      if (p.pyroFlameRegenDelay > 0) p.pyroFlameRegenDelay -= wallDt;

      // Windup countdown
      if (p.pyroFlameActive && p.pyroFlameWindup > 0) {
        p.pyroFlameWindup -= wallDt;
      }

      if (p.pyroFlameActive && p.alive && p.pyroFlameWindup <= 0) {
        const abil = p.fighter.abilities[0];
        const dps = abil.dps || 100;
        const range = (abil.range || 5) * GAME_TILE;
        const coneHalf = (abil.coneWidth || 3) * GAME_TILE / 2;
        const effectiveRange = p.pyroFireBuffTimer > 0 ? range * 2 : range;
        const nx = p.pyroFlameNx || 0;
        const ny = p.pyroFlameNy || 0;
        p.pyroFlameRange = effectiveRange;

        // Accumulate and apply damage per target to avoid rounding issues
        if (!p.pyroFlameDmgAccum) p.pyroFlameDmgAccum = {};
        let baseDpsMultiplier = 1;
        if (p.supportBuff > 0) baseDpsMultiplier *= 1.5;
        if (p.intimidated > 0) baseDpsMultiplier *= 0.5;
        if (p.pyroFireBuffTimer > 0) baseDpsMultiplier *= 2;

        for (const target of gamePlayers) {
          if (target.id === p.id || !target.alive) continue;
          if (target.isSummon && target.summonOwner === p.id) continue;
          if (gameMode === 'teams' && p.team && target.team === p.team && !target.isSummon) continue;
          const tx = target.x - p.x; const ty = target.y - p.y;
          const tdist = Math.sqrt(tx * tx + ty * ty);
          if (tdist > effectiveRange || tdist < 1) continue;
          // Cone check using perpendicular distance
          const dot = tx * nx + ty * ny;
          if (dot < 0) continue;
          const perp = Math.abs(-ny * tx + nx * ty);
          if (perp > coneHalf) continue;
          if (!_hasLineOfSight(p.x, p.y, target.x, target.y)) continue;
          // Accumulate damage
          const accKey = target.id;
          if (!p.pyroFlameDmgAccum[accKey]) p.pyroFlameDmgAccum[accKey] = 0;
          p.pyroFlameDmgAccum[accKey] += dps * baseDpsMultiplier * wallDt;
          if (p.pyroFlameDmgAccum[accKey] >= 1) {
            const dmg = Math.floor(p.pyroFlameDmgAccum[accKey]);
            p.pyroFlameDmgAccum[accKey] -= dmg;
            dealDamage(p, target, dmg, false);
          }
          // Apply burn every second (throttled)
          if (!p._pyroBurnApplyTimer) p._pyroBurnApplyTimer = 0;
        }
        // Apply burn periodically (every 1s of continuous fire)
        if (!p._pyroBurnApplyTimer) p._pyroBurnApplyTimer = 0;
        p._pyroBurnApplyTimer += wallDt;
        if (p._pyroBurnApplyTimer >= 1) {
          p._pyroBurnApplyTimer = 0;
          for (const target of gamePlayers) {
            if (target.id === p.id || !target.alive) continue;
            if (target.isSummon && target.summonOwner === p.id) continue;
            const tx = target.x - p.x; const ty = target.y - p.y;
            const tdist = Math.sqrt(tx * tx + ty * ty);
            if (tdist > effectiveRange || tdist < 1) continue;
            const dot = tx * nx + ty * ny;
            if (dot < 0) continue;
            const perp = Math.abs(-ny * tx + nx * ty);
            if (perp > coneHalf) continue;
            if (!_hasLineOfSight(p.x, p.y, target.x, target.y)) continue;
            _applyPyroBurn(target, abil.burnDPS || 100, abil.burnDuration || 3);
          }
        }
        // Ignite gasoline puddles in cone
        for (const op of gamePlayers) {
          if (!op.pyroGasolineTrail) continue;
          for (const g of op.pyroGasolineTrail) {
            if (g.lit) continue;
            const gx = g.x - p.x; const gy = g.y - p.y;
            const gd = Math.sqrt(gx * gx + gy * gy);
            if (gd > effectiveRange) continue;
            const gdot = gx * nx + gy * ny;
            if (gdot < 0) continue;
            g.lit = true;
            if (!p.pyroFireZones) p.pyroFireZones = [];
            p.pyroFireZones.push({ x: g.x, y: g.y, timer: 10, radius: 1.5 });
          }
        }
        // Tree damage
        if (appleTree && appleTree.alive) {
          const treeCX = (appleTree.col + 1) * GAME_TILE;
          const treeCY = (appleTree.row + 1) * GAME_TILE;
          const tx = treeCX - p.x; const ty = treeCY - p.y;
          const tdist = Math.sqrt(tx * tx + ty * ty);
          if (tdist <= effectiveRange + GAME_TILE && tdist > 1) {
            const dot = tx * nx + ty * ny;
            if (dot >= 0) {
              const perp = Math.abs(-ny * tx + nx * ty);
              if (perp <= coneHalf + GAME_TILE) {
                appleTree.hp -= dps * baseDpsMultiplier * wallDt;
                if (appleTree.hp <= 0) { appleTree.hp = 0; appleTree.alive = false; appleTree.regrowTimer = 30; appleTree.apples = []; pushPlayersOffStump(); }
              }
            }
          }
        }
      }
      // Consume fuel
      if (p.pyroFlameActive) {
        p.pyroFlameFuel -= wallDt;
        if (p.pyroFlameFuel <= 0.5) p.pyroFlameRegenDelay = 3;
        if (p.pyroFlameFuel <= 0) {
          p.pyroFlameFuel = 0;
          p.pyroFlameActive = false;
        }
      }
    }

    // Tick Pyromaniac roar
    if (p.pyroRoarTimer > 0) {
      p.pyroRoarTimer = Math.max(0, p.pyroRoarTimer - wallDt);
      // When roar finishes and special roar was charging, start map-wide rain
      if (p.pyroRoarTimer <= 0 && p.pyroSpecialRoarCharging) {
        p.pyroSpecialRoarCharging = false;
        const sAbil = p.fighter && p.fighter.abilities[4];
        p.pyroSpecialRainTimer = (sAbil && sAbil.rainDuration) || 5;
        p._pyroSpecialRainTick = 0;
      }
    }

    // Tick Pyromaniac map-wide special rain
    if (p.pyroSpecialRainTimer > 0 && p.alive) {
      p.pyroSpecialRainTimer -= wallDt;
      if (!p._pyroSpecialRainTick) p._pyroSpecialRainTick = 0;
      p._pyroSpecialRainTick -= wallDt;
      if (p._pyroSpecialRainTick <= 0) {
        p._pyroSpecialRainTick = 0.3;
        const sAbil = p.fighter && p.fighter.abilities[4];
        let dmg = (sAbil && sAbil.damage) || 10;
        if (p.supportBuff > 0) dmg *= 1.5;
        if (p.pyroFireBuffTimer > 0) dmg *= 2;
        const burnDPS = (sAbil && sAbil.burnDPS) || 100;
        const burnDur = (sAbil && sAbil.burnDuration) || 3;
        // Hit ALL enemies on the map (no range check — map-wide)
        for (const t of gamePlayers) {
          if (!t.alive || t.isSummon) continue;
          if (t.id === p.id) {
            // Self-burn from rain (blocked by burn immunity)
            _applyPyroBurn(t, burnDPS, burnDur, true);
            continue;
          }
          if (gameMode === 'teams' && p.team && t.team === p.team) continue;
          dealDamage(p, t, dmg);
          _applyPyroBurn(t, burnDPS, burnDur);
          t.effects.push({ type: 'hit', timer: 0.3 });
        }
      }
      // When rain ends, leave fire zones scattered across the map
      if (p.pyroSpecialRainTimer <= 0) {
        p.pyroSpecialRainTimer = 0;
        if (!p.pyroFireZones) p.pyroFireZones = [];
        const sAbil = p.fighter && p.fighter.abilities[4];
        const fireDur = (sAbil && sAbil.fireDuration) || 8;
        // Scatter fire zones across the map
        const mapW = gameMap.cols * GAME_TILE;
        const mapH = gameMap.rows * GAME_TILE;
        const zoneSpacing = 6 * GAME_TILE;
        for (let zx = zoneSpacing; zx < mapW; zx += zoneSpacing) {
          for (let zy = zoneSpacing; zy < mapH; zy += zoneSpacing) {
            p.pyroFireZones.push({ x: zx, y: zy, timer: fireDur, radius: 3, isRain: true });
          }
        }
      }
    }

    // Tick Pyromaniac fire buff
    if (p.pyroFireBuffTimer > 0) p.pyroFireBuffTimer = Math.max(0, p.pyroFireBuffTimer - wallDt);
    if (p.pyroBurnImmuneTimer > 0) p.pyroBurnImmuneTimer = Math.max(0, p.pyroBurnImmuneTimer - wallDt);

    // Pyromaniac trait: burn on touch
    if (p.traitActive && p.alive && !p.isSummon && p.fighter && p.fighter.id === 'pyromaniac') {
      const touchR = GAME_TILE * PLAYER_RADIUS_RATIO * 2.5;
      for (const t of gamePlayers) {
        if (t.id === p.id || !t.alive) continue;
        if (gameMode === 'teams' && p.team && t.team === p.team) continue;
        const dx = t.x - p.x, dy = t.y - p.y;
        if (Math.sqrt(dx * dx + dy * dy) < touchR) {
          _applyPyroBurn(t, 100, 3);
        }
      }
    }

    // Tick Unstable Eye timer
    if (p.unstableEyeTimer > 0) {
      p.unstableEyeTimer = Math.max(0, p.unstableEyeTimer - wallDt);
    }

    // ── Heavy Rope ticks ──
    // Tick Second Grip timer
    if (p.ropeSecondGripTimer > 0) {
      p.ropeSecondGripTimer = Math.max(0, p.ropeSecondGripTimer - wallDt);
    }

    // Tick ROPE POWER spin
    if (p.ropePowerTimer > 0) {
      p.ropePowerTimer -= wallDt;
      if (p.ropePowerTimer <= 0) { p.ropePowerTimer = 0; }
      // Only apply damage on host, local player, or CPU (authoritative sources)
      if (p.id === localPlayerId || isHostAuthority || p.isCPU) {
        const spinRange = 3.5 * GAME_TILE;
        const spinDmg = (p.fighter && p.fighter.abilities[4] ? p.fighter.abilities[4].damage : 500);
        const spinKB = (p.fighter && p.fighter.abilities[4] ? p.fighter.abilities[4].knockback : 4) * GAME_TILE;
        for (const t of gamePlayers) {
          if (t.id === p.id || !t.alive) continue;
          if (t.isSummon && t.summonOwner === p.id) continue;
          if (gameMode === 'teams' && p.team && t.team === p.team) continue;
          const dx = t.x - p.x; const dy = t.y - p.y;
          const d = Math.sqrt(dx * dx + dy * dy);
          if (d < spinRange && !p.ropePowerHit[t.id]) {
            dealDamage(p, t, spinDmg);
            p.ropePowerHit[t.id] = true;
            t.effects.push({ type: 'hit', timer: 0.5 });
            const kbNx = dx / (d || 1); const kbNy = dy / (d || 1);
            let newTX = t.x + kbNx * spinKB; let newTY = t.y + kbNy * spinKB;
            for (let s = 10; s >= 1; s--) {
              const tryX = t.x + kbNx * spinKB * (s / 10);
              const tryY = t.y + kbNy * spinKB * (s / 10);
              if (canMoveTo(tryX, tryY, GAME_TILE * PLAYER_RADIUS_RATIO)) { newTX = tryX; newTY = tryY; break; }
              if (s === 1) { newTX = t.x; newTY = t.y; }
            }
            t.x = newTX; t.y = newTY;
          } else if (d >= spinRange && p.ropePowerHit[t.id]) {
            delete p.ropePowerHit[t.id];
          }
        }
      } // end authoritative damage gate
    }

    // Tick Rope Grab projectile (only on host or local player)
    if (p.ropeGrabActive && (p.id === localPlayerId || isHostAuthority || p.isCPU)) {
      const grabSpd = (p.fighter && p.fighter.abilities[3] ? p.fighter.abilities[3].speed : 40) * GAME_TILE;
      p.ropeGrabX += p.ropeGrabNx * grabSpd * wallDt;
      p.ropeGrabY += p.ropeGrabNy * grabSpd * wallDt;
      // Check if hit obstacle or sea (out of bounds)
      const pr = GAME_TILE * PLAYER_RADIUS_RATIO;
      if (!canMoveTo(p.ropeGrabX, p.ropeGrabY, pr)) {
        // Teleport player just before the obstacle
        const landX = p.ropeGrabX - p.ropeGrabNx * GAME_TILE * 0.6;
        const landY = p.ropeGrabY - p.ropeGrabNy * GAME_TILE * 0.6;
        if (canMoveTo(landX, landY, pr)) {
          p.x = landX; p.y = landY;
        } else {
          // Try stepping back more
          for (let s = 10; s >= 1; s--) {
            const tryX = p.ropeGrabX - p.ropeGrabNx * GAME_TILE * (s * 0.2);
            const tryY = p.ropeGrabY - p.ropeGrabNy * GAME_TILE * (s * 0.2);
            if (canMoveTo(tryX, tryY, pr)) { p.x = tryX; p.y = tryY; break; }
          }
        }
        p.ropeGrabActive = false;
        p.effects.push({ type: 'rope-grab-land', timer: 0.3 });
      }
    }

    // Heavy Rope trait: Hard Worker Breaks — heal 200 every 30s
    if (p.traitActive && p.alive && !p.isSummon && p.fighter && p.fighter.id === 'heavyrope') {
      if (p.ropeTraitTimer === undefined) p.ropeTraitTimer = 30;
      p.ropeTraitTimer -= wallDt;
      if (p.ropeTraitTimer <= 0) {
        p.ropeTraitTimer = 30;
        const healAmt = Math.min(200, p.maxHp - p.hp);
        if (healAmt > 0) {
          p.hp += healAmt;
          p.effects.push({ type: 'heal', timer: 1.0 });
        }
      }
    }

    // Tick Cricket Gear Up timer
    if (p.gearUpTimer > 0) {
      p.gearUpTimer = Math.max(0, p.gearUpTimer - wallDt);
    }

    // Tick Cricket Drive reflect window
    if (p.driveReflectTimer > 0) {
      p.driveReflectTimer = Math.max(0, p.driveReflectTimer - wallDt);
    }

    // Tick Deer Fear timer
    if (p.deerFearTimer > 0) {
      p.deerFearTimer = Math.max(0, p.deerFearTimer - wallDt);
    }

    // Tick Deer Seer timer
    if (p.deerSeerTimer > 0) {
      p.deerSeerTimer = Math.max(0, p.deerSeerTimer - wallDt);
    }

    // Tick Deer build-slow timer
    if (p.deerBuildSlowTimer > 0) {
      p.deerBuildSlowTimer = Math.max(0, p.deerBuildSlowTimer - wallDt);
    }

    // Tick Deer Igloo — 50 dps to anyone inside (freely walkable, severe slow)
    if (p.iglooTimer > 0) {
      p.iglooTimer = Math.max(0, p.iglooTimer - wallDt);
      const iglooAbil = p.fighter && p.fighter.abilities[4];
      const iglooRadius = (iglooAbil ? (iglooAbil.radius || 4.5) : 4.5) * GAME_TILE;
      const dps = iglooAbil ? (iglooAbil.damage || 50) : 50;
      for (const t of gamePlayers) {
        if (t.id === p.id || !t.alive) continue;
        if (t.isSummon) continue;
        const dx = t.x - p.iglooX; const dy = t.y - p.iglooY;
        if (Math.sqrt(dx * dx + dy * dy) < iglooRadius) {
          dealDamage(p, t, Math.round(dps * wallDt));
        }
      }
    }

    // Tick Exploding Cat timers
    if (p.catAttackBuff > 0) p.catAttackBuff = Math.max(0, p.catAttackBuff - wallDt);
    if (p.catSeerTimer > 0) p.catSeerTimer = Math.max(0, p.catSeerTimer - wallDt);
    if (p.catNopeTimer > 0) p.catNopeTimer = Math.max(0, p.catNopeTimer - wallDt);

    // Tick Moderator timers
    if (p.modFirewallTimer > 0) p.modFirewallTimer = Math.max(0, p.modFirewallTimer - wallDt);
    if (p.modServerUpdateTimer > 0) p.modServerUpdateTimer = Math.max(0, p.modServerUpdateTimer - wallDt);
    if (p.modFearTimer > 0) p.modFearTimer = Math.max(0, p.modFearTimer - wallDt);

    // Tick D&D Campaigner timers
    if (p.dndBlurTimer > 0) p.dndBlurTimer = Math.max(0, p.dndBlurTimer - wallDt);
    if (p.dndHealPool > 0 && p.alive) {
      const potionDur = 3;
      const healPerSec = 300 / potionDur;
      const healAmt = healPerSec * wallDt;
      p.hp = Math.min(p.maxHp, p.hp + healAmt);
      p.dndHealPool = Math.max(0, p.dndHealPool - healAmt);
      // Team potion heal sharing
      if (gameMode === 'teams' && p.team && !p.isSummon) {
        const healRange = TEAM_HEAL_RANGE * GAME_TILE;
        const allyAmt = healAmt * 0.5;
        for (const ally of gamePlayers) {
          if (ally.id === p.id || !ally.alive || ally.isSummon || ally.team !== p.team) continue;
          const adx = ally.x - p.x; const ady = ally.y - p.y;
          if (Math.sqrt(adx * adx + ady * ady) <= healRange && ally.hp < ally.maxHp) {
            ally.hp = Math.min(ally.maxHp, ally.hp + allyAmt);
          }
        }
      }
    }
    // D&D Charm: doubled autoheal rate
    if (p.dndCharm && p.isHealing) {
      // Apply extra heal matching normal rate (effectively doubling it)
      const extraHeal = (p.fighter ? p.fighter.healAmount : 100) * wallDt / (p.fighter ? p.fighter.healTick : 4);
      p.hp = Math.min(p.maxHp, p.hp + extraHeal);
    }

    // Tick Dragon of Icespire timers
    if (p.fighter && p.fighter.id === 'dragon') {
      // Breath fuel regen when not breathing
      if (!p.dragonBreathActive) {
        // If regen delay is active (fuel hit <=0.5), count it down first
        if (p.dragonBreathRegenDelay > 0) {
          p.dragonBreathRegenDelay -= wallDt;
          if (p.dragonBreathRegenDelay < 0) p.dragonBreathRegenDelay = 0;
        } else {
          const maxFuel = (p.fighter.abilities[0].maxFuel || 5);
          const regen = (p.fighter.abilities[0].fuelRegen || 1) * wallDt;
          p.dragonBreathFuel = Math.min(maxFuel, (p.dragonBreathFuel || 0) + regen);
        }
      }
      // Breath windup timer
      if (p.dragonBreathActive && p.dragonBreathWindup > 0) {
        p.dragonBreathWindup -= wallDt;
        if (p.dragonBreathWindup < 0) p.dragonBreathWindup = 0;
      }
      // Fly timer
      if (p.dragonFlying) {
        p.dragonFlyTimer -= wallDt;
        if (p.dragonFlyTimer <= 0) {
          p.dragonFlying = false;
          p.dragonFlyTimer = 0;
          // Check if landed on obstacle — push to nearest safe tile + 500 dmg
          const pr = GAME_TILE * PLAYER_RADIUS_RATIO;
          if (!canMoveTo(p.x, p.y, pr)) {
            // Take landing damage
            p.hp -= (p.fighter.abilities[1].landDamage || 500);
            p.effects.push({ type: 'hit', timer: 0.3 });
            if (p.hp <= 0) _handleDeath(p);
            // Push to nearest safe position
            let placed = false;
            for (let a = 0; a < 16 && !placed; a++) {
              const angle = (a / 16) * Math.PI * 2;
              for (let step = 1; step <= 10 && !placed; step++) {
                const tryX = p.x + Math.cos(angle) * GAME_TILE * step * 0.5;
                const tryY = p.y + Math.sin(angle) * GAME_TILE * step * 0.5;
                if (canMoveTo(tryX, tryY, pr)) {
                  p.x = tryX; p.y = tryY; placed = true;
                }
              }
            }
            if (!placed) { const safe = getRandomSafePosition(); p.x = safe.x; p.y = safe.y; }
            if (p.id === localPlayerId) {
              combatLog.push({ text: '💥 Crash landing! Took 500 damage!', timer: 3, color: '#ff4444' });
            }
          }
        }
      }
      // Beam charge — slowly rotate aim toward mouse/target
      if (p.dragonBeamCharging) {
        const beamTurnRate = 0.8; // radians per second (slow)
        const curAngle = Math.atan2(p.dragonBeamAimNy, p.dragonBeamAimNx);
        let desiredAngle = curAngle;
        if (p.id === localPlayerId && !p.isCPU) {
          const cw = gameCanvas.width, ch = gameCanvas.height;
          const camX = p.x - cw / 2, camY = p.y - ch / 2;
          const mx = mouseX + camX, my = mouseY + camY;
          desiredAngle = Math.atan2(my - p.y, mx - p.x);
        } else if (p.isCPU) {
          // CPU: track closest alive enemy
          let bestD = Infinity, bestT = null;
          for (const t of gamePlayers) {
            if (t.id === p.id || !t.alive || t.isSummon) continue;
            const d = Math.sqrt((t.x - p.x) ** 2 + (t.y - p.y) ** 2);
            if (d < bestD) { bestD = d; bestT = t; }
          }
          if (bestT) desiredAngle = Math.atan2(bestT.y - p.y, bestT.x - p.x);
        } else {
          // Remote player: use relayed aim
          const ri = remoteInputs[p.id];
          if (ri) desiredAngle = Math.atan2((ri.aimWorldY || 0) - p.y, (ri.aimWorldX || 0) - p.x);
        }
        let diff = desiredAngle - curAngle;
        while (diff > Math.PI) diff -= Math.PI * 2;
        while (diff < -Math.PI) diff += Math.PI * 2;
        const maxTurn = beamTurnRate * wallDt;
        const turn = Math.max(-maxTurn, Math.min(maxTurn, diff));
        const newAngle = curAngle + turn;
        p.dragonBeamAimNx = Math.cos(newAngle);
        p.dragonBeamAimNy = Math.sin(newAngle);
        p.dragonBeamChargeTimer -= wallDt;
        if (p.dragonBeamChargeTimer <= 0) {
          // Fire the beam
          p.dragonBeamCharging = false;
          p.dragonBeamFiring = true;
          p.dragonBeamRecovery = (p.fighter.abilities[2].recoveryTime || 2);
          // Deal damage to all enemies in the beam path
          const beamWidth = (p.fighter.abilities[2].beamWidth || 2) * GAME_TILE;
          const beamDmg = p.fighter.abilities[2].damage || 450;
          const nx = p.dragonBeamAimNx; const ny = p.dragonBeamAimNy;
          for (const target of gamePlayers) {
            if (target.id === p.id || !target.alive) continue;
            if (target.isSummon && target.summonOwner === p.id) continue;
            // Project target onto beam line
            const tx = target.x - p.x; const ty = target.y - p.y;
            const along = tx * nx + ty * ny;
            if (along < 0) continue; // behind the player
            const perpDist = Math.abs(tx * (-ny) + ty * nx);
            if (perpDist < beamWidth / 2 + GAME_TILE * PLAYER_RADIUS_RATIO) {
              dealDamage(p, target, beamDmg, false);
            }
          }
          p.effects.push({ type: 'dragon-beam-fire', timer: 0.5, aimNx: nx, aimNy: ny });
          if (p.id === localPlayerId) {
            combatLog.push({ text: '❄️ Dragon Beam fired!', timer: 3, color: '#00ccff' });
          }
        }
      }
      // Beam recovery
      if (p.dragonBeamRecovery > 0) {
        p.dragonBeamRecovery -= wallDt;
        if (p.dragonBeamRecovery <= 0) {
          p.dragonBeamRecovery = 0;
          p.dragonBeamFiring = false;
        }
      }
      // Dragon breath DPS (continuous while active, skip during windup)
      if (p.dragonBreathActive && p.alive) {
        if (p.dragonBreathWindup <= 0) {
          const dps = p.fighter.abilities[0].dps || 100;
          const range = (p.fighter.abilities[0].range || 4) * GAME_TILE;
          const nx = p.dragonBreathAimNx || 0;
          const ny = p.dragonBreathAimNy || 0;
          // Accumulate damage per target to avoid rounding issues in dealDamage
          if (!p._dragonBreathDmgAccum) p._dragonBreathDmgAccum = {};
          // Cone-shaped: 60 degree spread
          for (const target of gamePlayers) {
            if (target.id === p.id || !target.alive) continue;
            if (target.isSummon && target.summonOwner === p.id) continue;
            const tx = target.x - p.x; const ty = target.y - p.y;
            const tdist = Math.sqrt(tx * tx + ty * ty);
            if (tdist > range || tdist < 1) continue;
            const dot = (tx * nx + ty * ny) / tdist;
            if (dot > 0.5) { // ~60 degree cone
              const accKey = target.id;
              if (!p._dragonBreathDmgAccum[accKey]) p._dragonBreathDmgAccum[accKey] = 0;
              p._dragonBreathDmgAccum[accKey] += dps * wallDt;
              if (p._dragonBreathDmgAccum[accKey] >= 1) {
                const dmg = Math.floor(p._dragonBreathDmgAccum[accKey]);
                p._dragonBreathDmgAccum[accKey] -= dmg;
                dealDamage(p, target, dmg, false);
              }
            }
          }
          // Dragon breath also damages apple tree
          if (appleTree && appleTree.alive) {
            const treeCX = (appleTree.col + 1) * GAME_TILE;
            const treeCY = (appleTree.row + 1) * GAME_TILE;
            const tx = treeCX - p.x; const ty = treeCY - p.y;
            const tdist = Math.sqrt(tx * tx + ty * ty);
            if (tdist <= range + GAME_TILE && tdist > 1) {
              const dot = (tx * nx + ty * ny) / tdist;
              if (dot > 0.5) {
                appleTree.hp -= dps * wallDt;
                if (appleTree.hp <= 0) {
                  appleTree.hp = 0;
                  appleTree.alive = false;
                  appleTree.regrowTimer = 30;
                  appleTree.apples = [];
                  pushPlayersOffStump();
                }
              }
            }
          }
        }
        // Consume fuel
        p.dragonBreathFuel -= wallDt;
        if (p.dragonBreathFuel <= 0.5) {
          // If fuel hits <=0.5, trigger 3s regen delay
          p.dragonBreathRegenDelay = 3;
        }
        if (p.dragonBreathFuel <= 0) {
          p.dragonBreathFuel = 0;
          p.dragonBreathActive = false;
        }
      }
    }

    // ── Dog Tooth timers ──
    if (p.fighter && p.fighter.id === 'dogtooth' && p.alive) {
      // Smile Tapes: auto-chase nearest enemy + timer countdown
      if (p.dogtoothSmileTimer > 0) {
        p.dogtoothSmileTimer -= wallDt;
        if (p.dogtoothSmileTimer <= 0) {
          p.dogtoothSmileTimer = 0;
          p.dogtoothSmileDmg = 0;
          if (p.id === localPlayerId) combatLog.push({ text: '😈 Smile Tapes wore off.', timer: 3, color: '#888' });
        } else {
          // Auto-chase nearest enemy
          let nearDist = Infinity, nearTarget = null;
          for (const t of gamePlayers) {
            if (t.id === p.id || !t.alive || (t.isSummon && t.summonOwner === p.id)) continue;
            if (gameMode === 'teams' && p.team && t.team === p.team) continue;
            const d = Math.sqrt((t.x - p.x) ** 2 + (t.y - p.y) ** 2);
            if (d < nearDist) { nearDist = d; nearTarget = t; }
          }
          if (nearTarget) {
            const dx = nearTarget.x - p.x; const dy = nearTarget.y - p.y;
            const dist = Math.sqrt(dx * dx + dy * dy) || 1;
            const speed = (p.fighter.speed || 1.6) * GAME_TILE * 1.1; // 10% faster during smile
            const moveX = (dx / dist) * speed * wallDt;
            const moveY = (dy / dist) * speed * wallDt;
            const newX = p.x + moveX; const newY = p.y + moveY;
            const pr = GAME_TILE * PLAYER_RADIUS_RATIO;
            if (canMoveTo(newX, newY, pr)) { p.x = newX; p.y = newY; }
            else if (canMoveTo(newX, p.y, pr)) { p.x = newX; }
            else if (canMoveTo(p.x, newY, pr)) { p.y = newY; }
            // Auto-fire M1 when close
            if (nearDist < 1.5 * GAME_TILE && p.cdM1 <= 0) {
              const abil0 = p.fighter.abilities[0];
              p.cdM1 = abil0.cooldown || 1.5;
              let dmg = 500; // smile damage
              if (p.supportBuff > 0) dmg *= 1.5;
              dealDamage(p, nearTarget, dmg);
              if (!nearTarget.poisonTimers) nearTarget.poisonTimers = [];
              nearTarget.poisonTimers.push({ sourceId: p.id, dps: 10, remaining: 5 });
              p.effects.push({ type: 'stab', timer: 0.2, aimNx: dx / dist, aimNy: dy / dist });
            }
          }
        }
      }
      // Moon impact timer
      if (p.dogtoothMoonTimer > 0) {
        p.dogtoothMoonTimer -= wallDt;
        if (p.dogtoothMoonTimer <= 0) {
          // MOON IMPACT
          const moonX = p.dogtoothMoonX || p.x;
          const moonY = p.dogtoothMoonY || p.y;
          const moonR = p.dogtoothMoonRadius || (8 * GAME_TILE);
          const moonDmg = p.dogtoothMoonDmg || 1200;
          for (const target of gamePlayers) {
            if (target.id === p.id || !target.alive) continue;
            if (target.isSummon && target.summonOwner === p.id) continue;
            if (gameMode === 'teams' && p.team && target.team === p.team) continue;
            const d = Math.sqrt((target.x - moonX) ** 2 + (target.y - moonY) ** 2);
            if (d < moonR) {
              dealDamage(p, target, moonDmg);
              target.effects.push({ type: 'hit', timer: 0.5 });
            }
          }
          p.effects.push({ type: 'moon-impact', timer: 1.5 });
          if (p.id === localPlayerId) combatLog.push({ text: '🌙 THE MOON CRASHES DOWN!', timer: 4, color: '#ffeeaa' });
          p.dogtoothMoonTimer = 0;
        }
      }
      // Complex Room DPS aura
      if (p.dogtoothInComplex && p.dogtoothComplexRoomId) {
        const room = gamePlayers.find(r => r.id === p.dogtoothComplexRoomId);
        if (room && room.alive) {
          // Room deals 30 DPS constantly while in the Complex
          const auraDmg = 30 * wallDt;
          p.hp -= auraDmg;
          p.noDamageTimer = 0;
          p.isHealing = false;
            if (p.hp <= 0) _handleDeath(p);
        } else {
          // Room killed → exit Complex, return to normal world at spawn
          p.dogtoothInComplex = false;
          if (p.spawnX != null && p.spawnY != null) {
            p.x = p.spawnX; p.y = p.spawnY;
          } else {
            const safe = getRandomSafePosition(); p.x = safe.x; p.y = safe.y;
          }
          // Heal 500 HP for defeating the Love Letter room
          p.hp = Math.min(p.hp + 500, p.maxHp);
          if (p.id === localPlayerId) combatLog.push({ text: '⚔️ Room defeated! THE FINAL BATTLE WON! +500 HP! Teleported back.', timer: 5, color: '#ffd700' });
          p.effects.push({ type: 'complex-exit', timer: 2.0 });
        }
      }
    }
    // ── Omori timers ──
    if (p.fighter && p.fighter.id === 'omori' && p.alive) {
      // Kel buff timer
      if (p.omoriKelBuffTimer > 0) {
        p.omoriKelBuffTimer -= wallDt;
        if (p.omoriKelBuffTimer <= 0) { p.omoriKelBuffTimer = 0; if (p.id === localPlayerId) combatLog.push({ text: '🏀 Kel buff wore off.', timer: 3, color: '#888' }); }
      }
      // Aubrey buff timer
      if (p.omoriAubreyBuffTimer > 0) {
        p.omoriAubreyBuffTimer -= wallDt;
        if (p.omoriAubreyBuffTimer <= 0) { p.omoriAubreyBuffTimer = 0; if (p.id === localPlayerId) combatLog.push({ text: '🦇 Aubrey buff wore off.', timer: 3, color: '#888' }); }
      }
      // Hero heal over time
      if (p.omoriHeroHealTimer > 0 && p.omoriHeroHealPool > 0) {
        const healPerSec = p.omoriHeroHealPool / (p.omoriHeroHealTimer + 0.001);
        const heal = healPerSec * wallDt;
        p.hp = Math.min(p.maxHp, p.hp + heal);
        p.omoriHeroHealPool -= heal;
        p.omoriHeroHealTimer -= wallDt;
        if (p.omoriHeroHealTimer <= 0 || p.omoriHeroHealPool <= 0) { p.omoriHeroHealPool = 0; p.omoriHeroHealTimer = 0; }
      }
      // Sad Poem pause → activate sadness on enemies
      if (p.omoriSadPoemPause > 0) {
        p.omoriSadPoemPause -= wallDt;
        if (p.omoriSadPoemPause <= 0) {
          p.omoriSadPoemPause = 0;
          const sadDur = (p.fighter.abilities[3] && p.fighter.abilities[3].sadDuration) || 30;
          for (const t of gamePlayers) {
            if (t.id === p.id || !t.alive) continue;
            if (t.isSummon && t.summonOwner === p.id) continue;
            if (gameMode === 'teams' && p.team && t.team === p.team) continue;
            // Check if enemy can "see" Omori (within camera range)
            const d = Math.sqrt((t.x - p.x) ** 2 + (t.y - p.y) ** 2);
            if (d < CAMERA_RANGE * GAME_TILE * 2) {
              t.omoriSadTimer = sadDur;
              t.effects.push({ type: 'omori-sad', timer: sadDur });
            }
          }
          if (p.id === localPlayerId) combatLog.push({ text: '📖 Sad Poem... enemies weakened for 30s.', timer: 4, color: '#6c5ce7' });
        }
      }
      // Special despawn timer
      if (p.omoriSpecialTimer > 0) {
        p.omoriSpecialTimer -= wallDt;
        if (p.omoriSpecialTimer <= 0) {
          p.omoriSpecialTimer = 0;
          // Despawn special party members
          for (const pid of (p.omoriSpecialPartyIds || [])) {
            const pm = gamePlayers.find(pp => pp.id === pid);
            if (pm && pm.alive) { pm.alive = false; pm.hp = 0; pm.effects.push({ type: 'death', timer: 2 }); }
          }
          p.omoriSpecialPartyIds = [];
        }
      }
      // Plot Armour cooldown
      if (p.omoriPlotArmourCooldown > 0) {
        p.omoriPlotArmourCooldown -= wallDt;
        if (p.omoriPlotArmourCooldown <= 0) {
          p.omoriPlotArmourCooldown = 0;
          p.omoriPlotArmourAvailable = true;
          if (p.id === localPlayerId) combatLog.push({ text: '🛡 Plot Armour recharged!', timer: 4, color: '#00cec9' });
        }
      }
      // Plot Armour immunity timer
      if (p.omoriPlotArmourImmunity > 0) {
        p.omoriPlotArmourImmunity -= wallDt;
        if (p.omoriPlotArmourImmunity <= 0) {
          p.omoriPlotArmourImmunity = 0;
          if (p.id === localPlayerId) combatLog.push({ text: '🛡 Immunity ended.', timer: 3, color: '#888' });
        }
      }
    }
    // Tick Omori Sad debuff on any player
    if (p.omoriSadTimer > 0) {
      p.omoriSadTimer -= wallDt;
      if (p.omoriSadTimer <= 0) p.omoriSadTimer = 0;
    }
    // ── Illusion timers ──
    // Illusion bush trait: invisible while in grass + 1s after leaving
    if (p.traitActive && p.fighter && p.fighter.id === 'illusion' && !p.isSummon) {
      const col = Math.floor(p.x / GAME_TILE);
      const row = Math.floor(p.y / GAME_TILE);
      const inGrassNow = row >= 0 && row < gameMap.rows && col >= 0 && col < gameMap.cols && gameMap.tiles[row][col] === TILE.GRASS;
      if (inGrassNow) {
        // While in grass — stay invisible
        p.illusionBushInvisTimer = 1.0;
      } else if (p._wasInGrass && !inGrassNow) {
        // Just left grass — grant 1s invisibility
        p.illusionBushInvisTimer = 1.0;
      }
      p._wasInGrass = inGrassNow;
    }
    if (p.illusionBushInvisTimer > 0) p.illusionBushInvisTimer = Math.max(0, p.illusionBushInvisTimer - wallDt);
    // Tick Illusion invisibility (E ability)
    if (p.illusionInvisTimer > 0) {
      p.illusionInvisTimer = Math.max(0, p.illusionInvisTimer - wallDt);
      if (p.illusionInvisTimer <= 0 && p.id === localPlayerId) {
        combatLog.push({ text: '👻 Invisibility wore off.', timer: 3, color: '#888' });
      }
    }
    // Tick Illusion dodge timer (M1 teleattack)
    if (p.illusionDodgeTimer > 0) {
      p.illusionDodgeTimer = Math.max(0, p.illusionDodgeTimer - wallDt);
      if (p.illusionDodgeTimer <= 0) p.illusionDodgeTargetId = null;
    }
    // Tick Illusion time freeze timer
    if (p.illusionTimeFreezeTimer > 0) p.illusionTimeFreezeTimer = Math.max(0, p.illusionTimeFreezeTimer - wallDt);
    // Tick Illusion see-grass timer (F ability)
    if (p.illusionSeeGrassTimer > 0) p.illusionSeeGrassTimer = Math.max(0, p.illusionSeeGrassTimer - wallDt);
    // Illusion special: check if all copies are dead → end special invis
    if (p.illusionSpecialInvis && p.illusionSpecialCopyIds && p.illusionSpecialCopyIds.length > 0) {
      const anyCopyAlive = p.illusionSpecialCopyIds.some(cid => {
        const c = gamePlayers.find(cp => cp.id === cid);
        return c && c.alive;
      });
      if (!anyCopyAlive) {
        p.illusionSpecialInvis = false;
        p.illusionSpecialCopyIds = [];
        if (p.id === localPlayerId) combatLog.push({ text: '👻 All illusions destroyed! You are visible!', timer: 3, color: '#ff4444' });
      }
    }
    // Record position history for rewind (Illusion R)
    if (p.alive && !p.isSummon) {
      if (!p.illusionPositionHistory) p.illusionPositionHistory = [];
      p.illusionPositionHistory.push({ x: p.x, y: p.y, t: Date.now() });
      // Keep only last 5 seconds of history
      const cutoff = Date.now() - 5000;
      while (p.illusionPositionHistory.length > 0 && p.illusionPositionHistory[0].t < cutoff) {
        p.illusionPositionHistory.shift();
      }
    }
    // Ouriel summon: heal owner, track hits
    if (p.isSummon && p.summonType === 'ouriel' && p.alive) {
      const owner = gamePlayers.find(o => o.id === p.summonOwner);
      if (owner && owner.alive) {
        owner.hp = Math.min(owner.maxHp, owner.hp + (p.ourielHealPerSec || 40) * wallDt);
      }
    }
    // Ouriel→Room: deal 20 DPS to its own owner (punishment for Ouriel being destroyed)
    if (p.isSummon && p.summonType === 'ouriel-room' && p.alive) {
      const dps = 20;
      const owner = gamePlayers.find(o => o.id === p.summonOwner);
      if (owner && owner.alive) {
        const d = Math.sqrt((owner.x - p.x) ** 2 + (owner.y - p.y) ** 2);
        if (d < 5 * GAME_TILE) {
          const dmg = dps * wallDt;
          // Dogtooth Self CPR trait: Room cannot kill, only reduce 200 HP total
          if (owner.traitActive && owner.fighter && owner.fighter.id === 'dogtooth') {
            if (!owner._roomDmgTaken) owner._roomDmgTaken = 0;
            if (owner._roomDmgTaken >= 200) {
              // Already lost 200 HP from Room — no more damage
            } else {
              const allowed = Math.min(dmg, 200 - owner._roomDmgTaken);
              owner._roomDmgTaken += allowed;
              owner.hp -= allowed;
              owner.noDamageTimer = 0; owner.isHealing = false;
              if (owner.hp < 1) owner.hp = 1; // can't die from Room
            }
          } else {
            owner.hp -= dmg;
            owner.noDamageTimer = 0;
            owner.isHealing = false;
            if (owner.hp <= 0 && owner.alive) _handleDeath(owner);
          }
        }
      }
    }

    // Tick Noli Void Rush dash
    if (p.noliVoidRushActive && p.alive) {
      p.noliVoidRushTimer -= wallDt;
      // Steer toward mouse (local player only) or toward target (CPU)
      const abil = p.fighter && p.fighter.abilities[1];
      const chain = p.noliVoidRushChain || 0;
      const steerBase = abil ? (abil.steerRate || 8) : 8;
      const steerDecay = abil ? (abil.steerDecayPerChain || 1.0) : 1.0;
      const minSteer = abil ? (abil.minSteerRate || 2) : 2;
      const steerRate = Math.max(minSteer, steerBase - chain * steerDecay);
      if (p.id === localPlayerId) {
        // Auto-aim: home toward nearest alive enemy
        let nearDist2 = Infinity, nearTarget2 = null;
        for (const t of gamePlayers) {
          if (t.id === p.id || !t.alive || (t.isSummon && t.summonOwner === p.id)) continue;
          if (gameMode === 'teams' && p.team) {
            const tTeam = t.isSummon ? (gamePlayers.find(o => o.id === t.summonOwner) || {}).team : t.team;
            if (tTeam === p.team) continue;
          }
          const dd = Math.sqrt((t.x - p.x) ** 2 + (t.y - p.y) ** 2);
          if (dd < nearDist2) { nearDist2 = dd; nearTarget2 = t; }
        }
        if (nearTarget2) {
          const wantDx = nearTarget2.x - p.x, wantDy = nearTarget2.y - p.y;
          const wantDist = Math.sqrt(wantDx * wantDx + wantDy * wantDy) || 1;
          const wantNx = wantDx / wantDist, wantNy = wantDy / wantDist;
          const curSpeed = Math.sqrt(p.noliVoidRushVx * p.noliVoidRushVx + p.noliVoidRushVy * p.noliVoidRushVy) || 1;
          const curNx = p.noliVoidRushVx / curSpeed, curNy = p.noliVoidRushVy / curSpeed;
          const blendAmt = Math.min(1, steerRate * wallDt);
          const newNx = curNx + (wantNx - curNx) * blendAmt;
          const newNy = curNy + (wantNy - curNy) * blendAmt;
          const newDist = Math.sqrt(newNx * newNx + newNy * newNy) || 1;
          p.noliVoidRushVx = (newNx / newDist) * curSpeed;
          p.noliVoidRushVy = (newNy / newDist) * curSpeed;
        }
      } else if (isHostAuthority && !p.isCPU) {
        // Host: auto-aim remote player's Void Rush toward nearest enemy
        let nearDistR = Infinity, nearTargetR = null;
        for (const t of gamePlayers) {
          if (t.id === p.id || !t.alive || (t.isSummon && t.summonOwner === p.id)) continue;
          if (gameMode === 'teams' && p.team) {
            const tTeam = t.isSummon ? (gamePlayers.find(o => o.id === t.summonOwner) || {}).team : t.team;
            if (tTeam === p.team) continue;
          }
          const dd = Math.sqrt((t.x - p.x) ** 2 + (t.y - p.y) ** 2);
          if (dd < nearDistR) { nearDistR = dd; nearTargetR = t; }
        }
        if (nearTargetR) {
          const wantDx = nearTargetR.x - p.x, wantDy = nearTargetR.y - p.y;
          const wantDist = Math.sqrt(wantDx * wantDx + wantDy * wantDy) || 1;
          const wantNx = wantDx / wantDist, wantNy = wantDy / wantDist;
          const curSpeed = Math.sqrt(p.noliVoidRushVx * p.noliVoidRushVx + p.noliVoidRushVy * p.noliVoidRushVy) || 1;
          const curNx = p.noliVoidRushVx / curSpeed, curNy = p.noliVoidRushVy / curSpeed;
          const blendAmt = Math.min(1, steerRate * wallDt);
          const newNx = curNx + (wantNx - curNx) * blendAmt;
          const newNy = curNy + (wantNy - curNy) * blendAmt;
          const newDist = Math.sqrt(newNx * newNx + newNy * newNy) || 1;
          p.noliVoidRushVx = (newNx / newDist) * curSpeed;
          p.noliVoidRushVy = (newNy / newDist) * curSpeed;
        }
      }
      // Update position for local player, CPU, and remote players under host authority
      if (p.id === localPlayerId || p.isCPU || isHostAuthority) {
        p.x += p.noliVoidRushVx * wallDt * 60;
        p.y += p.noliVoidRushVy * wallDt * 60;
      }
      // Store trail position
      if (!p._voidRushTrail) p._voidRushTrail = [];
      p._voidRushTrail.push({ x: p.x, y: p.y, t: 0.3 });
      // Check if hit a player
      let hitSomeone = false;
      for (const t of gamePlayers) {
        if (t.id === p.id || !t.alive || (t.isSummon && t.summonOwner === p.id)) continue;
        if (t.id === p.noliVoidRushLastHitId) continue; // can't hit same target consecutively
        // Skip teammates in team mode
        if (gameMode === 'teams' && p.team) {
          const tTeam = t.isSummon ? (gamePlayers.find(o => o.id === t.summonOwner) || {}).team : t.team;
          if (tTeam === p.team) continue;
        }
        const dx = t.x - p.x, dy = t.y - p.y;
        if (Math.sqrt(dx * dx + dy * dy) < GAME_TILE * 1.5) {
          // Hit! Unlimited chain — damage & speed scale up each hit
          const chain = p.noliVoidRushChain;
          const abil = p.fighter && p.fighter.abilities[1];
          const baseDmg = abil ? abil.damage : 300;
          const perChain = abil ? (abil.damagePerChain || 100) : 100;
          let dmg = baseDmg + chain * perChain;
          if (p.supportBuff > 0) dmg *= 1.5;
          if (p.intimidated > 0) dmg *= 0.5;
          const _vrTargetWasAlive = t.alive;
          dealDamage(p, t, Math.round(dmg));
          // Achievement: Noli Void Rush kills in MP (not team mode)
          if (_vrTargetWasAlive && !t.alive && p.id === localPlayerId && gameMode !== 'training' && gameMode !== 'fight' && gameMode !== 'fight-hard' && gameMode !== 'teams') {
            _noliVoidRushKillsThisGame++;
            if (_noliVoidRushKillsThisGame >= 2 && typeof trackNoliVoidRushAch === 'function') {
              trackNoliVoidRushAch();
            }
          }
          p.noliVoidRushActive = false;
          p.noliVoidRushLastHitId = t.id;
          p.noliVoidRushChain = chain + 1;
          p.noliVoidRushChainTimer = (abil ? abil.chainWindow : 3);
          p.cdE = 0; // can use E again immediately
          p.effects.push({ type: 'void-rush-hit', timer: 0.3 });
          hitSomeone = true;
          break;
        }
      }
      // Check if hit wall/out of bounds
      if (!hitSomeone && p.noliVoidRushActive) {
        const mapW = gameMap.cols * GAME_TILE, mapH = gameMap.rows * GAME_TILE;
        const tileR = Math.floor(p.y / GAME_TILE), tileC = Math.floor(p.x / GAME_TILE);
        const outOfBounds = p.x < 0 || p.y < 0 || p.x > mapW || p.y > mapH;
        const onRock = (tileR >= 0 && tileR < gameMap.rows && tileC >= 0 && tileC < gameMap.cols) ? (gameMap.tiles[tileR][tileC] === TILE.ROCK) : true;
        const onSea = (tileR >= 0 && tileR < gameMap.rows && tileC >= 0 && tileC < gameMap.cols) ? (gameMap.tiles[tileR][tileC] === TILE.WATER) : true;
        if (outOfBounds || onRock || onSea) {
          const lostChain = p.noliVoidRushChain;
          p.noliVoidRushActive = false;
          p.noliVoidRushChain = 0;
          p.noliVoidRushChainTimer = 0;
          p.noliVoidRushLastHitId = null;
          const baseMissStun = (p.fighter && p.fighter.abilities[1]) ? p.fighter.abilities[1].missStun : 2;
          const missStun = baseMissStun + lostChain * 0.3; // higher chain = longer stun
          p.stunned = Math.max(p.stunned, missStun);
          p.effects.push({ type: 'stun', timer: missStun });
          // 30s cooldown on miss
          p.cdE = 30;
          // Push back to valid position
          p.x = Math.max(GAME_TILE, Math.min(mapW - GAME_TILE, p.x - p.noliVoidRushVx * wallDt * 60 * 2));
          p.y = Math.max(GAME_TILE, Math.min(mapH - GAME_TILE, p.y - p.noliVoidRushVy * wallDt * 60 * 2));
          combatLog.push({ text: '💫 Void Rush missed! (30s CD)' + (lostChain > 0 ? ' chain ' + lostChain + ' lost' : ''), timer: 2, color: '#a020f0' });
        }
      }
      // Void Rush is infinite — only ends on wall/sea hit or player hit (no timer timeout)
    }
    // Tick Noli Void Rush chain window
    if (p.noliVoidRushChainTimer > 0) {
      p.noliVoidRushChainTimer -= wallDt;
      if (p.noliVoidRushChainTimer <= 0) {
        p.noliVoidRushChain = 0;
        p.noliVoidRushLastHitId = null;
      }
    }
    // Decay Void Rush trail
    if (p._voidRushTrail && p._voidRushTrail.length > 0) {
      for (let ti = p._voidRushTrail.length - 1; ti >= 0; ti--) {
        p._voidRushTrail[ti].t -= wallDt;
        if (p._voidRushTrail[ti].t <= 0) p._voidRushTrail.splice(ti, 1);
      }
    }
    // Tick Noli Observant charge
    if (p.noliObservantCharging > 0 && p.alive) {
      p.noliObservantCharging -= wallDt;
      if (p.noliObservantCharging <= 0) {
        p.noliObservantCharging = 0;
        // Execute teleport
        const oMapW = gameMap.cols * GAME_TILE, oMapH = gameMap.rows * GAME_TILE;
        let oNewX = oMapW - p.x, oNewY = oMapH - p.y;
        const oPr = GAME_TILE * PLAYER_RADIUS_RATIO;
        oNewX = Math.max(oPr, Math.min(oMapW - oPr, oNewX));
        oNewY = Math.max(oPr, Math.min(oMapH - oPr, oNewY));
        if (!canMoveTo(oNewX, oNewY, oPr)) {
          let foundValid = false;
          for (let attempts = 0; attempts < 30; attempts++) {
            const tryX = oNewX + (Math.random() - 0.5) * GAME_TILE * 3;
            const tryY = oNewY + (Math.random() - 0.5) * GAME_TILE * 3;
            const cx = Math.max(oPr, Math.min(oMapW - oPr, tryX));
            const cy = Math.max(oPr, Math.min(oMapH - oPr, tryY));
            if (canMoveTo(cx, cy, oPr)) { oNewX = cx; oNewY = cy; foundValid = true; break; }
          }
          if (!foundValid) {
            oNewX = (gameMap.cols / 2 + 0.5) * GAME_TILE;
            oNewY = (gameMap.rows / 2 + 0.5) * GAME_TILE;
          }
        }
        p.stunned = 0;
        p.x = oNewX; p.y = oNewY;
        p.effects.push({ type: 'observant-tp', timer: 1.0 });
        const oAbil = p.fighter && p.fighter.abilities[3];
        combatLog.push({ text: '👁 Observant! (' + ((oAbil ? oAbil.maxUses || 3 : 3) - (p.noliObservantUses || 0)) + ' left)', timer: 3, color: '#a020f0' });
      }
    }
    // Tick Noli Void Star aiming
    if (p.noliVoidStarAiming && p.alive) {
      // Track mouse position each frame (local player)
      if (p.id === localPlayerId) {
        const cw = gameCanvas.width, ch = gameCanvas.height;
        const camX = p.x - cw / 2, camY = p.y - ch / 2;
        p.noliVoidStarAimX = mouseX + camX;
        p.noliVoidStarAimY = mouseY + camY;
      }
      p.noliVoidStarTimer -= wallDt;
      // Fire on timer expire, local click, or remote click
      let remoteClick = false;
      if (isHostAuthority && p.id !== localPlayerId && remoteInputs[p.id]) {
        remoteClick = remoteInputs[p.id].mouseDown;
      }
      if (p.noliVoidStarTimer <= 0 || (p.id === localPlayerId && mouseDown) || remoteClick) {
        // Throw the star
        p.noliVoidStarAiming = false;
        const abil = p.fighter && p.fighter.abilities[2];
        const starR = (abil ? abil.radius || 1.5 : 1.5) * GAME_TILE;
        const dmg = abil ? abil.damage : 300;
        for (const t of gamePlayers) {
          if (t.id === p.id || !t.alive) continue;
          if (t.isSummon && t.summonOwner === p.id) continue;
          const dx = t.x - p.noliVoidStarAimX, dy = t.y - p.noliVoidStarAimY;
          if (Math.sqrt(dx * dx + dy * dy) < starR) {
            let d = dmg;
            if (p.supportBuff > 0) d *= 1.5;
            if (p.intimidated > 0) d *= 0.5;
            dealDamage(p, t, Math.round(d));
          }
        }
        // Self-stun after throwing — removed
        p.effects.push({ type: 'void-star-throw', timer: 0.5 });
        combatLog.push({ text: '⭐ Void Star thrown!', timer: 2, color: '#a020f0' });
      }
    }
    // Noli: check if clone is still alive
    if (p.noliCloneId) {
      const clone = gamePlayers.find(x => x.id === p.noliCloneId);
      if (!clone || !clone.alive) {
        if (clone) { clone.alive = false; _deferredRemoveIds.push(p.noliCloneId); }
        p.noliCloneId = null;
      }
    }

    // ── Hitman ticks ────────────────────────────────────────────
    if (p.fighter && p.fighter.id === 'hitman') {
      // Tick timers
      if (p.hitmanSenseTimer > 0) p.hitmanSenseTimer = Math.max(0, p.hitmanSenseTimer - wallDt);
      if (p.hitmanConcealTimer > 0) p.hitmanConcealTimer = Math.max(0, p.hitmanConcealTimer - wallDt);
      if (p.hitmanEquipTimer > 0) {
        p.hitmanEquipTimer = Math.max(0, p.hitmanEquipTimer - wallDt);
        if (p.hitmanEquipTimer <= 0 && p.hitmanEquipping) {
          p.hitmanEquipping = false;
          // Sync ammo to new weapon
          const wDef = p.fighter.abilities[0].weapons[p.hitmanWeapon];
          p.hitmanAmmo = wDef ? wDef.maxAmmo : 20;
          p.hitmanReloading = false;
          p.hitmanReloadTimer = 0;
          if (p.id === localPlayerId) combatLog.push({ text: '🔫 ' + (wDef ? wDef.label : p.hitmanWeapon) + ' ready!', timer: 2, color: '#f5c842' });
        }
      }
      // Reload tick
      if (p.hitmanReloading && p.hitmanReloadTimer > 0) {
        p.hitmanReloadTimer = Math.max(0, p.hitmanReloadTimer - wallDt);
        if (p.hitmanReloadTimer <= 0) {
          p.hitmanReloading = false;
          const wDef = p.fighter.abilities[0].weapons[p.hitmanWeapon];
          p.hitmanAmmo = wDef ? wDef.maxAmmo : 20;
          if (p.id === localPlayerId) combatLog.push({ text: '🔄 Reloaded!', timer: 1.5, color: '#aaa' });
        }
      }
      // Locking In: count down timer, auto-fire all 3 weapons toward mouse
      if (p.hitmanLockingIn) {
        p.hitmanLockingInTimer -= dt;
        // Auto-fire all 3 weapons simultaneously at fastest rate (0.1s)
        if (!p.hitmanLockingFireTimer) p.hitmanLockingFireTimer = 0;
        p.hitmanLockingFireTimer -= dt;
        if (p.hitmanLockingFireTimer <= 0) {
          p.hitmanLockingFireTimer = 0.1; // fire every 0.1s
          const wDefs = p.fighter.abilities[0].weapons || {};
          // Calculate aim direction toward mouse (or random for CPU)
          let aimNx, aimNy;
          if (p.id === localPlayerId) {
            const cw = gameCanvas.width; const ch = gameCanvas.height;
            const camX = p.x - cw / 2; const camY = p.y - ch / 2;
            const aimX = mouseX + camX; const aimY = mouseY + camY;
            const aimDx = aimX - p.x; const aimDy = aimY - p.y;
            const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
            aimNx = aimDx / aimDist; aimNy = aimDy / aimDist;
          } else if (!p.isCPU && isHostAuthority && remoteInputs[p.id]) {
            // Host: use remote player's real aim direction
            const ri = remoteInputs[p.id];
            const aimDx = (ri.aimWorldX || p.x) - p.x;
            const aimDy = (ri.aimWorldY || p.y) - p.y;
            const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
            aimNx = aimDx / aimDist; aimNy = aimDy / aimDist;
          } else {
            // CPU/remote: aim at closest enemy
            let closest = null, closestD = Infinity;
            for (const t of gamePlayers) {
              if (t.id === p.id || !t.alive || t.isSummon) continue;
              if (t.team && t.team === p.team) continue;
              const d = Math.sqrt((t.x - p.x) ** 2 + (t.y - p.y) ** 2);
              if (d < closestD) { closestD = d; closest = t; }
            }
            if (closest) {
              const d = closestD || 1;
              aimNx = (closest.x - p.x) / d; aimNy = (closest.y - p.y) / d;
            } else {
              aimNx = Math.cos(p.aimAngle || 0); aimNy = Math.sin(p.aimAngle || 0);
            }
          }
          // Fire all 3 weapons
          const weaponKeys = ['pistol', 'akm', 'sniper'];
          for (const wKey of weaponKeys) {
            const wDef = wDefs[wKey];
            if (!wDef) continue;
            const bulletSpeed = (wDef.speed || 28) * GAME_TILE / 10;
            let dmg = wDef.damage || 100;
            if (p.supportBuff > 0) dmg *= 1.5;
            if (p.intimidated > 0) dmg *= 0.5;
            // Slight spread for AKM
            let nx = aimNx, ny = aimNy;
            if (wKey === 'akm') {
              const spread = (Math.random() - 0.5) * 0.15;
              const cos = Math.cos(spread), sin = Math.sin(spread);
              nx = aimNx * cos - aimNy * sin;
              ny = aimNx * sin + aimNy * cos;
            }
            projectiles.push({
              x: p.x, y: p.y,
              vx: nx * bulletSpeed, vy: ny * bulletSpeed,
              ownerId: p.id, damage: Math.round(dmg),
              timer: 4, type: 'hitman-bullet',
              weaponKey: wKey, color: wDef.color || '#f5c842',
              traitRange: 6 * GAME_TILE,
              spawnX: p.x, spawnY: p.y,
            });
          }
          p.effects.push({ type: 'hitman-fire', timer: 0.1, aimNx, aimNy, wKey: 'pistol' });
        }
      }
      if (p.hitmanLockingIn && p.hitmanLockingInTimer <= 0) {
        p.hitmanLockingIn = false;
        p.hitmanLockingFireTimer = 0;
        if (p.id === localPlayerId) combatLog.push({ text: '🔓 Locking In ended.', timer: 2, color: '#ff4400' });
      }
      // Backup: prune dead backup summons
      if (p.hitmanBackupIds && p.hitmanBackupIds.length > 0) {
        p.hitmanBackupIds = p.hitmanBackupIds.filter(bid => {
          const b = gamePlayers.find(x => x.id === bid);
          if (!b || !b.alive) { if (b) _deferredRemoveIds.push(bid); return false; }
          return true;
        });
      }
    }

    // Cricket: check if wickets are still alive (both must survive)
    if (p.wicketIds && p.wicketIds.length === 2) {
      const w0 = gamePlayers.find(x => x.id === p.wicketIds[0]);
      const w1 = gamePlayers.find(x => x.id === p.wicketIds[1]);
      if (!w0 || !w0.alive || !w1 || !w1.alive) {
        // One wicket died, remove both
        for (const wid of p.wicketIds) {
          const w = gamePlayers.find(x => x.id === wid);
          if (w) { w.alive = false; _deferredRemoveIds.push(wid); }
        }
        p.wicketIds = [];
      }
    }
  }

  // Flush deferred removals (splicing inside for..of corrupts the iterator)
  if (_deferredRemoveIds.length > 0) {
    for (let ri = gamePlayers.length - 1; ri >= 0; ri--) {
      if (_deferredRemoveIds.includes(gamePlayers[ri].id)) gamePlayers.splice(ri, 1);
    }
    _deferredRemoveIds.length = 0;
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
    localPlayer.specialAimTimer -= wallDt;
    if (localPlayer.specialAimTimer <= 0 || mouseDown) {
      executeSpecialLanding();
    }
    // Skip normal movement while aiming, but continue world sim below
  }

  // Movement (only if alive and not stunned/aiming/channeling/dashing)
  if (localPlayer.alive && !localPlayer.specialAiming && localPlayer.stunned <= 0
      && !localPlayer.isCraftingChair && !localPlayer.isEatingChair
      && !localPlayer.noliVoidRushActive && !localPlayer.noliVoidStarAiming) {
    updateMovement(dt);
  }

  // HOST: apply remote ability inputs (positions come from player-position relay, not keys)
  if (isHostAuthority) {
    for (const p of gamePlayers) {
      if (p.id === localPlayerId || p.isCPU || p.isSummon || !p.alive) continue;
      const inp = remoteInputs[p.id];
      if (!inp) continue;

      // Tick special aiming for remote players (host processes aim timer + landing)
      if (p.specialAiming) {
        p.specialAimX = inp.aimWorldX || 0;
        p.specialAimY = inp.aimWorldY || 0;
        p.specialAimTimer -= wallDt;
        if (p.specialAimTimer <= 0 || inp.mouseDown) {
          // Swap context and call executeSpecialLanding for this remote player
          const savedLP = localPlayer, savedLPID = localPlayerId;
          localPlayer = p; localPlayerId = p.id;
          executeSpecialLanding();
          localPlayer = savedLP; localPlayerId = savedLPID;
        }
      }

      // Tick Void Star aiming for remote players (host tracks aim + fires)
      if (p.noliVoidStarAiming) {
        p.noliVoidStarAimX = inp.aimWorldX || 0;
        p.noliVoidStarAimY = inp.aimWorldY || 0;
      }

      // NOTE: p.x/p.y for remote players is updated by onRemotePosition (no applyRemoteMovement needed)
      // Skip manual M1 during Smile Tapes (auto-chase handles M1 attacks)
      if (inp.mouseDown && p.cdM1 <= 0 && !(p.dogtoothSmileTimer > 0)) applyRemoteAbility(p, 'M1', inp);
      // Dragon breath: stop when remote player releases mouse
      if (p.dragonBreathActive && !inp.mouseDown) {
        p.dragonBreathActive = false;
      }
      // Pyromaniac flame: stop when remote player releases mouse
      if (p.pyroFlameActive && !inp.mouseDown) {
        p.pyroFlameActive = false;
      }
      if (inp.pendingAbilities && inp.pendingAbilities.length > 0) {
        for (const abilKey of inp.pendingAbilities) applyRemoteAbility(p, abilKey, inp);
        inp.pendingAbilities = [];
      }
    }
  }

  // Update projectiles
  updateProjectiles(dt);

  // ── Move 4 ticks ──────────────────────────────────────────
  // Potion heal tick (Fighter F)
  for (const p of gamePlayers) {
    if (p.potionHealTimer > 0 && p.alive) {
      const fAbil = p.fighter.abilities[5];
      const totalHeal = fAbil ? (fAbil.healAmount || 300) : 300;
      const totalDur = fAbil ? (fAbil.healDuration || 3) : 3;
      const healPerSec = totalHeal / totalDur;
      const healAmt = healPerSec * dt;
      p.hp = Math.min(p.maxHp, p.hp + healAmt);
      p.potionHealTimer -= dt;
      if (p.potionHealTimer <= 0) p.potionHealTimer = 0;
      // Team potion heal sharing
      if (gameMode === 'teams' && p.team && !p.isSummon) {
        const healRange = TEAM_HEAL_RANGE * GAME_TILE;
        const allyAmt = healAmt * 0.5;
        for (const ally of gamePlayers) {
          if (ally.id === p.id || !ally.alive || ally.isSummon || ally.team !== p.team) continue;
          const adx = ally.x - p.x; const ady = ally.y - p.y;
          if (Math.sqrt(adx * adx + ady * ady) <= healRange && ally.hp < ally.maxHp) {
            ally.hp = Math.min(ally.maxHp, ally.hp + allyAmt);
          }
        }
      }
    }
  }
  // Spike entity tick (Noli F — John Doe spikes)
  if (window._spikeEntities && window._spikeEntities.length > 0) {
    for (let i = window._spikeEntities.length - 1; i >= 0; i--) {
      const spike = window._spikeEntities[i];
      spike.timer -= dt;
      if (spike.timer <= 0) { window._spikeEntities.splice(i, 1); continue; }
      // Touch DPS to players standing on spikes
      for (const p of gamePlayers) {
        if (p.id === spike.ownerId || !p.alive || p.isSummon) continue;
        const dx = p.x - spike.x; const dy = p.y - spike.y;
        if (Math.sqrt(dx * dx + dy * dy) < GAME_TILE * 0.7) {
          const owner = gamePlayers.find(pl => pl.id === spike.ownerId);
          dealDamage(owner || p, p, Math.round(spike.touchDPS * dt), true);
        }
      }
    }
  }

  // ── Backrooms tick ──
  for (const p of gamePlayers) {
    if (!p.alive || !p.inBackrooms) continue;
    // 20 DPS while trapped in backrooms
    const brDmg = Math.round(20 * wallDt);
    if (brDmg > 0) dealDamage(null, p, brDmg);
    // Check if reached door
    const doorDx = p.x - p.backroomsDoorX;
    const doorDy = p.y - p.backroomsDoorY;
    if (Math.sqrt(doorDx * doorDx + doorDy * doorDy) < GAME_TILE * 1.2) {
      _exitBackrooms(p, 'escaped');
      continue;
    }
    // Auto-exit only when 2 non-summon players left and one is in backrooms
    const aliveNonSummon = gamePlayers.filter(q => q.alive && !q.isSummon);
    if (aliveNonSummon.length <= 2 && aliveNonSummon.some(q => q.inBackrooms)) {
      _exitBackrooms(p, 'final-two');
      continue;
    }
  }

  // ── Alternate tick: check if alternate was killed ──
  for (const p of gamePlayers) {
    if (!p.hasAlternate || !p.alternateId) continue;
    // 10 DPS while hunted by alternate
    if (p.alive) {
      const altDmg = Math.round(10 * wallDt);
      if (altDmg > 0) dealDamage(null, p, altDmg);
    }
    const alt = gamePlayers.find(a => a.id === p.alternateId);
    if (!alt || !alt.alive) {
      // Alternate killed — player becomes visible again
      p.hasAlternate = false;
      p.alternateId = null;
      p.effects.push({ type: 'alternate-end', timer: 1.5 });
      if (p.id === localPlayerId) {
        combatLog.push({ text: '✅ Your Alternate was destroyed! You are visible again.', timer: 4, color: '#2ecc71' });
      }
    }
  }

  // ── Cat Unicorn tick: check if unicorn was killed ──
  for (const p of gamePlayers) {
    if (!p.catUnicornId) continue;
    const uni = gamePlayers.find(a => a.id === p.catUnicornId);
    if (!uni || !uni.alive) {
      const wasType = uni ? uni.summonType : null;
      p.catUnicornId = null;
      if (p.id === localPlayerId) {
        if (wasType === 'queenbee-unicorn') {
          combatLog.push({ text: '👑 Queen Bee Unicorn destroyed! M1 attacks restored.', timer: 4, color: '#ffd700' });
        } else if (wasType === 'seductive-unicorn') {
          combatLog.push({ text: '💖 Seductive Unicorn destroyed! You are no longer invulnerable.', timer: 4, color: '#ff69b4' });
        }
      }
    }
  }

  // Tick combat log
  for (let i = combatLog.length - 1; i >= 0; i--) {
    combatLog[i].timer -= dt;
    if (combatLog[i].timer <= 0) combatLog.splice(i, 1);
  }

  // M1 – auto-fire while mouse held (only if alive)
  // Skip during Smile Tapes — auto-chase handles M1 attacks
  if (localPlayer.alive && mouseDown && localPlayer.cdM1 <= 0 && !(localPlayer.dogtoothSmileTimer > 0)) {
    const _m1NonHost = (gameMode === undefined || gameMode === 'teams') && !isHostAuthority;
    if (!_m1NonHost) useAbility('M1');
    // Non-host M1 is relayed via mouseDown in player-input, host runs it
  }
  // Dragon breath: stop when mouse released
  if (localPlayer.dragonBreathActive && !mouseDown) {
    localPlayer.dragonBreathActive = false;
  }
  // Pyromaniac flame: stop when mouse released
  if (localPlayer.pyroFlameActive && !mouseDown) {
    localPlayer.pyroFlameActive = false;
  }

  // CPU AI update (use wallDt for consistent timer behaviour with player)
  // Also run in multiplayer host mode so illusion clones, noli clones, etc. get AI
  if (gameMode === 'fight' || gameMode === 'fight-hard' || isHostAuthority) {
    updateCPUs(wallDt);
    // Flush deferred removals from CPU ability functions
    if (_deferredRemoveIds.length > 0) {
      for (let ri = gamePlayers.length - 1; ri >= 0; ri--) {
        if (_deferredRemoveIds.includes(gamePlayers[ri].id)) gamePlayers.splice(ri, 1);
      }
      _deferredRemoveIds.length = 0;
    }
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
      dummy.hp = 3000;
      dummy.maxHp = 3000;
      gamePlayers.push(dummy);
    }
  }

  // ── Apple Tree update ──────────────────────────────────────
  if (appleTree) {
    if (appleTree.alive) {
      // Spawn apples every 15 seconds (max 3)
      appleTree.appleTimer -= wallDt;
      if (appleTree.appleTimer <= 0 && appleTree.apples.length < 3) {
        appleTree.appleTimer = 15;
        // Find adjacent walkable tiles (around the 2x2 tree footprint)
        const adj = [];
        for (let dr = -1; dr <= 2; dr++) {
          for (let dc = -1; dc <= 2; dc++) {
            // Skip the tree's own tiles
            if (dr >= 0 && dr <= 1 && dc >= 0 && dc <= 1) continue;
            const ar = appleTree.row + dr;
            const ac = appleTree.col + dc;
            if (ar < 0 || ar >= gameMap.rows || ac < 0 || ac >= gameMap.cols) continue;
            const t = gameMap.tiles[ar][ac];
            if (t === TILE.GROUND || t === TILE.GRASS) {
              // Don't place on existing apple
              if (!appleTree.apples.some(a => a.col === ac && a.row === ar)) {
                adj.push({ col: ac, row: ar });
              }
            }
          }
        }
        if (adj.length > 0) {
          const pick = adj[Math.floor(Math.random() * adj.length)];
          appleTree.apples.push({ col: pick.col, row: pick.row });
        }
      }
      // Reset timer if max apples reached
      if (appleTree.apples.length >= 3) appleTree.appleTimer = 15;
    } else {
      // Tree is dead — regrow timer
      appleTree.regrowTimer -= wallDt;
      if (appleTree.regrowTimer <= 0) {
        appleTree.alive = true;
        appleTree.hp = appleTree.maxHp;
        appleTree.regrowTimer = 0;
        appleTree.appleTimer = 15;
        // Tiles are already GROUND — stump blocking was via isStumpTile() which
        // now returns false since alive=true. No tile changes needed.
      }
    }

    // Apple pickup: any alive player touching an apple eats it and heals 300
    for (let ai = appleTree.apples.length - 1; ai >= 0; ai--) {
      const apple = appleTree.apples[ai];
      const appleX = (apple.col + 0.5) * GAME_TILE;
      const appleY = (apple.row + 0.5) * GAME_TILE;
      for (const p of gamePlayers) {
        if (!p.alive || p.isSummon) continue;
        const dx = p.x - appleX;
        const dy = p.y - appleY;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist < GAME_TILE * 0.6) {
          // Eat apple
          p.hp = Math.min(p.maxHp, p.hp + 300);
          p.effects.push({ type: 'apple-heal', timer: 1.0 });
          if (p.id === localPlayerId) {
            combatLog.push({ text: '🍎 Ate an apple! +300 HP', timer: 3, color: '#2ecc71' });
          }
          appleTree.apples.splice(ai, 1);
          break;
        }
      }
    }
  }
}

function tickCooldowns(p, dt) {
  if (p.cdM1 > 0) p.cdM1 = Math.max(0, p.cdM1 - dt);
  if (p.cdE > 0) p.cdE = Math.max(0, p.cdE - dt);
  if (p.cdR > 0) p.cdR = Math.max(0, p.cdR - dt);
  if (p.cdT > 0) p.cdT = Math.max(0, p.cdT - dt);
  if (p.cdF > 0) p.cdF = Math.max(0, p.cdF - dt);
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
  // Unstable: use random speed
  if (localPlayer.unstableOriginalFighter && localPlayer.unstableRandomSpeed) speed = localPlayer.unstableRandomSpeed;  // Unstable Eye: speed boost (as fast as Deer)
  if (localPlayer.unstableEyeTimer > 0) speed *= 3.0;
  // Napoleon Cavalry: 2.5x speed boost
  if (localPlayer.napoleonCavalry) speed *= 2.5;
  // Napoleon Charisma trait: allies near Napoleon get 50% speed buff
  if (gameMode === 'teams' && localPlayer.fighter && localPlayer.fighter.id !== 'napoleon') {
    for (const p of gamePlayers) {
      if (!p.alive || p.isSummon || p.id === localPlayer.id) continue;
      if (p.fighter && p.fighter.id === 'napoleon' && p.traitActive && p.team === localPlayer.team) {
        const ndx = p.x - localPlayer.x, ndy = p.y - localPlayer.y;
        if (ndx * ndx + ndy * ndy < (GAME_TILE * 6) * (GAME_TILE * 6)) { speed *= 1.5; break; }
      }
    }
  }
  // Moderator Server Update: 50% speed buff
  if (localPlayer.modServerUpdateTimer > 0) speed *= 1.5;
  // Moderator Fear: 2x speed when running away from source
  if (localPlayer.modFearTimer > 0 && localPlayer.modFearSourceId) {
    const src = gamePlayers.find(p => p.id === localPlayer.modFearSourceId);
    if (src && src.alive) {
      const fdx = localPlayer.x - src.x; const fdy = localPlayer.y - src.y;
      const mdx = (keys['d'] || keys['D'] || keys['ArrowRight'] ? 1 : 0) - (keys['a'] || keys['A'] || keys['ArrowLeft'] ? 1 : 0);
      const mdy = (keys['s'] || keys['S'] || keys['ArrowDown'] ? 1 : 0) - (keys['w'] || keys['W'] || keys['ArrowUp'] ? 1 : 0);
      if (fdx * mdx + fdy * mdy > 0) speed *= 2.0; // running away
    }
  }
  // Cricket Gear Up: slower speed
  if (localPlayer.gearUpTimer > 0) speed *= 0.6;
  // D&D Human: 1.2x speed
  if (localPlayer.dndRace === 'human') speed *= 1.2;
  // Dragon: roar speed buff, fly speed, beam immobilization, breath slow
  if (localPlayer.dragonRoarActive) speed *= 1.3;
  if (localPlayer.dragonFlying) speed *= 2.5; // same as Napoleon cavalry
  if (localPlayer.dragonBreathActive) speed *= 0.5;
  if (localPlayer.pyroFlameActive) speed *= 0.5;
  // Heavy Rope: slower while swinging, faster during ROPE POWER
  if (localPlayer.ropeSwingActive) speed *= 0.6;
  if (localPlayer.ropePowerTimer > 0) speed *= 1.8;
  if (localPlayer.dragonBeamCharging || localPlayer.dragonBeamRecovery > 0) speed = 0;
  // Dog Tooth: Smile Tapes overrides movement (handled in update loop), Smile speed boost
  if (localPlayer.dogtoothSmileTimer > 0) speed = 0; // movement is auto-chase
  // Buff slow debuff
  if (localPlayer.buffSlowed > 0) speed *= 0.6;
  // Cricket Wicket line: 50% speed boost when on the line between both wickets
  if (localPlayer.wicketIds && localPlayer.wicketIds.length === 2) {
    const w0 = gamePlayers.find(p => p.id === localPlayer.wicketIds[0]);
    const w1 = gamePlayers.find(p => p.id === localPlayer.wicketIds[1]);
    if (w0 && w0.alive && w1 && w1.alive) {
      // Check distance from player to line segment w0-w1
      const lx = w1.x - w0.x, ly = w1.y - w0.y;
      const lineLen = Math.sqrt(lx * lx + ly * ly) || 1;
      const t = Math.max(0, Math.min(1, ((localPlayer.x - w0.x) * lx + (localPlayer.y - w0.y) * ly) / (lineLen * lineLen)));
      const closestX = w0.x + t * lx, closestY = w0.y + t * ly;
      const distToLine = Math.sqrt((localPlayer.x - closestX) ** 2 + (localPlayer.y - closestY) ** 2);
      if (distToLine < GAME_TILE * 1.5) speed *= 1.5;
    }
  }
  // Intimidation: cannot move TOWARD the intimidator (within 3.5 tile range)
  if (localPlayer.intimidated > 0 && localPlayer.intimidatedBy) {
    const src = gamePlayers.find((p) => p.id === localPlayer.intimidatedBy);
    if (src) {
      const towardX = src.x - localPlayer.x;
      const towardY = src.y - localPlayer.y;
      const towardDist = Math.sqrt(towardX * towardX + towardY * towardY) || 1;
      if (towardDist < GAME_TILE * 3.5) {
        const towardNx = towardX / towardDist;
        const towardNy = towardY / towardDist;
        // Project movement onto toward-direction; if positive, strip that component
        const dot = dx * towardNx + dy * towardNy;
        if (dot > 0) {
          dx -= dot * towardNx;
          dy -= dot * towardNy;
        }
      }
    }
  }
  // Deer Fear: 50% speed boost when moving away from the enemy who was closest at cast
  if (localPlayer.deerFearTimer > 0) {
    const awayX = localPlayer.x - localPlayer.deerFearTargetX;
    const awayY = localPlayer.y - localPlayer.deerFearTargetY;
    const dot = dx * awayX + dy * awayY;
    if (dot > 0) speed *= 1.5;
  }
  // Noli: 50% speed boost when no fighter is within 5 tiles
  if (localPlayer.fighter && localPlayer.fighter.id === 'noli') {
    const fiveTiles = GAME_TILE * 5;
    let anyClose = false;
    for (const p of gamePlayers) {
      if (p.id === localPlayer.id || !p.alive || p.isSummon) continue;
      const ndx = p.x - localPlayer.x, ndy = p.y - localPlayer.y;
      if (ndx * ndx + ndy * ndy < fiveTiles * fiveTiles) { anyClose = true; break; }
    }
    if (!anyClose) speed *= 1.5;
  }
  // Deer: slower while building robot
  if (localPlayer.deerBuildSlowTimer > 0 && localPlayer.fighter && localPlayer.fighter.id === 'deer') {
    speed *= 0.6;
  }
  // Igloo slow: severely slow anyone inside an enemy igloo
  for (const owner of gamePlayers) {
    if (owner.iglooTimer > 0 && owner.id !== localPlayer.id) {
      const iglooAbil = owner.fighter && owner.fighter.abilities[4];
      const ir = ((iglooAbil ? iglooAbil.radius : 4.5) || 4.5) * GAME_TILE;
      const dxI = localPlayer.x - owner.iglooX, dyI = localPlayer.y - owner.iglooY;
      if (Math.sqrt(dxI * dxI + dyI * dyI) < ir) { speed *= 0.35; break; }
    }
  }
  // Fighter Aura trait: moving toward a Fighter with trait slows you 0.8x
  for (const p of gamePlayers) {
    if (!p.alive || p.isSummon || p.id === localPlayer.id) continue;
    if (!p.traitActive || !p.fighter || p.fighter.id !== 'fighter') continue;
    if (gameMode === 'teams' && localPlayer.team && p.team === localPlayer.team) continue;
    const toFx = p.x - localPlayer.x; const toFy = p.y - localPlayer.y;
    const toFdist = Math.sqrt(toFx * toFx + toFy * toFy) || 1;
    if (toFdist > GAME_TILE * 8) continue; // aura range: 8 tiles
    const dot = dx * (toFx / toFdist) + dy * (toFy / toFdist);
    if (dot > 0) speed *= 0.8;
  }
  // Black hole trapped: no movement at all (spinning in center)
  if (localPlayer.bhTrapped) { return; }
  // Black hole zone: directional speed modifiers
  //   Moving TOWARD the hole: 50% faster
  //   Moving AWAY or sideways: zone-dependent slow
  if (localPlayer.bhZoneTimer > 0 && localPlayer.bhZone && localPlayer.bhSourceX != null) {
    localPlayer.bhZoneTimer -= dt;
    const toBHx = localPlayer.bhSourceX - localPlayer.x;
    const toBHy = localPlayer.bhSourceY - localPlayer.y;
    const toBHdist = Math.sqrt(toBHx * toBHx + toBHy * toBHy) || 1;
    const toBHnx = toBHx / toBHdist; const toBHny = toBHy / toBHdist;
    // dot > 0 means moving toward black hole
    const dot = dx * toBHnx + dy * toBHny;
    if (dot > 0.2) {
      // Moving toward: 50% speed boost
      speed *= 1.5;
    } else {
      // Moving away or sideways: apply zone-based slow
      if (localPlayer.bhZone === 'outer') speed *= 0.4; // 60% slower
      else if (localPlayer.bhZone === 'mid') speed *= 0.0; // can't escape — pull matches speed
      else if (localPlayer.bhZone === 'inner') speed *= 0.0; // inescapable
    }
  }

  const move = speed * dt * 60; // frame-rate independent: same effective speed at any FPS
  const newX = localPlayer.x + dx * move;
  const newY = localPlayer.y + dy * move;
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;

  const prevX = localPlayer.x, prevY = localPlayer.y;
  if (localPlayer.dragonFlying) {
    // Flying: ignore obstacles but stay in map bounds
    const nxClamped = Math.max(radius, Math.min(newX, gameMap.cols * GAME_TILE - radius));
    const nyClamped = Math.max(radius, Math.min(newY, gameMap.rows * GAME_TILE - radius));
    localPlayer.x = nxClamped;
    localPlayer.y = nyClamped;
  } else {
    if (canMoveTo(newX, localPlayer.y, radius)) localPlayer.x = newX;
    if (canMoveTo(localPlayer.x, newY, radius)) localPlayer.y = newY;
  }

  // Spike collision (John Doe spikes): push player out of spike radius, but allow sliding
  if (window._spikeEntities && window._spikeEntities.length > 0) {
    const spikeRadius = GAME_TILE * 0.7;
    for (const spike of window._spikeEntities) {
      if (spike.ownerId === localPlayer.id) continue; // own spikes don't block
      const sdx = localPlayer.x - spike.x;
      const sdy = localPlayer.y - spike.y;
      const sDist = Math.sqrt(sdx * sdx + sdy * sdy);
      if (sDist < spikeRadius && sDist > 0.01) {
        // Push player to edge of spike radius (slide around rather than full revert)
        const pushNx = sdx / sDist;
        const pushNy = sdy / sDist;
        localPlayer.x = spike.x + pushNx * spikeRadius;
        localPlayer.y = spike.y + pushNy * spikeRadius;
      } else if (sDist <= 0.01) {
        // Exactly on spike center — push in movement direction
        localPlayer.x = prevX;
        localPlayer.y = prevY;
      }
    }
  }

  // Igloo containment removed — igloo is now freely walkable (slow applied in speed calc)
}

// Check if a tile is part of the dead apple tree stump (blocks movement like rock)
function isStumpTile(col, row) {
  if (!appleTree || appleTree.alive) return false;
  return col >= appleTree.col && col <= appleTree.col + 1 &&
         row >= appleTree.row && row <= appleTree.row + 1;
}

// Push any players standing on the stump to a safe position when the tree dies
function pushPlayersOffStump() {
  if (!appleTree) return;
  const stumpCenterX = (appleTree.col + 1) * GAME_TILE;
  const stumpCenterY = (appleTree.row + 1) * GAME_TILE;
  const pr = GAME_TILE * PLAYER_RADIUS_RATIO;
  for (const pl of gamePlayers) {
    if (!pl.alive) continue;
    const pCol = Math.floor(pl.x / GAME_TILE);
    const pRow = Math.floor(pl.y / GAME_TILE);
    if (pCol >= appleTree.col && pCol <= appleTree.col + 1 &&
        pRow >= appleTree.row && pRow <= appleTree.row + 1) {
      let pushDx = pl.x - stumpCenterX;
      let pushDy = pl.y - stumpCenterY;
      const pushDist = Math.sqrt(pushDx * pushDx + pushDy * pushDy) || 1;
      pushDx /= pushDist; pushDy /= pushDist;
      let placed = false;
      for (let step = 1; step <= 8; step++) {
        const tryX = stumpCenterX + pushDx * GAME_TILE * (1.2 + step * 0.3);
        const tryY = stumpCenterY + pushDy * GAME_TILE * (1.2 + step * 0.3);
        if (canMoveTo(tryX, tryY, pr)) {
          pl.x = tryX; pl.y = tryY; placed = true; break;
        }
      }
      if (!placed) {
        for (let a = 0; a < 8 && !placed; a++) {
          const angle = (a / 8) * Math.PI * 2;
          for (let step = 1; step <= 6 && !placed; step++) {
            const tryX = stumpCenterX + Math.cos(angle) * GAME_TILE * (1.2 + step * 0.3);
            const tryY = stumpCenterY + Math.sin(angle) * GAME_TILE * (1.2 + step * 0.3);
            if (canMoveTo(tryX, tryY, pr)) {
              pl.x = tryX; pl.y = tryY; placed = true;
            }
          }
        }
      }
      if (!placed) {
        const safe = getRandomSafePosition();
        pl.x = safe.x; pl.y = safe.y;
      }
    }
  }
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
    if (isStumpTile(col, row)) return false;
  }
  return true;
}

// Line-of-sight check: steps along the line from (x1,y1) to (x2,y2) and returns false if any obstacle tile is hit
function _hasLineOfSight(x1, y1, x2, y2) {
  const dx = x2 - x1, dy = y2 - y1;
  const dist = Math.sqrt(dx * dx + dy * dy);
  const steps = Math.ceil(dist / (GAME_TILE * 0.5));
  for (let i = 1; i < steps; i++) {
    const t = i / steps;
    const px = x1 + dx * t;
    const py = y1 + dy * t;
    const col = Math.floor(px / GAME_TILE);
    const row = Math.floor(py / GAME_TILE);
    if (col < 0 || col >= gameMap.cols || row < 0 || row >= gameMap.rows) return false;
    const tile = gameMap.tiles[row][col];
    if (tile === TILE.ROCK) return false;
    if (isStumpTile(col, row)) return false;
  }
  return true;
}

// Raycast along a direction and return the distance to the first obstacle (or maxDist if none)
function _getFlameBlockedDist(x1, y1, nx, ny, maxDist) {
  const stepSize = GAME_TILE * 0.4;
  const steps = Math.ceil(maxDist / stepSize);
  for (let i = 1; i <= steps; i++) {
    const d = Math.min(i * stepSize, maxDist);
    const px = x1 + nx * d;
    const py = y1 + ny * d;
    const col = Math.floor(px / GAME_TILE);
    const row = Math.floor(py / GAME_TILE);
    if (col < 0 || col >= gameMap.cols || row < 0 || row >= gameMap.rows) return d;
    const tile = gameMap.tiles[row][col];
    if (tile === TILE.ROCK) return d;
    if (isStumpTile(col, row)) return d;
  }
  return maxDist;
}

// Ochre jelly: goes through obstacles (rocks/trees) but NOT water or out-of-bounds
function canMoveToNoSea(px, py, radius) {
  const offsets = [
    { x: -radius, y: -radius }, { x: radius, y: -radius },
    { x: -radius, y: radius },  { x: radius, y: radius },
  ];
  for (const off of offsets) {
    const col = Math.floor((px + off.x) / GAME_TILE);
    const row = Math.floor((py + off.y) / GAME_TILE);
    if (col < 0 || col >= gameMap.cols || row < 0 || row >= gameMap.rows) return false;
    const tile = gameMap.tiles[row][col];
    if (tile === TILE.WATER) return false;
  }
  return true;
}

// ═══════════════════════════════════════════════════════════════
// SAFE RANDOM TELEPORT — find a random walkable position
// ═══════════════════════════════════════════════════════════════
function getRandomSafePosition() {
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;
  const candidates = [];
  for (let r = 1; r < gameMap.rows - 1; r++) {
    for (let c = 1; c < gameMap.cols - 1; c++) {
      const t = gameMap.tiles[r][c];
      if (t === TILE.GROUND || t === TILE.GRASS) {
        candidates.push({ r, c });
      }
    }
  }
  // Shuffle and find one that passes canMoveTo
  for (let i = candidates.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [candidates[i], candidates[j]] = [candidates[j], candidates[i]];
  }
  for (const pt of candidates) {
    const px = (pt.c + 0.5) * GAME_TILE;
    const py = (pt.r + 0.5) * GAME_TILE;
    if (canMoveTo(px, py, radius)) return { x: px, y: py };
  }
  // Fallback: center of map
  return { x: (gameMap.cols / 2) * GAME_TILE, y: (gameMap.rows / 2) * GAME_TILE };
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
    if (tile === TILE.ROCK || isStumpTile(col, row)) {
      if (!p.dndFireball) { projectiles.splice(i, 1); continue; }
    }
    // Fireball stops at water/sea
    if (p.dndFireball && tile === TILE.WATER) {
      projectiles.splice(i, 1); continue;
    }

    // Projectile hits apple tree (alive tree blocks projectiles and takes damage)
    if (appleTree && appleTree.alive) {
      if (col >= appleTree.col && col <= appleTree.col + 1 &&
          row >= appleTree.row && row <= appleTree.row + 1) {
        const dmg = p.damage || 100;
        appleTree.hp -= dmg;
        if (appleTree.hp <= 0) {
          appleTree.hp = 0;
          appleTree.alive = false;
          appleTree.regrowTimer = 30;
          appleTree.apples = [];
          pushPlayersOffStump();
          combatLog.push({ text: '🪓 Apple tree destroyed!', timer: 4, color: '#e67e22' });
        }
        projectiles.splice(i, 1); continue;
      }
    }

    // Hit detection: host resolves ALL projectile hits; otherwise only local/CPU projectiles
    const isCpuProj = p.ownerId && p.ownerId.startsWith('cpu-');
    const isLocalProj = p.ownerId === localPlayerId;
    if (isLocalProj || isCpuProj || isHostAuthority) {
      const owner = isLocalProj ? localPlayer : gamePlayers.find(pl => pl.id === p.ownerId);
      for (const target of gamePlayers) {
        if (target.id === p.ownerId || !target.alive) continue;
        if (target.isSummon && target.summonOwner === p.ownerId && target.summonType !== 'dnd-orc') continue;
        // Skip backrooms players (they're in another dimension)
        if (target.inBackrooms) continue;
        // Skip Complex players (isolated in Final Battle)
        if (target.dogtoothInComplex) continue;
        // Skip teammates in team mode (projectiles shouldn't hit allies)
        if (gameMode === 'teams' && owner) {
          const ownerTeam = owner.isSummon ? (gamePlayers.find(o => o.id === owner.summonOwner) || {}).team : owner.team;
          const targetTeam = target.isSummon ? (gamePlayers.find(o => o.id === target.summonOwner) || {}).team : target.team;
          if (ownerTeam && targetTeam && ownerTeam === targetTeam) continue;
        }
        // Shockwave: skip already-hit targets
        if (p.hitTargets && p.hitTargets.has(target.id)) continue;
        const dx = target.x - p.x;
        const dy = target.y - p.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        const hitRadius = p.type === 'shockwave' ? radius + 12
                        : p.dndFireball ? (p.aoeRadius || 1.5 * GAME_TILE)
                        : radius + 4;
        if (dist < hitRadius) {
          // D&D Fireball: AoE explosion — damage ALL targets in radius, then remove
          if (p.dndFireball) {
            const aoeR = p.aoeRadius || (1.5 * GAME_TILE);
            for (const t2 of gamePlayers) {
              if (t2.id === p.ownerId || !t2.alive || t2.inBackrooms || t2.dogtoothInComplex) continue;
              if (t2.isSummon && t2.summonOwner === p.ownerId && t2.summonType !== 'dnd-orc') continue;
              if (gameMode === 'teams' && owner) {
                const oT = owner.isSummon ? (gamePlayers.find(o => o.id === owner.summonOwner) || {}).team : owner.team;
                const tT = t2.isSummon ? (gamePlayers.find(o => o.id === t2.summonOwner) || {}).team : t2.team;
                if (oT && tT && oT === tT) continue;
              }
              const d2 = Math.sqrt((t2.x - p.x) ** 2 + (t2.y - p.y) ** 2);
              if (d2 < aoeR) dealDamage(owner, t2, Math.round(p.damage));
            }
            projectiles.splice(i, 1);
            break;
          }
          // Cricket Drive reflect: if target has active reflect window, bounce projectile back
          if (target.driveReflectTimer > 0 && target.fighter && target.fighter.id === 'cricket') {
            const driveAbil = target.fighter.abilities[1];
            const retSpd = (driveAbil.returnSpeed || 80) * GAME_TILE / 10;
            if (owner && owner.alive) {
              const rdx = owner.x - p.x; const rdy = owner.y - p.y;
              const rd = Math.sqrt(rdx * rdx + rdy * rdy) || 1;
              p.vx = (rdx / rd) * retSpd;
              p.vy = (rdy / rd) * retSpd;
            } else {
              p.vx = -p.vx; p.vy = -p.vy;
            }
            p.damage = (p.damage || 0) + (driveAbil.returnBonusDmg || 100);
            p.ownerId = target.id;
            p.timer = 3;
            target.driveReflectTimer = 0; // consume the reflect
            // Reduce E cooldown since reflection happened
            target.cdE = driveAbil.hitProjectileCD || 5;
            break;
          }
          // Hitman bullet: Professional trait — 1.3× if beyond traitRange at spawn
          if (p.type === 'hitman-bullet') {
            // Use stored spawn position for accurate range calculation
            const spawnX = p.spawnX != null ? p.spawnX : (owner ? owner.x : p.x);
            const spawnY = p.spawnY != null ? p.spawnY : (owner ? owner.y : p.y);
            const travelDist = Math.sqrt((target.x - spawnX) ** 2 + (target.y - spawnY) ** 2);
            if (travelDist >= (p.traitRange || 6 * GAME_TILE)) {
              p.damage = Math.round(p.damage * 1.3);
            }
          }
          dealDamage(owner, target, Math.round(p.damage), !!p.fromSummon);
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
            if (typeof socket !== 'undefined' && socket.emit && !isHostAuthority) {
              socket.emit('player-knockback', { targetId: target.id, x: target.x, y: target.y });
              socket.emit('player-debuff', { targetId: target.id, type: 'stun', duration: stunDur });
            }
            combatLog.push({ text: '⚔ Entangled ' + target.name + '!', timer: 3, color: '#00ff66' });
          }
          // Shockwave: apply poison, passes through enemies (don't splice)
          if (p.type === 'shockwave') {
            if (!target.poisonTimers) target.poisonTimers = [];
            target.poisonTimers.push({ sourceId: p.ownerId, dps: p.poisonDPS || 50, remaining: p.poisonDuration || 3 });
            target.effects.push({ type: 'poison', timer: p.poisonDuration || 3 });
            // Mark this target as already hit by this wave so it doesn't double-hit
            if (!p.hitTargets) p.hitTargets = new Set();
            p.hitTargets.add(target.id);
            continue; // don't splice — shockwave passes through
          }
          // D&D Blur bolt: apply blur debuff to target
          if (p.dndBlurDuration && p.dndBlurDuration > 0) {
            target.dndBlurTimer = p.dndBlurDuration;
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
    if (s.summonType === 'noli-clone') continue; // Noli clones use full CPU AI
    if (s.summonType === 'illusion-copy' || s.summonType === 'illusion-special-copy') continue; // Illusion copies use full CPU AI
    if (s.stunned > 0) continue;

    const owner = gamePlayers.find(p => p.id === s.summonOwner);
    const radius = GAME_TILE * PLAYER_RADIUS_RATIO;

    // Find nearest enemy (not owner, not fellow summons of same owner, not teammates)
    let bestTarget = null;
    let bestDist = Infinity;
    const ownerTeam = owner ? owner.team : null;
    for (const p of gamePlayers) {
      if (p.id === s.id || p.id === s.summonOwner || !p.alive) continue;
      if (p.isSummon && p.summonOwner === s.summonOwner) continue;
      // Skip teammates in team mode
      if (ownerTeam && !p.isSummon && p.team === ownerTeam) continue;
      if (ownerTeam && p.isSummon) {
        const pOwner = gamePlayers.find(o => o.id === p.summonOwner);
        if (pOwner && pOwner.team === ownerTeam) continue;
      }
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
          dealDamage(owner || s, p, p.hp, true); // instant kill
          combatLog.push({ text: '⚱️ ' + p.name + ' touched the Obelisk!', timer: 4, color: '#d4af37' });
        }
      }
    } else if (s.summonType === 'guby-tv') {
      // Filbus GUBY TV: chase nearest enemy, instant kill on touch, despawn after 8s
      s.gubyTimer -= dt;
      if (s.gubyTimer <= 0) { s.alive = false; s.hp = 0; continue; }
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const spd = (s.summonSpeed || 2.5) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const tryX = s.x + nx * spd; const tryY = s.y + ny * spd;
        if (canMoveTo(tryX, tryY, radius)) { s.x = tryX; s.y = tryY; }
        // Touch kill
        if (dist < radius * 2.5) {
          dealDamage(owner || s, bestTarget, bestTarget.hp, true);
          if (bestTarget.id === localPlayerId || (owner && owner.id === localPlayerId)) {
            combatLog.push({ text: '📺 GUBY TV got ' + bestTarget.name + '!', timer: 4, color: '#a29bfe' });
          }
          s.alive = false; s.hp = 0;
        }
      }
    } else if (s.summonType === 'macrocosms') {
      // Headless Macrocosms: very slow movement, melee attack with cooldown
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = s.summonSpeed * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Attack when in range and off cooldown
        if (bestDist < radius * 2.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage, true);
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
        const moveSpeed = s.summonSpeed * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Attack within melee range
        if (bestDist < GAME_TILE * 1.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage, true);
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
        const moveSpeed = s.summonSpeed * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Slash attack within melee range
        if (bestDist < GAME_TILE * 1.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage, true);
          s.summonAttackTimer = s.summonAttackCD;
          s.effects.push({ type: 'zombie-slash', timer: 0.2, aimNx: nx, aimNy: ny });
        }
      }
    } else if (s.summonType === 'deer-robot') {
      // Deer Robot: stationary, fires poker chips at closest enemy every second
      // Cap at 10 active chips per owner to prevent lag
      const ownerChipCount = projectiles.filter(pr => pr.ownerId === s.summonOwner && pr.type === 'chip').length;
      if (bestTarget && s.summonAttackTimer <= 0 && ownerChipCount < 10) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const spd = 12 * GAME_TILE / 10;
        const angle = Math.atan2(dy, dx);
        projectiles.push({
          x: s.x, y: s.y,
          vx: Math.cos(angle) * spd, vy: Math.sin(angle) * spd,
          ownerId: s.summonOwner, damage: s.summonDamage,
          timer: 2, type: 'chip', fromSummon: true,
        });
        s.summonAttackTimer = s.summonAttackCD;
        s.effects.push({ type: 'robot-fire', timer: 0.3 });
      }
    } else if (s.summonType === 'exploding-kitten') {
      // Exploding Kitten: chase nearest enemy and explode on contact
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 2.5) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Explode on touch (dot overlap)
        if (dist < radius * 2) {
          const _kitTargetWasAlive = bestTarget.alive;
          dealDamage(owner || s, bestTarget, s.summonDamage, true);
          // Achievement: Cat kitten kills (not team mode)
          if (_kitTargetWasAlive && !bestTarget.alive && owner && owner.id === localPlayerId && !bestTarget.isSummon && gameMode !== 'teams') {
            _catKittenKillsThisGame++;
            if (_catKittenKillsThisGame >= 2 && typeof trackCatKittenAch === 'function') {
              trackCatKittenAch();
            }
          }
          combatLog.push({ text: '💥 Kitten exploded on ' + bestTarget.name + '! (' + s.summonDamage + ' dmg)', timer: 3, color: '#ff4444' });
          s.alive = false;
          s.hp = 0;
          s.effects.push({ type: 'death', timer: 2 });
          // Remove from owner's kitten list
          if (owner && owner.catKittenIds) {
            const kidx = owner.catKittenIds.indexOf(s.id);
            if (kidx >= 0) owner.catKittenIds.splice(kidx, 1);
          }
        }
      }
    } else if (s.summonType === 'coolkidd') {
      // c00lkidd: stationary, throws red balls (like Gamble) at nearest enemy
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget && s.summonAttackTimer <= 0) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const dmg = 100;
        const speed = s.summonProjectileSpeed || 30;
        const nx = dx / dist; const ny = dy / dist;
        projectiles.push({
          x: s.x, y: s.y,
          vx: nx * speed * GAME_TILE, vy: ny * speed * GAME_TILE,
          ownerId: owner ? owner.id : s.id,
          damage: dmg,
          timer: 3,
          type: 'coolkidd-ball',
          color: '#ff0000',
        });
        s.summonAttackTimer = s.summonAttackCD || 4;
        s.effects.push({ type: 'coolkidd-fire', timer: 0.3 });
      }
    } else if (s.summonType === 'bowler') {
      // Bowler: stationary, sends ball to owner (Cricket) who bats it at closest enemy
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (owner && owner.alive && s.summonAttackTimer <= 0) {
        // Find closest enemy to owner for targeting
        let ownerTarget = null; let ownerTargetDist = Infinity;
        for (const t of gamePlayers) {
          if (t.id === owner.id || !t.alive || t.isSummon) continue;
          const tdx = t.x - owner.x; const tdy = t.y - owner.y;
          const td = Math.sqrt(tdx * tdx + tdy * tdy);
          if (td < ownerTargetDist) { ownerTargetDist = td; ownerTarget = t; }
        }
        if (ownerTarget) {
          // Fire ball from bowler toward the target (via cricket's position)
          const dx = ownerTarget.x - s.x; const dy = ownerTarget.y - s.y;
          const dist = Math.sqrt(dx * dx + dy * dy) || 1;
          const speed = 40;
          projectiles.push({
            x: s.x, y: s.y,
            vx: (dx / dist) * speed * GAME_TILE, vy: (dy / dist) * speed * GAME_TILE,
            ownerId: owner.id,
            damage: s.summonDamage || 200,
            timer: 3,
            type: 'bowler-ball',
            color: '#228b22',
          });
          s.summonAttackTimer = s.summonAttackCD || 5;
          s.effects.push({ type: 'bowler-fire', timer: 0.3 });
        }
      }
    } else if (s.summonType === 'crab') {
      // Crab: chase nearest enemy and deal damage on contact (with cooldown)
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 2.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Touch damage with cooldown
        if (dist < radius * 2 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage, true);
          s.summonAttackTimer = s.summonAttackCD || 1;
          s.effects.push({ type: 'crab-attack', timer: 0.3 });
        }
      }
    } else if (s.summonType === 'hitman-backup') {
      // Backup Agent: chases nearest enemy and fires pistol bullets (with windup)
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        // Chase until within 4 tiles, then stand and shoot
        if (dist > GAME_TILE * 4) {
          const moveSpeed = (s.summonSpeed || 3.0) * GAME_TILE * dt;
          const nx = dx / dist; const ny = dy / dist;
          const newX = s.x + nx * moveSpeed;
          const newY = s.y + ny * moveSpeed;
          if (canMoveTo(newX, s.y, radius)) s.x = newX;
          if (canMoveTo(s.x, newY, radius)) s.y = newY;
        }
        // Fire when ready
        if (s.summonAttackTimer <= 0) {
          const bSpd = (s.summonProjectileSpeed || 28) * GAME_TILE / 10;
          const nx = dx / dist; const ny = dy / dist;
          projectiles.push({
            x: s.x, y: s.y,
            vx: nx * bSpd, vy: ny * bSpd,
            ownerId: owner ? owner.id : s.id,
            damage: s.summonDamage || 100,
            timer: 3, type: 'hitman-bullet',
            color: '#aabbcc',
            fromSummon: true,
          });
          s.summonAttackTimer = s.summonAttackCD || 0.5;
          s.effects.push({ type: 'hitman-fire', timer: 0.15 });
        }
      }
    } else if (s.summonType === 'johndoe') {
      // John Doe: stationary, fires spikes in a line toward nearest enemy
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget && s.summonAttackTimer <= 0) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const nx = dx / dist; const ny = dy / dist;
        // Create spike line from John Doe's position toward target, extending until water/edge
        const spikeDuration = s.spikeDuration || 5;
        const hitDmg = s.summonDamage || 500;
        const touchDPS = s.touchDPS || 100;
        // Place spikes every tile along the line
        let sx = s.x; let sy = s.y;
        const step = GAME_TILE;
        for (let d = 0; d < 50; d++) {
          sx += nx * step; sy += ny * step;
          const col = Math.floor(sx / GAME_TILE);
          const row = Math.floor(sy / GAME_TILE);
          if (col < 0 || col >= gameMap.cols || row < 0 || row >= gameMap.rows) break;
          if (gameMap.tiles[row][col] === TILE.WATER) break;
          if (gameMap.tiles[row][col] === TILE.ROCK) break;
          // Add spike entity
          if (!window._spikeEntities) window._spikeEntities = [];
          window._spikeEntities.push({
            x: (col + 0.5) * GAME_TILE,
            y: (row + 0.5) * GAME_TILE,
            timer: spikeDuration,
            hitDmg: hitDmg,
            touchDPS: touchDPS,
            ownerId: owner ? owner.id : s.id,
            hitPlayers: new Set(),
          });
        }
        // Hit damage on initial placement — any player standing on the spike line
        if (window._spikeEntities) {
          for (const spike of window._spikeEntities) {
            if (spike.timer < spikeDuration - 0.01) continue; // only new spikes
            for (const t of gamePlayers) {
              if (t.id === (owner ? owner.id : s.id) || !t.alive || t.isSummon) continue;
              const sdx = t.x - spike.x; const sdy = t.y - spike.y;
              if (Math.sqrt(sdx * sdx + sdy * sdy) < GAME_TILE * 0.8) {
                dealDamage(owner || s, t, hitDmg, true);
                spike.hitPlayers.add(t.id);
              }
            }
          }
        }
        s.summonAttackTimer = s.summonAttackCD || 10;
        s.effects.push({ type: 'johndoe-fire', timer: 0.5 });
        combatLog.push({ text: '🗡️ Spikes deployed!', timer: 2, color: '#8b0000' });
      }
    } else if (s.summonType === 'backrooms-chaser') {
      // Backrooms chaser: relentlessly chase the specific target
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      const prey = s.summonTargetId ? gamePlayers.find(t => t.id === s.summonTargetId) : null;
      if (prey && prey.alive && prey.inBackrooms) {
        const dx = prey.x - s.x; const dy = prey.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 2.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Touch = instant kill (bypass all damage reduction)
        if (dist < radius * 2 && s.summonAttackTimer <= 0) {
          prey.hp = 0;
          prey.alive = false;
          prey.effects.push({ type: 'death', timer: 2 });
          s.summonAttackTimer = s.summonAttackCD || 0.5;
        }
      } else if (!prey || !prey.alive || !prey.inBackrooms) {
        // Target escaped or died — remove chaser
        s.alive = false;
        s.hp = 0;
        s.effects.push({ type: 'death', timer: 2 });
      }
    } else if (s.summonType === 'alternate') {
      // Alternate: chase the specific target (slightly slower), one-touch kill
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      const prey = s.summonTargetId ? gamePlayers.find(t => t.id === s.summonTargetId) : null;
      if (prey && prey.alive) {
        const dx = prey.x - s.x; const dy = prey.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 2.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Touch = instant kill on the target
        if (dist < radius * 2 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, prey, s.summonDamage, true);
          s.summonAttackTimer = s.summonAttackCD || 0.5;
        }
      }
    } else if (s.summonType === 'room') {
      // Room (Boisvert): chase its specific target + constant 40 DPS + melee on contact
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      const prey = s.summonTargetId ? gamePlayers.find(t => t.id === s.summonTargetId) : null;
      if (prey && prey.alive) {
        // Chase
        const dx = prey.x - s.x; const dy = prey.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 2.5) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Constant DPS regardless of distance
        const roomDPS = s.roomDPS || 50;
        const dmgThisTick = Math.round(roomDPS * dt);
        if (dmgThisTick > 0) {
          dealDamage(owner || s, prey, dmgThisTick, true);
        }
        // Room does not melee — only DPS aura
      } else if (!prey || !prey.alive) {
        // Target died — Room despawns
        s.alive = false;
        s.hp = 0;
        s.effects.push({ type: 'death', timer: 2 });
      }
    } else if (s.summonType === 'destructive-unicorn') {
      // Extremely Destructive Unicorn: chase nearest enemy, explode on contact for 999 dmg
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 3.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Explode on touch
        if (bestDist < radius * 2 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, 999, true);
          combatLog.push({ text: '💥 Destructive Unicorn exploded on ' + bestTarget.name + '! (999 dmg)', timer: 3, color: '#ff2200' });
          s.alive = false;
          s.hp = 0;
          s.effects.push({ type: 'death', timer: 2 });
          // Clear owner reference
          if (owner) owner.catUnicornId = null;
        }
      }
    } else if (s.summonType === 'queenbee-unicorn') {
      // Queen Bee Unicorn: stays still, M1 block is passive
    } else if (s.summonType === 'seductive-unicorn') {
      // Seductive Unicorn: stays still, invulnerability is passive
    } else if (s.summonType === 'napoleon-cannon') {
      // Napoleon Cannon: stationary, fires cannonballs at closest enemy
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget && s.summonAttackTimer <= 0) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const speed = (s.summonProjectileSpeed || 30) * GAME_TILE / 10;
        const nx = dx / dist; const ny = dy / dist;
        projectiles.push({
          x: s.x, y: s.y,
          vx: nx * speed, vy: ny * speed,
          ownerId: owner ? owner.id : s.id,
          damage: s.summonDamage || 700,
          timer: 999,
          type: 'cannonball',
          color: '#333',
          fromSummon: true,
          napoleonOwner: owner ? owner.id : s.id,
        });
        s.summonAttackTimer = s.summonAttackCD || 5;
        s.effects.push({ type: 'cannon-fire', timer: 0.5 });
        combatLog.push({ text: '💣 Cannon fired!', timer: 2, color: '#555' });
      }
    } else if (s.summonType === 'napoleon-infantry') {
      // Napoleon Infantry: chase nearest enemy, fire ranged bullets
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 2.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        // Move toward target but stop at close range
        const stopRange = 1.5 * GAME_TILE;
        if (dist > stopRange) {
          const newX = s.x + nx * moveSpeed;
          const newY = s.y + ny * moveSpeed;
          if (canMoveTo(newX, s.y, radius)) s.x = newX;
          if (canMoveTo(s.x, newY, radius)) s.y = newY;
        }
        // Fire ranged bullet when in range
        if (s.summonAttackTimer <= 0) {
          const speed = (s.summonProjectileSpeed || 38) * GAME_TILE / 10;
          projectiles.push({
            x: s.x, y: s.y,
            vx: nx * speed, vy: ny * speed,
            ownerId: owner ? owner.id : s.id,
            damage: s.summonDamage || 100,
            timer: s.summonProjectileRange || 0.8,
            type: 'infantry-bullet',
            color: '#2c3e50',
            fromSummon: true,
            napoleonOwner: owner ? owner.id : s.id,
          });
          s.summonAttackTimer = s.summonAttackCD || 1;
          s.effects.push({ type: 'infantry-fire', timer: 0.2 });
        }
      }
    } else if (s.summonType === 'napoleon-wall') {
      // Napoleon Wall: stationary, invincible, 30s duration — half damage for anyone inside (handled in dealDamage)
      if (s.wallTimer !== undefined) {
        s.wallTimer -= dt;
        if (s.wallTimer <= 0) {
          s.alive = false;
          s.hp = 0;
          s.effects.push({ type: 'death', timer: 2 });
          if (owner) owner.napoleonWallId = null;
          continue;
        }
      }
    } else if (s.summonType === 'dnd-orc') {
      // D&D Orc: chase the summoner (its target), melee attack
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      const prey = s.summonTargetId ? gamePlayers.find(t => t.id === s.summonTargetId) : null;
      if (prey && prey.alive) {
        const dx = prey.x - s.x; const dy = prey.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 2.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        if (dist < radius * 2.5 && s.summonAttackTimer <= 0) {
          dealDamage(s, prey, s.summonDamage, true);
          s.summonAttackTimer = s.summonAttackCD || 1.5;
          s.effects.push({ type: 'orc-slash', timer: 0.2, aimNx: nx, aimNy: ny });
        }
      }
    } else if (s.summonType === 'dnd-zombie') {
      // D&D Zombie: chase nearest enemy (not owner), melee attack
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 1.5) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        if (bestDist < radius * 2.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage, true);
          s.summonAttackTimer = s.summonAttackCD || 2.0;
          s.effects.push({ type: 'zombie-slash', timer: 0.2, aimNx: nx, aimNy: ny });
        }
      }
    } else if (s.summonType === 'dnd-sidekick') {
      // D&D Sidekick: chase nearest enemy (not owner), attack based on race
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 3.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        const attackRange = s.dndRace === 'elf' ? 10 * GAME_TILE : radius * 2.5;
        if (bestDist < attackRange && s.summonAttackTimer <= 0) {
          if (s.dndRace === 'elf') {
            const spd = 60 * GAME_TILE / 10;
            projectiles.push({
              x: s.x, y: s.y,
              vx: nx * spd, vy: ny * spd,
              ownerId: owner ? owner.id : s.id,
              damage: s.summonDamage, timer: 999, type: 'dnd-arrow',
            });
            s.summonAttackTimer = s.summonAttackCD || 0.5;
            s.effects.push({ type: 'bow-shot', timer: 0.3 });
          } else {
            const dmg = s.dndRace === 'dwarf' ? 300 + (s.summonDamage - 100) : s.summonDamage;
            dealDamage(owner || s, bestTarget, dmg, true);
            s.summonAttackTimer = s.summonAttackCD || (s.dndRace === 'dwarf' ? 2 : 0.5);
            s.effects.push({ type: s.dndRace === 'dwarf' ? 'axe-swing' : 'sword-slash', timer: 0.3, aimNx: nx, aimNy: ny });
          }
        }
      }
    } else if (s.summonType === 'dragon-ochre') {
      // Yellow Ochre: 3x3 jelly, goes through obstacles but not sea
      const ochreRadius = radius * 3;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 1.5) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveToNoSea(newX, s.y, ochreRadius)) s.x = newX;
        if (canMoveToNoSea(s.x, newY, ochreRadius)) s.y = newY;
      }
      // Area DPS + slow to all enemies within 3x3 area
      const aoeRange = GAME_TILE * 3;
      for (const target of gamePlayers) {
        if (target.id === s.id || target.id === s.summonOwner || !target.alive) continue;
        if (target.isSummon && target.summonOwner === s.summonOwner) continue;
        const tdx = target.x - s.x; const tdy = target.y - s.y;
        const tdist = Math.sqrt(tdx * tdx + tdy * tdy);
        if (tdist < aoeRange) {
          dealDamage(owner || s, target, (s.summonDamage || 50) * dt, true);
          // Slow enemies inside the ochre
          target.buffSlowed = Math.max(target.buffSlowed || 0, 0.5);
        }
      }
    } else if (s.summonType === 'dragon-lich') {
      // Lich: medium speed, short-range lightning attacks, autoheal
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      // Fast autoheal (20% maxHP per second)
      if (s.hp < s.maxHp) {
        s.hp = Math.min(s.maxHp, s.hp + s.maxHp * 0.2 * dt);
      }
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 2.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        // Move toward target — stay in melee range
        if (dist > 1.2 * GAME_TILE) {
          const newX = s.x + nx * moveSpeed;
          const newY = s.y + ny * moveSpeed;
          if (canMoveTo(newX, s.y, radius)) s.x = newX;
          if (canMoveTo(s.x, newY, radius)) s.y = newY;
        }
        // Lightning strike: very short melee range (same as M1)
        if (bestDist < 1.5 * GAME_TILE && s.summonAttackTimer <= 0) {
          const prevHp = bestTarget.hp;
          dealDamage(owner || s, bestTarget, s.summonDamage || 100, true);
          s.summonAttackTimer = s.summonAttackCD || 0.4;
          s.effects.push({ type: 'lich-lightning', timer: 0.2, targetX: bestTarget.x, targetY: bestTarget.y });
          // Track kills — lich dies after 2
          if (bestTarget.hp <= 0 && prevHp > 0 && !bestTarget.isSummon) {
            s.lichKillCount = (s.lichKillCount || 0) + 1;
            if (s.lichKillCount >= 2) {
              s.alive = false; s.hp = 0;
              s.effects.push({ type: 'death', timer: 2 });
              if (owner && owner.dragonSummonId === s.id) owner.dragonSummonId = null;
            }
          }
        }
      }
    } else if (s.summonType === 'ouriel') {
      // Ouriel: follow owner (stay close)
      if (owner && owner.alive) {
        const dx = owner.x - s.x; const dy = owner.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        if (dist > 2 * GAME_TILE) {
          const moveSpeed = (s.summonSpeed || 2.0) * GAME_TILE * dt;
          const nx = dx / dist; const ny = dy / dist;
          const newX = s.x + nx * moveSpeed;
          const newY = s.y + ny * moveSpeed;
          if (canMoveTo(newX, s.y, radius)) s.x = newX;
          if (canMoveTo(s.x, newY, radius)) s.y = newY;
        }
      }
    } else if (s.summonType === 'omori-kel' || s.summonType === 'omori-aubrey' || s.summonType === 'omori-hero') {
      // Omori Party Members: follow owner, attack enemies
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      // Despawn timer for special-spawned party
      if (s.omoriSpecialDespawnTimer !== undefined) {
        s.omoriSpecialDespawnTimer -= dt;
        if (s.omoriSpecialDespawnTimer <= 0) {
          s.alive = false; s.hp = 0; s.effects.push({ type: 'death', timer: 2 });
          continue;
        }
      }
      // Headspace sync from owner
      if (owner && owner.alive) {
        s.omoriHeadspaceActive = owner.omoriHeadspaceActive || false;
      }
      // Choose attack target: if special target exists, use that; otherwise nearest enemy
      let attackTarget = null;
      if (s.summonTargetId) {
        attackTarget = gamePlayers.find(t => t.id === s.summonTargetId && t.alive);
      }
      if (!attackTarget) attackTarget = bestTarget;
      // Follow owner (stay close, like Ouriel)
      if (owner && owner.alive && (!attackTarget || Math.sqrt((owner.x - s.x) ** 2 + (owner.y - s.y) ** 2) > 5 * GAME_TILE)) {
        const dx = owner.x - s.x; const dy = owner.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        if (dist > 2 * GAME_TILE) {
          const moveSpeed = (s.summonSpeed || 3.4) * GAME_TILE * dt;
          const nx = dx / dist; const ny = dy / dist;
          const newX = s.x + nx * moveSpeed;
          const newY = s.y + ny * moveSpeed;
          if (canMoveTo(newX, s.y, radius)) s.x = newX;
          if (canMoveTo(s.x, newY, radius)) s.y = newY;
        }
      } else if (attackTarget) {
        const dx = attackTarget.x - s.x; const dy = attackTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const nx = dx / dist; const ny = dy / dist;
        if (s.summonType === 'omori-kel') {
          // Kel: ranged — chase and stop at 5 tiles, throw basketballs
          const fireRange = 5 * GAME_TILE;
          if (dist > fireRange) {
            const moveSpeed = (s.summonSpeed || 3.4) * GAME_TILE * dt;
            const newX = s.x + nx * moveSpeed;
            const newY = s.y + ny * moveSpeed;
            if (canMoveTo(newX, s.y, radius)) s.x = newX;
            if (canMoveTo(s.x, newY, radius)) s.y = newY;
          }
          if (s.summonAttackTimer <= 0) {
            let dmg = s.summonDamage || 200;
            if (s.omoriHeadspaceActive) dmg = Math.round(dmg * 1.5);
            const speed = (s.summonProjectileSpeed || 30) * GAME_TILE / 10;
            projectiles.push({
              x: s.x, y: s.y,
              vx: nx * speed, vy: ny * speed,
              ownerId: owner ? owner.id : s.id,
              damage: dmg, timer: 10,
              type: 'kel-basketball', color: '#f39c12', fromSummon: true,
            });
            s.summonAttackTimer = s.summonAttackCD || 1;
            s.effects.push({ type: 'kel-throw', timer: 0.3 });
          }
        } else if (s.summonType === 'omori-aubrey') {
          // Aubrey: melee — chase and bat swing
          const meleeRange = 1.5 * GAME_TILE;
          const moveSpeed = (s.summonSpeed || 3.4) * GAME_TILE * dt;
          const newX = s.x + nx * moveSpeed;
          const newY = s.y + ny * moveSpeed;
          if (canMoveTo(newX, s.y, radius)) s.x = newX;
          if (canMoveTo(s.x, newY, radius)) s.y = newY;
          if (dist < meleeRange && s.summonAttackTimer <= 0) {
            let dmg = s.summonDamage || 200;
            if (s.omoriHeadspaceActive) dmg = Math.round(dmg * 1.5);
            dealDamage(owner || s, attackTarget, dmg, true);
            s.summonAttackTimer = s.summonAttackCD || 0.5;
            s.effects.push({ type: 'aubrey-swing', timer: 0.2, aimNx: nx, aimNy: ny });
          }
        } else if (s.summonType === 'omori-hero') {
          // Hero: melee — does NOT chase enemies, stays near owner, only attacks when enemies come close
          const meleeRange = 1.5 * GAME_TILE;
          if (dist < meleeRange && s.summonAttackTimer <= 0) {
            let dmg = s.summonDamage || 100;
            if (s.omoriHeadspaceActive) dmg = Math.round(dmg * 1.5);
            dealDamage(owner || s, attackTarget, dmg, true);
            s.summonAttackTimer = s.summonAttackCD || 0.5;
            s.effects.push({ type: 'hero-slap', timer: 0.2, aimNx: nx, aimNy: ny });
          }
        }
      }
    } else if (s.summonType === 'ouriel-room') {
      // Ouriel→Room: chase its owner (hostile), DPS handled in update loop
      const owner = gamePlayers.find(o => o.id === s.summonOwner && o.alive);
      if (owner) {
        const dx = owner.x - s.x; const dy = owner.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 1.5) * GAME_TILE * dt;
        if (dist > 1.0 * GAME_TILE) {
          const nx = dx / dist; const ny = dy / dist;
          const newX = s.x + nx * moveSpeed;
          const newY = s.y + ny * moveSpeed;
          if (canMoveTo(newX, s.y, radius)) s.x = newX;
          if (canMoveTo(s.x, newY, radius)) s.y = newY;
        }
      }
    } else if (s.summonType === 'complex-room') {
      // Complex Room: chase its target (Dog Tooth), 40 DPS aura only
      const huntTarget = gamePlayers.find(p => p.id === s.summonTargetId && p.alive);
      if (huntTarget) {
        const dx = huntTarget.x - s.x; const dy = huntTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 1.8) * GAME_TILE * dt;
        if (dist > 0.8 * GAME_TILE) {
          const nx = dx / dist; const ny = dy / dist;
          const newX = s.x + nx * moveSpeed;
          const newY = s.y + ny * moveSpeed;
          if (canMoveTo(newX, s.y, radius)) s.x = newX;
          if (canMoveTo(s.x, newY, radius)) s.y = newY;
        }
      }
    } else if (s.summonType === 'unstable-infantry') {
      // Unstable Infantry: chase nearest enemy, melee hit teleports target to their spawn
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 2.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Melee attack: deal damage and teleport target to their spawn
        if (dist < GAME_TILE * 1.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage, true);
          // Teleport target to their spawn position
          if (bestTarget.spawnRow != null && bestTarget.spawnCol != null) {
            bestTarget.x = (bestTarget.spawnCol + 0.5) * GAME_TILE;
            bestTarget.y = (bestTarget.spawnRow + 0.5) * GAME_TILE;
          } else if (bestTarget.spawn) {
            bestTarget.x = (bestTarget.spawn.c + 0.5) * GAME_TILE;
            bestTarget.y = (bestTarget.spawn.r + 0.5) * GAME_TILE;
          }
          bestTarget.effects.push({ type: 'unstable-teleport', timer: 1.0 });
          s.summonAttackTimer = s.summonAttackCD || 2.5;
          s.effects.push({ type: 'unstable-infantry-hit', timer: 0.3 });
          combatLog.push({ text: '⚡ Infantry teleported ' + bestTarget.name + ' to spawn!', timer: 3, color: '#ff00ff' });
        }
      }
    } else if (s.summonType === 'filbus-dino') {
      // Filbus Dinosaur: slow chase, 150 damage + 5s bleed, 3s CD
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 1.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Melee attack
        if (dist < GAME_TILE * 1.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage || 150, true);
          // Apply bleed
          if (bestTarget.alive) {
            if (!bestTarget.bleedTimers) bestTarget.bleedTimers = [];
            bestTarget.bleedTimers.push({ dps: (s.summonBleedDps || 50), remaining: (s.summonBleedDur || 5) });
            bestTarget.effects.push({ type: 'power-bleed', timer: (s.summonBleedDur || 5) });
          }
          s.summonAttackTimer = s.summonAttackCD || 3.0;
          s.effects.push({ type: 'dino-bite', timer: 0.4 });
        }
      }
    } else if (s.summonType === 'slasher') {
      // 1X Slasher: fast chase, 150 damage, 0.5s CD
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 4.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        // Attack
        if (dist < GAME_TILE * 1.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage || 150, true);
          s.summonAttackTimer = s.summonAttackCD || 0.5;
          s.effects.push({ type: 'slasher-slash', timer: 0.3 });
        }
      }
    } else if (s.summonType === 'cricket-trophy') {
      // Cricket Trophy: stationary, doesn't attack or move. Just exists until destroyed.
      // No movement or attacks needed.
    } else if (s.summonType === 'guest666') {
      // Guest666: fast melee beast with jump ability. Lacerates (3s stun + 400dmg + bleed)
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (s.summonJumpTimer > 0) s.summonJumpTimer -= dt;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 3.5) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        // Jump to target if far away and jump ready (can skip obstacles)
        if (dist > GAME_TILE * 4 && s.summonJumpTimer <= 0) {
          const jumpDist = Math.min(dist - GAME_TILE, GAME_TILE * 6);
          s.x = s.x + nx * jumpDist;
          s.y = s.y + ny * jumpDist;
          s.summonJumpTimer = s.summonJumpCD || 8.0;
          s.effects.push({ type: 'guest666-jump', timer: 0.6 });
        } else {
          const newX = s.x + nx * moveSpeed;
          const newY = s.y + ny * moveSpeed;
          if (canMoveTo(newX, s.y, radius)) s.x = newX;
          if (canMoveTo(s.x, newY, radius)) s.y = newY;
        }
        // Melee attack: lacerate — 3s stun + 400dmg + bleed
        if (dist < GAME_TILE * 2 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage || 400, true);
          if (bestTarget.alive) {
            bestTarget.stunned = s.summonStunDur || 3;
            bestTarget.effects.push({ type: 'stun', timer: s.summonStunDur || 3 });
            if (!bestTarget.bleedTimers) bestTarget.bleedTimers = [];
            bestTarget.bleedTimers.push({ dps: (s.summonBleedDps || 100), remaining: (s.summonBleedDur || 3) });
            bestTarget.effects.push({ type: 'power-bleed', timer: (s.summonBleedDur || 3) });
          }
          s.summonAttackTimer = s.summonAttackCD || 5.0;
          s.effects.push({ type: 'guest666-lacerate', timer: 0.5 });
        }
      }
    } else if (s.summonType === 'imploding-kitten') {
      // Imploding Kitten: 3s kitten phase, then stationary black hole with 3-tier suction
      // ── Kitten phase (first 3 seconds) ──
      if (s.kittenTimer > 0) {
        s.kittenTimer -= dt;
        if (s.kittenTimer <= 0) {
          // Transition to black hole
          s.kittenTimer = 0;
          s.blackHoleActive = true;
          s.effects.push({ type: 'kitten-implode', timer: 1.5 });
          combatLog.push({ text: '🌀 Kitten imploded into a black hole! 6s until detonation!', timer: 5, color: '#4a0080' });
        }
      }
      // ── Black hole phase ──
      if (s.blackHoleActive && s.blackHoleTimer > 0) {
        s.blackHoleTimer -= dt;
        const outerR = s.blackHoleRadius || (8 * GAME_TILE);
        const midR = s.blackHoleMidRadius || (6 * GAME_TILE);
        const innerR = s.blackHoleInnerRadius || (4 * GAME_TILE);
        const coreR = GAME_TILE * 0.5; // center trap radius
        // Pull all non-immune players toward center
        for (const target of gamePlayers) {
          if (!target.alive || target.isSummon) continue;
          if (target.id === s.summonOwner) continue;
          if (gameMode === 'teams' && owner && owner.team && target.team === owner.team) continue;
          const tdx = s.x - target.x; const tdy = s.y - target.y;
          const tdist = Math.sqrt(tdx * tdx + tdy * tdy) || 1;
          if (tdist > outerR) continue;
          const tnx = tdx / tdist; const tny = tdy / tdist;

          // Center trap: if within core, spin in place
          if (tdist <= coreR) {
            target.bhTrapped = true;
            target.bhTrapX = s.x; target.bhTrapY = s.y;
            // Spin around center
            const angle = Math.atan2(target.y - s.y, target.x - s.x);
            const spinSpeed = 4.0 * dt;
            const newAngle = angle + spinSpeed;
            const orbitR = coreR * 0.3;
            target.x = s.x + Math.cos(newAngle) * orbitR;
            target.y = s.y + Math.sin(newAngle) * orbitR;
            continue;
          }

          // Tag as being in black hole zone for movement modifier
          target.bhSourceX = s.x; target.bhSourceY = s.y;

          if (tdist <= innerR) {
            // 4x4 zone: inescapable — pull faster than any movement speed
            const pullStrength = 8.0 * GAME_TILE * dt;
            const nx = target.x + tnx * pullStrength;
            const ny = target.y + tny * pullStrength;
            if (canMoveTo(nx, target.y, GAME_TILE * PLAYER_RADIUS_RATIO)) target.x = nx;
            if (canMoveTo(target.x, ny, GAME_TILE * PLAYER_RADIUS_RATIO)) target.y = ny;
            target.bhZone = 'inner'; target.bhZoneTimer = 0.15;
          } else if (tdist <= midR) {
            // 6x6 zone: pull matches speed — away=stationary, toward/side = drawn in
            const pullStrength = 4.0 * GAME_TILE * dt;
            const nx = target.x + tnx * pullStrength;
            const ny = target.y + tny * pullStrength;
            if (canMoveTo(nx, target.y, GAME_TILE * PLAYER_RADIUS_RATIO)) target.x = nx;
            if (canMoveTo(target.x, ny, GAME_TILE * PLAYER_RADIUS_RATIO)) target.y = ny;
            target.bhZone = 'mid'; target.bhZoneTimer = 0.15;
          } else {
            // 8x8 zone: moderate pull + 60% movement slow
            const pullStrength = 1.5 * GAME_TILE * dt;
            const nx = target.x + tnx * pullStrength;
            const ny = target.y + tny * pullStrength;
            if (canMoveTo(nx, target.y, GAME_TILE * PLAYER_RADIUS_RATIO)) target.x = nx;
            if (canMoveTo(target.x, ny, GAME_TILE * PLAYER_RADIUS_RATIO)) target.y = ny;
            target.bhZone = 'outer'; target.bhZoneTimer = 0.15;
          }
        }
        // Detonation at 0
        if (s.blackHoleTimer <= 0) {
          for (const target of gamePlayers) {
            if (!target.alive) continue;
            if (target.id === s.summonOwner) continue;
            if (target.isSummon && (target.summonType === 'exploding-kitten' || target.summonType === 'imploding-kitten') && target.summonOwner === s.summonOwner) continue;
            if (gameMode === 'teams' && owner && owner.team && !target.isSummon && target.team === owner.team) continue;
            const tdx = target.x - s.x; const tdy = target.y - s.y;
            const tdist = Math.sqrt(tdx * tdx + tdy * tdy);
            const detonateR = 2 * GAME_TILE; // only damages players in the 2x2 black center
            if (tdist <= detonateR) {
              dealDamage(owner || s, target, s.summonDamage || 900, true);
              target.effects.push({ type: 'blackhole-detonate', timer: 1.5 });
            }
            // Release trapped players
            if (target.bhTrapped) { target.bhTrapped = false; target.bhTrapX = null; target.bhTrapY = null; }
          }
          s.blackHoleActive = false;
          s.alive = false; s.hp = 0;
          s.effects.push({ type: 'death', timer: 2 });
          combatLog.push({ text: '🌀 Black hole detonated! 900 damage!', timer: 4, color: '#4a0080' });
          if (owner) owner.catImplodingKittenId = null;
        }
      }
    } else if (s.summonType === 'napoleon-power-cannon') {
      // Same AI as regular cannon
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget && s.summonAttackTimer <= 0) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const speed = (s.summonProjectileSpeed || 30) * GAME_TILE / 10;
        const nx = dx / dist; const ny = dy / dist;
        projectiles.push({
          x: s.x, y: s.y, vx: nx * speed, vy: ny * speed,
          ownerId: owner ? owner.id : s.id,
          damage: s.summonDamage || 700, timer: 999,
          type: 'cannonball', color: '#333', fromSummon: true,
          napoleonOwner: owner ? owner.id : s.id,
        });
        s.summonAttackTimer = s.summonAttackCD || 5;
        s.effects.push({ type: 'cannon-fire', timer: 0.5 });
      }
    } else if (s.summonType === 'napoleon-cavalry') {
      // Cavalry: fast melee chase, 400dmg, 2x dmg taken via napoleonCavalry flag
      if (s.summonAttackTimer > 0) s.summonAttackTimer -= dt;
      if (bestTarget) {
        const dx = bestTarget.x - s.x; const dy = bestTarget.y - s.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const moveSpeed = (s.summonSpeed || 4.0) * GAME_TILE * dt;
        const nx = dx / dist; const ny = dy / dist;
        const newX = s.x + nx * moveSpeed;
        const newY = s.y + ny * moveSpeed;
        if (canMoveTo(newX, s.y, radius)) s.x = newX;
        if (canMoveTo(s.x, newY, radius)) s.y = newY;
        if (dist < GAME_TILE * 1.5 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, bestTarget, s.summonDamage || 400, true);
          s.summonAttackTimer = s.summonAttackCD || 2.0;
          s.effects.push({ type: 'cavalry-charge', timer: 0.4 });
        }
      }
    }

    // Clean up summon if owner died or left the game entirely
    // Complex Room has owner='none' — skip cleanup for it
    if (s.summonType !== 'complex-room' && (!owner || !owner.alive)) {
      s.alive = false;
      s.hp = 0;
      s.effects.push({ type: 'death', timer: 2 });
      // Clear owner's reference to this summon (only if owner still exists)
      if (owner) {
        if (s.summonType === 'coolkidd' && owner.coolkiddId === s.id) owner.coolkiddId = null;
        if (s.summonType === 'bowler' && owner.bowlerId === s.id) owner.bowlerId = null;
        if (s.summonType === 'crab' && owner.crabIds) {
          const cidx = owner.crabIds.indexOf(s.id);
          if (cidx >= 0) owner.crabIds.splice(cidx, 1);
        }
        if (s.summonType === 'johndoe' && owner.johnDoeId === s.id) owner.johnDoeId = null;
        if ((s.summonType === 'destructive-unicorn' || s.summonType === 'queenbee-unicorn' || s.summonType === 'seductive-unicorn') && owner.catUnicornId === s.id) owner.catUnicornId = null;
        if (s.summonType === 'napoleon-cannon' && owner.napoleonCannonId === s.id) owner.napoleonCannonId = null;
        if (s.summonType === 'napoleon-wall' && owner.napoleonWallId === s.id) owner.napoleonWallId = null;
        if (s.summonType === 'napoleon-infantry' && owner.napoleonInfantryIds) {
          const idx = owner.napoleonInfantryIds.indexOf(s.id);
          if (idx >= 0) owner.napoleonInfantryIds.splice(idx, 1);
        }
        if (s.summonType === 'dnd-orc' && owner.dndOrcIds) {
          const idx = owner.dndOrcIds.indexOf(s.id);
          if (idx >= 0) owner.dndOrcIds.splice(idx, 1);
        }
        if (s.summonType === 'dnd-sidekick' && owner.dndSidekickId === s.id) owner.dndSidekickId = null;
        if ((s.summonType === 'dragon-ochre' || s.summonType === 'dragon-lich') && owner.dragonSummonId === s.id) owner.dragonSummonId = null;
        if ((s.summonType === 'ouriel' || s.summonType === 'ouriel-room') && owner.dogtoothOurielId === s.id) {
          owner.dogtoothOurielId = null;
          // Ouriel died (not recalled) — set 30s CD and reset stored HP
          owner.cdE = 30;
          owner.dogtoothOurielHp = null;
          owner.dogtoothOurielHitsLeft = null;
        }
        if (s.summonType === 'unstable-infantry' && owner.unstableInfantryIds) {
          const idx = owner.unstableInfantryIds.indexOf(s.id);
          if (idx >= 0) owner.unstableInfantryIds.splice(idx, 1);
        }
        if (s.summonType === 'filbus-dino' && owner.filbusDinoIds) {
          const idx = owner.filbusDinoIds.indexOf(s.id);
          if (idx >= 0) owner.filbusDinoIds.splice(idx, 1);
        }
        if (s.summonType === 'slasher' && owner.onexSlasherId === s.id) owner.onexSlasherId = null;
        if (s.summonType === 'cricket-trophy') {
          if (owner.cricketTrophyId === s.id) {
            owner.cricketTrophyId = null;
            owner.cricketTrophyShield = false;
          }
        }
        if (s.summonType === 'guest666' && owner.noliGuest666Id === s.id) owner.noliGuest666Id = null;
        if (s.summonType === 'imploding-kitten' && owner.catImplodingKittenId === s.id) owner.catImplodingKittenId = null;
        if (s.summonType === 'napoleon-power-cannon' && owner.napoleonPowerCannonIds) {
          const idx = owner.napoleonPowerCannonIds.indexOf(s.id);
          if (idx >= 0) owner.napoleonPowerCannonIds.splice(idx, 1);
        }
        if (s.summonType === 'napoleon-cavalry' && owner.napoleonCavalryIds) {
          const idx = owner.napoleonCavalryIds.indexOf(s.id);
          if (idx >= 0) owner.napoleonCavalryIds.splice(idx, 1);
        }
        if ((s.summonType === 'dragon-ochre' || s.summonType === 'dragon-lich') && owner.dragonSummonId2 === s.id) owner.dragonSummonId2 = null;
        if ((s.summonType === 'omori-kel' || s.summonType === 'omori-aubrey' || s.summonType === 'omori-hero') && owner.omoriPartyIds) {
          const idx = owner.omoriPartyIds.indexOf(s.id);
          if (idx >= 0) owner.omoriPartyIds.splice(idx, 1);
        }
        if ((s.summonType === 'omori-kel' || s.summonType === 'omori-aubrey' || s.summonType === 'omori-hero') && owner.omoriSpecialPartyIds) {
          const idx = owner.omoriSpecialPartyIds.indexOf(s.id);
          if (idx >= 0) owner.omoriSpecialPartyIds.splice(idx, 1);
        }
      }
    }
  }
}

// ═══════════════════════════════════════════════════════════════
// CPU AI
// ═══════════════════════════════════════════════════════════════

// Difficulty tuning
const AI_PARAMS = {
  easy:   { thinkDelay: 0.9, aimError: 0.25, abilityDelay: 2.0, aggroRange: 9,  retreatHp: 0.15, reactionTime: 0.6 },
  medium: { thinkDelay: 0.45, aimError: 0.12, abilityDelay: 1.0, aggroRange: 12, retreatHp: 0.25, reactionTime: 0.30 },
  hard:   { thinkDelay: 0.14, aimError: 0.03, abilityDelay: 0.4, aggroRange: 18, retreatHp: 0.38, reactionTime: 0.08 },
  expert: { thinkDelay: 0.12, aimError: 0.02, abilityDelay: 0.35, aggroRange: 20, retreatHp: 0.40, reactionTime: 0.06 },
};

function updateCPUs(dt) {
  for (const cpu of gamePlayers) {
    if (!cpu.isCPU || !cpu.alive || cpu.stunned > 0) continue;
    // Skip summons handled by updateSummons (noli-clone and illusion copies use full CPU AI)
    if (cpu.isSummon && cpu.summonType !== 'noli-clone'
        && cpu.summonType !== 'illusion-copy' && cpu.summonType !== 'illusion-special-copy') continue;
    const ai = cpu.aiState;
    if (!ai) continue; // safety: skip entities without AI state
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
      // Hard/expert CPUs can attack while retreating (kiting)
      if (!ai.retreating || cpu.difficulty === 'hard' || cpu.difficulty === 'expert') {
        cpuAttack(cpu, params);
        ai.abilityTimer = params.abilityDelay * (0.7 + Math.random() * 0.6);
      }
    }
  }
}

function cpuChooseTarget(cpu, params) {
  const ai = cpu.aiState;
  const aggroRange = params.aggroRange * GAME_TILE;
  const isExpert = cpu.difficulty === 'expert';

  // Target stickiness: prefer staying on current target unless a much better one exists
  const stickyBias = (cpu.difficulty === 'expert' || cpu.difficulty === 'hard') ? 1.5 * GAME_TILE : 0;

  // Find best enemy within aggro range
  let bestTarget = null;
  let bestDist = Infinity;
  let bestScore = Infinity;
  for (const p of gamePlayers) {
    if (p.id === cpu.id || !p.alive) continue;
    if (p.isSummon && p.summonOwner === cpu.id) continue; // skip own summons
    if (p.id === cpu.summonOwner) continue; // summons don't attack their owner
    // Skip players in backrooms or Complex (isolated dimensions)
    if (p.inBackrooms || p.dogtoothInComplex) continue;
    // Skip Illusion players that are invisible (E or SPACE)
    if ((p.illusionInvisTimer > 0 || p.illusionSpecialInvis || p.illusionBushInvisTimer > 0) && !p.isSummon) continue;
    // Skip Moderator with Firewall active
    if (p.modFirewallTimer > 0) continue;
    // Check if CPU can see the player (not hidden in grass)
    if (cpuIsHidden(p, cpu)) continue;
    const dx = p.x - cpu.x; const dy = p.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (isExpert || cpu.difficulty === 'hard') {
      // Smart: score = weighted combo of distance and HP fraction (prefer low-HP & close)
      const hpFraction = p.hp / p.maxHp;
      let score = dist + hpFraction * 5 * GAME_TILE;
      // Stickiness: bias toward current target so we don't constantly switch
      if (ai.attackTarget && ai.attackTarget.id === p.id) score -= stickyBias;
      // Fighter-specific target priority
      const fid = cpu.fighter.id;
      if (fid === 'deer' && p.isSummon) {
        // Deer prioritizes summons (Spear kills them instantly)
        score -= 4 * GAME_TILE;
      } else if (fid === 'poker' && hpFraction < 0.4) {
        // Poker wants to finish low-HP enemies (execute with Royal Flush)
        score -= 6 * GAME_TILE;
      } else if (fid === 'noli' && dist > 5 * GAME_TILE) {
        // Noli prefers distant targets to dash toward
        score -= 2 * GAME_TILE;
      } else if (fid === 'illusion' && p.isSummon) {
        // Illusion avoids summons, prefers real players
        score += 5 * GAME_TILE;
      } else if (fid === 'dnd' && p.isSummon && p.summonType === 'dnd-orc' && p.summonOwner === cpu.id) {
        // D&D: heavily prioritize own orcs for GP farming
        score -= 10 * GAME_TILE;
      }
      // Smart Ouriel targeting: prioritize Ouriels when close or being attacked by Dog Tooth
      if (p.isSummon && (p.summonType === 'ouriel' || p.summonType === 'ouriel-room')) {
        const ourielCloseRange = 5 * GAME_TILE;
        const owner = gamePlayers.find(o => o.id === p.summonOwner);
        const ownerIsDT = owner && owner.fighter && owner.fighter.id === 'dogtooth';
        const beingAttackedByDT = ai.attackTarget && ownerIsDT && ai.attackTarget.id === owner.id;
        if (dist < ourielCloseRange || beingAttackedByDT) {
          score -= 8 * GAME_TILE; // heavy bias toward targeting Ouriels
        }
      }
      if (score < bestScore) {
        bestScore = score;
        bestDist = dist;
        bestTarget = p;
      }
    } else if (cpu.difficulty === 'medium') {
      // Medium: mostly nearest but also prioritize Ouriels when close and own orcs
      let score = dist;
      if (p.isSummon && (p.summonType === 'ouriel' || p.summonType === 'ouriel-room')) {
        const ourielCloseRange = 4 * GAME_TILE;
        if (dist < ourielCloseRange) {
          score -= 5 * GAME_TILE; // bias toward nearby Ouriels
        }
      }
      // D&D medium: prioritize own orcs for GP
      if (cpu.fighter.id === 'dnd' && p.isSummon && p.summonType === 'dnd-orc' && p.summonOwner === cpu.id) {
        score -= 6 * GAME_TILE;
      }
      if (score < bestDist) {
        bestDist = score;
        bestTarget = p;
      }
    } else {
      if (dist < bestDist) {
        bestDist = dist;
        bestTarget = p;
      }
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
  // Unstable: use random speed
  if (cpu.unstableOriginalFighter && cpu.unstableRandomSpeed) speed = cpu.unstableRandomSpeed;
  // Unstable Eye: speed boost (as fast as Deer)
  if (cpu.unstableEyeTimer > 0) speed *= 3.0;
  // Napoleon Cavalry: 2.5x speed boost
  if (cpu.napoleonCavalry) speed *= 2.5;
  // Napoleon Charisma trait: allies near Napoleon get 50% speed buff
  if (gameMode === 'teams' && cpu.fighter && cpu.fighter.id !== 'napoleon') {
    for (const p of gamePlayers) {
      if (!p.alive || p.isSummon || p.id === cpu.id) continue;
      if (p.fighter && p.fighter.id === 'napoleon' && p.traitActive && p.team === cpu.team) {
        const ndx = p.x - cpu.x, ndy = p.y - cpu.y;
        if (ndx * ndx + ndy * ndy < (GAME_TILE * 6) * (GAME_TILE * 6)) { speed *= 1.5; break; }
      }
    }
  }
  // Gear Up: speed penalty
  if (cpu.gearUpTimer > 0) speed *= (cpu.fighter.abilities[2].speedPenalty || 0.6);
  // D&D Human: 1.2x speed
  if (cpu.dndRace === 'human') speed *= 1.2;
  // Dragon: roar speed buff, fly speed, beam immobilization, breath slow
  if (cpu.dragonRoarActive) speed *= 1.3;
  if (cpu.dragonFlying) speed *= 2.5; // same as Napoleon cavalry
  if (cpu.dragonBreathActive) speed *= 0.5;
  if (cpu.pyroFlameActive) speed *= 0.5;
  // Heavy Rope CPU: slower while swinging, faster during ROPE POWER
  if (cpu.ropeSwingActive) speed *= 0.6;
  if (cpu.ropePowerTimer > 0) speed *= 1.8;
  if (cpu.dragonBeamCharging || cpu.dragonBeamRecovery > 0) speed = 0;
  // Buff slow debuff
  if (cpu.buffSlowed > 0) speed *= 0.6;
  // Deer Fear: speed boost when retreating
  if (cpu.deerFearTimer > 0 && ai.retreating) speed *= 1.5;
  // Deer: slower while building robot
  if (cpu.deerBuildSlowTimer > 0 && cpu.fighter && cpu.fighter.id === 'deer') speed *= 0.6;
  // Moderator Fear: speed boost when running away from fear source
  if (cpu.modFearTimer > 0) {
    const src = gamePlayers.find(p => p.id === cpu.modFearSourceId);
    if (src && src.alive) {
      const fdx = cpu.x - src.x, fdy = cpu.y - src.y;
      const fd = Math.sqrt(fdx * fdx + fdy * fdy) || 1;
      // Force retreat from fear source
      if (!ai.retreating) {
        ai.retreating = true;
        ai.attackTarget = src;
      }
      speed *= 2.0;
    }
  }
  // Fighter Aura trait: moving toward a Fighter with trait slows CPU 0.8x
  if (ai.attackTarget && ai.attackTarget.alive && !ai.retreating) {
    for (const p of gamePlayers) {
      if (!p.alive || p.isSummon || p.id === cpu.id) continue;
      if (!p.traitActive || !p.fighter || p.fighter.id !== 'fighter') continue;
      if (gameMode === 'teams' && cpu.team && p.team === cpu.team) continue;
      const toFx = p.x - cpu.x; const toFy = p.y - cpu.y;
      const toFdist = Math.sqrt(toFx * toFx + toFy * toFy) || 1;
      if (toFdist < GAME_TILE * 8) { speed *= 0.8; break; }
    }
  }

  // Retreat if low HP — fighter-specific retreat thresholds
  const fid = cpu.fighter.id;
  let retreatThreshold = params.retreatHp;
  // Aggressive fighters retreat later; defensive fighters retreat earlier
  if (fid === 'dogtooth' || fid === 'cricket') retreatThreshold *= 0.7; // stay in longer
  else if (fid === 'deer' || fid === 'poker' || fid === 'illusion') retreatThreshold *= 1.3; // retreat sooner
  else if (fid === 'noli' && cpu.noliObservantUses < 3) retreatThreshold *= 0.8; // can escape with TP
  ai.retreating = cpu.hp / cpu.maxHp < retreatThreshold;

  let goalX, goalY;

  if (ai.attackTarget && ai.attackTarget.alive) {
    const target = ai.attackTarget;
    const dx = target.x - cpu.x; const dy = target.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);

    if (ai.retreating) {
      // Run away from target
      if ((cpu.difficulty === 'expert' || cpu.difficulty === 'hard') && appleTree && appleTree.apples.length > 0) {
        // Smart retreat: run toward nearest apple for healing
        let closestApple = null, closestAppleDist = Infinity;
        for (const a of appleTree.apples) {
          const ax = (a.col + 0.5) * GAME_TILE;
          const ay = (a.row + 0.5) * GAME_TILE;
          const d = Math.sqrt((ax - cpu.x) ** 2 + (ay - cpu.y) ** 2);
          if (d < closestAppleDist) { closestAppleDist = d; closestApple = a; }
        }
        if (closestApple) {
          goalX = (closestApple.col + 0.5) * GAME_TILE;
          goalY = (closestApple.row + 0.5) * GAME_TILE;
        } else {
          goalX = cpu.x - dx / (dist || 1) * GAME_TILE * 3;
          goalY = cpu.y - dy / (dist || 1) * GAME_TILE * 3;
        }
      } else {
        goalX = cpu.x - dx / (dist || 1) * GAME_TILE * 3;
        goalY = cpu.y - dy / (dist || 1) * GAME_TILE * 3;
      }
    } else {
      // ── Fighter-specific ideal range & positioning ──
      const fid = cpu.fighter.id;
      const isHardPlus = cpu.difficulty === 'hard' || cpu.difficulty === 'expert';
      const isMedPlus = isHardPlus || cpu.difficulty === 'medium';
      let idealRange;
      let shouldCircle = false;  // circle-strafe around target
      let shouldAmbush = false;  // try to approach through grass

      if (fid === 'poker') {
        // Poker wants max distance to chip safely; harder CPUs keep better spacing
        idealRange = (isHardPlus ? 5.5 : isMedPlus ? 4.5 : 3.5) * GAME_TILE;
      } else if (fid === 'filbus') {
        // Filbus needs to be in melee range for chair; crafts at distance
        idealRange = (cpu.chairCharges > 0 || cpu.isCraftingChair) ? 1.5 * GAME_TILE : (isMedPlus ? 5 : 3) * GAME_TILE;
      } else if (fid === 'onexonexonex') {
        // 1X prefers mid range to land Entanglement, close for slash
        idealRange = (cpu.cdE <= 0 && isMedPlus) ? 4 * GAME_TILE : 1.5 * GAME_TILE;
      } else if (fid === 'cricket') {
        // Cricket is short range melee; Gear Up means go in
        idealRange = (cpu.gearUpTimer > 0 ? 0.8 : 1.0) * GAME_TILE;
      } else if (fid === 'deer') {
        // Deer plays far away, relying on robot; close only for Spear
        idealRange = (cpu.deerRobotId && gamePlayers.find(p => p.id === cpu.deerRobotId && p.alive))
          ? (isHardPlus ? 7 : 4) * GAME_TILE : 1.0 * GAME_TILE;
      } else if (fid === 'noli') {
        // Noli dashes in; circle-strafe between dashes
        idealRange = (cpu.cdE <= 0 && isMedPlus) ? 5 * GAME_TILE : 1.5 * GAME_TILE;
        shouldCircle = isHardPlus;
      } else if (fid === 'explodingcat') {
        // Cat needs to be very close for Scratch; faster so can afford to zigzag
        idealRange = 0.8 * GAME_TILE;
        shouldCircle = isMedPlus;
      } else if (fid === 'napoleon') {
        // Napoleon on horse charges in; otherwise sword range
        idealRange = cpu.napoleonCavalry ? 0.8 * GAME_TILE : 1.5 * GAME_TILE;
      } else if (fid === 'moderator') {
        // Moderator plays safe, uses TP to bring enemies to him
        idealRange = (isHardPlus ? 4 : 2) * GAME_TILE;
      } else if (fid === 'dnd') {
        // D&D depends on race — also move toward own orcs to kill them for GP
        const race = cpu.dndRace || 'human';
        const hasLiveOrcs = cpu.dndOrcIds && cpu.dndOrcIds.length > 0 && gamePlayers.some(p => cpu.dndOrcIds.includes(p.id) && p.alive);
        if (hasLiveOrcs && (isHardPlus || (isMedPlus && cpu.dndOrcIds.length >= 2))) {
          // Prioritize killing orcs: move to melee range of nearest orc
          idealRange = 1.2 * GAME_TILE;
        } else {
          idealRange = race === 'elf' ? (isHardPlus ? 6 : 4) * GAME_TILE
                     : race === 'dwarf' ? 1.2 * GAME_TILE
                     : 1.5 * GAME_TILE;
        }
      } else if (fid === 'dragon') {
        // Dragon: breath range for M1, beam at mid range
        idealRange = (cpu.dragonBreathActive ? 3 : 4) * GAME_TILE;
      } else if (fid === 'illusion') {
        // Illusion sneaks up close or hides; when invisible, rush in
        shouldAmbush = isMedPlus;
        idealRange = (cpu.illusionInvisTimer > 0) ? 0.8 * GAME_TILE : (isHardPlus ? 3 : 1.5) * GAME_TILE;
      } else if (fid === 'dogtooth') {
        // Dogtooth chases aggressively; Smile mode = full rush
        idealRange = (cpu.dogtoothSmileTimer > 0) ? 0.5 * GAME_TILE : 1.5 * GAME_TILE;
      } else if (fid === 'heavyrope') {
        // Heavy Rope: stay in rope range (2.5 tiles), closer if grip active
        idealRange = (cpu.ropeGripActive ? 1.2 : 2.0) * GAME_TILE;
      } else if (fid === 'omori') {
        idealRange = 1.5 * GAME_TILE;
      } else {
        // Fighter: basic melee
        idealRange = 1.2 * GAME_TILE;
      }

      if (dist > idealRange + GAME_TILE) {
        // Move toward target
        goalX = target.x;
        goalY = target.y;
        // Ambush: prefer grass tiles on the approach
        if (shouldAmbush && !cpu.illusionInvisTimer) {
          for (let angle = -1; angle <= 1; angle += 2) {
            const testX = cpu.x + (dx / dist * Math.cos(angle * 0.4) - dy / dist * Math.sin(angle * 0.4)) * GAME_TILE * 3;
            const testY = cpu.y + (dx / dist * Math.sin(angle * 0.4) + dy / dist * Math.cos(angle * 0.4)) * GAME_TILE * 3;
            const tc = Math.floor(testX / GAME_TILE), tr = Math.floor(testY / GAME_TILE);
            if (tr >= 0 && tr < gameMap.rows && tc >= 0 && tc < gameMap.cols && gameMap.tiles[tr][tc] === TILE.GRASS) {
              goalX = testX; goalY = testY; break;
            }
          }
        }
      } else if (dist < idealRange - GAME_TILE * 0.5) {
        // Too close, back off slightly
        goalX = cpu.x - dx / (dist || 1) * GAME_TILE;
        goalY = cpu.y - dy / (dist || 1) * GAME_TILE;
      } else {
        // At ideal range — strafe or circle
        const perpX = -dy / (dist || 1);
        const perpY = dx / (dist || 1);
        if (shouldCircle) {
          // Circle-strafe: maintain distance while orbiting
          const orbitX = perpX * ai.strafeDir;
          const orbitY = perpY * ai.strafeDir;
          goalX = cpu.x + orbitX * GAME_TILE * 2;
          goalY = cpu.y + orbitY * GAME_TILE * 2;
        } else {
          goalX = cpu.x + perpX * ai.strafeDir * GAME_TILE * 2;
          goalY = cpu.y + perpY * ai.strafeDir * GAME_TILE * 2;
        }
        // Switch strafe direction more frequently (harder CPUs strafe more)
        const strafeFlipChance = cpu.difficulty === 'expert' ? 0.06 : cpu.difficulty === 'hard' ? 0.04 : cpu.difficulty === 'medium' ? 0.025 : 0.01;
        if (Math.random() < strafeFlipChance) ai.strafeDir *= -1;
      }
    }
    // Projectile dodge: sidestep incoming projectiles (medium/hard only)
    if (cpu.difficulty !== 'easy') {
      for (const proj of projectiles) {
        if (proj.ownerId === cpu.id) continue;
        const pdx = proj.x - cpu.x, pdy = proj.y - cpu.y;
        const pDist = Math.sqrt(pdx * pdx + pdy * pdy);
        if (pDist > GAME_TILE * 3) continue;
        // Check if projectile is heading toward us
        const projSpeed = Math.sqrt(proj.vx * proj.vx + proj.vy * proj.vy) || 1;
        const dot = (proj.vx * pdx + proj.vy * pdy) / (projSpeed * pDist);
        if (dot < -0.5) {
          // Projectile is heading at us — dodge perpendicular
          const dodgeX = -proj.vy / projSpeed;
          const dodgeY = proj.vx / projSpeed;
          goalX = cpu.x + dodgeX * ai.strafeDir * GAME_TILE * 2;
          goalY = cpu.y + dodgeY * ai.strafeDir * GAME_TILE * 2;
          break;
        }
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
    const isSmartCPU = cpu.difficulty === 'expert' || cpu.difficulty === 'hard';
    const centerX = (gameMap.cols / 2) * GAME_TILE;
    const centerY = (gameMap.rows / 2) * GAME_TILE;

    // Smart CPUs: seek apples or apple tree area when idle
    if (isSmartCPU && appleTree) {
      const treeX = (appleTree.col + 1) * GAME_TILE;
      const treeY = (appleTree.row + 1) * GAME_TILE;
      // Go pick up nearby apples if we need healing
      if (appleTree.apples.length > 0 && cpu.hp < cpu.maxHp * 0.85) {
        let closestApple = null, closestAppleDist = Infinity;
        for (const a of appleTree.apples) {
          const ax = (a.col + 0.5) * GAME_TILE;
          const ay = (a.row + 0.5) * GAME_TILE;
          const d = Math.sqrt((ax - cpu.x) ** 2 + (ay - cpu.y) ** 2);
          if (d < closestAppleDist) { closestAppleDist = d; closestApple = a; }
        }
        if (closestApple) {
          goalX = (closestApple.col + 0.5) * GAME_TILE;
          goalY = (closestApple.row + 0.5) * GAME_TILE;
        }
      } else {
        // Wander near the apple tree to control it
        goalX = treeX + (Math.random() - 0.5) * GAME_TILE * 3;
        goalY = treeY + (Math.random() - 0.5) * GAME_TILE * 3;
      }
    } else {
      // Wander toward zone center
      goalX = centerX + (Math.random() - 0.5) * GAME_TILE * 4;
      goalY = centerY + (Math.random() - 0.5) * GAME_TILE * 4;
    }

    // Anti-corner: if near a corner, strongly push toward center
    if (isSmartCPU) {
      const mapW = gameMap.cols * GAME_TILE, mapH = gameMap.rows * GAME_TILE;
      const edgeMargin = GAME_TILE * 3;
      const nearLeft = cpu.x < edgeMargin, nearRight = cpu.x > mapW - edgeMargin;
      const nearTop = cpu.y < edgeMargin, nearBottom = cpu.y > mapH - edgeMargin;
      if ((nearLeft || nearRight) && (nearTop || nearBottom)) {
        goalX = centerX;
        goalY = centerY;
      }
    }
  }

  if (goalX === undefined) return;

  let moveX = goalX - cpu.x;
  let moveY = goalY - cpu.y;
  const moveDist = Math.sqrt(moveX * moveX + moveY * moveY);
  if (moveDist < 2) return;
  moveX /= moveDist;
  moveY /= moveDist;

  // Natural jitter: add slight random drift to movement so CPUs don't move in perfectly straight lines
  const jitter = cpu.difficulty === 'easy' ? 0.15 : 0.08;
  moveX += (Math.random() - 0.5) * jitter;
  moveY += (Math.random() - 0.5) * jitter;

  // Stay in zone — prefer moving toward zone center if out of bounds
  if (zoneInset > 0) {
    const pCol = Math.floor(cpu.x / GAME_TILE);
    const pRow = Math.floor(cpu.y / GAME_TILE);
    if (pCol < zoneInset + 1 || pCol >= gameMap.cols - zoneInset - 1 ||
        pRow < zoneInset + 1 || pRow >= gameMap.rows - zoneInset - 1) {
      const centerX = (gameMap.cols / 2) * GAME_TILE;
      const centerY = (gameMap.rows / 2) * GAME_TILE;
      const toCenter = Math.sqrt((centerX - cpu.x) ** 2 + (centerY - cpu.y) ** 2) || 1;
      const toCenterX = (centerX - cpu.x) / toCenter;
      const toCenterY = (centerY - cpu.y) / toCenter;
      if (cpu.difficulty === 'expert' || cpu.difficulty === 'hard') {
        // Smart CPUs: soft pull toward center (0.7 blend) — allows zone entry to avoid worse outcomes
        moveX = moveX * 0.3 + toCenterX * 0.7;
        moveY = moveY * 0.3 + toCenterY * 0.7;
      } else {
        // Others: hard override to center
        moveX = toCenterX;
        moveY = toCenterY;
      }
    }
    // Smart CPUs: preemptive zone awareness — avoid moving INTO the zone edge
    if (cpu.difficulty === 'expert' || cpu.difficulty === 'hard') {
      const futureX = cpu.x + moveX * GAME_TILE * 2;
      const futureY = cpu.y + moveY * GAME_TILE * 2;
      const fCol = Math.floor(futureX / GAME_TILE);
      const fRow = Math.floor(futureY / GAME_TILE);
      if (fCol < zoneInset + 1 || fCol >= gameMap.cols - zoneInset - 1 ||
          fRow < zoneInset + 1 || fRow >= gameMap.rows - zoneInset - 1) {
        const centerX = (gameMap.cols / 2) * GAME_TILE;
        const centerY = (gameMap.rows / 2) * GAME_TILE;
        const toCenter = Math.sqrt((centerX - cpu.x) ** 2 + (centerY - cpu.y) ** 2) || 1;
        moveX = moveX * 0.5 + (centerX - cpu.x) / toCenter * 0.5;
        moveY = moveY * 0.5 + (centerY - cpu.y) / toCenter * 0.5;
      }
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

  // Wicket line speed boost for Cricket CPUs
  if (cpu.wicketIds && cpu.wicketIds.length === 2) {
    const w0 = gamePlayers.find(p => p.id === cpu.wicketIds[0]);
    const w1 = gamePlayers.find(p => p.id === cpu.wicketIds[1]);
    if (w0 && w0.alive && w1 && w1.alive) {
      const lx = w1.x - w0.x, ly = w1.y - w0.y;
      const ll = lx * lx + ly * ly;
      if (ll > 0) {
        const t = Math.max(0, Math.min(1, ((cpu.x - w0.x) * lx + (cpu.y - w0.y) * ly) / ll));
        const cx = w0.x + t * lx, cy = w0.y + t * ly;
        const dd = Math.sqrt((cpu.x - cx) ** 2 + (cpu.y - cy) ** 2);
        if (dd < 1.5 * GAME_TILE) speed *= (cpu.fighter.abilities[3].speedBoost || 1.5);
      }
    }
  }

  // Intimidation: cannot move TOWARD the intimidator (within 3.5 tile range)
  if (cpu.intimidated > 0 && cpu.intimidatedBy) {
    const src = gamePlayers.find((p) => p.id === cpu.intimidatedBy);
    if (src) {
      const towardX = src.x - cpu.x;
      const towardY = src.y - cpu.y;
      const towardDist = Math.sqrt(towardX * towardX + towardY * towardY) || 1;
      if (towardDist < GAME_TILE * 3.5) {
        const towardNx = towardX / towardDist;
        const towardNy = towardY / towardDist;
        const dot = moveX * towardNx + moveY * towardNy;
        if (dot > 0) {
          moveX -= dot * towardNx;
          moveY -= dot * towardNy;
        }
      }
    }
  }

  const move = speed * dt * 60; // frame-rate independent
  const newX = cpu.x + moveX * move;
  const newY = cpu.y + moveY * move;
  if (cpu.dragonFlying) {
    cpu.x = Math.max(radius, Math.min(newX, gameMap.cols * GAME_TILE - radius));
    cpu.y = Math.max(radius, Math.min(newY, gameMap.rows * GAME_TILE - radius));
  } else {
    if (canMoveTo(newX, cpu.y, radius)) cpu.x = newX;
    if (canMoveTo(cpu.x, newY, radius)) cpu.y = newY;
  }
}

function cpuAttack(cpu, params) {
  const ai = cpu.aiState;
  const target = ai.attackTarget;
  if (!target || !target.alive) return;

  // Illusion E copies cannot attack at all; special copies handled below (M1 only)
  if (cpu.illusionNoAttack) return;

  const dx = target.x - cpu.x; const dy = target.y - cpu.y;
  const dist = Math.sqrt(dx * dx + dy * dy);
  const fighter = cpu.fighter;
  const isPoker = fighter.id === 'poker';
  const isFilbus = fighter.id === 'filbus';
  const is1x = fighter.id === 'onexonexonex';
  const isCricket = fighter.id === 'cricket';
  const isDeer = fighter.id === 'deer';
  const isNoli = fighter.id === 'noli';
  const isCat = fighter.id === 'explodingcat';
  const isNapoleon = fighter.id === 'napoleon';
  const isModerator = fighter.id === 'moderator';
  const isDnd = fighter.id === 'dnd';
  const isDragon = fighter.id === 'dragon';
  const isPyro = fighter.id === 'pyromaniac';
  const isHeavyRope = fighter.id === 'heavyrope';
  const isOmori = fighter.id === 'omori';

  // Add aim error based on difficulty
  const errorAngle = (Math.random() - 0.5) * params.aimError * 2;
  const baseAngle = Math.atan2(dy, dx);
  const aimAngle = baseAngle + errorAngle;
  const aimNx = Math.cos(aimAngle);
  const aimNy = Math.sin(aimAngle);

  // Try to use abilities in priority order: Special > R > E > T > M1
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;

  // Illusion special copies: skip all abilities, only use M1
  if (!cpu.illusionM1Only) {

  // ── Difficulty helpers for conditional ability usage ──
  const isHardPlus = cpu.difficulty === 'hard' || cpu.difficulty === 'expert';
  const isMedPlus = isHardPlus || cpu.difficulty === 'medium';
  const hpFrac = cpu.hp / cpu.maxHp;
  const targetHpFrac = target.hp / target.maxHp;

  // Special
  if (cpu.specialUnlocked && !cpu.specialUsed) {
    // CPUs get more urgent about using special during decay
    const decayUrgent = cpu.specialGraceTimer <= 0 && cpu.specialDecayTimer > 2;
    if (isPoker) {
      // Poker Special (Royal Flush): Hard+ waits for close range to execute low-HP enemies.
      // Easy/Medium use at medium range.
      const closeRange = 3 * GAME_TILE;
      const mediumRange = 10 * GAME_TILE;
      const shouldFlush = isHardPlus
        ? ((dist < closeRange && targetHpFrac < 0.4) || decayUrgent)
        : (dist < mediumRange || decayUrgent);
      if (shouldFlush) {
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
    } else if (isCricket) {
      if (dist < 10 * GAME_TILE || decayUrgent) {
        cpuUseSpecialCricket(cpu, target);
        return;
      }
    } else if (isDeer) {
      if (dist < 10 * GAME_TILE || decayUrgent) {
        cpuUseSpecialDeer(cpu, target);
        return;
      }
    } else if (isNoli) {
      // Clone closest fighter
      cpuUseSpecialNoli(cpu);
      return;
    } else if (isCat) {
      // Exploding Kitten: spawn kittens when enemy nearby
      if (dist < 10 * GAME_TILE || decayUrgent) {
        cpuUseSpecialCat(cpu);
        return;
      }
    } else if (isNapoleon) {
      // Grande Armée: spawn infantry
      cpuUseSpecialNapoleon(cpu);
      return;
    } else if (isModerator) {
      // Server Update: buff self (CPU doesn't have real teammates)
      cpu.specialUsed = true;
      cpu.modServerUpdateTimer = 10;
      cpu.effects.push({ type: 'server-update', timer: 2 });
      // Reset cooldowns
      cpu.cdE = 0; cpu.cdR = 0; cpu.cdT = 0;
      return;
    } else if (isDnd) {
      // D20: buff M1 to 650 damage. Hard+ only uses when close enough to capitalize.
      const shouldD20 = isHardPlus
        ? (dist < 4 * GAME_TILE || hpFrac < 0.3 || decayUrgent)
        : (dist < 8 * GAME_TILE || decayUrgent);
      if (shouldD20) {
        cpu.specialUsed = true;
        cpu.dndD20Active = true;
        cpu.effects.push({ type: 'd20-roll', timer: 3.0 });
      }
      return;
    } else if (isDragon) {
      // Power of Evil: summon Yellow Ochre or Lich
      if (!cpu.dragonSummonId || !gamePlayers.find(p => p.id === cpu.dragonSummonId && p.alive)) {
        cpu.specialUsed = true;
        const sumId = 'summon-' + cpu.id + '-dragon-' + Date.now();
        const safe = getRandomSafePosition();
        if (Math.random() < 0.5) {
          // Yellow Ochre
          gamePlayers.push({
            id: sumId, name: '🟡 Yellow Ochre', color: '#c8a832',
            x: safe.x, y: safe.y,
            hp: 1000, maxHp: 1000,
            fighter: fighter, alive: true,
            cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
            totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
            supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
            noDamageTimer: 0, healTickTimer: 0, isHealing: false,
            specialJumping: false, specialAiming: false,
            specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
            effects: [],
            isSummon: true, summonOwner: cpu.id, summonType: 'dragon-ochre',
            summonSpeed: 1.5, summonDamage: 50,
            summonAttackCD: 0, summonAttackTimer: 0,
          });
        } else {
          // Lich
          gamePlayers.push({
            id: sumId, name: '💀 Lich', color: '#3a0066',
            x: safe.x, y: safe.y,
            hp: 700, maxHp: 700,
            fighter: fighter, alive: true,
            cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
            totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
            supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
            noDamageTimer: 0, healTickTimer: 0, isHealing: false,
            specialJumping: false, specialAiming: false,
            specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
            effects: [],
            isSummon: true, summonOwner: cpu.id, summonType: 'dragon-lich',
            summonSpeed: 2.0, summonDamage: 100,
            summonAttackCD: 0.4, summonAttackTimer: 0,
            lichKillCount: 0,
          });
        }
        cpu.dragonSummonId = sumId;
        cpu.effects.push({ type: 'summon', timer: 1.5 });
        return;
      }
    } else if (fighter.id === 'illusion') {
      // Illusion CPU: spawn 3 illusion copies + go invis
      cpu.specialUsed = true;
      cpu.illusionSpecialInvis = true;
      cpu.illusionSpecialCopyIds = [];
      const sAbil = fighter.abilities[4];
      const count = sAbil.illusionCount || 3;
      const copyHp = 500 + Math.floor(Math.random() * 101);
      for (let i = 0; i < count; i++) {
        const copyId = 'illusion-special-cpu-' + cpu.id + '-' + i + '-' + Date.now();
        const safe = getRandomSafePosition();
        const copy = createPlayerState(
          { id: copyId, name: cpu.name, color: cpu.color || '#7f8fa6', fighterId: 'illusion' },
          { r: Math.floor(safe.y / GAME_TILE), c: Math.floor(safe.x / GAME_TILE) }, fighter
        );
        copy.x = cpu.x + (Math.random() - 0.5) * GAME_TILE * 4;
        copy.y = cpu.y + (Math.random() - 0.5) * GAME_TILE * 4;
        const cR = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(copy.x, copy.y, cR)) { copy.x = safe.x; copy.y = safe.y; }
        copy.hp = copyHp; copy.maxHp = copyHp;
        copy.isSummon = true; copy.summonOwner = cpu.id;
        copy.summonType = 'illusion-special-copy';
        copy.isCPU = true; copy.difficulty = 'hard';
        copy.noCloneHeal = true; copy.illusionM1Only = true;
        copy.aiState = { moveTarget: null, attackTarget: null, thinkTimer: 0, abilityTimer: 0, lastSeenPositions: {}, strafeDir: Math.random() < 0.5 ? 1 : -1, retreating: false };
        gamePlayers.push(copy);
        cpu.illusionSpecialCopyIds.push(copyId);
      }
      cpu.effects.push({ type: 'illusion-everything', timer: 2.0 });
      return;
    } else if (fighter.id === 'dogtooth') {
      // Dog Tooth CPU: 50% Puppet God, 50% Moon
      cpu.specialUsed = true;
      if (Math.random() < 0.5) {
        cpu.dogtoothSpecialChoice = 'puppet';
        cpu.dogtoothPuppetGod = true;
      } else {
        cpu.dogtoothSpecialChoice = 'moon';
        cpu.dogtoothMoonUsed = true;
        const moonAbil = fighter.abilities[4];
        const moonRadius = (moonAbil.moonRadius || 10) * GAME_TILE;
        const moonDelay = moonAbil.moonDelay || 3;
        cpu.dogtoothMoonX = cpu.x;
        cpu.dogtoothMoonY = cpu.y;
        cpu.dogtoothMoonTimer = moonDelay;
        cpu.dogtoothMoonRadius = moonRadius;
        cpu.dogtoothMoonDmg = moonAbil.damage || 1200;
        cpu.effects.push({ type: 'moon-shadow', timer: moonDelay + 1 });
      }
      return;
    } else if (isOmori) {
      // Omori SPACE: Release Energy
      cpu.specialUsed = true;
      const sAbil = fighter.abilities[4];
      const stunRange = (sAbil.range || 6) * GAME_TILE;
      let closestE = null; let closestD = Infinity;
      for (const t of gamePlayers) {
        if (t.id === cpu.id || !t.alive || t.isSummon) continue;
        if (gameMode === 'teams' && cpu.team && t.team === cpu.team) continue;
        const d = Math.sqrt((t.x - cpu.x) ** 2 + (t.y - cpu.y) ** 2);
        if (d < stunRange && d < closestD) { closestD = d; closestE = t; }
      }
      if (closestE) {
        closestE.stunned = sAbil.stunDuration || 5;
        closestE.effects.push({ type: 'stun', timer: sAbil.stunDuration || 5 });
        // Kill old party
        if (cpu.omoriPartyIds) {
          for (const pid of cpu.omoriPartyIds) {
            const old = gamePlayers.find(p => p.id === pid);
            if (old && old.alive) { old.alive = false; old.hp = 0; }
          }
        }
        cpu.omoriPartyIds = [];
        cpu.omoriSpecialPartyIds = [];
        const friendDefs = [
          { type: 'omori-kel', name: 'Kel', hp: 1000, color: '#f39c12', dmg: 200, cd: 1, projSpd: 30 },
          { type: 'omori-aubrey', name: 'Aubrey', hp: 1300, color: '#e84393', dmg: 200, cd: 0.5 },
          { type: 'omori-hero', name: 'Hero', hp: 1000, color: '#00b894', dmg: 100, cd: 0.5 },
        ];
        for (const fd of friendDefs) {
          const fid2 = fd.type + '-cpu-sp-' + cpu.id + '-' + Date.now() + '-' + Math.random().toString(36).slice(2, 5);
          const ff = { id: fd.type, name: fd.name, hp: fd.hp, healAmount: 0, healDelay: 999, healTick: 999, speed: 3.4, abilities: [] };
          // Spawn around the stunned enemy (evenly spaced)
          const ang = (friendDefs.indexOf(fd) / friendDefs.length) * Math.PI * 2 - Math.PI / 2;
          const spawnDist = GAME_TILE * 2.5;
          let spX = closestE.x + Math.cos(ang) * spawnDist;
          let spY = closestE.y + Math.sin(ang) * spawnDist;
          const fr = createPlayerState({ id: fid2, name: fd.name, color: fd.color }, { r: Math.floor(spY / GAME_TILE), c: Math.floor(spX / GAME_TILE) }, ff);
          fr.x = spX; fr.y = spY;
          const fR = GAME_TILE * PLAYER_RADIUS_RATIO;
          if (!canMoveTo(fr.x, fr.y, fR)) { const safe2 = getRandomSafePosition(); fr.x = safe2.x; fr.y = safe2.y; }
          fr.hp = fd.hp; fr.maxHp = fd.hp;
          fr.isSummon = true; fr.summonOwner = cpu.id; fr.summonType = fd.type;
          fr.summonSpeed = 3.4; fr.summonDamage = fd.dmg; fr.summonAttackCD = fd.cd; fr.summonAttackTimer = 0;
          fr.summonTargetId = closestE.id;
          fr.omoriSpecialDespawnTimer = sAbil.partyDuration || 5;
          if (fd.projSpd) fr.summonProjectileSpeed = fd.projSpd;
          fr.isCPU = true;
          gamePlayers.push(fr);
          cpu.omoriSpecialPartyIds.push(fid2);
        }
        cpu.omoriSpecialTimer = sAbil.partyDuration || 5;
        cpu.cdE = 0;
      }
      cpu.effects.push({ type: 'omori-release', timer: 2.0 });
      return;
    } else if (isPyro) {
      // Pyromaniac SPACE: roar charge → map-wide fire rain
      if (dist < 15 * GAME_TILE) {
        cpu.specialUsed = true;
        const abil = fighter.abilities[4];
        cpu.pyroRoarTimer = abil.roarDuration || 1;
        cpu.pyroSpecialRoarCharging = true;
        cpu.stunned = abil.roarDuration || 1;
        cpu.pyroBurnImmuneTimer = (abil.rainDuration || 5) + (abil.roarDuration || 1) + 5;
        const fearDur = abil.fearDuration || 3;
        const fearRange = CAMERA_RANGE * GAME_TILE * 2;
        const fearImmune = ['noli', 'napoleon', 'onexonexonex', 'fighter', 'dragon'];
        for (const t of gamePlayers) {
          if (t.id === cpu.id || !t.alive || t.isSummon) continue;
          if (gameMode === 'teams' && cpu.team && t.team === cpu.team) continue;
          const d = Math.sqrt((t.x - cpu.x) ** 2 + (t.y - cpu.y) ** 2);
          if (d > fearRange) continue;
          if (fearImmune.includes(t.fighter.id)) continue;
          t.modFearTimer = Math.max(t.modFearTimer || 0, fearDur);
          t.modFearSourceId = cpu.id;
          t.effects.push({ type: 'fear', timer: fearDur });
        }
        cpu.effects.push({ type: 'pyro-roar', timer: 1.5 });
        return;
      }
    } else if (fighter.id === 'heavyrope') {
      // Heavy Rope SPACE: ROPE POWER — spin rope for 5s
      if (dist < 5 * GAME_TILE) {
        cpu.specialUsed = true;
        const abil = fighter.abilities[4];
        cpu.ropePowerTimer = abil.duration || 5;
        cpu.ropePowerHit = {};
        cpu.effects.push({ type: 'rope-power', timer: (abil.duration || 5) + 0.5 });
        return;
      }
    } else {
      if (dist < 10 * GAME_TILE) {
        cpuUseSpecialFighter(cpu, target);
        return;
      }
    }
  }

  // F ability (Move 4) — medium+ CPUs can use F, but easy CPUs never use it
  if (cpu.difficulty !== 'easy' && cpu.cdF <= 0 && cpu.fighter.abilities.length > 5 && cpu.move4Uses < (cpu.fighter.abilities[5].maxUses || 3)) {
    const fAbil = cpu.fighter.abilities[5];
    // Medium CPUs use F less frequently (50% chance per opportunity)
    if (cpu.difficulty === 'medium' && Math.random() > 0.5) { /* skip */ }
    else { cpuUseF(cpu, target, fAbil); }
  }

  // E ability
  if (cpu.cdE <= 0) {
    if (isPoker) {
      // Poker E (Gamble): Hard+ saves Gamble to combo with Full House.
      // Easy/Medium use it whenever in range.
      const gambleRange = (isHardPlus ? 7 : 12) * GAME_TILE;
      const shouldGamble = isHardPlus
        ? (dist < gambleRange && (cpu.pokerFullHouseActive || targetHpFrac < 0.4))
        : (dist < gambleRange);
      if (shouldGamble) {
        cpuFireProjectile(cpu, target, 'card', aimAngle);
        return;
      }
    } else if (isFilbus) {
      // Filbism (1): Hard+ crafts proactively when far; Medium crafts when no chairs; Easy rarely crafts.
      const craftDist = isHardPlus ? 3 : 4;
      const shouldCraft = cpu.chairCharges <= (isHardPlus ? 1 : 0)
        && dist > craftDist * GAME_TILE
        && !cpu.isCraftingChair
        && (cpu.difficulty !== 'easy' || Math.random() < 0.3);
      if (shouldCraft) {
        cpu.isCraftingChair = true;
        cpu.craftTimer = fighter.abilities[1].channelTime || 10;
        return;
      }
    } else if (is1x) {
      // Entanglement: Hard+ uses it to initiate (drag enemy in), then follow up with M1.
      // Easy just uses it when close. Medium uses at mid range.
      const entangleRange = (isHardPlus ? 8 : isMedPlus ? 6 : 4) * GAME_TILE;
      const minEntangleDist = isHardPlus ? 2 * GAME_TILE : 0; // Hard+ won't waste at point blank
      if (dist < entangleRange && dist > minEntangleDist) {
        cpu1xEntangle(cpu, target, aimAngle);
        return;
      }
    } else if (isCricket) {
      // Drive: Hard+ uses Drive to reflect incoming projectiles OR stun close enemies.
      // Easy/Medium use it only in melee range.
      const hasIncomingProjectile = isHardPlus && projectiles.some(p => {
        if (p.ownerId === cpu.id) return false;
        const pdx = p.x - cpu.x, pdy = p.y - cpu.y;
        const pDist = Math.sqrt(pdx * pdx + pdy * pdy);
        if (pDist > 3 * GAME_TILE) return false;
        const projSpeed = Math.sqrt(p.vx * p.vx + p.vy * p.vy) || 1;
        return (p.vx * pdx + p.vy * pdy) / (projSpeed * pDist) < -0.3;
      });
      if (hasIncomingProjectile || dist < 2 * GAME_TILE) {
        cpuCricketDrive(cpu, target, aimNx, aimNy);
        return;
      }
    } else if (isDeer) {
      // Deer's Fear: Hard+ uses it ONLY when retreating or when low HP.
      // Easy uses it whenever enemy is nearby. Medium uses when below 60%.
      const shouldFear = cpu.deerFearTimer <= 0 && dist < 5 * GAME_TILE && (
        (cpu.difficulty === 'easy') ||
        (cpu.difficulty === 'medium' && hpFrac < 0.6) ||
        (isHardPlus && (ai.retreating || hpFrac < 0.4))
      );
      if (shouldFear) {
        cpu.cdE = fighter.abilities[1].cooldown;
        cpu.deerFearTimer = fighter.abilities[1].duration || 5;
        cpu.deerFearTargetX = target.x;
        cpu.deerFearTargetY = target.y;
        cpu.effects.push({ type: 'deer-fear', timer: fighter.abilities[1].duration || 5 });
        return;
      }
    } else if (isNoli) {
      // Void Rush: Hard+ chains dashes to maximize damage; only dashes when target is in sweet spot.
      // Easy just dashes whenever off cooldown. Medium checks range.
      const voidRushRange = isHardPlus ? 6 : isMedPlus ? 8 : 10;
      const shouldDash = !cpu.noliVoidRushActive && !cpu.noliVoidStarAiming
        && dist < voidRushRange * GAME_TILE
        && (isHardPlus ? dist > 2 * GAME_TILE : true); // Hard+ won't dash at point blank
      if (shouldDash) {
        cpuNoliVoidRush(cpu, target);
        return;
      }
    } else if (isCat) {
      // Draw: Hard+ saves draws for tactical moments (low HP or enemy engaged).
      // Easy/Medium draw whenever available.
      const shouldDraw = !isHardPlus || hpFrac < 0.6 || dist < 4 * GAME_TILE;
      if (shouldDraw) {
        cpuCatDraw(cpu);
        return;
      }
    } else if (isNapoleon) {
      // Cavalry: Hard+ mounts to chase injured enemies or dismounts when low HP.
      // Easy/Medium just mount and stay mounted.
      if (isHardPlus) {
        if (!cpu.napoleonCavalry && (targetHpFrac < 0.5 || dist > 5 * GAME_TILE)) {
          cpu.napoleonCavalry = true;
          cpu.effects.push({ type: 'cavalry-mount', timer: 1.5 });
          return;
        } else if (cpu.napoleonCavalry && hpFrac < 0.3) {
          // Dismount to take less damage when low HP
          cpu.napoleonCavalry = false;
          cpu.effects.push({ type: 'cavalry-dismount', timer: 1.0 });
          return;
        }
      } else if (!cpu.napoleonCavalry) {
        cpu.napoleonCavalry = true;
        cpu.effects.push({ type: 'cavalry-mount', timer: 1.5 });
        return;
      }
    } else if (isModerator) {
      // TP: Hard+ TPs the lowest HP enemy. Easy/Medium TP random.
      const enemies = gamePlayers.filter(p => p.alive && !p.isSummon && p.id !== cpu.id);
      if (enemies.length > 0) {
        let pick;
        if (isHardPlus) {
          pick = enemies.reduce((a, b) => a.hp < b.hp ? a : b);
        } else {
          pick = enemies[Math.floor(Math.random() * enemies.length)];
        }
        pick.x = cpu.x + (Math.random() - 0.5) * GAME_TILE;
        pick.y = cpu.y + (Math.random() - 0.5) * GAME_TILE;
        pick.stunned = 1;
        pick.modFearTimer = 5;
        pick.modFearSourceId = cpu.id;
        cpu.cdE = fighter.abilities[1].cooldown;
        cpu.effects.push({ type: 'scare-tp', timer: 1.5 });
      }
      return;
    } else if (isDnd) {
      // Questing: spawn orcs strategically based on difficulty.
      // Expert/Hard: only farm when safe AND when not overwhelmed by existing orcs
      // Medium: spawn if reasonably safe
      // Easy: spawn whenever possible (can overwhelm itself)
      const abil = fighter.abilities[1];
      const liveOrcs = cpu.dndOrcIds.filter(oid => gamePlayers.some(p => p.id === oid && p.alive)).length;
      // Expert/Hard: max 1 orc at a time, only when safe and HP is decent
      // Medium: max 2 orcs, spawn when not too close to enemy
      // Easy: max 3 orcs, no restrictions
      const maxOrcs = isHardPlus ? 1 : (isMedPlus ? 2 : 3);
      const safeToFarm = isHardPlus ? (dist > 8 * GAME_TILE && hpFrac > 0.6)
                       : isMedPlus ? (dist > 5 * GAME_TILE || hpFrac > 0.7)
                       : true;
      if (liveOrcs < maxOrcs && safeToFarm) {
        cpu.cdE = abil.cooldown;
        const orcId = 'summon-' + cpu.id + '-orc-' + Date.now();
        const safe = getRandomSafePosition();
        const orc = {
          id: orcId, name: '⚔ Orc', color: '#556b2f',
          x: safe.x, y: safe.y,
          hp: abil.orcHp || 600, maxHp: abil.orcHp || 600,
          fighter: fighter, alive: true,
          cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
          totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
          supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
          noDamageTimer: 0, healTickTimer: 0, isHealing: false,
          specialJumping: false, specialAiming: false,
          specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
          effects: [],
          isSummon: true, summonOwner: cpu.id, summonType: 'dnd-orc',
          summonTargetId: cpu.id,
          summonSpeed: 2.0, summonDamage: abil.damage || 200,
          summonAttackCD: 1.5, summonAttackTimer: 0,
        };
        gamePlayers.push(orc);
        cpu.dndOrcIds.push(orcId);
        return;
      }
      return;
    } else if (isDragon) {
      // Dragon Ride: Hard+ flies strategically (escape or close distance).
      // Easy/Medium fly more loosely.
      if (!cpu.dragonFlying && !cpu.dragonBeamCharging && !cpu.dragonBeamFiring) {
        const shouldFly = isHardPlus
          ? (hpFrac < 0.25 || (dist > 10 * GAME_TILE && targetHpFrac < 0.5))
          : (cpu.hp < cpu.maxHp * 0.3 || dist > 8 * GAME_TILE);
        if (shouldFly) {
          cpu.cdE = fighter.abilities[1].cooldown;
          cpu.dragonFlying = true;
          cpu.dragonFlyTimer = fighter.abilities[1].flyDuration || 5;
          cpu.effects.push({ type: 'dragon-fly', timer: 1.5 });
          return;
        }
      }
    } else if (fighter.id === 'illusion') {
      // Illusion E: go invisible + spawn copy.
      // ALL difficulties: only use when retreating/sneaking up, NOT in direct combat.
      // Hard+: use to reposition and ambush from behind.
      // Medium: use when low HP to escape. Easy: use when very low HP.
      if (cpu.illusionInvisTimer <= 0 && !cpu.illusionSpecialInvis) {
        const shouldInvis = isHardPlus
          ? (ai.retreating || dist > 5 * GAME_TILE || hpFrac < 0.4)
          : isMedPlus
            ? (ai.retreating || hpFrac < 0.5)
            : (hpFrac < 0.3);
        if (shouldInvis) {
          cpu.cdE = fighter.abilities[1].cooldown;
          cpu.illusionInvisTimer = fighter.abilities[1].duration || 10;
          // Kill old copy
          if (cpu.illusionCopyId) {
            const oldCopy = gamePlayers.find(p => p.id === cpu.illusionCopyId);
            if (oldCopy && oldCopy.alive) { oldCopy.alive = false; oldCopy.hp = 0; }
          }
          const copyId = 'illusion-copy-cpu-' + cpu.id + '-' + Date.now();
          const copy = createPlayerState(
            { id: copyId, name: cpu.name, color: cpu.color || '#7f8fa6', fighterId: 'illusion' },
            { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) }, fighter
          );
          copy.x = cpu.x; copy.y = cpu.y;
          copy.hp = cpu.hp; copy.maxHp = cpu.maxHp;
          copy.isSummon = true; copy.summonOwner = cpu.id;
          copy.summonType = 'illusion-copy';
          copy.isCPU = true; copy.difficulty = 'hard';
          copy.noCloneHeal = true; copy.illusionNoAttack = true;
          copy.aiState = { moveTarget: null, attackTarget: null, thinkTimer: 0, abilityTimer: 0, lastSeenPositions: {}, strafeDir: Math.random() < 0.5 ? 1 : -1, retreating: false };
          gamePlayers.push(copy);
          cpu.illusionCopyId = copyId;
          cpu.effects.push({ type: 'illusion-vanish', timer: 1.0 });
          return;
        }
      }
    } else if (fighter.id === 'dogtooth') {
      // CPU: spawn Ouriel if none alive (no CD set here — CD only on Ouriel death)
      if (!cpu.dogtoothOurielId || !gamePlayers.find(p => p.id === cpu.dogtoothOurielId && p.alive)) {
        const ourielId = 'ouriel-' + cpu.id + '-' + Date.now();
        const safe = getRandomSafePosition();
        const ourielFighter = { id: 'ouriel-summon', name: 'Ouriel', hp: 999999, healAmount: 0, healDelay: 999, healTick: 999, speed: 2.0, abilities: [] };
        const ouriel = createPlayerState(
          { id: ourielId, name: 'Ouriel', color: '#ddd' },
          { r: Math.floor(safe.y / GAME_TILE), c: Math.floor(safe.x / GAME_TILE) },
          ourielFighter
        );
        ouriel.x = safe.x; ouriel.y = safe.y;
        const carryHp = cpu.dogtoothOurielHp || 999999;
        const carryHits = cpu.dogtoothOurielHitsLeft || 2;
        ouriel.hp = carryHp; ouriel.maxHp = 999999;
        ouriel.isSummon = true; ouriel.summonOwner = cpu.id;
        ouriel.summonType = 'ouriel';
        ouriel.summonSpeed = 2.0;
        ouriel.ourielHitsLeft = carryHits;
        ouriel.ourielHealPerSec = 40;
        ouriel.ourielRoomHp = 500;
        ouriel.ourielRoomDPS = 40;
        ouriel.isCPU = true;
        gamePlayers.push(ouriel);
        cpu.dogtoothOurielId = ourielId;
        cpu.effects.push({ type: 'ouriel-summon', timer: 1.5 });
        return;
      }
    } else if (isOmori) {
      // Omori E: Spawn a party friend if none alive
      const hasParty = cpu.omoriPartyIds && cpu.omoriPartyIds.some(pid => gamePlayers.find(p => p.id === pid && p.alive));
      if (!hasParty) {
        cpu.cdE = fighter.abilities[1].cooldown;
        if (cpu.omoriPartyIds) {
          for (const pid of cpu.omoriPartyIds) {
            const old = gamePlayers.find(p => p.id === pid);
            if (old && old.alive) { old.alive = false; old.hp = 0; }
          }
        }
        cpu.omoriPartyIds = [];
        const roll = Math.random();
        let fType, fName, fHp, fColor, fDmg, fCd;
        const eAbil = fighter.abilities[1];
        if (roll < 0.333) { fType = 'omori-kel'; fName = 'Kel'; fHp = eAbil.kelHp || 1000; fColor = '#f39c12'; fDmg = eAbil.kelDamage || 200; fCd = eAbil.kelFireCD || 1; }
        else if (roll < 0.666) { fType = 'omori-aubrey'; fName = 'Aubrey'; fHp = eAbil.aubreyHp || 1300; fColor = '#e84393'; fDmg = eAbil.aubreyDamage || 200; fCd = eAbil.aubreyAttackCD || 0.5; }
        else { fType = 'omori-hero'; fName = 'Hero'; fHp = eAbil.heroHp || 1000; fColor = '#00b894'; fDmg = eAbil.heroDamage || 100; fCd = eAbil.heroAttackCD || 0.5; }
        const fid2 = fType + '-' + cpu.id + '-' + Date.now();
        const ff = { id: fType, name: fName, hp: fHp, healAmount: 0, healDelay: 999, healTick: 999, speed: 3.4, abilities: [] };
        const safe = getRandomSafePosition();
        const fr = createPlayerState({ id: fid2, name: fName, color: fColor }, { r: Math.floor(safe.y / GAME_TILE), c: Math.floor(safe.x / GAME_TILE) }, ff);
        fr.x = safe.x; fr.y = safe.y;
        fr.hp = fHp; fr.maxHp = fHp;
        fr.isSummon = true; fr.summonOwner = cpu.id; fr.summonType = fType;
        fr.summonSpeed = 3.4; fr.summonDamage = fDmg; fr.summonAttackCD = fCd; fr.summonAttackTimer = 0;
        if (fType === 'omori-kel') fr.summonProjectileSpeed = eAbil.kelProjectileSpeed || 30;
        fr.isCPU = true;
        gamePlayers.push(fr);
        cpu.omoriPartyIds.push(fid2);
        cpu.effects.push({ type: 'omori-party-spawn', timer: 1.5 });
        return;
      }
    } else if (isPyro) {
      // Pyromaniac E: Gasoline trail
      cpu.cdE = fighter.abilities[1].cooldown;
      cpu.pyroGasolineTimer = fighter.abilities[1].duration || 5;
      cpu._pyroGasDrop = 0;
      if (!cpu.pyroGasolineTrail) cpu.pyroGasolineTrail = [];
      cpu.effects.push({ type: 'pyro-gasoline', timer: 5 });
      return;
    } else {
      cpu.cdE = fighter.abilities[1].cooldown;
      cpu.supportBuff = fighter.abilities[1].duration;
      cpu.effects.push({ type: 'support', timer: 1.5 });
      // Slow nearby enemies
      const abil = fighter.abilities[1];
      const slowRange = (abil.slowRange || 8) * GAME_TILE;
      const slowDur = abil.slowDuration || 7;
      for (const target of gamePlayers) {
        if (target.id === cpu.id || !target.alive || (target.isSummon && target.summonOwner === cpu.id)) continue;
        const sdx = target.x - cpu.x, sdy = target.y - cpu.y;
        if (Math.sqrt(sdx * sdx + sdy * sdy) < slowRange) {
          target.buffSlowed = slowDur;
        }
      }
      return;
    }
  }

  // R ability
  if (cpu.cdR <= 0) {
    if (isPoker) {
      // Blinds: Hard+ always takes Small Blind for damage reduction.
      // Medium sometimes takes Big. Easy is random.
      cpu.cdR = fighter.abilities[2].cooldown;
      if (isHardPlus) {
        // Smart: prefer Small Blind (safe), take Dealer to reset Gamble if on CD
        if (cpu.cdE > 15) {
          cpu.blindBuff = 'dealer'; cpu.blindTimer = 0; cpu.cdE = 0;
        } else {
          cpu.blindBuff = 'small'; cpu.blindTimer = 0;
        }
      } else {
        const roll = Math.random();
        if (roll < 0.70) { cpu.blindBuff = 'small'; cpu.blindTimer = 0; }
        else if (roll < 0.90) { cpu.blindBuff = 'big'; cpu.blindTimer = 60; }
        else { cpu.blindBuff = 'dealer'; cpu.blindTimer = 0; cpu.cdE = 0; }
      }
      cpu.effects.push({ type: 'blind-small', timer: 1.0 });
      return;
    } else if (isFilbus) {
      // Filbism (2): Hard+ eats chair as soon as hurt. Easy eats only when low.
      const eatThreshold = isHardPlus ? 0.8 : isMedPlus ? 0.6 : 0.4;
      if (cpu.chairCharges > 0 && hpFrac < eatThreshold && !cpu.isEatingChair) {
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
    } else if (isCricket) {
      // Gear Up: Hard+ uses when enemy is committed (close + low CD on M1).
      // Easy/Medium just pop it near enemies.
      const gearUpRange = isHardPlus ? 3 : 4;
      if (cpu.gearUpTimer <= 0 && dist < gearUpRange * GAME_TILE) {
        cpu.cdR = fighter.abilities[2].cooldown;
        cpu.gearUpTimer = fighter.abilities[2].duration || 10;
        cpu.effects.push({ type: 'gear-up', timer: 1.5 });
        return;
      }
    } else if (isDeer) {
      // Deer's Seer: Hard+ uses proactively when enemy is about to attack.
      // Easy uses only when desperate.
      const seerThreshold = isHardPlus ? 0.7 : isMedPlus ? 0.5 : 0.35;
      const seerRange = isHardPlus ? 5 : 4;
      if (cpu.deerSeerTimer <= 0 && dist < seerRange * GAME_TILE && hpFrac < seerThreshold) {
        cpu.cdR = fighter.abilities[2].cooldown;
        cpu.deerSeerTimer = fighter.abilities[2].duration || 5;
        cpu.effects.push({ type: 'deer-seer', timer: fighter.abilities[2].duration || 5 });
        return;
      }
    } else if (isNoli) {
      // Void Star: Hard+ uses Void Star after stunning with Entanglement.
      // Easy/Medium fire it whenever in range.
      const canCombo = isHardPlus ? (target.stunned > 0 || dist < 4 * GAME_TILE) : true;
      if (!cpu.noliVoidRushActive && !cpu.noliVoidStarAiming && dist < 8 * GAME_TILE && canCombo) {
        cpuNoliVoidStar(cpu, target);
        return;
      }
    } else if (isCat) {
      // Attack buff: Hard+ saves it for when close to enemy + Scratch off CD.
      // Easy/Medium use when in range.
      const attackRange = isHardPlus ? 2 : 3;
      if (cpu.catAttackBuff <= 0 && dist < attackRange * GAME_TILE) {
        cpuCatAttack(cpu);
        return;
      }
    } else if (isNapoleon) {
      // Cannon: spawn cannon if not already placed
      if (!cpu.napoleonCannonId) {
        cpuNapoleonCannon(cpu);
        return;
      }
    } else if (isModerator) {
      // Bug Fixing: disable a random ability on target
      if (!target.modDisabledAbilities) target.modDisabledAbilities = [];
      const slots = [1, 2, 3]; // E, R, T
      const available = slots.filter(s => !target.modDisabledAbilities.includes(s));
      if (available.length > 0) {
        const pick = available[Math.floor(Math.random() * available.length)];
        target.modDisabledAbilities.push(pick);
        cpu.cdR = fighter.abilities[2].cooldown;
        cpu.effects.push({ type: 'bug-fix', timer: 1.5 });
      }
      return;
    } else if (isDnd) {
      // Buy/Use: spend GP intelligently based on difficulty and situation
      const gp = cpu.dndGP || 0;
      if (gp >= 1) {
        cpu.cdR = fighter.abilities[2].cooldown || 1;
        // Expert/Hard: save for charm (8GP) when close, buy weapon at 5GP if charm owned,
        //   use potion when low HP, use spell only when target is close
        // Medium: spend at sensible thresholds
        // Easy: spend immediately on whatever is available
        if (gp >= 8 && !cpu.dndCharm) {
          // Always buy charm when affordable — best investment
          cpu.dndGP = 0;
          cpu.dndCharm = true;
          cpu.dndWeaponBonus = (cpu.dndWeaponBonus || 0) + 50;
        } else if (isHardPlus && gp < 8 && !cpu.dndCharm && gp >= 5 && hpFrac > 0.5) {
          // Hard+: save for charm if HP is fine — don't spend 5GP on weapon if charm not owned yet
          // Skip spending, keep saving
          return;
        } else if (gp >= 5) {
          // Buy weapon upgrade
          cpu.dndGP = 0;
          cpu.dndWeaponBonus = (cpu.dndWeaponBonus || 0) + 50;
        } else if (gp >= 2 && hpFrac < 0.4 && isMedPlus) {
          // Medium+: if low HP with 2+ GP, buy potion instead of spell
          cpu.dndGP = 0;
          cpu.dndHealPool = (cpu.dndHealPool || 0) + 300;
          return;
        } else if (gp >= 2) {
          // Random spell — Hard+ only uses when target is in range
          if (isHardPlus && dist > 8 * GAME_TILE) return;  // save GP, target too far
          cpu.dndGP = 0;
          const roll = Math.random();
          if (roll < 0.33) {
            // Zombie summon
            const zId = 'summon-' + cpu.id + '-zombie-' + Date.now();
            const safe = getRandomSafePosition();
            gamePlayers.push({
              id: zId, name: '🧟 Zombie', color: '#2d5a1e',
              x: safe.x, y: safe.y,
              hp: 400, maxHp: 400,
              fighter: fighter, alive: true,
              cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
              totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
              supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
              noDamageTimer: 0, healTickTimer: 0, isHealing: false,
              specialJumping: false, specialAiming: false,
              specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
              effects: [],
              isSummon: true, summonOwner: cpu.id, summonType: 'dnd-zombie',
              summonSpeed: 1.5, summonDamage: 150,
              summonAttackCD: 2.0, summonAttackTimer: 0,
            });
          } else if (roll < 0.66) {
            // Fireball (3×3 AoE)
            const spd = 30 * GAME_TILE / 10;
            projectiles.push({
              x: cpu.x, y: cpu.y,
              vx: aimNx * spd, vy: aimNy * spd,
              ownerId: cpu.id, damage: 300,
              timer: 3, type: 'dnd-fireball',
              dndFireball: true, aoeRadius: 3 * GAME_TILE,
            });
          } else {
            // Blur bolt
            const spd = 35 * GAME_TILE / 10;
            projectiles.push({
              x: cpu.x, y: cpu.y,
              vx: aimNx * spd, vy: aimNy * spd,
              ownerId: cpu.id, damage: 300,
              timer: 2, type: 'dnd-blur-bolt',
              dndBlurDuration: 10,
            });
          }
        } else {
          // Potion
          cpu.dndGP = 0;
          cpu.dndHealPool = (cpu.dndHealPool || 0) + 300;
        }
        return;
      }
      return;
    } else if (isDragon) {
      // Dragon Beam: Hard+ charges beam when enemy is stunned/slowed for easier hit.
      // Easy/Medium fire at mid range regardless.
      if (!cpu.dragonBeamCharging && !cpu.dragonBeamFiring && cpu.dragonBeamRecovery <= 0 && !cpu.dragonFlying) {
        const beamMin = isHardPlus ? 2 : 3;
        const beamMax = 12;
        const shouldBeam = isHardPlus
          ? (dist < beamMax * GAME_TILE && dist > beamMin * GAME_TILE && (target.stunned > 0 || target.buffSlowed > 0 || dist > 6 * GAME_TILE))
          : (dist < beamMax * GAME_TILE && dist > beamMin * GAME_TILE);
        if (shouldBeam) {
          cpu.cdR = fighter.abilities[2].cooldown;
          cpu.dragonBeamCharging = true;
          cpu.dragonBeamChargeTimer = fighter.abilities[2].chargeTime || 3;
          cpu.dragonBeamAimNx = aimNx;
          cpu.dragonBeamAimNy = aimNy;
          cpu.effects.push({ type: 'dragon-beam-charge', timer: fighter.abilities[2].chargeTime || 3 });
          return;
        }
      }
    } else if (fighter.id === 'illusion') {
      // Illusion R: Rewind — Hard+ uses it when they've been pushed into a bad position.
      // Medium uses when low HP. Easy uses randomly.
      const shouldRewind = isHardPlus
        ? (hpFrac < 0.4 || (ai.retreating && dist < 3 * GAME_TILE))
        : isMedPlus
          ? (hpFrac < 0.5)
          : (Math.random() < 0.4);
      if (!shouldRewind) { /* skip */ }
      else {
      cpu.cdR = fighter.abilities[2].cooldown;
      const rewindTime = (fighter.abilities[2].rewindTime || 3) * 1000;
      const now = Date.now();
      const pRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
      for (const p of gamePlayers) {
        if (!p.alive || p.isSummon) continue;
        if (p.id === cpu.id) continue; // don't rewind self
        if (!p.illusionPositionHistory || p.illusionPositionHistory.length === 0) continue;
        let bestPos = null; let bestDiff = Infinity;
        for (const entry of p.illusionPositionHistory) {
          const diff = Math.abs((now - entry.t) - rewindTime);
          if (diff < bestDiff) { bestDiff = diff; bestPos = entry; }
        }
        if (bestPos && canMoveTo(bestPos.x, bestPos.y, pRadius)) {
          p.x = bestPos.x; p.y = bestPos.y;
          p.effects.push({ type: 'illusion-rewind', timer: 1.0 });
        }
      }
      cpu.effects.push({ type: 'illusion-space', timer: 1.5 });
      return;
      }
    } else if (fighter.id === 'dogtooth') {
      // Smile Tapes: Hard+ uses when enemy is close and health is okay.
      // Easy uses more recklessly.
      const smileRange = isHardPlus ? 4 : 6;
      const smileHpMin = isHardPlus ? 0.4 : 0.3;
      if (cpu.dogtoothSmileTimer <= 0 && dist < smileRange * GAME_TILE && hpFrac > smileHpMin) {
        cpu.cdR = fighter.abilities[2].cooldown;
        cpu.dogtoothSmileTimer = fighter.abilities[2].duration || 10;
        cpu.dogtoothSmileDmg = fighter.abilities[2].damage || 500;
        cpu.effects.push({ type: 'smile-tapes', timer: 10 });
        return;
      }
    } else if (isOmori) {
      // Omori R: Party Skill — use if party friend alive
      const nearParty = cpu.omoriPartyIds ? gamePlayers.find(p => cpu.omoriPartyIds.includes(p.id) && p.alive) : null;
      if (nearParty) {
        cpu.cdR = fighter.abilities[2].cooldown;
        const rAbil = fighter.abilities[2];
        if (nearParty.summonType === 'omori-kel') {
          cpu.omoriKelBuffTimer = rAbil.kelBuffDuration || 15;
        } else if (nearParty.summonType === 'omori-aubrey') {
          cpu.omoriAubreyBuffTimer = rAbil.aubreyBuffDuration || 20;
        } else if (nearParty.summonType === 'omori-hero') {
          cpu.omoriHeroHealPool = rAbil.heroHealAmount || 700;
          cpu.omoriHeroHealTimer = rAbil.heroHealDuration || 1;
        }
        return;
      }
    } else if (isPyro) {
      // Pyromaniac R: Molotov ×3 — shadow delay before landing
      if (dist < 12 * GAME_TILE) {
        cpu.cdR = fighter.abilities[2].cooldown;
        const abil = fighter.abilities[2];
        let dmg = abil.damage || 200;
        if (cpu.supportBuff > 0) dmg *= 1.5;
        if (cpu.pyroFireBuffTimer > 0) dmg *= 2;
        if (!cpu.pyroMolotovShadows) cpu.pyroMolotovShadows = [];
        const fallDelay = abil.fallDelay || 2;
        const offsets = [{ x: 0, y: 0 }, { x: (abil.radius || 3) * GAME_TILE * 0.8, y: 0 }, { x: -(abil.radius || 3) * GAME_TILE * 0.8, y: 0 }];
        for (const off of offsets) {
          const fx = target.x + off.x + (Math.random() - 0.5) * GAME_TILE;
          const fy = target.y + off.y + (Math.random() - 0.5) * GAME_TILE;
          cpu.pyroMolotovShadows.push({
            x: fx, y: fy, timer: fallDelay, radius: abil.radius || 3,
            dmg: dmg, burnDPS: abil.burnDPS || 100, burnDur: abil.burnDuration || 3, fireDur: abil.fireDuration || 5,
          });
        }
        cpu.effects.push({ type: 'pyro-molotov', timer: 0.5 });
        return;
      }
    } else {
      if (dist < fighter.abilities[2].range * GAME_TILE) {
        cpuPowerSwing(cpu, target, aimNx, aimNy);
        return;
      }
    }
  }

  // T ability — per-fighter strategic conditions
  const tAbilityChance = cpu.difficulty === 'expert' ? 0.65 : cpu.difficulty === 'hard' ? 0.55 : cpu.difficulty === 'medium' ? 0.3 : 0.15;
  if (cpu.cdT <= 0 && Math.random() < tAbilityChance) {
    if (isPoker) {
      // Chip Change: Hard+ uses when M1 damage is low. Easy uses randomly.
      const shouldChipChange = isHardPlus ? (cpu.chipChangeDmg < 0 || cpu.chipChangeDmg < 150) : true;
      if (shouldChipChange) {
        cpu.cdT = fighter.abilities[3].cooldown;
        const options = [50, 100, 200, 300, 400];
        cpu.chipChangeDmg = options[Math.floor(Math.random() * options.length)];
        cpu.chipChangeTimer = fighter.abilities[3].duration || 30;
        return;
      }
    } else if (isFilbus) {
      // Oddity Overthrow: summon a companion (block if enemy too close)
      if (!cpu.summonId) {
        const minSummonDist = GAME_TILE * 2;
        let tooClose = false;
        for (const other of gamePlayers) {
          if (other.id === cpu.id || !other.alive || other.isSummon) continue;
          const sdx = other.x - cpu.x, sdy = other.y - cpu.y;
          if (Math.sqrt(sdx * sdx + sdy * sdy) < minSummonDist) { tooClose = true; break; }
        }
        if (tooClose) return;
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
          cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
          totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
          supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
          noDamageTimer: 0, healTickTimer: 0, isHealing: false,
          specialJumping: false, specialAiming: false,
          specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
          effects: [],
          blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
          chairCharges: 0, isCraftingChair: false, craftTimer: 0,
          isEatingChair: false, eatTimer: 0, eatHealPool: 0,
          summonId: null, boiledOneActive: false, boiledOneTimer: 0,
          poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
          gearUpTimer: 0, wicketIds: [], driveReflectTimer: 0,
          deerFearTimer: 0, deerFearTargetX: 0, deerFearTargetY: 0,
          deerSeerTimer: 0, deerRobotId: null, iglooX: 0, iglooY: 0, iglooTimer: 0,
          noliVoidRushActive: false, noliVoidRushVx: 0, noliVoidRushVy: 0, noliVoidRushTimer: 0,
          noliVoidRushChain: 0, noliVoidRushChainTimer: 0, noliVoidRushLastHitId: null,
          noliVoidStarAiming: false, noliVoidStarAimX: 0, noliVoidStarAimY: 0, noliVoidStarTimer: 0,
          noliObservantUses: 0, noliCloneId: null,
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
      // Unstable Eye: Hard+ uses before engaging to track enemies + speed boost.
      // Easy uses when close.
      const eyeRange = isHardPlus ? 10 : 6;
      if (cpu.unstableEyeTimer <= 0 && dist < eyeRange * GAME_TILE) {
        cpu.cdT = fighter.abilities[3].cooldown;
        cpu.unstableEyeTimer = fighter.abilities[3].duration || 6;
        cpu.effects.push({ type: 'unstable-eye', timer: fighter.abilities[3].duration || 6 });
        return;
      }
    } else if (isCricket) {
      // Wicket: place wickets between self and enemy
      if (!cpu.wicketIds || cpu.wicketIds.length === 0) {
        cpuCricketWicket(cpu, target);
        return;
      }
    } else if (isDeer) {
      // Deer T: Spear — Hard+ saves Spear for summons (killsSummons) or stunned targets.
      // Easy/Medium just stab when in range.
      const spearRange = (fighter.abilities[3].range || 1.2) * GAME_TILE;
      if (cpu.deerSeerTimer <= 0 && dist < spearRange) {
        const targetIsSummon = target.isSummon;
        const shouldSpear = isHardPlus ? (targetIsSummon || target.stunned > 0 || targetHpFrac < 0.3) : true;
        if (shouldSpear) {
          cpuDeerSpear(cpu, target, aimNx, aimNy);
          return;
        }
      }
    } else if (isNoli) {
      // Observant (teleport): Hard+ saves it as an escape tool.
      // Easy uses it more freely.
      const tpThreshold = isHardPlus ? 0.2 : isMedPlus ? 0.3 : 0.4;
      if (cpu.noliObservantUses < (fighter.abilities[3].maxUses || 3) && hpFrac < tpThreshold) {
        cpuNoliObservant(cpu);
        return;
      }
    } else if (isCat) {
      // Steal: copy opponent's Move 3
      if (dist < 6 * GAME_TILE) {
        cpuCatSteal(cpu, target);
        return;
      }
    } else if (isNapoleon) {
      // Defensive Tactics: place wall between CPU and enemy
      if (!cpu.napoleonWallId) {
        cpuNapoleonWall(cpu, target);
        return;
      }
    } else if (isModerator) {
      // Server Reset: TP all players to spawn positions (limited uses)
      if (cpu.modServerResetUses < 3) {
        cpu.modServerResetUses++;
        cpu.cdT = fighter.abilities[3].cooldown;
        const resetRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
        for (const p of gamePlayers) {
          if (!p.alive || p.isSummon) continue;
          if (p.spawnX != null && p.spawnY != null && canMoveTo(p.spawnX, p.spawnY, resetRadius)) {
            p.x = p.spawnX;
            p.y = p.spawnY;
          } else {
            const safe = getRandomSafePosition();
            p.x = safe.x;
            p.y = safe.y;
          }
        }
        cpu.effects.push({ type: 'server-reset', timer: 2 });
        return;
      }
    } else if (isDnd) {
      // Race Change: pick race intelligently based on situation and difficulty
      const curRace = cpu.dndRace || 'human';
      let wantRace = curRace;
      if (isHardPlus) {
        // Expert/Hard: strategic race selection
        // Elf when target is far (ranged poke), Dwarf when low HP (damage reduction),
        // Human when chasing or farming orcs (speed)
        const hasLiveOrcs = cpu.dndOrcIds && cpu.dndOrcIds.some(oid => gamePlayers.some(p => p.id === oid && p.alive));
        if (hpFrac < 0.35) {
          wantRace = 'dwarf'; // tank mode when low
        } else if (hasLiveOrcs) {
          wantRace = 'human'; // speed to kill orcs faster
        } else if (dist > 5 * GAME_TILE) {
          wantRace = 'elf'; // ranged poke at distance
        } else if (dist < 2 * GAME_TILE) {
          wantRace = 'dwarf'; // tanky in close fights
        } else {
          wantRace = 'human'; // balanced default
        }
      } else if (isMedPlus) {
        // Medium: simpler logic — elf at range, dwarf when low, human otherwise
        if (hpFrac < 0.3) wantRace = 'dwarf';
        else if (dist > 6 * GAME_TILE) wantRace = 'elf';
        else wantRace = 'human';
      } else {
        // Easy: random (original behavior)
        const races = ['human', 'elf', 'dwarf'].filter(r => r !== curRace);
        wantRace = races[Math.floor(Math.random() * races.length)];
      }
      if (wantRace === curRace) return; // don't waste cooldown switching to same race
      cpu.cdT = fighter.abilities[3].cooldown;
      cpu.dndRace = wantRace;
      cpu.effects.push({ type: 'race-change', timer: 1.5 });
      return;
    } else if (isDragon) {
      // Draconic Roar: Hard+ only uses when HP is comfortable. Easy uses recklessly.
      const roarHpMin = isHardPlus ? 500 : 300;
      if (!cpu.dragonRoarActive && cpu.hp > roarHpMin) {
        cpu.cdT = fighter.abilities[3].cooldown;
        cpu.dragonRoarActive = true;
        cpu.hp -= (fighter.abilities[3].selfDamage || 200);
        if (cpu.hp <= 0) cpu.hp = 1;
        cpu.effects.push({ type: 'dragon-roar', timer: 2 });
        return;
      }
    } else if (fighter.id === 'illusion') {
      // Illusion T: Time Freeze — Hard+ uses when enemy is close and about to attack.
      // All difficulties only use when enemy is in range for follow-up.
      const freezeRange = isHardPlus ? 5 : 8;
      const shouldFreeze = isHardPlus
        ? (dist < freezeRange * GAME_TILE && (targetHpFrac < 0.5 || cpu.cdM1 <= 0))
        : (dist < freezeRange * GAME_TILE);
      if (shouldFreeze) {
        cpu.cdT = fighter.abilities[3].cooldown;
        const freezeDur = fighter.abilities[3].freezeDuration || 1.5;
        cpu.illusionTimeFreezeTimer = freezeDur;
        for (const t of gamePlayers) {
          if (t.id === cpu.id || !t.alive) continue;
          if (t.isSummon && t.summonOwner === cpu.id) continue;
          t.stunned = Math.max(t.stunned, freezeDur);
          t.effects.push({ type: 'illusion-frozen', timer: freezeDur });
        }
        cpu.effects.push({ type: 'illusion-time', timer: freezeDur + 0.5 });
        return;
      }
    } else if (fighter.id === 'dogtooth') {
      cpu.cdT = fighter.abilities[3].cooldown;
      for (const t of gamePlayers) {
        if (t.id === cpu.id || !t.alive) continue;
        if (t.isSummon && t.summonOwner === cpu.id) continue;
        dealDamage(cpu, t, fighter.abilities[3].damage || 450, false, true);
      }
      // Self-damage
      cpu.hp -= 600;
      cpu.noDamageTimer = 0; cpu.isHealing = false;
      if (cpu.hp <= 0) { cpu.hp = 0; cpu.alive = false; cpu.effects.push({ type: 'death', timer: 2 }); }
      cpu.effects.push({ type: 'love-letter', timer: 1.5 });
      return;
    } else if (isOmori) {
      // Omori T: Sad Poem — stun self 1s then debuff enemies
      cpu.cdT = fighter.abilities[3].cooldown;
      cpu.omoriSadPoemPause = fighter.abilities[3].pauseDuration || 1;
      cpu.stunned = fighter.abilities[3].pauseDuration || 1;
      cpu.effects.push({ type: 'omori-sad-poem', timer: 1.5 });
      return;
    } else if (isPyro) {
      // Pyromaniac T: RAIN RAIN RAIN
      cpu.cdT = fighter.abilities[3].cooldown;
      const abil = fighter.abilities[3];
      const rainRadius = (abil.fireRadius || 5) * GAME_TILE;
      let dmg = abil.damage || 10;
      if (cpu.supportBuff > 0) dmg *= 1.5;
      if (cpu.pyroFireBuffTimer > 0) dmg *= 2;
      for (const t of gamePlayers) {
        if (t.id === cpu.id || !t.alive) continue;
        if (gameMode === 'teams' && cpu.team && t.team === cpu.team) continue;
        const d = Math.sqrt((t.x - cpu.x) ** 2 + (t.y - cpu.y) ** 2);
        if (d < rainRadius) {
          dealDamage(cpu, t, dmg);
          _applyPyroBurn(t, abil.burnDPS || 100, abil.burnDuration || 3);
          t.effects.push({ type: 'hit', timer: 0.3 });
        }
      }
      if (!cpu.pyroFireZones) cpu.pyroFireZones = [];
      cpu.pyroFireZones.push({ x: cpu.x, y: cpu.y, timer: abil.fireDuration || 10, radius: abil.fireRadius || 5 });
      cpu.pyroRainTimer = 2; cpu.pyroRainX = cpu.x; cpu.pyroRainY = cpu.y;
      cpu.effects.push({ type: 'pyro-rain', timer: 2 });
      // Grant burn immunity for 10s
      cpu.pyroBurnImmuneTimer = 10;
      if (cpu.pyroBurnTimers) cpu.pyroBurnTimers = [];
      return;
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

  } // end if (!cpu.illusionM1Only)

  // M1 — primary attack
  // Queen Bee Unicorn: blocks M1 attacks while alive (except creator)
  const cpuQueenBee = gamePlayers.find(p => p.alive && p.isSummon && p.summonType === 'queenbee-unicorn');
  const cpuQueenBeeBlocked = cpuQueenBee && cpuQueenBee.summonOwner !== cpu.id;
  if (cpu.cdM1 <= 0 && !cpuQueenBeeBlocked && !cpu.illusionNoAttack) {
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
    } else if (isCricket) {
      if (dist < (fighter.abilities[0].range || 1.2) * GAME_TILE) {
        cpuCricketBatSwing(cpu, target, aimNx, aimNy);
      }
    } else if (isDeer) {
      if (cpu.deerSeerTimer <= 0) {
        cpuDeerEngineer(cpu);
      }
    } else if (isNoli) {
      // Tendril Stab melee
      if (!cpu.noliVoidRushActive && dist < (fighter.abilities[0].range || 1.5) * GAME_TILE) {
        cpuNoliTendrilStab(cpu, target, aimNx, aimNy);
      }
    } else if (isCat) {
      // Cat Scratch melee
      if (dist < (fighter.abilities[0].range || 0.9) * GAME_TILE) {
        cpuCatScratch(cpu, target, aimNx, aimNy);
      }
    } else if (isNapoleon) {
      // Napoleon Sword melee
      if (dist < (fighter.abilities[0].range || 1.5) * GAME_TILE) {
        cpuNapoleonSword(cpu, target, aimNx, aimNy);
      }
    } else if (isModerator) {
      // Ban Hammer melee
      if (dist < (fighter.abilities[0].range || 1.5) * GAME_TILE) {
        const abil = fighter.abilities[0];
        cpu.cdM1 = abil.cooldown;
        let baseDmg = abil.damage || 100;
        if (cpu.modServerUpdateTimer > 0) baseDmg = Math.round(baseDmg * 1.5);
        dealDamage(cpu, target, baseDmg, false);
        _lastDealDamageWasM1 = true;
        // 10% chance to teleport target to random safe position
        if (Math.random() < 0.1) {
          const safe = getRandomSafePosition();
          if (safe) {
            target.x = safe.x;
            target.y = safe.y;
          }
        }
        cpu.effects.push({ type: 'ban-hammer', timer: 0.5, aimNx: aimNx, aimNy: aimNy });
      }
    } else if (isDnd) {
      // D&D M1: race-dependent attack
      const race = cpu.dndRace || 'human';
      const abil = fighter.abilities[0];
      if (race === 'elf') {
        // Bow: ranged attack — unlimited range (stops at wall/sea)
        if (dist < 15 * GAME_TILE) {
          cpu.cdM1 = abil.cooldown;
          const spd = (abil.bowSpeed || 40) * GAME_TILE / 10;
          let dmg = abil.damage + (cpu.dndWeaponBonus || 0);
          if (cpu.dndD20Active) dmg = 650;
          projectiles.push({
            x: cpu.x, y: cpu.y,
            vx: aimNx * spd, vy: aimNy * spd,
            ownerId: cpu.id, damage: dmg,
            timer: 999, type: 'dnd-arrow',
          });
          cpu.effects.push({ type: 'bow-shot', timer: 0.3 });
        }
      } else if (race === 'dwarf') {
        // Axe: melee, higher damage, slower CD
        if (dist < (abil.range || 1.5) * GAME_TILE) {
          cpu.cdM1 = abil.axeCooldown || 2;
          let dmg = (abil.axeDamage || 300) + (cpu.dndWeaponBonus || 0);
          if (cpu.dndD20Active) dmg = 750;
          dealDamage(cpu, target, dmg, false);
          _lastDealDamageWasM1 = true;
          cpu.effects.push({ type: 'axe-swing', timer: 0.4 });
        }
      } else {
        // Human: sword melee
        if (dist < (abil.range || 1.5) * GAME_TILE) {
          cpu.cdM1 = abil.cooldown;
          let dmg = abil.damage + (cpu.dndWeaponBonus || 0);
          if (cpu.dndD20Active) dmg = 650;
          dealDamage(cpu, target, dmg, false);
          _lastDealDamageWasM1 = true;
          cpu.effects.push({ type: 'sword-slash', timer: 0.3, aimNx, aimNy });
        }
      }
    } else if (isDragon) {
      // Dragon Breath: continuous DPS toward target
      const range = (fighter.abilities[0].range || 4) * GAME_TILE;
      if (dist < range && (cpu.dragonBreathFuel || 0) > 0.5 && !cpu.dragonBeamCharging && !cpu.dragonBeamFiring) {
        if (!cpu.dragonBreathActive) {
          cpu.dragonBreathWindup = 0.2; // windup on first activation
        }
        cpu.dragonBreathActive = true;
        cpu.dragonBreathAimNx = aimNx;
        cpu.dragonBreathAimNy = aimNy;
        cpu.cdM1 = 0.05;
        cpu.effects.push({ type: 'dragon-breath', timer: 0.2, aimNx, aimNy });
      } else {
        cpu.dragonBreathActive = false;
      }
    } else if (fighter.id === 'illusion') {
      // Illusion M1: Teleattack — melee 150, dodge attacks from hit player for 0.5s
      const range = (fighter.abilities[0].range || 1.5) * GAME_TILE;
      if (dist < range) {
        const abil = fighter.abilities[0];
        cpu.cdM1 = abil.cooldown;
        let dmg = abil.damage || 150;
        if (cpu.supportBuff > 0) dmg *= 1.5;
        dealDamage(cpu, target, dmg, false);
        _lastDealDamageWasM1 = true;
        cpu.illusionDodgeTargetId = target.id;
        cpu.illusionDodgeTimer = abil.dodgeDuration || 0.5;
        cpu.effects.push({ type: 'teleattack', timer: 0.2, aimNx, aimNy });
      }
    } else if (fighter.id === 'dogtooth') {
      // Dog Tooth M1: Stab — melee 150 + bleed
      const range = (fighter.abilities[0].range || 1.5) * GAME_TILE;
      if (dist < range) {
        const abil = fighter.abilities[0];
        cpu.cdM1 = abil.cooldown;
        let dmg = abil.damage || 150;
        if (cpu.dogtoothSmileTimer > 0) dmg = 500;
        if (cpu.supportBuff > 0) dmg *= 1.5;
        dealDamage(cpu, target, dmg, false);
        _lastDealDamageWasM1 = true;
        // Apply bleed
        if (!target.poisonTimers) target.poisonTimers = [];
        target.poisonTimers.push({
          sourceId: cpu.id,
          dps: (abil.bleedDamage || 50) / (abil.bleedDuration || 5),
          remaining: abil.bleedDuration || 5
        });
        cpu.effects.push({ type: 'stab', timer: 0.2, aimNx, aimNy });
      }
    } else if (isOmori) {
      // Omori M1: same as Dogtooth stab
      const range = (fighter.abilities[0].range || 1.5) * GAME_TILE;
      if (dist < range) {
        const abil = fighter.abilities[0];
        cpu.cdM1 = abil.cooldown;
        let dmg = abil.damage || 150;
        if (cpu.omoriKelBuffTimer > 0) dmg *= 1.5;
        if (cpu.supportBuff > 0) dmg *= 1.5;
        if (cpu.omoriAubreyBuffTimer > 0 && Math.random() < 0.1) dmg = 600;
        dealDamage(cpu, target, dmg, false);
        _lastDealDamageWasM1 = true;
        if (!target.poisonTimers) target.poisonTimers = [];
        target.poisonTimers.push({
          sourceId: cpu.id,
          dps: (abil.bleedDamage || 50) / (abil.bleedDuration || 5),
          remaining: abil.bleedDuration || 5
        });
        cpu.effects.push({ type: 'stab', timer: 0.2, aimNx, aimNy });
      }
    } else if (isPyro) {
      // Pyromaniac M1: Flamethrower — continuous DPS (like Dragon Breath)
      const range = (fighter.abilities[0].range || 5) * GAME_TILE;
      const effectiveRange = cpu.pyroFireBuffTimer > 0 ? range * 2 : range;
      if (dist < effectiveRange && (cpu.pyroFlameFuel || 0) > 0.5) {
        if (!cpu.pyroFlameActive) {
          cpu.pyroFlameWindup = 0.2;
        }
        cpu.pyroFlameActive = true;
        cpu.pyroFlameNx = aimNx;
        cpu.pyroFlameNy = aimNy;
        cpu.cdM1 = 0.05;
        cpu.effects.push({ type: 'pyro-flame', timer: 0.2, aimNx, aimNy });
      } else {
        cpu.pyroFlameActive = false;
      }
    } else if (isHeavyRope) {
      // Heavy Rope CPU AI
      let ropeRange = (fighter.abilities[0].range || 2.5) * GAME_TILE;
      if (cpu.ropeGripActive) ropeRange *= 0.5;

      // T: Rope Grab — use when far from target to close distance
      if (cpu.cdT <= 0 && dist > 6 * GAME_TILE) {
        cpu.cdT = fighter.abilities[3].cooldown;
        // Simulate grapple: find nearest obstacle in target direction
        const grabSpeed = (fighter.abilities[3].speed || 40) * GAME_TILE;
        let gx = cpu.x, gy = cpu.y;
        const step = GAME_TILE * 0.5;
        for (let d = step; d < 50 * GAME_TILE; d += step) {
          const tx = cpu.x + aimNx * d;
          const ty = cpu.y + aimNy * d;
          if (!canMoveTo(tx, ty, GAME_TILE * PLAYER_RADIUS_RATIO)) {
            // Found obstacle — teleport just outside it
            gx = cpu.x + aimNx * (d - step);
            gy = cpu.y + aimNy * (d - step);
            break;
          }
        }
        if (canMoveTo(gx, gy, GAME_TILE * PLAYER_RADIUS_RATIO) && (gx !== cpu.x || gy !== cpu.y)) {
          cpu.x = gx; cpu.y = gy;
          cpu.effects.push({ type: 'rope-grab-land', timer: 0.3 });
        }
      }

      // E: Rope Swing — use when in range and E is off cooldown
      if (cpu.cdE <= 0 && dist < ropeRange && !cpu.ropeSwingActive) {
        cpu.ropeSwingActive = true;
        cpu.ropeSwingNx = aimNx;
        cpu.ropeSwingNy = aimNy;
      }
      // Release swing when active and target is in range
      if (cpu.ropeSwingActive && dist < ropeRange) {
        let swingDmg = fighter.abilities[1].damage || 500;
        if (cpu.ropeGripActive) swingDmg = fighter.abilities[2].swingDamage || 750;
        if (cpu.supportBuff > 0) swingDmg *= 1.5;
        const nx = cpu.ropeSwingNx; const ny = cpu.ropeSwingNy;
        for (const t of gamePlayers) {
          if (t.id === cpu.id || !t.alive) continue;
          if (t.isSummon && t.summonOwner === cpu.id) continue;
          if (gameMode === 'teams' && cpu.team && t.team === cpu.team) continue;
          const tdx = t.x - cpu.x; const tdy = t.y - cpu.y;
          const td = Math.sqrt(tdx * tdx + tdy * tdy);
          if (td > ropeRange) continue;
          const dot = (tdx * nx + tdy * ny) / (td || 1);
          if (dot < 0.3) continue;
          dealDamage(cpu, t, swingDmg);
          t.effects.push({ type: 'hit', timer: 0.5 });
        }
        cpu.ropeSwingActive = false;
        cpu.cdE = fighter.abilities[1].cooldown;
        cpu.stunned = 0.5;
        cpu.effects.push({ type: 'rope-swing-release', timer: 0.4, aimNx: nx, aimNy: ny });
      }

      // R: Rope Grip toggle — use when close to enemies
      if (cpu.cdR <= 0 && dist < 1.5 * GAME_TILE && !cpu.ropeGripActive) {
        cpu.ropeGripActive = true;
        cpu.effects.push({ type: 'rope-grip-on', timer: 0.5 });
      } else if (cpu.ropeGripActive && dist > 3 * GAME_TILE) {
        cpu.ropeGripActive = false;
        cpu.effects.push({ type: 'rope-grip-off', timer: 0.5 });
      }

      // M1: Rope Hit
      if (cpu.cdM1 <= 0 && dist < ropeRange) {
        let ropeDmg = fighter.abilities[0].damage || 200;
        if (cpu.ropeGripActive) ropeDmg = fighter.abilities[2].m1Damage || 300;
        if (cpu.supportBuff > 0) ropeDmg *= 1.5;
        cpu.cdM1 = cpu.ropeSecondGripTimer > 0 ? 0.5 : (fighter.abilities[0].cooldown || 1.5);
        for (const t of gamePlayers) {
          if (t.id === cpu.id || !t.alive) continue;
          if (t.isSummon && t.summonOwner === cpu.id) continue;
          if (gameMode === 'teams' && cpu.team && t.team === cpu.team) continue;
          const tdx = t.x - cpu.x; const tdy = t.y - cpu.y;
          const td = Math.sqrt(tdx * tdx + tdy * tdy);
          if (td > ropeRange) continue;
          const dot = (tdx * aimNx + tdy * aimNy) / (td || 1);
          if (dot < 0.3) continue;
          dealDamage(cpu, t, ropeDmg);
          t.effects.push({ type: 'hit', timer: 0.3 });
        }
        cpu.effects.push({ type: 'rope-hit', timer: 0.25, aimNx, aimNy });
      }
    } else {
      if (dist < fighter.abilities[0].range * GAME_TILE) {
        cpuSwordSwing(cpu, target, aimNx, aimNy);
      }
    }
  }
}

function cpuUseF(cpu, target, fAbil) {
  const fighter = cpu.fighter;
  const fid = fighter.id;

  if (fid === 'poker') {
    // Full House: next move guaranteed best option
    cpu.move4Uses++;
    cpu.pokerFullHouseActive = true;
    cpu.cdF = fAbil.cooldown;
    cpu.effects.push({ type: 'full-house', timer: 2.0 });
    return;
  }

  if (fid === 'filbus') {
    // Analogus: only use on the real (local/human) player
    const aliveNonSummon = gamePlayers.filter(p => p.alive && !p.isSummon);
    if (aliveNonSummon.length <= 2) return;
    // Find the real player (non-CPU, non-summon)
    const realPlayer = gamePlayers.find(p => p.alive && !p.isSummon && !p.isCPU);
    if (!realPlayer) return;
    // 3-player HP check
    if (aliveNonSummon.length === 3) {
      const thirdPlayer = aliveNonSummon.find(p => p.id !== cpu.id && p.id !== realPlayer.id);
      if (thirdPlayer && thirdPlayer.hp <= thirdPlayer.maxHp * 0.5) return;
    }
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    // Cleanup existing effects on target
    if (realPlayer.inBackrooms) _exitBackrooms(realPlayer, 'new-analogus');
    if (realPlayer.hasAlternate && realPlayer.alternateId) {
      const oldAlt = gamePlayers.find(a => a.id === realPlayer.alternateId);
      if (oldAlt && oldAlt.alive) { oldAlt.alive = false; oldAlt.hp = 0; }
      realPlayer.hasAlternate = false; realPlayer.alternateId = null;
    }
    const roll = Math.random();
    if (roll < 0.33) {
      // Backrooms
      const mapW = gameMap.cols, mapH = gameMap.rows;
      let bestDoorR = -1, bestDoorC = -1, bestDoorDist = 0;
      for (let attempt = 0; attempt < 40; attempt++) {
        const rr = Math.floor(Math.random() * mapH);
        const cc = Math.floor(Math.random() * mapW);
        if (gameMap.tiles[rr] && gameMap.tiles[rr][cc] !== undefined
            && gameMap.tiles[rr][cc] !== TILE.WATER && gameMap.tiles[rr][cc] !== TILE.ROCK) {
          const dd = Math.sqrt((rr - Math.floor(realPlayer.y / GAME_TILE)) ** 2 +
                               (cc - Math.floor(realPlayer.x / GAME_TILE)) ** 2);
          if (dd > bestDoorDist) { bestDoorDist = dd; bestDoorR = rr; bestDoorC = cc; }
        }
      }
      if (bestDoorR < 0) { bestDoorR = 1; bestDoorC = 1; }
      realPlayer.inBackrooms = true;
      realPlayer.backroomsDoorX = (bestDoorC + 0.5) * GAME_TILE;
      realPlayer.backroomsDoorY = (bestDoorR + 0.5) * GAME_TILE;
      realPlayer.backroomsTimer = 30;
      const chaserId = 'br-chaser-' + realPlayer.id + '-' + Date.now();
      const chaserFighter = getFighter('fighter');
      const chaser = createPlayerState(
        { id: chaserId, name: '???', color: '#8b8000', fighterId: 'fighter' },
        { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) }, chaserFighter
      );
      const chaserRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
      if (canMoveTo(cpu.x, cpu.y, chaserRadius)) { chaser.x = cpu.x; chaser.y = cpu.y; }
      else { const safe = getRandomSafePosition(); chaser.x = safe.x; chaser.y = safe.y; }
      chaser.hp = 999999; chaser.maxHp = 999999;
      chaser.isSummon = true; chaser.summonOwner = cpu.id; chaser.summonType = 'backrooms-chaser';
      chaser.summonSpeed = realPlayer.fighter.speed * 1.5;
      chaser.summonDamage = 999999; chaser.summonAttackCD = 0.5; chaser.summonAttackTimer = 0;
      chaser.summonTargetId = realPlayer.id; chaser.isCPU = true; chaser.noCloneHeal = true;
      gamePlayers.push(chaser);
      realPlayer.backroomsChaserId = chaserId;
      realPlayer.effects.push({ type: 'backrooms-enter', timer: 2.0 });
    } else if (roll < 0.66) {
      // Alternate
      const altId = 'alternate-' + realPlayer.id + '-' + Date.now();
      const alt = createPlayerState(
        { id: altId, name: realPlayer.name, color: realPlayer.color, fighterId: realPlayer.fighter.id },
        { r: Math.floor(realPlayer.y / GAME_TILE), c: Math.floor(realPlayer.x / GAME_TILE) }, realPlayer.fighter
      );
      const altRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
      let altPlaced = false;
      for (let attempt = 0; attempt < 20; attempt++) {
        const angle = Math.random() * Math.PI * 2;
        const d = GAME_TILE * (6 + Math.random() * 2);
        const tryX = realPlayer.x + Math.cos(angle) * d;
        const tryY = realPlayer.y + Math.sin(angle) * d;
        if (canMoveTo(tryX, tryY, altRadius)) { alt.x = tryX; alt.y = tryY; altPlaced = true; break; }
      }
      if (!altPlaced) { const safe = getRandomSafePosition(); alt.x = safe.x; alt.y = safe.y; }
      alt.hp = 500; alt.maxHp = 500;
      alt.isSummon = true; alt.summonOwner = cpu.id; alt.summonType = 'alternate';
      alt.summonSpeed = realPlayer.fighter.speed * 0.9;
      alt.summonDamage = 999999; alt.summonAttackCD = 0.5; alt.summonAttackTimer = 0;
      alt.summonTargetId = realPlayer.id; alt.isCPU = true; alt.noCloneHeal = true;
      gamePlayers.push(alt);
      realPlayer.hasAlternate = true; realPlayer.alternateId = altId;
      realPlayer.effects.push({ type: 'alternate-spawn', timer: 2.0 });
    } else {
      // Boisvert — spawn Room entities on the real player only
      const roomId = 'room-' + realPlayer.id + '-' + Date.now();
      const roomFighter = getFighter('fighter');
      const room = createPlayerState(
        { id: roomId, name: 'Room', color: '#000', fighterId: 'fighter' },
        { r: Math.floor(realPlayer.y / GAME_TILE), c: Math.floor(realPlayer.x / GAME_TILE) }, roomFighter
      );
      const roomRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
      let roomPlaced = false;
      for (let ra = 0; ra < 16; ra++) {
        const angle = Math.random() * Math.PI * 2;
        const d = GAME_TILE * (2 + Math.random() * 2);
        const tryX = realPlayer.x + Math.cos(angle) * d;
        const tryY = realPlayer.y + Math.sin(angle) * d;
        if (canMoveTo(tryX, tryY, roomRadius)) { room.x = tryX; room.y = tryY; roomPlaced = true; break; }
      }
      if (!roomPlaced) { const safe = getRandomSafePosition(); room.x = safe.x; room.y = safe.y; }
      room.hp = 500; room.maxHp = 500;
      room.isSummon = true; room.summonOwner = cpu.id; room.summonType = 'room';
      room.summonSpeed = 2.5; room.summonDamage = 0;
      room.summonAttackCD = 1; room.summonAttackTimer = 0;
      room.summonTargetId = realPlayer.id; room.roomDPS = 50;
      room.isCPU = true; room.noCloneHeal = true;
      gamePlayers.push(room);
    }
    return;
  }

  if (fid === 'onexonexonex') {
    // c00lkidd summon
    if (cpu.coolkiddId) return; // already has one
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    const summonId = 'coolkidd-' + cpu.id + '-' + Date.now();
    const summon = createPlayerState(
      { id: summonId, name: 'c00lkidd', color: '#ff0000', fighterId: 'onexonexonex' },
      { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) }, fighter
    );
    summon.x = cpu.x + (Math.random() - 0.5) * GAME_TILE * 2;
    summon.y = cpu.y + (Math.random() - 0.5) * GAME_TILE * 2;
    summon.hp = fAbil.summonHp || 500; summon.maxHp = fAbil.summonHp || 500;
    summon.isSummon = true; summon.summonOwner = cpu.id; summon.summonType = 'coolkidd';
    summon.summonSpeed = 0; summon.summonDamage = 0;
    summon.summonAttackCD = fAbil.summonFireCD || 4; summon.summonAttackTimer = 0;
    summon.summonProjectileSpeed = fAbil.projectileSpeed || 30;
    gamePlayers.push(summon);
    cpu.coolkiddId = summonId;
    cpu.effects.push({ type: 'coolkidd-spawn', timer: 1.5 });
    return;
  }

  if (fid === 'cricket') {
    // Bowler summon
    if (cpu.bowlerId) return;
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    const summonId = 'bowler-' + cpu.id + '-' + Date.now();
    const summon = createPlayerState(
      { id: summonId, name: 'Bowler', color: '#228b22', fighterId: 'cricket' },
      { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) }, fighter
    );
    summon.x = cpu.x + (Math.random() - 0.5) * GAME_TILE * 2;
    summon.y = cpu.y + (Math.random() - 0.5) * GAME_TILE * 2;
    summon.hp = fAbil.summonHp || 300; summon.maxHp = fAbil.summonHp || 300;
    summon.isSummon = true; summon.summonOwner = cpu.id; summon.summonType = 'bowler';
    summon.summonSpeed = 0; summon.summonDamage = fAbil.damage || 200;
    summon.summonAttackCD = fAbil.summonFireCD || 5; summon.summonAttackTimer = 0;
    gamePlayers.push(summon);
    cpu.bowlerId = summonId;
    cpu.effects.push({ type: 'bowler-spawn', timer: 1.5 });
    return;
  }

  if (fid === 'deer') {
    // Crabs
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    const count = fAbil.crabCount || 5;
    if (!cpu.crabIds) cpu.crabIds = [];
    for (let i = 0; i < count; i++) {
      const crabId = 'crab-' + cpu.id + '-' + i + '-' + Date.now();
      const crab = createPlayerState(
        { id: crabId, name: 'Crab', color: '#ff6347', fighterId: 'deer' },
        { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) }, fighter
      );
      crab.x = cpu.x + (Math.random() - 0.5) * GAME_TILE * 3;
      crab.y = cpu.y + (Math.random() - 0.5) * GAME_TILE * 3;
      const crabRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
      if (!canMoveTo(crab.x, crab.y, crabRadius)) { crab.x = cpu.x; crab.y = cpu.y; }
      crab.hp = fAbil.crabHp || 400; crab.maxHp = fAbil.crabHp || 400;
      crab.isSummon = true; crab.summonOwner = cpu.id; crab.summonType = 'crab';
      crab.summonSpeed = fAbil.crabSpeed || 2.0; crab.summonDamage = fAbil.damage || 200;
      crab.summonAttackCD = fAbil.crabAttackCD || 1; crab.summonAttackTimer = 0;
      gamePlayers.push(crab);
      cpu.crabIds.push(crabId);
    }
    cpu.effects.push({ type: 'crab-spawn', timer: 2.0 });
    return;
  }

  if (fid === 'noli') {
    // John Doe
    if (cpu.johnDoeId) {
      const old = gamePlayers.find(p => p.id === cpu.johnDoeId);
      if (old && old.alive) return; // already active
    }
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    const edgeTiles = [];
    for (let c = 0; c < gameMap.cols; c++) {
      if (gameMap.tiles[0] && gameMap.tiles[0][c] !== TILE.WATER && gameMap.tiles[0][c] !== TILE.ROCK) edgeTiles.push({ r: 0, c });
      if (gameMap.tiles[gameMap.rows - 1] && gameMap.tiles[gameMap.rows - 1][c] !== TILE.WATER && gameMap.tiles[gameMap.rows - 1][c] !== TILE.ROCK) edgeTiles.push({ r: gameMap.rows - 1, c });
    }
    for (let r = 1; r < gameMap.rows - 1; r++) {
      if (gameMap.tiles[r] && gameMap.tiles[r][0] !== TILE.WATER && gameMap.tiles[r][0] !== TILE.ROCK) edgeTiles.push({ r, c: 0 });
      if (gameMap.tiles[r] && gameMap.tiles[r][gameMap.cols - 1] !== TILE.WATER && gameMap.tiles[r][gameMap.cols - 1] !== TILE.ROCK) edgeTiles.push({ r, c: gameMap.cols - 1 });
    }
    const edgeSpawn = edgeTiles.length > 0 ? edgeTiles[Math.floor(Math.random() * edgeTiles.length)] : { r: 0, c: 0 };
    const summonId = 'johndoe-' + cpu.id + '-' + Date.now();
    const summon = createPlayerState(
      { id: summonId, name: 'John Doe', color: '#8b0000', fighterId: 'noli' }, edgeSpawn, fighter
    );
    summon.hp = fAbil.summonHp || 500; summon.maxHp = fAbil.summonHp || 500;
    summon.isSummon = true; summon.summonOwner = cpu.id; summon.summonType = 'johndoe';
    summon.summonSpeed = 0; summon.summonDamage = fAbil.damage || 500;
    summon.summonAttackCD = fAbil.summonFireCD || 10; summon.summonAttackTimer = fAbil.summonFireCD || 10;
    summon.spikeDuration = fAbil.spikeDuration || 5; summon.touchDPS = 0;
    gamePlayers.push(summon);
    cpu.johnDoeId = summonId;
    cpu.effects.push({ type: 'johndoe-spawn', timer: 1.5 });
    return;
  }

  if (fid === 'explodingcat') {
    // Unicorn summon
    if (cpu.catUnicornId) return;
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    const uniRoll = Math.random();
    let uniType, uniName, uniColor;
    if (uniRoll < 0.33) { uniType = 'destructive-unicorn'; uniName = 'Extremely Destructive Unicorn'; uniColor = '#ff2200'; }
    else if (uniRoll < 0.66) { uniType = 'queenbee-unicorn'; uniName = 'Queen Bee Unicorn'; uniColor = '#ffd700'; }
    else { uniType = 'seductive-unicorn'; uniName = 'Seductive Unicorn'; uniColor = '#ff69b4'; }
    const uniId = 'unicorn-' + cpu.id + '-' + Date.now();
    const uniFighter = getFighter('fighter');
    const uni = createPlayerState(
      { id: uniId, name: uniName, color: uniColor, fighterId: 'fighter' },
      { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) }, uniFighter
    );
    uni.x = cpu.x + (Math.random() - 0.5) * GAME_TILE * 3;
    uni.y = cpu.y + (Math.random() - 0.5) * GAME_TILE * 3;
    uni.hp = 500; uni.maxHp = 500;
    uni.isSummon = true; uni.summonOwner = cpu.id; uni.summonType = uniType;
    uni.summonSpeed = 3.0; uni.summonDamage = uniType === 'destructive-unicorn' ? 999 : 0;
    uni.summonAttackCD = 0.5; uni.summonAttackTimer = 0;
    uni.isCPU = true; uni.noCloneHeal = true;
    gamePlayers.push(uni);
    cpu.catUnicornId = uniId;
    cpu.effects.push({ type: 'unicorn-spawn', timer: 1.5 });
    return;
  }

  if (fid === 'napoleon') {
    // Light Infantry
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    const count = fAbil.infantryCount || 3;
    if (!cpu.napoleonInfantryIds) cpu.napoleonInfantryIds = [];
    for (let i = 0; i < count; i++) {
      const infId = 'infantry-' + cpu.id + '-f-' + i + '-' + Date.now();
      const inf = createPlayerState(
        { id: infId, name: 'Infantryman', color: '#2c3e50', fighterId: 'napoleon' },
        { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) }, fighter
      );
      inf.x = cpu.x + (Math.random() - 0.5) * GAME_TILE * 3;
      inf.y = cpu.y + (Math.random() - 0.5) * GAME_TILE * 3;
      const infRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
      if (!canMoveTo(inf.x, inf.y, infRadius)) { inf.x = cpu.x; inf.y = cpu.y; }
      inf.hp = fAbil.infantryHp || 50; inf.maxHp = fAbil.infantryHp || 50;
      inf.isSummon = true; inf.summonOwner = cpu.id; inf.summonType = 'napoleon-infantry';
      inf.summonSpeed = fAbil.infantrySpeed || 2.0; inf.summonDamage = fAbil.damage || 100;
      inf.summonAttackCD = fAbil.infantryFireCD || 1; inf.summonAttackTimer = 0;
      inf.summonProjectileSpeed = fAbil.infantryProjectileSpeed || 38;
      inf.summonProjectileRange = fAbil.infantryRange || 0.8;
      gamePlayers.push(inf);
      cpu.napoleonInfantryIds.push(infId);
    }
    cpu.effects.push({ type: 'infantry-spawn', timer: 1.5 });
    return;
  }

  if (fid === 'moderator') {
    // Firewall: invincible + invisible for 5s
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    cpu.modFirewallTimer = fAbil.duration || 5;
    cpu.effects.push({ type: 'firewall', timer: (fAbil.duration || 5) + 0.5 });
    return;
  }

  if (fid === 'dnd') {
    // Sidekick
    if (cpu.dndSidekickId) {
      const oldSk = gamePlayers.find(p => p.id === cpu.dndSidekickId);
      if (oldSk && oldSk.alive) return;
    }
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    const skId = 'dnd-sidekick-' + cpu.id + '-' + Date.now();
    const sk = createPlayerState(
      { id: skId, name: cpu.name + "'s Sidekick", color: cpu.color || '#daa520', fighterId: 'dnd' },
      { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) }, fighter
    );
    const skRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
    const angle = Math.random() * Math.PI * 2;
    sk.x = cpu.x + Math.cos(angle) * GAME_TILE * 2;
    sk.y = cpu.y + Math.sin(angle) * GAME_TILE * 2;
    if (!canMoveTo(sk.x, sk.y, skRadius)) { const safe = getRandomSafePosition(); sk.x = safe.x; sk.y = safe.y; }
    sk.hp = Math.floor(cpu.maxHp / 2); sk.maxHp = Math.floor(cpu.maxHp / 2);
    sk.isSummon = true; sk.summonOwner = cpu.id; sk.summonType = 'dnd-sidekick';
    sk.dndRace = cpu.dndRace || 'human';
    sk.summonSpeed = 3.0; sk.summonDamage = 100 + (cpu.dndWeaponBonus || 0);
    sk.summonAttackCD = sk.dndRace === 'dwarf' ? 2 : 0.5; sk.summonAttackTimer = 0;
    sk.isCPU = true;
    gamePlayers.push(sk);
    cpu.dndSidekickId = skId;
    cpu.effects.push({ type: 'dnd-sidekick-spawn', timer: 1.5 });
    return;
  }

  if (fid === 'dogtooth') {
    // Dog Tooth F: The Final Battle — CPU spawns Complex Room to fight
    if (cpu.dogtoothFUsed) return;
    cpu.dogtoothFUsed = true;
    cpu.move4Uses++;
    cpu.dogtoothInComplex = true;
    // Kill Ouriel (don't let it transform into a room)
    if (cpu.dogtoothOurielId) {
      const ouriel = gamePlayers.find(p => p.id === cpu.dogtoothOurielId);
      if (ouriel && ouriel.alive) { ouriel.alive = false; ouriel.hp = 0; ouriel.effects.push({ type: 'death', timer: 2 }); }
      cpu.dogtoothOurielId = null;
      cpu.dogtoothOurielHp = null;
      cpu.dogtoothOurielHitsLeft = null;
    }
    const roomId = 'complex-room-' + cpu.id + '-' + Date.now();
    const roomFighter = { id: 'complex-room', name: 'Room', hp: 1300, healAmount: 0, healDelay: 999, healTick: 999, speed: 1.8, abilities: [] };
    const safe = getRandomSafePosition();
    const room = createPlayerState(
      { id: roomId, name: 'Room', color: '#000' },
      { r: Math.floor(safe.y / GAME_TILE), c: Math.floor(safe.x / GAME_TILE) },
      roomFighter
    );
    room.x = safe.x; room.y = safe.y;
    room.hp = 1300; room.maxHp = 1300;
    room.isSummon = true; room.summonOwner = 'none';
    room.summonType = 'complex-room';
    room.summonTargetId = cpu.id;
    room.summonSpeed = 1.8;
    room.summonDamage = 0;
    room.summonAttackCD = 999;
    room.summonAttackTimer = 0;
    room.complexDPS = 40;
    room.isCPU = true;
    gamePlayers.push(room);
    cpu.dogtoothComplexRoomId = roomId;
    cpu.effects.push({ type: 'complex-enter', timer: 2.0 });
    return;
  }

  if (fid === 'omori') {
    // Omori F: Headspace toggle — CPU toggles on when fighting, off when retreating
    if (!cpu.omoriHeadspaceActive && hpFrac > 0.4) {
      cpu.omoriHeadspaceActive = true;
      for (const pid of (cpu.omoriPartyIds || [])) {
        const pm = gamePlayers.find(p => p.id === pid && p.alive);
        if (pm) pm.omoriHeadspaceActive = true;
      }
    } else if (cpu.omoriHeadspaceActive && hpFrac < 0.3) {
      cpu.omoriHeadspaceActive = false;
      for (const pid of (cpu.omoriPartyIds || [])) {
        const pm = gamePlayers.find(p => p.id === pid && p.alive);
        if (pm) pm.omoriHeadspaceActive = false;
      }
    }
    return;
  }

  if (fid === 'heavyrope') {
    // Heavy Rope F: Second Grip — faster M1 + wider shield
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    cpu.ropeSecondGripTimer = fAbil.duration || 10;
    cpu.effects.push({ type: 'rope-second-grip', timer: (fAbil.duration || 10) + 0.5 });
    return;
  }

  if (fid === 'pyromaniac') {
    // Pyromaniac F: Wildfire — set all grass tiles on fire
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    if (!cpu.pyroFireZones) cpu.pyroFireZones = [];
    for (let r = 0; r < gameMap.rows; r++) {
      for (let c = 0; c < gameMap.cols; c++) {
        if (gameMap.tiles[r][c] === TILE.GRASS) {
          const fx = c * GAME_TILE + GAME_TILE / 2;
          const fy = r * GAME_TILE + GAME_TILE / 2;
          cpu.pyroFireZones.push({ x: fx, y: fy, timer: fAbil.grassFireDuration || 10, radius: 0.6, isGrassFire: true, burnDelay: fAbil.burnDelay || 3, burnDuration: fAbil.burnDuration || 5 });
        }
      }
    }
    cpu.effects.push({ type: 'pyro-wildfire', timer: 2 });
    return;
  }

  // Default (Fighter): Potion — heal 300 over 3s
  if (cpu.hp < cpu.maxHp * 0.5) {
    cpu.move4Uses++;
    cpu.cdF = fAbil.cooldown;
    cpu.potionHealPool = fAbil.healAmount || 300;
    cpu.potionHealTimer = fAbil.healDuration || 3;
    cpu.effects.push({ type: 'potion', timer: (fAbil.healDuration || 3) + 0.5 });
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
    if (t.id === cpu.id || !t.alive || t.isSummon) continue;
    const dx = t.x - cpu.x; const dy = t.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > mediumRange) continue;
    if (dist <= closeRange) {
      if (t.hp <= execThresh) { dealDamage(cpu, t, t.hp); }
      else { t.stunned = stunDur; t.effects.push({ type: 'stun', timer: stunDur }); }
    }
    if (t.fighter && t.fighter.abilities) {
      t.cdM1 = t.fighter.abilities[0] ? t.fighter.abilities[0].cooldown : 0;
      t.cdE = t.fighter.abilities[1] ? t.fighter.abilities[1].cooldown : 0;
      t.cdR = t.fighter.abilities[2] ? t.fighter.abilities[2].cooldown : 0;
      t.cdT = t.fighter.abilities[3] ? t.fighter.abilities[3].cooldown : 0;
    }
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
  const range = (isTable ? (abil.tableRange || 3.2) : (abil.range || 2.5)) * GAME_TILE;
  let baseDmg = isTable ? (abil.tableDamage || 400) : (abil.damage || 250);
  if (cpu.supportBuff > 0) baseDmg *= 1.5;
  if (cpu.intimidated > 0) baseDmg *= 0.5;
  const initialHitIds = [cpu.id];
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    if (t.isSummon && t.summonOwner === cpu.id) continue;
    const dx = t.x - cpu.x; const dy = t.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > range) continue;
    const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
    if (dot < 0) continue;
    dealDamage(cpu, t, baseDmg);
    initialHitIds.push(t.id);
  }
  cpu.effects.push({ type: isTable ? 'table-swing' : 'chair-swing', timer: 0.8, aimNx, aimNy });
  if (!isTable) {
    cpu.chairSwingTimer = 0.7;
    cpu.chairSwingAimNx = aimNx; cpu.chairSwingAimNy = aimNy;
    cpu.chairSwingRange = range;
    cpu.chairSwingDmg = Math.round(baseDmg * 0.5);
    cpu.chairSwingHitIds = initialHitIds.slice();
  }
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
  let dmg = abil.damage;
  if (cpu.supportBuff > 0) dmg *= 1.5;
  if (cpu.intimidated > 0) dmg *= 0.5;
  const baseAngle = Math.atan2(aimNy, aimNx);
  // Close-range slash: 50 bonus damage to anyone within melee range in front
  const slashRange = 1.5 * GAME_TILE;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    if (t.isSummon && t.summonOwner === cpu.id) continue;
    const sdx = t.x - cpu.x; const sdy = t.y - cpu.y;
    const sDist = Math.sqrt(sdx * sdx + sdy * sdy);
    if (sDist > slashRange) continue;
    const toAngle = Math.atan2(sdy, sdx);
    let angleDiff = toAngle - baseAngle;
    while (angleDiff > Math.PI) angleDiff -= Math.PI * 2;
    while (angleDiff < -Math.PI) angleDiff += Math.PI * 2;
    if (Math.abs(angleDiff) > Math.PI / 2) continue;
    dealDamage(cpu, t, 50);
  }
  cpu.effects.push({ type: 'mass-infection-slash', timer: 0.3, aimNx, aimNy });
  // Invisible shockwave projectiles
  const waveCount = 7;
  const totalSpread = Math.PI;
  const spd = 12 * GAME_TILE / 10;
  for (let i = 0; i < waveCount; i++) {
    const angle = baseAngle + (i - (waveCount - 1) / 2) * (totalSpread / (waveCount - 1));
    const vx = Math.cos(angle) * spd;
    const vy = Math.sin(angle) * spd;
    projectiles.push({
      x: cpu.x, y: cpu.y, vx, vy,
      ownerId: cpu.id, damage: dmg,
      timer: 10.0, type: 'shockwave',
      poisonDPS: abil.poisonDPS || 50,
      poisonDuration: abil.poisonDuration || 3,
    });
  }
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
      cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
      totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
      supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
      noDamageTimer: 0, healTickTimer: 0, isHealing: false,
      specialJumping: false, specialAiming: false,
      specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
      effects: [],
      blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
      chairCharges: 0, isCraftingChair: false, craftTimer: 0,
      isEatingChair: false, eatTimer: 0, eatHealPool: 0,
      summonId: null, boiledOneActive: false, boiledOneTimer: 0,
      poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
      gearUpTimer: 0, wicketIds: [], driveReflectTimer: 0,
      deerFearTimer: 0, deerFearTargetX: 0, deerFearTargetY: 0,
      deerSeerTimer: 0, deerRobotId: null, iglooX: 0, iglooY: 0, iglooTimer: 0,
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

function cpuCricketBatSwing(cpu, target, aimNx, aimNy) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[0];
  cpu.cdM1 = abil.cooldown;
  const range = (abil.range || 1.2) * GAME_TILE;
  let baseDmg = abil.damage;
  if (cpu.gearUpTimer > 0) baseDmg = Math.round(baseDmg * (fighter.abilities[2].damageBoost || 1.5));
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
  cpu.effects.push({ type: 'bat-swing', timer: 0.2, aimNx, aimNy });
}

function cpuCricketDrive(cpu, target, aimNx, aimNy) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[1];
  const range = (abil.range || 1.5) * GAME_TILE;
  let baseDmg = abil.damage;
  if (cpu.gearUpTimer > 0) baseDmg = Math.round(baseDmg * (fighter.abilities[2].damageBoost || 1.5));
  if (cpu.supportBuff > 0) baseDmg *= 1.5;
  if (cpu.intimidated > 0) baseDmg *= 0.5;
  // Start 1-second reflect window
  cpu.driveReflectTimer = abil.reflectDuration || 1.0;
  // Melee hit with 3s stun
  const stunDur = abil.stunDuration || 3;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    const dx = t.x - cpu.x; const dy = t.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > range) continue;
    const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
    if (dot < 0) continue;
    dealDamage(cpu, t, baseDmg);
    t.stunned = stunDur;
    t.effects.push({ type: 'stun', timer: stunDur });
  }
  cpu.cdE = abil.cooldown || 20;
  cpu.effects.push({ type: 'drive', timer: 0.3, aimNx, aimNy });
}

function cpuCricketWicket(cpu, target) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[3];
  cpu.cdT = abil.cooldown;
  // Remove old wickets
  if (cpu.wicketIds && cpu.wicketIds.length > 0) {
    for (let wi = gamePlayers.length - 1; wi >= 0; wi--) {
      if (cpu.wicketIds.includes(gamePlayers[wi].id)) {
        gamePlayers.splice(wi, 1);
      }
    }
  }
  cpu.wicketIds = [];
  // Place two wickets in a line toward the target
  const dx = target.x - cpu.x; const dy = target.y - cpu.y;
  const dist = Math.sqrt(dx * dx + dy * dy) || 1;
  const nx = dx / dist; const ny = dy / dist;
  const wicketDist = (abil.wicketDistance || 12) * GAME_TILE;
  const midX = cpu.x + nx * wicketDist * 0.5;
  const midY = cpu.y + ny * wicketDist * 0.5;
  const r = GAME_TILE * PLAYER_RADIUS_RATIO;
  for (let w = 0; w < 2; w++) {
    const offset = w === 0 ? -0.5 : 0.5;
    const wx = midX + nx * wicketDist * offset;
    const wy = midY + ny * wicketDist * offset;
    const wicketId = 'wicket-' + cpu.id + '-' + Date.now() + '-' + w;
    const wicket = {
      id: wicketId, name: 'Wicket', color: '#c8a96e',
      x: wx, y: wy,
      hp: abil.wicketHp || 300, maxHp: abil.wicketHp || 300,
      fighter: fighter, alive: true,
      cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
      totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
      supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
      noDamageTimer: 0, healTickTimer: 0, isHealing: false,
      specialJumping: false, specialAiming: false,
      specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
      effects: [],
      blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
      chairCharges: 0, isCraftingChair: false, craftTimer: 0,
      isEatingChair: false, eatTimer: 0, eatHealPool: 0,
      summonId: null, boiledOneActive: false, boiledOneTimer: 0,
      poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
      gearUpTimer: 0, wicketIds: [], driveReflectTimer: 0,
      deerFearTimer: 0, deerFearTargetX: 0, deerFearTargetY: 0,
      deerSeerTimer: 0, deerRobotId: null, iglooX: 0, iglooY: 0, iglooTimer: 0,
      isSummon: true, summonOwner: cpu.id, summonType: 'wicket',
      summonSpeed: 0, summonDamage: 0,
      summonStunDur: 0, summonAttackCD: 999, summonAttackTimer: 0,
    };
    gamePlayers.push(wicket);
    cpu.wicketIds.push(wicketId);
  }
  cpu.effects.push({ type: 'summon', timer: 1.5 });
}

function cpuUseSpecialCricket(cpu, target) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[4];
  cpu.specialUsed = true;
  // CPU aims directly at target (instant, no aiming phase)
  const landX = target.x;
  const landY = target.y;
  const hitRange = GAME_TILE * 1.2;
  let hitSomeone = false;
  let baseDmg = abil.damage;
  if (cpu.gearUpTimer > 0) baseDmg = Math.round(baseDmg * (fighter.abilities[2].damageBoost || 1.5));
  if (cpu.supportBuff > 0) baseDmg *= 1.5;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    const dx = t.x - landX; const dy = t.y - landY;
    if (Math.sqrt(dx * dx + dy * dy) < hitRange) {
      dealDamage(cpu, t, baseDmg);
      hitSomeone = true;
    }
  }
  // Cricket stays in place — ball lands at target
  if (!hitSomeone) {
    cpu.stunned = abil.missStun || 3;
    cpu.hp = Math.max(0, cpu.hp - (abil.missDamage || 200));
    if (cpu.hp <= 0) { cpu.alive = false; cpu.hp = 0; cpu.effects.push({ type: 'death', timer: 2 }); }
    cpu.effects.push({ type: 'stun', timer: abil.missStun || 3 });
  }
  cpu.effects.push({ type: 'land', timer: 0.5 });
}

function cpuDeerSpear(cpu, target, aimNx, aimNy) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[3];
  cpu.cdT = abil.cooldown;
  const range = (abil.range || 1.2) * GAME_TILE;
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
    if (t.isSummon) {
      dealDamage(cpu, t, t.hp); // kills summons instantly
    } else {
      dealDamage(cpu, t, baseDmg);
      t.stunned = Math.max(t.stunned, abil.stunDuration || 3);
      t.effects.push({ type: 'stun', timer: abil.stunDuration || 3 });
    }
  }
  cpu.effects.push({ type: 'deer-spear', timer: 0.2, aimNx, aimNy });
}

function cpuDeerEngineer(cpu) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[0];
  cpu.cdM1 = abil.cooldown;
  // One robot at a time, HP carries over
  let carryHp = abil.robotHp || 500;
  if (cpu.deerRobotId) {
    const oldRobot = gamePlayers.find(p => p.id === cpu.deerRobotId);
    if (oldRobot && oldRobot.alive) carryHp = oldRobot.hp;
    const oldIdx = gamePlayers.findIndex(p => p.id === cpu.deerRobotId);
    if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; _deferredRemoveIds.push(gamePlayers[oldIdx].id); }
  }
  const robotId = 'robot-' + cpu.id + '-' + Date.now();
  const robot = {
    id: robotId, name: 'Deer Robot', color: '#708090',
    x: cpu.x + (Math.random() - 0.5) * GAME_TILE * 2,
    y: cpu.y + (Math.random() - 0.5) * GAME_TILE * 2,
    hp: carryHp, maxHp: abil.robotHp || 500,
    fighter: fighter, alive: true,
    cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
    totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
    supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
    noDamageTimer: 0, healTickTimer: 0, isHealing: false,
    specialJumping: false, specialAiming: false,
    specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
    effects: [],
    blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
    chairCharges: 0, isCraftingChair: false, craftTimer: 0,
    isEatingChair: false, eatTimer: 0, eatHealPool: 0,
    summonId: null, boiledOneActive: false, boiledOneTimer: 0,
    poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
    gearUpTimer: 0, wicketIds: [], driveReflectTimer: 0,
    deerFearTimer: 0, deerFearTargetX: 0, deerFearTargetY: 0,
    deerSeerTimer: 0, deerRobotId: null, iglooX: 0, iglooY: 0, iglooTimer: 0,
    isSummon: true, summonOwner: cpu.id, summonType: 'deer-robot',
    summonSpeed: 0, summonDamage: abil.damage || 100,
    summonStunDur: 0, summonAttackCD: abil.robotFireRate || 1, summonAttackTimer: 0,
  };
  gamePlayers.push(robot);
  cpu.deerRobotId = robotId;
  cpu.deerBuildSlowTimer = 1.0;
  cpu.effects.push({ type: 'summon', timer: 1.5 });
}

function cpuUseSpecialDeer(cpu, target) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[4];
  cpu.specialUsed = true;
  // CPU places igloo directly on target
  cpu.iglooX = target.x;
  cpu.iglooY = target.y;
  cpu.iglooTimer = abil.duration || 5;
  cpu.effects.push({ type: 'igloo', timer: (abil.duration || 5) + 1 });
}

// ── Noli CPU helper functions ──
function cpuNoliTendrilStab(cpu, target, aimNx, aimNy) {
  const abil = cpu.fighter.abilities[0];
  cpu.cdM1 = abil.cooldown;
  let dmg = abil.damage;
  if (cpu.supportBuff > 0) dmg *= 1.5;
  if (cpu.intimidated > 0) dmg *= 0.5;
  const range = (abil.range || 1.5) * GAME_TILE;
  for (const t of gamePlayers) {
    if (t.id === cpu.id || !t.alive) continue;
    if (t.isSummon && t.summonOwner === cpu.id) continue;
    const dx = t.x - cpu.x, dy = t.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist > range) continue;
    const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
    if (dot < 0) continue;
    dealDamage(cpu, t, dmg);
  }
  cpu.effects.push({ type: 'tendril-stab', timer: 0.25, aimNx, aimNy });
}

function cpuNoliVoidRush(cpu, target) {
  const abil = cpu.fighter.abilities[1];
  const dx = target.x - cpu.x, dy = target.y - cpu.y;
  const dist = Math.sqrt(dx * dx + dy * dy) || 1;
  const chain = cpu.noliVoidRushChain;
  const baseSpeed = (abil.dashSpeed || 10) * GAME_TILE / 10;
  const dashSpeed = baseSpeed * (1 + chain * (abil.speedScalePerChain || 0.15));
  cpu.noliVoidRushVx = (dx / dist) * dashSpeed;
  cpu.noliVoidRushVy = (dy / dist) * dashSpeed;
  cpu.noliVoidRushActive = true;
  cpu.noliVoidRushTimer = Infinity; // infinite dash — ends on wall/sea or player hit
  if (cpu.noliVoidRushChain === 0) cpu.cdE = abil.cooldown;
  cpu.effects.push({ type: 'void-rush', timer: 0.5 });
}

function cpuNoliVoidStar(cpu, target) {
  const abil = cpu.fighter.abilities[2];
  cpu.cdR = abil.cooldown;
  cpu.noliVoidStarAiming = true;
  cpu.noliVoidStarAimX = target.x;
  cpu.noliVoidStarAimY = target.y;
  cpu.noliVoidStarTimer = abil.aimTime || 1.5;
  cpu.effects.push({ type: 'void-star-aim', timer: (abil.aimTime || 1.5) + 0.5 });
}

function cpuNoliObservant(cpu) {
  const abil = cpu.fighter.abilities[3];
  cpu.cdT = abil.cooldown;
  cpu.noliObservantUses++;
  cpu.stunned = 0;
  const mapW = gameMap.cols * GAME_TILE, mapH = gameMap.rows * GAME_TILE;
  let newX = mapW - cpu.x, newY = mapH - cpu.y;
  const pr = GAME_TILE * PLAYER_RADIUS_RATIO;
  newX = Math.max(pr, Math.min(mapW - pr, newX));
  newY = Math.max(pr, Math.min(mapH - pr, newY));
  let foundValid = false;
  for (let attempts = 0; attempts < 20; attempts++) {
    const tr = Math.floor(newY / GAME_TILE), tc = Math.floor(newX / GAME_TILE);
    const tile = (tr >= 0 && tr < gameMap.rows && tc >= 0 && tc < gameMap.cols) ? gameMap.tiles[tr][tc] : -1;
    if (tile === TILE.GROUND || tile === TILE.GRASS) { foundValid = true; break; }
    newX += (Math.random() - 0.5) * GAME_TILE * 2;
    newY += (Math.random() - 0.5) * GAME_TILE * 2;
    newX = Math.max(pr, Math.min(mapW - pr, newX));
    newY = Math.max(pr, Math.min(mapH - pr, newY));
  }
  if (!foundValid) {
    newX = (gameMap.cols / 2 + 0.5) * GAME_TILE;
    newY = (gameMap.rows / 2 + 0.5) * GAME_TILE;
  }
  cpu.x = newX; cpu.y = newY;
  cpu.effects.push({ type: 'observant-tp', timer: 1.0 });
}

function cpuUseSpecialNoli(cpu) {
  const fighter = cpu.fighter;
  cpu.specialUsed = true;
  // Remove existing clone
  if (cpu.noliCloneId) {
    const oldIdx = gamePlayers.findIndex(x => x.id === cpu.noliCloneId);
    if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; _deferredRemoveIds.push(gamePlayers[oldIdx].id); }
    cpu.noliCloneId = null;
  }
  // Find target to clone
  let closestDist = Infinity, closestTarget = null;
  const candidates = gamePlayers.filter(t => t.id !== cpu.id && t.alive && !t.isSummon);
  if (gameMode === 'training' && candidates.length > 0) {
    closestTarget = candidates[Math.floor(Math.random() * candidates.length)];
  } else {
    for (const t of candidates) {
      const d = Math.sqrt((t.x - cpu.x) ** 2 + (t.y - cpu.y) ** 2);
      if (d < closestDist) { closestDist = d; closestTarget = t; }
    }
  }
  if (!closestTarget) return;
  const clonedFighter = closestTarget.fighter;
  const cloneId = 'noli-clone-' + cpu.id + '-' + Date.now();
  let cloneColor = '#a020f0';
  if (clonedFighter.id === 'onexonexonex') cloneColor = '#50a070';
  else if (clonedFighter.id === 'noli') cloneColor = '#ffffff';
  const clone = createPlayerState(
    { id: cloneId, name: closestTarget.name, color: cloneColor, fighterId: clonedFighter.id },
    { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) },
    clonedFighter
  );
  clone.x = cpu.x + (Math.random() - 0.5) * GAME_TILE * 2;
  clone.y = cpu.y + (Math.random() - 0.5) * GAME_TILE * 2;
  clone.isSummon = true;
  clone.summonOwner = cpu.id;
  clone.summonType = 'noli-clone';
  clone.isCPU = true;
  clone.noCloneHeal = true;
  clone.difficulty = 'hard';
  clone.aiState = {
    moveTarget: null, attackTarget: null, thinkTimer: 0, abilityTimer: 0,
    lastSeenPositions: {}, strafeDir: Math.random() < 0.5 ? 1 : -1, retreating: false,
  };
  clone.hp = closestTarget.maxHp;
  clone.maxHp = closestTarget.maxHp;
  gamePlayers.push(clone);
  cpu.noliCloneId = cloneId;
  cpu.effects.push({ type: 'hallucination', timer: 2.0 });
}

// ── Exploding Cat CPU AI ──
function cpuCatScratch(cpu, target, aimNx, aimNy) {
  const abil = cpu.fighter.abilities[0];
  cpu.cdM1 = abil.cooldown;
  let dmg = abil.damage;
  if (cpu.catAttackBuff > 0) dmg = cpu.fighter.abilities[2].buffDamage || 200;
  if (cpu.supportBuff > 0) dmg *= 1.5;
  if (cpu.intimidated > 0) dmg *= 0.5;
  dealDamage(cpu, target, dmg);
  cpu.effects.push({ type: 'cat-scratch', timer: 0.6 });
}

function cpuCatDraw(cpu) {
  const abil = cpu.fighter.abilities[1];
  cpu.cdE = abil.cooldown;
  const roll = Math.random();
  if (roll < 0.25) {
    cpu.catCards = (cpu.catCards || 0) + 1;
    cpu.effects.push({ type: 'cat-draw-cat', timer: 1.0 });
  } else if (roll < 0.5) {
    // Defuse: heal 300 HP + burn immunity for 10s
    cpu.hp = Math.min(cpu.maxHp, cpu.hp + 300);
    cpu.pyroBurnImmuneTimer = 10;
    if (cpu.pyroBurnTimers) cpu.pyroBurnTimers = [];
    cpu.effects.push({ type: 'cat-draw-defuse', timer: 1.0 });
  } else if (roll < 0.75) {
    // Nope: block one ability for all alive
    const nopeAbilities = ['E', 'R', 'T'];
    const blocked = nopeAbilities[Math.floor(Math.random() * nopeAbilities.length)];
    const nopeDur = abil.nopeDuration || 5;
    for (const p of gamePlayers) {
      if (!p.alive || p.isSummon || p.id === cpu.id) continue;
      p.catNopeTimer = nopeDur;
      p.catNopeAbility = blocked;
    }
    cpu.effects.push({ type: 'cat-draw-nope', timer: 1.0 });
  } else {
    // Reveal: seer timer
    cpu.catSeerTimer = abil.revealDuration || 5;
    cpu.effects.push({ type: 'cat-draw-reveal', timer: 1.0 });
  }
}

function cpuCatSteal(cpu, target) {
  const abil = cpu.fighter.abilities[3];
  cpu.cdT = abil.cooldown;
  if (cpu.catStolenReady && cpu.catStolenAbil) {
    // Fire saved ability (costs 1 cat card)
    if ((cpu.catCards || 0) < 1) { cpu.cdT = 0; return; }
    cpu.catCards--;
    // Fire saved ability
    const stolenFighter = FIGHTERS[cpu.catStolenAbil.fighterId];
    if (stolenFighter) {
      const stolenAbil = stolenFighter.abilities[cpu.catStolenAbil.abilIndex];
      if (stolenAbil) {
        if (stolenAbil.type === 'buff') {
          cpu.supportBuff = stolenAbil.duration || 7;
          if (stolenAbil.slowRange) {
            const slowRange = (stolenAbil.slowRange || 8) * GAME_TILE;
            const slowDur = stolenAbil.slowDuration || 7;
            for (const t of gamePlayers) {
              if (t.id === cpu.id || !t.alive || (t.isSummon && t.summonOwner === cpu.id)) continue;
              const sdx = t.x - cpu.x, sdy = t.y - cpu.y;
              if (Math.sqrt(sdx * sdx + sdy * sdy) < slowRange) t.buffSlowed = slowDur;
            }
          }
        } else if (stolenAbil.type === 'debuff') {
          const sightRange = (stolenAbil.range || 10) * GAME_TILE;
          for (const t of gamePlayers) {
            if (t.id === cpu.id || !t.alive || (t.isSummon && t.summonOwner === cpu.id)) continue;
            const sdx = t.x - cpu.x, sdy = t.y - cpu.y;
            if (Math.sqrt(sdx * sdx + sdy * sdy) < sightRange) {
              t.intimidated = stolenAbil.duration || 10;
              t.intimidatedBy = cpu.id;
            }
          }
        } else if (stolenAbil.type === 'self') {
          cpu.supportBuff = stolenAbil.duration || 5;
        } else if (stolenAbil.type === 'summon' && stolenAbil.companions && !cpu.summonId) {
          const companionKeys = Object.keys(stolenAbil.companions);
          const pick = companionKeys[Math.floor(Math.random() * companionKeys.length)];
          const compDef = stolenAbil.companions[pick];
          const summonId = 'summon-' + cpu.id + '-' + Date.now();
          const summon = {
            id: summonId, name: compDef.name,
            color: pick === 'fleshbed' ? '#8b4513' : pick === 'macrocosms' ? '#4a0080' : '#d4af37',
            x: cpu.x + (Math.random() - 0.5) * GAME_TILE * 2,
            y: cpu.y + (Math.random() - 0.5) * GAME_TILE * 2,
            hp: compDef.hp, maxHp: compDef.hp,
            fighter: cpu.fighter, alive: true,
            cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
            totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
            supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
            noDamageTimer: 0, healTickTimer: 0, isHealing: false,
            specialJumping: false, specialAiming: false,
            specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
            effects: [],
            blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
            chairCharges: 0, isCraftingChair: false, craftTimer: 0,
            isEatingChair: false, eatTimer: 0, eatHealPool: 0,
            summonId: null, boiledOneActive: false, boiledOneTimer: 0,
            poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
            gearUpTimer: 0, wicketIds: [], driveReflectTimer: 0,
            deerFearTimer: 0, deerFearTargetX: 0, deerFearTargetY: 0,
            deerSeerTimer: 0, deerRobotId: null, iglooX: 0, iglooY: 0, iglooTimer: 0,
            isSummon: true, summonOwner: cpu.id, summonType: pick,
            summonSpeed: compDef.speed, summonDamage: compDef.damage,
            summonStunDur: compDef.stunDuration, summonAttackCD: compDef.attackCooldown,
            summonAttackTimer: 0,
          };
          if (pick === 'obelisk') { summon.x = cpu.x; summon.y = cpu.y; }
          gamePlayers.push(summon);
          cpu.summonId = summonId;
        } else {
          const dx = target.x - cpu.x, dy = target.y - cpu.y;
          const dist = Math.sqrt(dx * dx + dy * dy) || 1;
          if (dist < (stolenAbil.range || 2) * GAME_TILE) {
            let dmg = stolenAbil.damage || 50;
            if (cpu.supportBuff > 0) dmg *= 1.5;
            if (cpu.intimidated > 0) dmg *= 0.5;
            dealDamage(cpu, target, dmg);
          }
        }
      }
    }
    cpu.catStolenAbil = null;
    cpu.catStolenReady = false;
    cpu.effects.push({ type: 'cat-steal-fire', timer: 0.5 });
  } else {
    // Copy Move 3 (T ability) from the target (costs 1 cat card, skip cats)
    if ((cpu.catCards || 0) < 1) { cpu.cdT = 0; return; }
    if (!target.fighter) return;
    if (target.fighter.id === 'explodingcat') return;
    cpu.catCards--;
    const fid = target.fighter.id;
    const abilIdx = 3; // Always steal Move 3 (T ability)
    cpu.catStolenAbil = { fighterId: fid, abilIndex: abilIdx };
    cpu.catStolenReady = true;
    cpu.effects.push({ type: 'cat-steal-copy', timer: 0.5 });
  }
}

function cpuCatAttack(cpu) {
  const abil = cpu.fighter.abilities[2];
  cpu.cdR = abil.cooldown;
  cpu.catAttackBuff = abil.buffDuration || 5;
  cpu.effects.push({ type: 'cat-attack-buff', timer: 1.0 });
}

function cpuUseSpecialCat(cpu) {
  const fighter = cpu.fighter;
  cpu.specialUsed = true;
  const abil = fighter.abilities[4];
  const count = abil.kittenCount || 4;
  const kittenHp = abil.kittenHp || 400;
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;
  for (let i = 0; i < count; i++) {
    const kittenId = 'kitten-' + cpu.id + '-' + Date.now() + '-' + i;
    const angle = (i / count) * Math.PI * 2;
    const spawnDist = GAME_TILE * 2;
    const kitten = createPlayerState(
      { id: kittenId, name: 'Kitten', color: '#111', fighterId: fighter.id },
      { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) },
      fighter
    );
    kitten.x = cpu.x + Math.cos(angle) * spawnDist;
    kitten.y = cpu.y + Math.sin(angle) * spawnDist;
    // Nudge out of obstacles
    if (!canMoveTo(kitten.x, kitten.y, radius)) {
      kitten.x = cpu.x;
      kitten.y = cpu.y;
    }
    kitten.hp = kittenHp;
    kitten.maxHp = kittenHp;
    kitten.isSummon = true;
    kitten.summonOwner = cpu.id;
    kitten.summonType = 'exploding-kitten';
    kitten.summonSpeed = abil.kittenSpeed || 2.5;
    kitten.summonDamage = abil.damage || 1200;
    kitten.explodeRadius = abil.explodeRadius || 1.5;
    gamePlayers.push(kitten);
    if (!cpu.catKittenIds) cpu.catKittenIds = [];
    cpu.catKittenIds.push(kittenId);
  }
  cpu.effects.push({ type: 'exploding-kitten-spawn', timer: 1.5 });
}

// ── Napoleon CPU helpers ────────────────────────────────────
function cpuNapoleonSword(cpu, target, aimNx, aimNy) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[0];
  cpu.cdM1 = abil.cooldown;
  const range = (abil.range || 1.5) * GAME_TILE;
  let baseDmg = abil.damage;
  if (cpu.supportBuff > 0) baseDmg *= 1.5;
  if (cpu.intimidated > 0) baseDmg *= 0.5;
  if (cpu.napoleonCavalry) baseDmg *= 2;
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
  cpu.effects.push({ type: 'sword', timer: 0.2, aimNx, aimNy });
}

function cpuNapoleonCannon(cpu) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[2];
  cpu.cdR = abil.cooldown;
  if (cpu.napoleonCannonId) {
    const oldIdx = gamePlayers.findIndex(p => p.id === cpu.napoleonCannonId);
    if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; _deferredRemoveIds.push(gamePlayers[oldIdx].id); }
    cpu.napoleonCannonId = null;
  }
  const cannonId = 'cannon-' + cpu.id + '-' + Date.now();
  const cannon = createPlayerState(
    { id: cannonId, name: 'Cannon', color: '#555', fighterId: 'napoleon' },
    { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) },
    fighter
  );
  cannon.x = cpu.x + (Math.random() - 0.5) * GAME_TILE * 2;
  cannon.y = cpu.y + (Math.random() - 0.5) * GAME_TILE * 2;
  cannon.hp = abil.cannonHp || 600;
  cannon.maxHp = abil.cannonHp || 600;
  cannon.isSummon = true;
  cannon.summonOwner = cpu.id;
  cannon.summonType = 'napoleon-cannon';
  cannon.summonSpeed = 0;
  cannon.summonDamage = abil.damage || 700;
  cannon.summonAttackCD = abil.cannonFireCD || 5;
  cannon.summonAttackTimer = 0;
  cannon.summonProjectileSpeed = abil.projectileSpeed || 30;
  gamePlayers.push(cannon);
  cpu.napoleonCannonId = cannonId;
  cpu.effects.push({ type: 'cannon-place', timer: 1.0 });
}

function cpuNapoleonWall(cpu, target) {
  const fighter = cpu.fighter;
  const abil = fighter.abilities[3];
  cpu.cdT = abil.cooldown;
  if (cpu.napoleonWallId) {
    const oldIdx = gamePlayers.findIndex(p => p.id === cpu.napoleonWallId);
    if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; _deferredRemoveIds.push(gamePlayers[oldIdx].id); }
    cpu.napoleonWallId = null;
  }
  const dx = target.x - cpu.x; const dy = target.y - cpu.y;
  const dist = Math.sqrt(dx * dx + dy * dy) || 1;
  const nx = dx / dist; const ny = dy / dist;
  const wallDist = GAME_TILE * 2;
  const wx = cpu.x + nx * wallDist;
  const wy = cpu.y + ny * wallDist;
  const wallId = 'wall-' + cpu.id + '-' + Date.now();
  const wall = createPlayerState(
    { id: wallId, name: 'Wall', color: '#8b7355', fighterId: 'napoleon' },
    { r: Math.floor(wy / GAME_TILE), c: Math.floor(wx / GAME_TILE) },
    fighter
  );
  wall.x = wx; wall.y = wy;
  wall.hp = 999999;
  wall.maxHp = 999999;
  wall.isSummon = true;
  wall.summonOwner = cpu.id;
  wall.summonType = 'napoleon-wall';
  wall.summonSpeed = 0;
  wall.summonDamage = 0;
  wall.summonAttackCD = 0;
  wall.summonAttackTimer = 0;
  wall.wallSize = abil.wallSize || 2;
  wall.wallTimer = 30;
  gamePlayers.push(wall);
  cpu.napoleonWallId = wallId;
  cpu.effects.push({ type: 'wall-place', timer: 0.5 });
}

function cpuUseSpecialNapoleon(cpu) {
  const fighter = cpu.fighter;
  cpu.specialUsed = true;
  const abil = fighter.abilities[4];
  const count = abil.infantryCount || 12;
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;
  if (!cpu.napoleonInfantryIds) cpu.napoleonInfantryIds = [];
  for (let i = 0; i < count; i++) {
    const infId = 'infantry-' + cpu.id + '-' + Date.now() + '-' + i;
    const angle = (i / count) * Math.PI * 2;
    const spawnDist = GAME_TILE * 2;
    const inf = createPlayerState(
      { id: infId, name: 'Infantryman', color: '#2c3e50', fighterId: 'napoleon' },
      { r: Math.floor(cpu.y / GAME_TILE), c: Math.floor(cpu.x / GAME_TILE) },
      fighter
    );
    inf.x = cpu.x + Math.cos(angle) * spawnDist;
    inf.y = cpu.y + Math.sin(angle) * spawnDist;
    if (!canMoveTo(inf.x, inf.y, radius)) { inf.x = cpu.x; inf.y = cpu.y; }
    inf.hp = abil.infantryHp || 50;
    inf.maxHp = abil.infantryHp || 50;
    inf.isSummon = true;
    inf.summonOwner = cpu.id;
    inf.summonType = 'napoleon-infantry';
    inf.summonSpeed = abil.infantrySpeed || 2.0;
    inf.summonDamage = abil.damage || 100;
    inf.summonAttackCD = abil.infantryFireCD || 1;
    inf.summonAttackTimer = 0;
    inf.summonProjectileSpeed = abil.infantryProjectileSpeed || 38;
    inf.summonProjectileRange = abil.infantryRange || 0.8;
    gamePlayers.push(inf);
    cpu.napoleonInfantryIds.push(infId);
  }
  cpu.effects.push({ type: 'grande-armee', timer: 2.0 });
}

// ═══════════════════════════════════════════════════════════════
// ABILITIES
// ═══════════════════════════════════════════════════════════════
function useAbility(key) {
  const lp = localPlayer;
  if (!lp || !lp.alive || lp.stunned > 0) return;

  // Track ability usage for achievement purposes
  usedAbilityKeys.add(key);

  const fighter = lp.fighter;
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;
  const isPoker = fighter.id === 'poker';
  const isFilbus = fighter.id === 'filbus';
  const is1x = fighter.id === 'onexonexonex';
  const isCricket = fighter.id === 'cricket';
  const isDeer = fighter.id === 'deer';
  const isNoli = fighter.id === 'noli';
  const isCat = fighter.id === 'explodingcat';
  const isNapoleon = fighter.id === 'napoleon';
  const isModerator = fighter.id === 'moderator';
  const isDnd = fighter.id === 'dnd';
  const isDragon = fighter.id === 'dragon';
  const isDogTooth = fighter.id === 'dogtooth';
  const isIllusion = fighter.id === 'illusion';
  const isUnstable = fighter.id === 'unstable';
  const isPyro = fighter.id === 'pyromaniac';
  const isHeavyRope = fighter.id === 'heavyrope';
  const isOmori = fighter.id === 'omori';
  const isHitman = fighter.id === 'hitman';

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
    // Queen Bee Unicorn: blocks M1 attacks while alive (except creator)
    const queenBee = gamePlayers.find(p => p.alive && p.isSummon && p.summonType === 'queenbee-unicorn');
    if (queenBee && queenBee.summonOwner !== lp.id) {
      combatLog.push({ text: '👑 M1 blocked by Queen Bee Unicorn!', timer: 1.5, color: '#ffd700' });
      return;
    }
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
        if (!isHostAuthority) socket.emit('projectile-spawn', { projectiles: spawnedChips });
      }
      // Clear small blind when using another move
      if (lp.blindBuff === 'small') lp.blindBuff = null;
      lp.effects.push({ type: 'chip-throw', timer: 0.2 });
    } else if (isFilbus) {
      // Filbus: Swing Chair (rare table chance)
      const isTable = Math.random() < (abil.tableChance || 0.05);
      const range = (isTable ? (abil.tableRange || 3.2) : (abil.range || 2.5)) * GAME_TILE;
      let baseDmg = isTable ? (abil.tableDamage || 400) : (abil.damage || 250);
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      const initialHitIds = [lp.id];
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        dealDamage(lp, target, baseDmg);
        initialHitIds.push(target.id);
      }
      if (isTable) {
        combatLog.push({ text: '🪑 TABLE SWING! 400 dmg!', timer: 3, color: '#ff6600' });
        lp.effects.push({ type: 'table-swing', timer: 0.8, aimNx, aimNy });
      } else {
        lp.effects.push({ type: 'chair-swing', timer: 0.8, aimNx, aimNy });
        // Set linger zone (half damage, 0.7s window, only hits new targets)
        if (!isTable) {
          lp.chairSwingTimer = 0.7;
          lp.chairSwingAimNx = aimNx; lp.chairSwingAimNy = aimNy;
          lp.chairSwingRange = range;
          lp.chairSwingDmg = Math.round(baseDmg * 0.5);
          lp.chairSwingHitIds = initialHitIds.slice();
        }
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
    } else if (isCricket) {
      // Cricket: Bat Swing — short-range melee
      const range = (abil.range || 1.2) * GAME_TILE;
      let baseDmg = abil.damage;
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      if (lp.gearUpTimer > 0) baseDmg *= 1.5;
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
      lp.effects.push({ type: 'bat-swing', timer: 0.25, aimNx, aimNy });
    } else if (isDeer) {
      // Deer M1: Deer's fast engineer — one robot at a time, HP carries over replacements
      if (lp.deerSeerTimer > 0) return; // cannot use during Seer
      let carryHp = abil.robotHp || 500;
      if (lp.deerRobotId) {
        const oldRobot = gamePlayers.find(p => p.id === lp.deerRobotId);
        if (oldRobot && oldRobot.alive) carryHp = oldRobot.hp;
        const oldIdx = gamePlayers.findIndex(p => p.id === lp.deerRobotId);
        if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers.splice(oldIdx, 1); }
      }
      const robotId = 'robot-' + lp.id + '-' + Date.now();
      const robot = {
        id: robotId, name: 'Deer Robot', color: '#708090',
        x: lp.x + (Math.random() - 0.5) * GAME_TILE * 2,
        y: lp.y + (Math.random() - 0.5) * GAME_TILE * 2,
        hp: carryHp, maxHp: abil.robotHp || 500,
        fighter: fighter, alive: true,
        cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
        totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
        supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
        noDamageTimer: 0, healTickTimer: 0, isHealing: false,
        specialJumping: false, specialAiming: false,
        specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
        effects: [],
        blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
        chairCharges: 0, isCraftingChair: false, craftTimer: 0,
        isEatingChair: false, eatTimer: 0, eatHealPool: 0,
        summonId: null, boiledOneActive: false, boiledOneTimer: 0,
        poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
        gearUpTimer: 0, wicketIds: [], driveReflectTimer: 0,
        deerFearTimer: 0, deerFearTargetX: 0, deerFearTargetY: 0,
        deerSeerTimer: 0, deerRobotId: null, iglooX: 0, iglooY: 0, iglooTimer: 0,
        isSummon: true, summonOwner: lp.id, summonType: 'deer-robot',
        summonSpeed: 0, summonDamage: abil.damage || 100,
        summonStunDur: 0, summonAttackCD: abil.robotFireRate || 1, summonAttackTimer: 0,
      };
      gamePlayers.push(robot);
      lp.deerRobotId = robotId;
      lp.deerBuildSlowTimer = 1.0; // 1 second build slowness
      lp.effects.push({ type: 'summon', timer: 1.5 });
    } else if (isNoli) {
      // Noli M1: Tendril Stab — melee
      if (lp.noliVoidRushActive || lp.noliVoidStarAiming) return;
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
      }
      lp.effects.push({ type: 'tendril-stab', timer: 0.25, aimNx, aimNy });
    } else if (isCat) {
      // Exploding Cat M1: Scratch — short melee
      const range = (abil.range || 0.9) * GAME_TILE;
      let baseDmg = (lp.catAttackBuff > 0) ? (fighter.abilities[2].buffDamage || 200) : abil.damage;
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
      lp.effects.push({ type: 'cat-scratch', timer: 0.4, aimNx, aimNy });
    } else if (isNapoleon) {
      // Napoleon M1: Sword — melee 200 dmg
      const range = (abil.range || 1.5) * GAME_TILE;
      let baseDmg = abil.damage;
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      if (lp.napoleonCavalry) baseDmg *= 2; // Cavalry: 2x damage dealt
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      _lastDealDamageWasM1 = true;
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
      _lastDealDamageWasM1 = false;
      lp.effects.push({ type: 'sword', timer: 0.2, aimNx, aimNy });
    } else if (isModerator) {
      // Moderator M1: Ban Hammer — melee 100 dmg, 10% teleport
      const range = (abil.range || 1.5) * GAME_TILE;
      let baseDmg = abil.damage;
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      if (lp.modServerUpdateTimer > 0) baseDmg = Math.round(baseDmg * 1.5);
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      _lastDealDamageWasM1 = true;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        dealDamage(lp, target, baseDmg);
        // 10% chance to teleport
        if (Math.random() < (abil.teleportChance || 0.1) && !target.isSummon) {
          const safePos = getRandomSafePosition();
          target.x = safePos.x;
          target.y = safePos.y;
          target.effects.push({ type: 'ban-teleport', timer: 1.0 });
          if (target.id === localPlayerId) {
            combatLog.push({ text: '🔨 You were BANNED to a random location!', timer: 4, color: '#ff0000' });
          }
          combatLog.push({ text: '🔨 Ban Hammer teleported ' + target.name + '!', timer: 3, color: '#ff4444' });
        }
      }
      _lastDealDamageWasM1 = false;
      lp.effects.push({ type: 'ban-hammer', timer: 0.5, aimNx: aimNx, aimNy: aimNy });
    } else if (isDnd) {
      // D&D M1: Sword (Human) / Bow (Elf) / Axe (Dwarf)
      const race = lp.dndRace || 'human';
      let baseDmg = race === 'dwarf' ? (abil.axeDamage || 150) : (abil.damage || 100);
      baseDmg += (lp.dndWeaponBonus || 0);
      if (lp.dndD20Active) baseDmg = race === 'dwarf' ? 750 : 650;
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      baseDmg = Math.floor(baseDmg);
      lp.cdM1 = race === 'dwarf' ? (abil.axeCooldown || 1.5) : (abil.cooldown || 1);
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      if (race === 'elf') {
        // Bow: ranged projectile — fast, unlimited range (stops at wall/sea)
        const speed = (abil.bowSpeed || 40) * GAME_TILE / 10;
        projectiles.push({
          x: lp.x, y: lp.y,
          vx: aimNx * speed, vy: aimNy * speed,
          ownerId: lp.id, damage: baseDmg,
          timer: 999,
          type: 'dnd-arrow', color: '#8b4513',
        });
        lp.effects.push({ type: 'dnd-bow', timer: 0.2, aimNx, aimNy });
      } else {
        // Sword/Axe: melee
        const range = (abil.range || 1.5) * GAME_TILE;
        for (const target of gamePlayers) {
          if (target.id === lp.id || !target.alive) continue;
          if (target.isSummon && target.summonOwner === lp.id && target.summonType !== 'dnd-orc') continue;
          const dx = target.x - lp.x; const dy = target.y - lp.y;
          const dist = Math.sqrt(dx * dx + dy * dy);
          if (dist > range) continue;
          const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
          if (dot < 0) continue;
          dealDamage(lp, target, baseDmg);
        }
        lp.effects.push({ type: race === 'dwarf' ? 'dnd-axe' : 'sword', timer: 0.2, aimNx, aimNy });
      }
    } else if (isDragon) {
      // Dragon M1: Dragon Breath — start/continue continuous icy breath
      if (lp.dragonBreathFuel <= 0) return;
      if (lp.dragonBeamCharging || lp.dragonBeamRecovery > 0) return;
      // Set windup on first activation (not when already breathing)
      if (!lp.dragonBreathActive) {
        lp.dragonBreathWindup = 0.2;
      }
      lp.dragonBreathActive = true;
      lp.cdM1 = 0.05; // very short CD so auto-fire updates aim each frame
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      lp.dragonBreathAimNx = aimDx / aimDist;
      lp.dragonBreathAimNy = aimDy / aimDist;
    } else if (isIllusion) {
      // Illusion M1: Teleattack — melee 150 dmg, if hit dodge that player's attacks for 0.5s
      const range = (abil.range || 1.5) * GAME_TILE;
      let baseDmg = abil.damage || 150;
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx2 = aimX - lp.x; const aimDy2 = aimY - lp.y;
      const aimDist2 = Math.sqrt(aimDx2 * aimDx2 + aimDy2 * aimDy2) || 1;
      const aimNx = aimDx2 / aimDist2; const aimNy = aimDy2 / aimDist2;
      let hitSomeone = false;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        dealDamage(lp, target, baseDmg);
        if (!hitSomeone) {
          lp.illusionDodgeTargetId = target.id;
          lp.illusionDodgeTimer = abil.dodgeDuration || 0.5;
          hitSomeone = true;
        }
      }
      lp.effects.push({ type: 'teleattack', timer: 0.2, aimNx, aimNy });
    } else if (isDogTooth) {
      // Dog Tooth M1: Stab — melee 150 dmg + 50 bleed over 5s
      const range = (abil.range || 1.5) * GAME_TILE;
      let baseDmg = abil.damage || 150;
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      // Smile Tapes boost: 500 dmg during Smile
      if (lp.dogtoothSmileTimer > 0) baseDmg = abil.damage > 0 ? 500 : 500;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        // Skip own summons EXCEPT ouriel-room (hostile to owner)
        if (target.isSummon && target.summonOwner === lp.id && target.summonType !== 'ouriel-room') continue;
        if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        dealDamage(lp, target, baseDmg);
        // Apply bleed DOT
        if (!target.poisonTimers) target.poisonTimers = [];
        target.poisonTimers.push({
          sourceId: lp.id,
          dps: (abil.bleedDamage || 50) / (abil.bleedDuration || 5),
          remaining: abil.bleedDuration || 5
        });
        target.effects.push({ type: 'bleed', timer: abil.bleedDuration || 5 });
      }
      lp.effects.push({ type: 'stab', timer: 0.2, aimNx, aimNy });
    } else if (isOmori) {
      // Omori M1: Attack — same as Dogtooth stab (150 dmg + bleed)
      const range = (abil.range || 1.5) * GAME_TILE;
      let baseDmg = abil.damage || 150;
      if (lp.supportBuff > 0) baseDmg *= 1.5;
      if (lp.intimidated > 0) baseDmg *= 0.5;
      if (lp.omoriKelBuffTimer > 0) baseDmg *= 1.5;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        let finalDmg = baseDmg;
        if (lp.omoriAubreyBuffTimer > 0 && Math.random() < 0.1) finalDmg = 600;
        dealDamage(lp, target, finalDmg);
        if (!target.poisonTimers) target.poisonTimers = [];
        target.poisonTimers.push({
          sourceId: lp.id,
          dps: (abil.bleedDamage || 50) / (abil.bleedDuration || 5),
          remaining: abil.bleedDuration || 5
        });
        target.effects.push({ type: 'bleed', timer: abil.bleedDuration || 5 });
      }
      lp.effects.push({ type: 'stab', timer: 0.2, aimNx, aimNy });
    } else if (isUnstable) {
      // Unstable Fist: 100 DMG + random buff/debuff on enemy
      const range = (abil.range || 1.5) * GAME_TILE;
      let baseDmg = abil.damage || 100;
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
        if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        dealDamage(lp, target, baseDmg);
        // Apply random buff or debuff
        const roll = Math.random();
        if (roll < 0.15) { target.stunned = 1.5; target.effects.push({ type: 'stun', timer: 1.5 }); }
        else if (roll < 0.30) { target.supportBuff = 5; } // buff enemy (bad for us, chaotic)
        else if (roll < 0.45) { target.intimidated = 5; target.intimidatedBy = lp.id; }
        else if (roll < 0.60) { target.buffSlowed = 3; }
        else if (roll < 0.75) { target.noDamageTimer = 0; target.isHealing = false; }
        // else no effect
      }
      lp.effects.push({ type: 'unstable-fist', timer: 0.3, aimNx, aimNy });
    } else if (isPyro) {
      // Pyromaniac: Flamethrower — hold to spray continuous DPS (like Dragon Breath)
      if (lp.pyroFlameFuel <= 0) return;
      if (!lp.pyroFlameActive) {
        lp.pyroFlameWindup = 0.2;
      }
      lp.pyroFlameActive = true;
      lp.cdM1 = 0.05; // short CD so auto-fire updates aim each frame
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      lp.pyroFlameNx = aimDx / aimDist;
      lp.pyroFlameNy = aimDy / aimDist;
    } else if (isHeavyRope) {
      // Heavy Rope: Rope Hit — straight-line melee in front
      let ropeRange = (abil.range || 2.5) * GAME_TILE;
      let ropeDmg = abil.damage;
      // Rope Grip: half range, 300 DMG
      if (lp.ropeGripActive) {
        ropeRange *= 0.5;
        ropeDmg = lp.fighter.abilities[2].m1Damage || 300;
      }
      // Second Grip: 0.5s cooldown
      if (lp.ropeSecondGripTimer > 0) {
        lp.cdM1 = 0.5;
      }
      if (lp.supportBuff > 0) ropeDmg *= 1.5;
      if (lp.intimidated > 0) ropeDmg *= 0.5;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > ropeRange) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0.3) continue; // tighter cone for straight-line hit
        dealDamage(lp, target, ropeDmg);
        target.effects.push({ type: 'hit', timer: 0.3 });
      }
      lp.effects.push({ type: 'rope-hit', timer: 0.25, aimNx, aimNy });
    } else if (isHitman) {
      // Hitman: Fire current weapon
      if (lp.hitmanConcealTimer > 0) { lp.cdM1 = 0; return; } // cannot attack while concealed
      if (lp.hitmanEquipping) { lp.cdM1 = 0; return; } // cannot fire during weapon equip
      if (lp.hitmanReloading) { lp.cdM1 = 0; return; } // cannot fire while reloading
      const wDefs = abil.weapons || {};
      const wKey = lp.hitmanWeapon || 'pistol';
      const wDef = wDefs[wKey] || wDefs['pistol'];
      if (!lp.hitmanAmmo || lp.hitmanAmmo <= 0) {
        // Auto-reload
        lp.hitmanReloading = true;
        let reloadT = wDef.reloadTime || 1;
        if (lp.hitmanLockingIn) reloadT = 0; // no reload during Locking In
        lp.hitmanReloadTimer = reloadT;
        lp.cdM1 = 0;
        if (!lp.hitmanLockingIn && lp.id === localPlayerId) combatLog.push({ text: '🔄 Reloading...', timer: wDef.reloadTime || 1, color: '#aaa' });
        return;
      }
      // Determine fire rate (Locking In = 1.5× faster)
      const baseFireRate = wDef.fireRate || 0.5;
      lp.cdM1 = lp.hitmanLockingIn ? baseFireRate / 1.5 : baseFireRate;
      // Consume ammo (skip during Locking In)
      if (!lp.hitmanLockingIn) lp.hitmanAmmo = Math.max(0, lp.hitmanAmmo - 1);
      // Fire projectile toward mouse
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      const bulletSpeed = (wDef.speed || 28) * GAME_TILE / 10;
      let dmg = wDef.damage || 100;
      if (lp.supportBuff > 0) dmg *= 1.5;
      if (lp.intimidated > 0) dmg *= 0.5;
      // Professional trait: 1.3× damage beyond 6 tiles
      // (applied on hit in dealDamage caller — we tag the projectile)
      projectiles.push({
        x: lp.x, y: lp.y,
        vx: aimNx * bulletSpeed, vy: aimNy * bulletSpeed,
        ownerId: lp.id, damage: Math.round(dmg),
        timer: 4, type: 'hitman-bullet',
        weaponKey: wKey, color: wDef.color || '#f5c842',
        traitRange: 6 * GAME_TILE, // range threshold for trait bonus
        spawnX: lp.x, spawnY: lp.y,
      });
      if (typeof socket !== 'undefined' && socket.emit && !isHostAuthority) {
        socket.emit('projectile-spawn', { projectiles: [{ x: lp.x, y: lp.y, vx: aimNx * bulletSpeed, vy: aimNy * bulletSpeed, timer: 4, type: 'hitman-bullet', color: wDef.color || '#f5c842' }] });
      }
      lp.effects.push({ type: 'hitman-fire', timer: 0.15, aimNx, aimNy, wKey });
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

    // ── Apple Tree melee damage ──
    if (appleTree && appleTree.alive) {
      const abil = fighter.abilities[0];
      const range = (abil.range || 1.5) * GAME_TILE;
      const treeCX = (appleTree.col + 1) * GAME_TILE; // center of 2x2
      const treeCY = (appleTree.row + 1) * GAME_TILE;
      const dx = treeCX - lp.x;
      const dy = treeCY - lp.y;
      const dist = Math.sqrt(dx * dx + dy * dy);
      if (dist < range + GAME_TILE) {
        // Check aim direction
        const cw2 = gameCanvas.width; const ch2 = gameCanvas.height;
        const camX2 = lp.x - cw2 / 2; const camY2 = lp.y - ch2 / 2;
        const aimX2 = mouseX + camX2; const aimY2 = mouseY + camY2;
        const aDx = aimX2 - lp.x; const aDy = aimY2 - lp.y;
        const aDist = Math.sqrt(aDx * aDx + aDy * aDy) || 1;
        const dot = (dx * aDx / aDist + dy * aDy / aDist) / (dist || 1);
        if (dot > 0) {
          let dmg = abil.damage || 100;
          if (lp.supportBuff > 0) dmg *= 1.5;
          appleTree.hp -= dmg;
          lp.effects.push({ type: 'tree-hit', timer: 0.3 });
          if (appleTree.hp <= 0) {
            appleTree.hp = 0;
            appleTree.alive = false;
            appleTree.regrowTimer = 30;
            appleTree.apples = [];
            pushPlayersOffStump();
            combatLog.push({ text: '🪓 Apple tree chopped down!', timer: 4, color: '#e67e22' });
          }
        }
      }
    }
  }

  else if (key === 'E') {
    // Heavy Rope: allow E release while swing is active even if on cooldown
    if (lp.cdE > 0 && !(fighter.id === 'heavyrope' && lp.ropeSwingActive)) return;
    // Bug Fixing: check if E (slot 1) is disabled
    if (lp.modDisabledAbilities && lp.modDisabledAbilities.includes(1)) {
      combatLog.push({ text: '🐛 Move 1 is disabled by Bug Fixing!', timer: 2, color: '#e67e22' });
      return;
    }
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
      if (lp.pokerFullHouseActive) {
        dmg = 1000; // Full House: guaranteed best
        lp.pokerFullHouseActive = false;
      } else if (roll < 0.60) dmg = 100 + Math.floor(Math.random() * 4) * 100; // 100-400
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
        if (!isHostAuthority) socket.emit('projectile-spawn', { projectiles: [{ x: lp.x, y: lp.y, vx: cvx, vy: cvy, timer: 999, type: 'card' }] });
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
        if (!isHostAuthority) socket.emit('projectile-spawn', { projectiles: [{ x: lp.x, y: lp.y, vx: evx, vy: evy, timer: 1.5, type: 'entangle' }] });
      }
      lp.effects.push({ type: 'entangle-cast', timer: 0.5 });
      combatLog.push({ text: '⚔ Entanglement!', timer: 2, color: '#00ff66' });
    } else if (isCricket) {
      // Cricket E: Drive — melee swing + 1-second projectile reflect window
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      const driveRange = (abil.range || 2.0) * GAME_TILE;
      // Start reflect window
      lp.driveReflectTimer = abil.reflectDuration || 1.0;
      // Hit enemies in melee range — stun for 3s
      let driveDmg = abil.damage || 350;
      if (lp.supportBuff > 0) driveDmg *= 1.5;
      if (lp.intimidated > 0) driveDmg *= 0.5;
      if (lp.gearUpTimer > 0) driveDmg *= 1.5;
      const stunDur = abil.stunDuration || 3;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > driveRange) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        dealDamage(lp, target, driveDmg);
        target.stunned = stunDur;
        target.effects.push({ type: 'stun', timer: stunDur });
      }
      // Set default cooldown (reduced if a projectile is reflected during the window)
      lp.cdE = abil.cooldown || 20;
      lp.effects.push({ type: 'drive', timer: 0.3, aimNx, aimNy });
      combatLog.push({ text: '🏏 Drive!', timer: 2, color: '#c8a96e' });
    } else if (isDeer) {
      // Deer E: Deer's Fear — 5s speed buff when moving away from closest enemy
      if (lp.deerSeerTimer > 0) return; // cannot use during Seer
      let closestDist = Infinity, closestP = null;
      for (const t of gamePlayers) {
        if (t.id === lp.id || !t.alive || t.isSummon) continue;
        const d = Math.sqrt((t.x - lp.x) ** 2 + (t.y - lp.y) ** 2);
        if (d < closestDist) { closestDist = d; closestP = t; }
      }
      lp.deerFearTimer = abil.duration || 5;
      lp.deerFearTargetX = closestP ? closestP.x : lp.x;
      lp.deerFearTargetY = closestP ? closestP.y : lp.y;
      lp.effects.push({ type: 'deer-fear', timer: abil.duration || 5 });
      combatLog.push({ text: '🦌 Fear! Run away faster!', timer: 3, color: '#8fbc8f' });
    } else if (isNoli) {
      // Noli E: Void Rush — auto-aim toward nearest enemy player
      if (lp.noliVoidRushActive || lp.noliVoidStarAiming) return;
      if (lp.stunned > 0) return;
      // Find nearest alive enemy
      let nearDist = Infinity, nearTarget = null;
      for (const t of gamePlayers) {
        if (t.id === lp.id || !t.alive) continue;
        if (t.isSummon && t.summonOwner === lp.id) continue;
        const d = Math.sqrt((t.x - lp.x) ** 2 + (t.y - lp.y) ** 2);
        if (d < nearDist) { nearDist = d; nearTarget = t; }
      }
      let dx, dy;
      if (nearTarget) {
        dx = nearTarget.x - lp.x; dy = nearTarget.y - lp.y;
      } else {
        // No enemies — fall back to mouse direction
        const cw = gameCanvas.width; const ch = gameCanvas.height;
        const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
        dx = mouseX + camX - lp.x; dy = mouseY + camY - lp.y;
      }
      const dist = Math.sqrt(dx * dx + dy * dy) || 1;
      const chain = lp.noliVoidRushChain;
      const baseSpeed = (abil.dashSpeed || 10) * GAME_TILE / 10;
      const dashSpeed = baseSpeed * (1 + chain * (abil.speedScalePerChain || 0.15));
      lp.noliVoidRushVx = (dx / dist) * dashSpeed;
      lp.noliVoidRushVy = (dy / dist) * dashSpeed;
      lp.noliVoidRushActive = true;
      lp.noliVoidRushTimer = Infinity; // infinite dash — ends on wall/sea or player hit
      if (chain === 0) lp.cdE = abil.cooldown;
      lp.effects.push({ type: 'void-rush', timer: 0.5 });
      combatLog.push({ text: chain > 0 ? '🌀 Void Rush x' + (chain + 1) + '!' : '🌀 Void Rush!', timer: 2, color: '#a020f0' });
    } else if (isCat) {
      // Exploding Cat E: Draw — random card
      if (lp.catNopeTimer > 0 && lp.catNopeAbility === 'E') {
        combatLog.push({ text: '🚫 Noped! Can\'t use Draw!', timer: 2, color: '#e94560' });
        lp.cdE = 0;
        return;
      }
      const roll = Math.random();
      if (roll < 0.25) {
        // Cat card — save it
        lp.catCards++;
        combatLog.push({ text: '🐱 Drew a Cat! (' + lp.catCards + ' saved)', timer: 3, color: '#ff9900' });
        showPopup('🐱 CAT! (' + lp.catCards + ')');
        lp.effects.push({ type: 'cat-draw-cat', timer: 1.0 });
      } else if (roll < 0.50) {
        // Defuse — heal 300 HP + burn immunity for 10s
        lp.hp = Math.min(lp.maxHp, lp.hp + 300);
        lp.pyroBurnImmuneTimer = 10;
        if (lp.pyroBurnTimers) lp.pyroBurnTimers = [];
        combatLog.push({ text: '🟢 Defuse! Healed 300 HP + burn immune 10s!', timer: 3, color: '#00ff88' });
        showPopup('🟢 DEFUSE!');
        lp.effects.push({ type: 'cat-draw-defuse', timer: 1.5 });
      } else if (roll < 0.75) {
        // Nope — block a random ability for all players
        const nopeKeys = ['E', 'R', 'T'];
        const nopeKey = nopeKeys[Math.floor(Math.random() * nopeKeys.length)];
        const nopeDur = abil.nopeDuration || 5;
        for (const p of gamePlayers) {
          if (!p.alive || p.isSummon || p.id === lp.id) continue;
          p.catNopeTimer = nopeDur;
          p.catNopeAbility = nopeKey;
        }
        const keyNames = { E: 'Move 1', R: 'Move 2', T: 'Move 3' };
        combatLog.push({ text: '🚫 Nope! ' + keyNames[nopeKey] + ' blocked for ' + nopeDur + 's!', timer: 3, color: '#e94560' });
        showPopup('🚫 NOPE! (' + keyNames[nopeKey] + ')');
        lp.effects.push({ type: 'cat-draw-nope', timer: 1.5 });
      } else {
        // Reveal the Future — seer mode
        const revealDur = abil.revealDuration || 5;
        lp.catSeerTimer = revealDur;
        lp.effects.push({ type: 'cat-draw-reveal', timer: revealDur });
        combatLog.push({ text: '🔮 Reveal the Future! See all enemies!', timer: 3, color: '#dda0dd' });
        showPopup('🔮 REVEAL!');
      }
    } else if (isNapoleon) {
      // Napoleon E: Cavalry — toggle mount/dismount
      lp.cdE = 0; // no cooldown, it's a toggle
      lp.napoleonCavalry = !lp.napoleonCavalry;
      if (lp.napoleonCavalry) {
        lp.effects.push({ type: 'cavalry-mount', timer: 1.5 });
        combatLog.push({ text: '🐴 Cavalry! Mounted! 2.5× speed, 2× dmg dealt & received.', timer: 3, color: '#c8a96e' });
      } else {
        lp.effects.push({ type: 'cavalry-dismount', timer: 0.5 });
        combatLog.push({ text: '🐴 Dismounted.', timer: 2, color: '#999' });
      }
    } else if (isModerator) {
      // Moderator E: Scare — TP a random enemy to you, stun 1s, add Fear
      lp.cdE = abil.cooldown;
      const enemies = gamePlayers.filter(p => {
        if (!p.alive || p.isSummon || p.id === lp.id) return false;
        if (gameMode === 'teams' && lp.team && p.team === lp.team) return false;
        return true;
      });
      if (enemies.length > 0) {
        const victim = enemies[Math.floor(Math.random() * enemies.length)];
        // TP victim near the moderator (safe position close by, not on rocks or inside moderator)
        const pr = GAME_TILE * PLAYER_RADIUS_RATIO;
        const minDist = GAME_TILE * 0.6; // minimum distance from moderator to avoid overlap
        let nx = null, ny = null;
        for (let attempt = 0; attempt < 16; attempt++) {
          const angle = Math.random() * Math.PI * 2;
          const dist = GAME_TILE * (0.8 + Math.random() * 0.7); // 0.8–1.5 tiles away
          const tx = lp.x + Math.cos(angle) * dist;
          const ty = lp.y + Math.sin(angle) * dist;
          if (canMoveTo(tx, ty, pr)) {
            const dx = tx - lp.x, dy = ty - lp.y;
            if (Math.sqrt(dx * dx + dy * dy) >= minDist) {
              nx = tx; ny = ty; break;
            }
          }
        }
        if (nx === null) { const safe = getRandomSafePosition(); nx = safe.x; ny = safe.y; }
        victim.x = nx; victim.y = ny;
        victim.stunned = abil.stunDuration || 1;
        victim.modFearTimer = abil.fearDuration || 5;
        victim.modFearSourceId = lp.id;
        victim.effects.push({ type: 'scare-tp', timer: 1.5 });
        if (victim.id === localPlayerId) {
          combatLog.push({ text: '😱 You were SCARED! Teleported to Moderator!', timer: 4, color: '#ff0000' });
        }
        combatLog.push({ text: '😱 Scare! ' + victim.name + ' teleported to you!', timer: 3, color: '#9b59b6' });
      } else {
        combatLog.push({ text: 'No enemies to scare!', timer: 2, color: '#999' });
      }
    } else if (isDnd) {
      // D&D E: Questing — spawn an orc that attacks ONLY this player. Earn 1GP on kill.
      lp.cdE = abil.cooldown || 0;
      const orcId = 'dnd-orc-' + lp.id + '-' + Date.now();
      const orcFighter = getFighter('fighter');
      const orc = createPlayerState(
        { id: orcId, name: 'Orc', color: '#556b2f', fighterId: 'fighter' },
        { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
        orcFighter
      );
      // Spawn 3-5 tiles away in random direction, safe position
      const orcRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
      let orcPlaced = false;
      for (let a = 0; a < 16; a++) {
        const angle = Math.random() * Math.PI * 2;
        const dist = GAME_TILE * (3 + Math.random() * 2);
        const tx = lp.x + Math.cos(angle) * dist;
        const ty = lp.y + Math.sin(angle) * dist;
        if (canMoveTo(tx, ty, orcRadius)) { orc.x = tx; orc.y = ty; orcPlaced = true; break; }
      }
      if (!orcPlaced) { const safe = getRandomSafePosition(); orc.x = safe.x; orc.y = safe.y; }
      orc.hp = abil.orcHp || 600;
      orc.maxHp = abil.orcHp || 600;
      orc.isSummon = true;
      orc.summonOwner = lp.id;
      orc.summonType = 'dnd-orc';
      orc.summonSpeed = abil.orcSpeed || 2.5;
      orc.summonDamage = abil.damage || 200;
      orc.summonAttackCD = abil.orcAttackCD || 1;
      orc.summonAttackTimer = 0;
      orc.summonTargetId = lp.id; // attacks its OWN summoner
      orc.isCPU = true;
      gamePlayers.push(orc);
      if (!lp.dndOrcIds) lp.dndOrcIds = [];
      lp.dndOrcIds.push(orcId);
      lp.effects.push({ type: 'dnd-quest', timer: 1.0 });
      combatLog.push({ text: '⚔️ Quest started! An Orc appears!', timer: 3, color: '#556b2f' });
    } else if (isIllusion) {
      // Illusion E: The Illusion Of Myself — go invisible, spawn a copy (hard AI, no attacks)
      lp.cdE = abil.cooldown;
      lp.illusionInvisTimer = abil.duration || 10;
      // Kill old copy if exists
      if (lp.illusionCopyId) {
        const oldCopy = gamePlayers.find(p => p.id === lp.illusionCopyId);
        if (oldCopy && oldCopy.alive) { oldCopy.alive = false; oldCopy.hp = 0; oldCopy.effects.push({ type: 'death', timer: 2 }); }
      }
      const copyId = 'illusion-copy-' + lp.id + '-' + Date.now();
      const copyFighter = lp.fighter;
      const copy = createPlayerState(
        { id: copyId, name: lp.name, color: lp.color || '#7f8fa6', fighterId: 'illusion' },
        { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
        copyFighter
      );
      copy.x = lp.x; copy.y = lp.y;
      copy.hp = lp.hp; copy.maxHp = lp.maxHp;
      copy.isSummon = true;
      copy.summonOwner = lp.id;
      copy.summonType = 'illusion-copy';
      copy.isCPU = true;
      copy.noCloneHeal = true;
      copy.illusionNoAttack = true; // copy cannot attack
      copy.difficulty = 'hard';
      copy.aiState = {
        moveTarget: null, attackTarget: null, thinkTimer: 0, abilityTimer: 0,
        lastSeenPositions: {}, strafeDir: Math.random() < 0.5 ? 1 : -1, retreating: false,
      };
      gamePlayers.push(copy);
      lp.illusionCopyId = copyId;
      lp.effects.push({ type: 'illusion-vanish', timer: 1.0 });
      combatLog.push({ text: '👻 The Illusion Of Myself! Invisible for 10s!', timer: 3, color: '#7f8fa6' });
    } else if (isDragon) {
      // Dragon E: Dragon Ride — fly over obstacles for 5s
      lp.cdE = abil.cooldown;
      lp.dragonFlying = true;
      lp.dragonFlyTimer = abil.flyDuration || 5;
      lp.effects.push({ type: 'dragon-fly', timer: (abil.flyDuration || 5) + 0.5 });
      combatLog.push({ text: '🐉 Dragon Ride! Flying for 5s!', timer: 3, color: '#5b8fa8' });
    } else if (isDogTooth) {
      // Dog Tooth E: Toggle Ouriel on/off (no CD unless Ouriel dies)
      // If Ouriel is already out and alive, despawn (no CD)
      if (lp.dogtoothOurielId) {
        const existingO = gamePlayers.find(p => p.id === lp.dogtoothOurielId);
        if (existingO && existingO.alive) {
          // Despawn Ouriel — save HP for next summon
          lp.dogtoothOurielHp = existingO.hp;
          lp.dogtoothOurielHitsLeft = existingO.ourielHitsLeft;
          existingO.alive = false; existingO.hp = 0;
          const idx = gamePlayers.indexOf(existingO);
          if (idx >= 0) gamePlayers.splice(idx, 1);
          lp.dogtoothOurielId = null;
          combatLog.push({ text: '✝️ Ouriel recalled.', timer: 3, color: '#ddd' });
          return;
        }
      }
      // Spawn Ouriel (no CD set here — CD only on Ouriel death)
      const ourielId = 'ouriel-' + lp.id + '-' + Date.now();
      const angle = Math.random() * Math.PI * 2;
      const spawnX = lp.x + Math.cos(angle) * GAME_TILE * 2;
      const spawnY = lp.y + Math.sin(angle) * GAME_TILE * 2;
      const ourielFighter = { id: 'ouriel-summon', name: 'Ouriel', hp: 999999, healAmount: 0, healDelay: 999, healTick: 999, speed: 2.0, abilities: [] };
      const ouriel = createPlayerState(
        { id: ourielId, name: 'Ouriel', color: '#ddd' },
        { r: Math.floor(spawnY / GAME_TILE), c: Math.floor(spawnX / GAME_TILE) },
        ourielFighter
      );
      ouriel.x = spawnX; ouriel.y = spawnY;
      const oR = GAME_TILE * PLAYER_RADIUS_RATIO;
      if (!canMoveTo(ouriel.x, ouriel.y, oR)) { const s = getRandomSafePosition(); ouriel.x = s.x; ouriel.y = s.y; }
      // Restore HP if Ouriel was previously recalled
      const carryHp = lp.dogtoothOurielHp || 999999;
      const carryHits = lp.dogtoothOurielHitsLeft || (abil.ourielHitsToBreak || 2);
      ouriel.hp = carryHp; ouriel.maxHp = 999999;
      ouriel.isSummon = true; ouriel.summonOwner = lp.id;
      ouriel.summonType = 'ouriel';
      ouriel.summonSpeed = 2.0;
      ouriel.ourielHitsLeft = carryHits;
      ouriel.ourielHealPerSec = abil.healPerSec || 40;
      ouriel.ourielRoomHp = abil.roomHp || 500;
      ouriel.ourielRoomDPS = abil.roomDPS || 40;
      ouriel.isCPU = true;
      gamePlayers.push(ouriel);
      lp.dogtoothOurielId = ourielId;
      lp.effects.push({ type: 'ouriel-summon', timer: 1.5 });
      combatLog.push({ text: '✝️ Ouriel summoned! Heals 40 HP/s, 2 hits to break.', timer: 4, color: '#ddd' });
    } else if (isOmori) {
      // Omori E: Party Friend — spawn Kel, Aubrey, or Hero
      lp.cdE = abil.cooldown;
      if (!lp.omoriPartyIds) lp.omoriPartyIds = [];
      // Kill old party friend if exists
      for (const pid of lp.omoriPartyIds) {
        const old = gamePlayers.find(p => p.id === pid);
        if (old && old.alive) { old.alive = false; old.hp = 0; old.effects.push({ type: 'death', timer: 2 }); }
      }
      lp.omoriPartyIds = [];
      const roll = Math.random();
      let friendType, friendName, friendHp, friendColor;
      if (roll < 0.333) {
        friendType = 'omori-kel'; friendName = 'Kel'; friendHp = abil.kelHp || 1000; friendColor = '#f39c12';
      } else if (roll < 0.666) {
        friendType = 'omori-aubrey'; friendName = 'Aubrey'; friendHp = abil.aubreyHp || 1300; friendColor = '#e84393';
      } else {
        friendType = 'omori-hero'; friendName = 'Hero'; friendHp = abil.heroHp || 1000; friendColor = '#00b894';
      }
      const friendId = friendType + '-' + lp.id + '-' + Date.now();
      const friendFighter = { id: friendType, name: friendName, hp: friendHp, healAmount: 0, healDelay: 999, healTick: 999, speed: 3.4, abilities: [] };
      const angle = Math.random() * Math.PI * 2;
      const spX = lp.x + Math.cos(angle) * GAME_TILE * 2;
      const spY = lp.y + Math.sin(angle) * GAME_TILE * 2;
      const friend = createPlayerState(
        { id: friendId, name: friendName, color: friendColor },
        { r: Math.floor(spY / GAME_TILE), c: Math.floor(spX / GAME_TILE) }, friendFighter
      );
      friend.x = spX; friend.y = spY;
      const fR = GAME_TILE * PLAYER_RADIUS_RATIO;
      if (!canMoveTo(friend.x, friend.y, fR)) { const s = getRandomSafePosition(); friend.x = s.x; friend.y = s.y; }
      friend.hp = friendHp; friend.maxHp = friendHp;
      friend.isSummon = true; friend.summonOwner = lp.id;
      friend.summonType = friendType;
      friend.summonSpeed = 3.4;
      friend.summonDamage = friendType === 'omori-kel' ? (abil.kelDamage || 200) : friendType === 'omori-aubrey' ? (abil.aubreyDamage || 200) : (abil.heroDamage || 100);
      friend.summonAttackCD = friendType === 'omori-kel' ? (abil.kelFireCD || 1) : friendType === 'omori-aubrey' ? (abil.aubreyAttackCD || 0.5) : (abil.heroAttackCD || 0.5);
      friend.summonAttackTimer = 0;
      if (friendType === 'omori-kel') friend.summonProjectileSpeed = abil.kelProjectileSpeed || 30;
      friend.isCPU = true;
      gamePlayers.push(friend);
      lp.omoriPartyIds.push(friendId);
      lp.effects.push({ type: 'omori-party-spawn', timer: 1.5 });
      combatLog.push({ text: '🎉 ' + friendName + ' joined the party!', timer: 4, color: friendColor });
    } else if (isUnstable) {
      // Unstable Gamble: 100-1000 DMG melee + teleport enemy to random safe location
      const range = (abil.range || 1.5) * GAME_TILE;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist > range) continue;
        const dot = (dx * aimNx + dy * aimNy) / (dist || 1);
        if (dot < 0) continue;
        // Random damage 100-1000
        const dmg = 100 + Math.floor(Math.random() * 901);
        dealDamage(lp, target, dmg);
        // Teleport to random safe location
        if (target.alive) {
          const safe = getRandomSafePosition();
          target.x = safe.x; target.y = safe.y;
          target.effects.push({ type: 'unstable-teleport', timer: 1.0 });
        }
        combatLog.push({ text: '🎲 Unstable Gamble! ' + dmg + ' damage!', timer: 3, color: '#ff00ff' });
      }
      lp.effects.push({ type: 'unstable-gamble', timer: 0.5, aimNx, aimNy });
    } else if (isPyro) {
      // Pyromaniac: Gasoline — pour gasoline trail behind for 5s
      lp.cdE = abil.cooldown;
      lp.pyroGasolineTimer = abil.duration || 5;
      lp._pyroGasDrop = 0;
      if (!lp.pyroGasolineTrail) lp.pyroGasolineTrail = [];
      lp.effects.push({ type: 'pyro-gasoline', timer: abil.duration || 5 });
      combatLog.push({ text: '🛢️ Pouring gasoline!', timer: 2, color: '#ff8800' });
    } else if (isHeavyRope) {
      // Heavy Rope: Rope Swing — toggle shield / release for damage
      if (lp.ropeSwingActive) {
        // Second press: release the swing for damage
        let swingRange = (abil.range || 2.5) * GAME_TILE;
        let swingDmg = abil.damage || 500;
        if (lp.ropeGripActive) {
          swingRange *= 0.5;
          swingDmg = lp.fighter.abilities[2].swingDamage || 750;        }
        if (lp.supportBuff > 0) swingDmg *= 1.5;
        if (lp.intimidated > 0) swingDmg *= 0.5;
        const nx = lp.ropeSwingNx; const ny = lp.ropeSwingNy;
        for (const target of gamePlayers) {
          if (target.id === lp.id || !target.alive) continue;
          if (target.isSummon && target.summonOwner === lp.id) continue;
          if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
          const dx = target.x - lp.x; const dy = target.y - lp.y;
          const dist = Math.sqrt(dx * dx + dy * dy);
          if (dist > swingRange) continue;
          const dot = (dx * nx + dy * ny) / (dist || 1);
          if (dot < 0.3) continue;
          dealDamage(lp, target, swingDmg);
          target.effects.push({ type: 'hit', timer: 0.5 });
        }
        lp.ropeSwingActive = false;
        lp.cdE = abil.cooldown;
        lp.stunned = 0.5; // 0.5s pause on release
        lp.effects.push({ type: 'rope-swing-release', timer: 0.4, aimNx: nx, aimNy: ny });
        combatLog.push({ text: '🪢 Rope released!', timer: 2, color: '#8b4513' });
      } else {
        // First press: start swinging rope — shield one side (no cooldown yet)
        lp.cdE = 0; // reset so player can press E again to release
        const cw = gameCanvas.width; const ch = gameCanvas.height;
        const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
        const aimX = mouseX + camX; const aimY = mouseY + camY;
        const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
        const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
        lp.ropeSwingActive = true;
        lp.ropeSwingNx = aimDx / aimDist;
        lp.ropeSwingNy = aimDy / aimDist;
        lp.effects.push({ type: 'rope-swing-start', timer: 0.5 });
        combatLog.push({ text: '🪢 Rope swing! Shield active. Press E again to release.', timer: 3, color: '#8b4513' });
      }
    } else if (isHitman) {
      // Hitman E: Heightened Senses — reveal all fighters for 10s
      if (lp.hitmanConcealTimer > 0) { lp.cdE = 0; return; } // blocked while concealed
      lp.hitmanSenseTimer = abil.duration || 10;
      lp.effects.push({ type: 'hitman-sense', timer: abil.duration || 10 });
      combatLog.push({ text: '👁 Heightened Senses! All fighters revealed for ' + (abil.duration || 10) + 's!', timer: 3, color: '#60cfff' });
    } else {
      // Fighter: Buff — damage boost + slow nearby enemies
      lp.supportBuff = abil.duration;
      lp.effects.push({ type: 'support', timer: 1.5 });
      // Team buff sharing: nearby allies get half-duration support buff
      if (gameMode === 'teams' && lp.team && !lp.isSummon) {
        const buffRange = TEAM_HEAL_RANGE * GAME_TILE;
        const allyDur = Math.round(abil.duration * 0.5);
        for (const ally of gamePlayers) {
          if (ally.id === lp.id || !ally.alive || ally.isSummon || ally.team !== lp.team) continue;
          const adx = ally.x - lp.x; const ady = ally.y - lp.y;
          if (Math.sqrt(adx * adx + ady * ady) <= buffRange) {
            ally.supportBuff = Math.max(ally.supportBuff, allyDur);
            ally.effects.push({ type: 'team-buff', timer: 0.5 });
          }
        }
      }
      // Slow nearby enemies
      const slowRange = (abil.slowRange || 8) * GAME_TILE;
      const slowDur = abil.slowDuration || 7;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive || (target.isSummon && target.summonOwner === lp.id)) continue;
        // Skip teammates in team mode
        if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
        const sdx = target.x - lp.x, sdy = target.y - lp.y;
        if (Math.sqrt(sdx * sdx + sdy * sdy) < slowRange) {
          target.buffSlowed = slowDur;
        }
      }
      if (typeof socket !== 'undefined' && socket.emit) {
        if (!isHostAuthority) socket.emit('player-buff', { type: 'support', duration: abil.duration });
      }
    }
  }

  else if (key === 'R') {
    if (lp.cdR > 0) return;
    // Bug Fixing: check if R (slot 2) is disabled
    if (lp.modDisabledAbilities && lp.modDisabledAbilities.includes(2)) {
      combatLog.push({ text: '🐛 Move 2 is disabled by Bug Fixing!', timer: 2, color: '#e67e22' });
      return;
    }
    const abil = fighter.abilities[2];
    lp.cdR = abil.cooldown;

    if (isPoker) {
      // Blinds: random outcome
      const roll = Math.random();
      if (lp.pokerFullHouseActive) {
        // Full House: guaranteed Dealer
        lp.pokerFullHouseActive = false;
        lp.blindBuff = 'dealer';
        lp.blindTimer = 0;
        lp.cdE = 0;
        showPopup('🎰 Full House → Dealer! Gamble reset!');
        lp.effects.push({ type: 'blind-dealer', timer: 2.0 });
      } else if (roll < 0.70) {
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
        if (!isHostAuthority) socket.emit('player-buff', { type: 'blind', duration: lp.blindBuff === 'big' ? 60 : 0 });
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
      // 1X1X1X1 R: Mass Infection — close-range slash + invisible expanding shockwave blocked by cover
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const baseAngle = Math.atan2(aimDy, aimDx);
      let dmg = abil.damage;
      if (lp.supportBuff > 0) dmg *= 1.5;
      if (lp.intimidated > 0) dmg *= 0.5;
      // Close-range slash: 50 bonus damage to anyone within melee range (1.5 tiles) in front
      const slashRange = 1.5 * GAME_TILE;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        const sdx = target.x - lp.x; const sdy = target.y - lp.y;
        const sDist = Math.sqrt(sdx * sdx + sdy * sdy);
        if (sDist > slashRange) continue;
        // Check target is roughly in front (within 90° of aim)
        const toAngle = Math.atan2(sdy, sdx);
        let angleDiff = toAngle - baseAngle;
        while (angleDiff > Math.PI) angleDiff -= Math.PI * 2;
        while (angleDiff < -Math.PI) angleDiff += Math.PI * 2;
        if (Math.abs(angleDiff) > Math.PI / 2) continue;
        dealDamage(lp, target, 50);
        if (typeof socket !== 'undefined' && socket.emit && !isHostAuthority) {
          socket.emit('player-damage', { targetId: target.id, amount: 50, attackerId: lp.id });
        }
      }
      lp.effects.push({ type: 'mass-infection-slash', timer: 0.3, aimNx: Math.cos(baseAngle), aimNy: Math.sin(baseAngle) });
      // Spawn 7 invisible shockwave projectiles in a wide 180-degree spread
      const waveCount = 7;
      const totalSpread = Math.PI; // 180 degrees
      const spd = 12 * GAME_TILE / 10; // slower than chips
      const spawnedWaves = [];
      for (let i = 0; i < waveCount; i++) {
        const angle = baseAngle + (i - (waveCount - 1) / 2) * (totalSpread / (waveCount - 1));
        const vx = Math.cos(angle) * spd;
        const vy = Math.sin(angle) * spd;
        const proj = {
          x: lp.x, y: lp.y, vx, vy,
          ownerId: lp.id, damage: dmg,
          timer: 10.0, type: 'shockwave',
          poisonDPS: abil.poisonDPS || 50,
          poisonDuration: abil.poisonDuration || 3,
        };
        projectiles.push(proj);
        spawnedWaves.push({ x: lp.x, y: lp.y, vx, vy, timer: 10.0, type: 'shockwave' });
      }
      if (typeof socket !== 'undefined' && socket.emit) {
        if (!isHostAuthority) socket.emit('projectile-spawn', { projectiles: spawnedWaves });
      }
      combatLog.push({ text: '☣ Mass Infection!', timer: 3, color: '#00ff66' });
    } else if (isCricket) {
      // Cricket R: Gear Up — damage reduction + damage boost + speed penalty for 10s
      lp.gearUpTimer = abil.duration || 10;
      lp.effects.push({ type: 'gear-up', timer: abil.duration || 10 });
      combatLog.push({ text: '🪖 Geared Up! 80% DR, 50% DMG for ' + (abil.duration || 10) + 's', timer: 3, color: '#3498db' });
      showPopup('🪖 GEAR UP!');
    } else if (isDeer) {
      // Deer R: Deer's Seer — dodge state for 5 seconds, cannot attack
      lp.deerSeerTimer = abil.duration || 5;
      lp.effects.push({ type: 'deer-seer', timer: abil.duration || 5 });
      combatLog.push({ text: '🦌 Seer! Dodging all attacks!', timer: 3, color: '#dda0dd' });
      showPopup('👁 SEER MODE!');
    } else if (isNoli) {
      // Noli R: Void Star — aim then throw area attack, self-stun after
      if (lp.noliVoidRushActive || lp.noliVoidStarAiming) return;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      lp.noliVoidStarAiming = true;
      lp.noliVoidStarAimX = mouseX + camX;
      lp.noliVoidStarAimY = mouseY + camY;
      lp.noliVoidStarTimer = abil.aimTime || 1.5;
      lp.effects.push({ type: 'void-star-aim', timer: (abil.aimTime || 1.5) + 0.5 });
      combatLog.push({ text: '⭐ Aiming Void Star...', timer: 2, color: '#a020f0' });
    } else if (isHitman) {
      // Hitman R: Backup — spawn 2 backup fighters (pistol agents)
      if (lp.hitmanConcealTimer > 0) { lp.cdR = 0; return; }
      // Remove any existing backup summons
      for (const bid of (lp.hitmanBackupIds || [])) {
        const b = gamePlayers.find(x => x.id === bid);
        if (b && b.alive) { b.alive = false; _deferredRemoveIds.push(bid); }
      }
      lp.hitmanBackupIds = [];
      const bCount = abil.backupCount || 2;
      for (let bi = 0; bi < bCount; bi++) {
        const bId = 'hitman-backup-' + lp.id + '-' + bi + '-' + Date.now();
        const bFighter = { id: 'backup-agent', name: 'Agent', hp: abil.backupHp || 600, healAmount: 0, healDelay: 999, healTick: 999, speed: abil.backupSpeed || 3.0, abilities: [] };
        const angle = (bi / bCount) * Math.PI * 2;
        const spX = lp.x + Math.cos(angle) * GAME_TILE * 2;
        const spY = lp.y + Math.sin(angle) * GAME_TILE * 2;
        const bAgent = createPlayerState(
          { id: bId, name: 'Agent', color: '#8899aa' },
          { r: Math.floor(spY / GAME_TILE), c: Math.floor(spX / GAME_TILE) }, bFighter
        );
        bAgent.x = spX; bAgent.y = spY;
        const bPr = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(bAgent.x, bAgent.y, bPr)) { const s = getRandomSafePosition(); bAgent.x = s.x; bAgent.y = s.y; }
        bAgent.hp = abil.backupHp || 600; bAgent.maxHp = abil.backupHp || 600;
        bAgent.isSummon = true; bAgent.summonOwner = lp.id;
        bAgent.summonType = 'hitman-backup';
        bAgent.summonSpeed = abil.backupSpeed || 3.0;
        bAgent.summonDamage = abil.damage || 100;
        bAgent.summonAttackCD = abil.backupAttackCD || 0.5;
        bAgent.summonAttackTimer = abil.backupWindup || 1; // windup before first shot
        bAgent.summonProjectileSpeed = 28;
        bAgent.isCPU = true;
        gamePlayers.push(bAgent);
        lp.hitmanBackupIds.push(bId);
      }
      lp.effects.push({ type: 'hitman-backup', timer: 1.0 });
      combatLog.push({ text: '🕵️ Backup called! 2 agents deployed!', timer: 3, color: '#8899aa' });
    } else if (isCat) {
      // Exploding Cat R: Attack buff — scratch does 200 for 5s
      if (lp.catNopeTimer > 0 && lp.catNopeAbility === 'R') {
        combatLog.push({ text: '🚫 Noped! Can\'t use Attack!', timer: 2, color: '#e94560' });
        return;
      }
      lp.cdR = abil.cooldown;
      const dur = abil.buffDuration || 5;
      lp.catAttackBuff = dur;
      lp.effects.push({ type: 'cat-attack-buff', timer: dur });
      combatLog.push({ text: '😼 Attack! Scratch deals 200 for ' + dur + 's!', timer: 3, color: '#ff4444' });
      showPopup('😼 ATTACK BUFF!');
    } else if (isNapoleon) {
      // Napoleon R: Cannon — spawn/replace a stationary cannon
      if (lp.napoleonCannonId) {
        const oldIdx = gamePlayers.findIndex(p => p.id === lp.napoleonCannonId);
        if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers.splice(oldIdx, 1); }
        lp.napoleonCannonId = null;
      }
      const cannonId = 'cannon-' + lp.id + '-' + Date.now();
      const cannon = createPlayerState(
        { id: cannonId, name: 'Cannon', color: '#555', fighterId: 'napoleon' },
        { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
        fighter
      );
      cannon.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 2;
      cannon.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 2;
      cannon.hp = abil.cannonHp || 600;
      cannon.maxHp = abil.cannonHp || 600;
      cannon.isSummon = true;
      cannon.summonOwner = lp.id;
      cannon.summonType = 'napoleon-cannon';
      cannon.summonSpeed = 0;
      cannon.summonDamage = abil.damage || 700;
      cannon.summonAttackCD = abil.cannonFireCD || 5;
      cannon.summonAttackTimer = 0;
      cannon.summonProjectileSpeed = abil.projectileSpeed || 30;
      gamePlayers.push(cannon);
      lp.napoleonCannonId = cannonId;
      lp.effects.push({ type: 'cannon-place', timer: 1.0 });
      combatLog.push({ text: '💣 Cannon deployed!', timer: 3, color: '#555' });
    } else if (isModerator) {
      // Moderator R: Bug Fixing — disable a random enemy's random move until next death
      lp.cdR = abil.cooldown;
      const enemies = gamePlayers.filter(p => {
        if (!p.alive || p.isSummon || p.id === lp.id || !p.fighter) return false;
        if (gameMode === 'teams' && lp.team && p.team === lp.team) return false;
        return true;
      });
      if (enemies.length > 0) {
        const victim = enemies[Math.floor(Math.random() * enemies.length)];
        const aliveNonSummons = gamePlayers.filter(p => p.alive && !p.isSummon && p.fighter).length;
        const is1v1 = aliveNonSummons <= 2;
        // Pick a random ability to disable (E=1, R=2, T=3)
        const disableSlots = [1, 2, 3];
        const slot = disableSlots[Math.floor(Math.random() * disableSlots.length)];
        const abilNames = { 1: 'Move 1 (E)', 2: 'Move 2 (R)', 3: 'Move 3 (T)' };
        if (!victim.modDisabledAbilities) victim.modDisabledAbilities = [];
        victim.modDisabledAbilities.push(slot);
        if (!lp.modBugFixedTargets) lp.modBugFixedTargets = [];
        lp.modBugFixedTargets.push({ targetId: victim.id, slot });
        combatLog.push({ text: '🐛 Bug Fix! Disabled ' + victim.name + '\'s ' + abilNames[slot] + '!', timer: 4, color: '#e67e22' });
        if (victim.id === localPlayerId) {
          combatLog.push({ text: '⚠️ Your ' + abilNames[slot] + ' was DISABLED by Moderator!', timer: 5, color: '#ff0000' });
        }
        // In 1v1: also disable their special
        if (is1v1) {
          victim.modDisabledAbilities.push(4); // 4 = SPACE special
          lp.modBugFixedTargets.push({ targetId: victim.id, slot: 4 });
          combatLog.push({ text: '🐛 1v1 Bug Fix! Also disabled ' + victim.name + '\'s Special!', timer: 4, color: '#e67e22' });
          if (victim.id === localPlayerId) {
            combatLog.push({ text: '⚠️ Your Special was DISABLED by Moderator!', timer: 5, color: '#ff0000' });
          }
        }
      } else {
        combatLog.push({ text: 'No enemies to bug fix!', timer: 2, color: '#999' });
      }
    } else if (isDnd) {
      // D&D R: Buy/Use — spend GP to buy items (highest affordable tier)
      const gp = lp.dndGP || 0;
      if (gp <= 0) {
        combatLog.push({ text: '💰 No GP! Complete quests first.', timer: 2, color: '#999' });
        return;
      }
      lp.cdR = 0;
      if (gp >= 8 && !lp.dndCharm) {
        // Charm: doubled autoheal + permanent M1 buff
        lp.dndCharm = true;
        lp.dndWeaponBonus = (lp.dndWeaponBonus || 0) + 50;
        lp.dndGP = 0;
        lp.effects.push({ type: 'dnd-charm', timer: 2.0 });
        combatLog.push({ text: '✨ Charm of Healing purchased! Autoheal doubled + M1 permanently buffed +50.', timer: 4, color: '#ffd700' });
      } else if (gp >= 8 && lp.dndCharm) {
        // Charm already purchased — don't spend GP, fall through to 5GP tier
        if (gp >= 5) {
          lp.dndWeaponBonus = (lp.dndWeaponBonus || 0) + 50;
          lp.dndGP = 0;
          lp.effects.push({ type: 'dnd-weapon', timer: 2.0 });
          combatLog.push({ text: 'Charm already purchased! Bought weapon instead. M1 +50 (total +' + lp.dndWeaponBonus + ').', timer: 4, color: '#c0c0c0' });
        }
      } else if (gp >= 5) {
        // Better weapon: +50 permanent M1 dmg
        lp.dndWeaponBonus = (lp.dndWeaponBonus || 0) + 50;
        lp.dndGP = 0;
        lp.effects.push({ type: 'dnd-weapon', timer: 2.0 });
        combatLog.push({ text: '⚔️ Better Weapon! M1 +50 damage (total +' + lp.dndWeaponBonus + ').', timer: 4, color: '#c0c0c0' });
      } else if (gp >= 2) {
        // Random spell (1 of 3)
        lp.dndGP = 0;
        const spellRoll = Math.random();
        const cw = gameCanvas.width; const ch = gameCanvas.height;
        const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
        const aimX = mouseX + camX; const aimY = mouseY + camY;
        const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
        const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
        const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
        if (spellRoll < 0.33) {
          // Zombie spawn: 2 zombies
          for (let zi = 0; zi < 2; zi++) {
            const zId = 'dnd-zombie-' + lp.id + '-' + Date.now() + '-' + zi;
            const zFighter = getFighter('fighter');
            const z = createPlayerState(
              { id: zId, name: 'Zombie', color: '#2d5e1e', fighterId: 'fighter' },
              { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) }, zFighter
            );
            const zRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
            const angle = Math.random() * Math.PI * 2;
            z.x = lp.x + Math.cos(angle) * GAME_TILE * 2;
            z.y = lp.y + Math.sin(angle) * GAME_TILE * 2;
            if (!canMoveTo(z.x, z.y, zRadius)) { const s = getRandomSafePosition(); z.x = s.x; z.y = s.y; }
            z.hp = 300; z.maxHp = 300;
            z.isSummon = true; z.summonOwner = lp.id;
            z.summonType = 'dnd-zombie';
            z.summonSpeed = 2.0; z.summonDamage = 150;
            z.summonAttackCD = 1.5; z.summonAttackTimer = 0;
            z.isCPU = true;
            gamePlayers.push(z);
          }
          combatLog.push({ text: '🧟 Zombie Spell! 2 zombies summoned.', timer: 3, color: '#2d5e1e' });
          lp.effects.push({ type: 'dnd-spell', timer: 1.5 });
        } else if (spellRoll < 0.66) {
          // Large fast 3×3 fireball (goes through walls, stops at sea)
          const speed = (abil.spellFireballSpeed || 30) * GAME_TILE / 10;
          const fbAoe = (abil.spellFireballRadius || 3) * GAME_TILE;
          projectiles.push({
            x: lp.x, y: lp.y,
            vx: aimNx * speed, vy: aimNy * speed,
            ownerId: lp.id, damage: abil.spellFireballDmg || 300,
            timer: 999, type: 'dnd-fireball', color: '#ff4500',
            dndFireball: true, aoeRadius: fbAoe,
          });
          combatLog.push({ text: '🔥 Fireball launched!', timer: 3, color: '#ff4500' });
          lp.effects.push({ type: 'dnd-spell', timer: 1.5 });
        } else {
          // Blur spell: fast projectile, hits = blur + 300 dmg
          const speed = (abil.spellBlurSpeed || 50) * GAME_TILE / 10;
          projectiles.push({
            x: lp.x, y: lp.y,
            vx: aimNx * speed, vy: aimNy * speed,
            ownerId: lp.id, damage: abil.spellBlurDmg || 300,
            timer: 999, type: 'dnd-blur-bolt', color: '#9b59b6',
            dndBlurDuration: abil.spellBlurDuration || 8,
          });
          combatLog.push({ text: '🌀 Blur Spell cast!', timer: 3, color: '#9b59b6' });
          lp.effects.push({ type: 'dnd-spell', timer: 1.5 });
        }
      } else {
        // 1 GP: Healing potion (300 HP over 3s)
        lp.dndGP = 0;
        lp.dndHealPool = abil.potionHeal || 300;
        lp.effects.push({ type: 'dnd-potion', timer: 1.5 });
        combatLog.push({ text: '🧪 Healing Potion! +300 HP over 3s.', timer: 3, color: '#e74c3c' });
      }
    } else if (isIllusion) {
      // Illusion R: The Illusion Of Space — teleport everyone (except self) back to where they were 3s ago
      lp.cdR = abil.cooldown;
      const rewindTime = (abil.rewindTime || 3) * 1000; // milliseconds
      const now = Date.now();
      const pRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
      for (const p of gamePlayers) {
        if (!p.alive || p.isSummon) continue;
        if (p.id === lp.id) continue; // don't rewind self
        if (!p.illusionPositionHistory || p.illusionPositionHistory.length === 0) continue;
        // Find the position closest to 3s ago
        let bestPos = null;
        let bestDiff = Infinity;
        for (const entry of p.illusionPositionHistory) {
          const diff = Math.abs((now - entry.t) - rewindTime);
          if (diff < bestDiff) { bestDiff = diff; bestPos = entry; }
        }
        if (bestPos && canMoveTo(bestPos.x, bestPos.y, pRadius)) {
          p.x = bestPos.x;
          p.y = bestPos.y;
          p.effects.push({ type: 'illusion-rewind', timer: 1.0 });
        }
      }
      lp.effects.push({ type: 'illusion-space', timer: 1.5 });
      combatLog.push({ text: '🌀 The Illusion Of Space! Everyone rewound 3 seconds!', timer: 4, color: '#7f8fa6' });
    } else if (isDragon) {
      // Dragon R: Dragon Beam — 3s charge, then fire
      if (lp.dragonBeamCharging || lp.dragonBeamRecovery > 0) return;
      lp.cdR = abil.cooldown;
      lp.dragonBeamCharging = true;
      lp.dragonBeamChargeTimer = abil.chargeTime || 3;
      lp.dragonBreathActive = false; // cancel breath
      // Set initial aim direction (will slowly track mouse during charge)
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      lp.dragonBeamAimNx = aimDx / aimDist;
      lp.dragonBeamAimNy = aimDy / aimDist;
      lp.effects.push({ type: 'dragon-beam-charge', timer: (abil.chargeTime || 3) + 0.5 });
      combatLog.push({ text: '❄️ Dragon Beam charging — aim slowly!', timer: 3, color: '#00ccff' });
    } else if (isDogTooth) {
      // Dog Tooth R: The Smile Tapes — auto-chase + 500 dmg M1 for 10s
      lp.cdR = abil.cooldown;
      lp.dogtoothSmileTimer = abil.duration || 10;
      lp.dogtoothSmileDmg = abil.damage || 500;
      lp.effects.push({ type: 'smile-tapes', timer: (abil.duration || 10) + 0.5 });
      combatLog.push({ text: '😈 The Smile Tapes! Auto-chasing for 10s! M1 = 500 dmg!', timer: 4, color: '#ff0000' });
    } else if (isOmori) {
      // Omori R: Party Skill — depends on nearby party friend
      if (!lp.omoriPartyIds || lp.omoriPartyIds.length === 0) {
        combatLog.push({ text: '❌ No party friend nearby!', timer: 2, color: '#888' });
        return;
      }
      const nearestParty = gamePlayers.find(p => lp.omoriPartyIds.includes(p.id) && p.alive);
      if (!nearestParty) {
        combatLog.push({ text: '❌ No party friend alive!', timer: 2, color: '#888' });
        return;
      }
      lp.cdR = abil.cooldown;
      if (nearestParty.summonType === 'omori-kel') {
        lp.omoriKelBuffTimer = abil.kelBuffDuration || 15;
        lp.effects.push({ type: 'omori-kel-buff', timer: (abil.kelBuffDuration || 15) + 0.5 });
        combatLog.push({ text: '🏀 Kel Skill! +50% ATK for 15s!', timer: 4, color: '#f39c12' });
      } else if (nearestParty.summonType === 'omori-aubrey') {
        lp.omoriAubreyBuffTimer = abil.aubreyBuffDuration || 20;
        lp.effects.push({ type: 'omori-aubrey-buff', timer: (abil.aubreyBuffDuration || 20) + 0.5 });
        combatLog.push({ text: '🦇 Aubrey Skill! 10% chance for 600 dmg hits for 20s!', timer: 4, color: '#e84393' });
      } else if (nearestParty.summonType === 'omori-hero') {
        lp.omoriHeroHealPool = abil.heroHealAmount || 700;
        lp.omoriHeroHealTimer = abil.heroHealDuration || 1;
        lp.effects.push({ type: 'omori-hero-heal', timer: (abil.heroHealDuration || 1) + 0.5 });
        combatLog.push({ text: '🍳 Hero Skill! Healing 700 HP!', timer: 4, color: '#00b894' });
      }
    } else if (isUnstable) {
      // Unstable Infantry: spawn 3 infantrymen that teleport enemies to spawn on hit
      if (!lp.unstableInfantryIds) lp.unstableInfantryIds = [];
      for (let i = 0; i < (abil.infantryCount || 3); i++) {
        const infId = 'unstable-inf-' + lp.id + '-' + i + '-' + Date.now();
        const infFighter = getFighter('fighter');
        const inf = createPlayerState(
          { id: infId, name: 'Unstable Infantry', color: '#ff00ff', fighterId: 'fighter' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) }, infFighter
        );
        inf.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 3;
        inf.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 3;
        const infR = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(inf.x, inf.y, infR)) { inf.x = lp.x; inf.y = lp.y; }
        inf.hp = abil.infantryHp || 50; inf.maxHp = abil.infantryHp || 50;
        inf.isSummon = true; inf.summonOwner = lp.id; inf.summonType = 'unstable-infantry';
        inf.summonSpeed = abil.infantrySpeed || 2.0; inf.summonDamage = abil.damage || 100;
        inf.summonAttackCD = abil.infantryFireCD || 2.5; inf.summonAttackTimer = 0;
        inf.summonProjectileSpeed = abil.infantryProjectileSpeed || 38;
        inf.summonProjectileRange = abil.infantryRange || 0.8;
        inf.unstableTeleportToSpawn = true; // flag: hit enemies get teleported to spawn
        gamePlayers.push(inf);
        lp.unstableInfantryIds.push(infId);
      }
      lp.effects.push({ type: 'unstable-infantry', timer: 1.5 });
      combatLog.push({ text: '⚡ Unstable Infantry spawned!', timer: 3, color: '#ff00ff' });
    } else if (isPyro) {
      // Pyromaniac: Molotov ×3 — throw 3 molotovs with shadow delay before landing
      lp.cdR = abil.cooldown;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const fireRadius = (abil.radius || 3);
      const fireDur = abil.fireDuration || 5;
      const fallDelay = abil.fallDelay || 2;
      let dmg = abil.damage || 200;
      if (lp.supportBuff > 0) dmg *= 1.5;
      if (lp.intimidated > 0) dmg *= 0.5;
      if (lp.pyroFireBuffTimer > 0) dmg *= 2;
      if (!lp.pyroMolotovShadows) lp.pyroMolotovShadows = [];
      // Create 3 shadow entries (pending impacts) spread around aim point
      const offsets = [{ x: 0, y: 0 }, { x: fireRadius * GAME_TILE * 0.8, y: 0 }, { x: -fireRadius * GAME_TILE * 0.8, y: 0 }];
      for (const off of offsets) {
        const fx = aimX + off.x + (Math.random() - 0.5) * GAME_TILE;
        const fy = aimY + off.y + (Math.random() - 0.5) * GAME_TILE;
        lp.pyroMolotovShadows.push({
          x: fx, y: fy, timer: fallDelay, radius: fireRadius,
          dmg: dmg, burnDPS: abil.burnDPS || 100, burnDur: abil.burnDuration || 3, fireDur: fireDur,
        });
      }
      lp.effects.push({ type: 'pyro-molotov', timer: 0.5 });
      combatLog.push({ text: '🔥 Molotov ×3! Impact in ' + fallDelay + 's!', timer: 2, color: '#ff4400' });
    } else if (isHeavyRope) {
      // Heavy Rope: Rope Grip — toggle half range, more damage
      // Cannot change grip while rope swing is active
      if (lp.ropeSwingActive) {
        combatLog.push({ text: '🪢 Cannot change grip while swinging!', timer: 2, color: '#cc0000' });
        return;
      }
      lp.ropeGripActive = !lp.ropeGripActive;
      if (lp.ropeGripActive) {
        combatLog.push({ text: '🪢 Rope Grip! Half range, more damage.', timer: 2, color: '#8b4513' });
        lp.effects.push({ type: 'rope-grip-on', timer: 0.5 });
      } else {
        combatLog.push({ text: '🪢 Rope Grip released.', timer: 2, color: '#8b4513' });
        lp.effects.push({ type: 'rope-grip-off', timer: 0.5 });
      }
    } else {
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
        if (typeof socket !== 'undefined' && socket.emit && !isHostAuthority) {
          socket.emit('player-knockback', { targetId: target.id, x: newTX, y: newTY });
        }
      }
      lp.effects.push({ type: 'power-arc', timer: 0.3 });
    }
  }

  else if (key === 'T') {
    if (lp.cdT > 0) return;
    // Bug Fixing: check if T (slot 3) is disabled
    if (lp.modDisabledAbilities && lp.modDisabledAbilities.includes(3)) {
      combatLog.push({ text: '🐛 Move 3 is disabled by Bug Fixing!', timer: 2, color: '#e67e22' });
      return;
    }
    const abil = fighter.abilities[3];

    if (isPoker) {
      lp.cdT = abil.cooldown;
      // Chip Change: randomize M1 damage for 30 seconds
      const options = [50, 100, 200, 300, 400];
      if (lp.pokerFullHouseActive) {
        lp.chipChangeDmg = 400; // Full House: guaranteed best
        lp.pokerFullHouseActive = false;
      } else {
        lp.chipChangeDmg = options[Math.floor(Math.random() * options.length)];
      }
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
        // Block summoning if any enemy is too close (prevents Obelisk instant-kills)
        const minSummonDist = GAME_TILE * 2;
        for (const other of gamePlayers) {
          if (other.id === lp.id || !other.alive || other.isSummon) continue;
          const sdx = other.x - lp.x, sdy = other.y - lp.y;
          if (Math.sqrt(sdx * sdx + sdy * sdy) < minSummonDist) {
            combatLog.push({ text: '⚠ Too close to an enemy to summon!', timer: 2, color: '#e94560' });
            return;
          }
        }
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
          cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
          totalDamageTaken: 0,
          specialUnlocked: false, specialUsed: false,
          supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
          noDamageTimer: 0, healTickTimer: 0, isHealing: false,
          specialJumping: false, specialAiming: false,
          specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
          effects: [],
          blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
          chairCharges: 0, isCraftingChair: false, craftTimer: 0,
          isEatingChair: false, eatTimer: 0, eatHealPool: 0,
          summonId: null, boiledOneActive: false, boiledOneTimer: 0,
          poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
          gearUpTimer: 0, wicketIds: [], driveReflectTimer: 0,
          deerFearTimer: 0, deerFearTargetX: 0, deerFearTargetY: 0,
          deerSeerTimer: 0, deerRobotId: null, iglooX: 0, iglooY: 0, iglooTimer: 0,
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
        lp.cdT = abil.cooldown;
        combatLog.push({ text: '🔮 Summoned ' + compDef.name + '!', timer: 3, color: '#d4af37' });
        lp.effects.push({ type: 'summon', timer: 1.5 });
      }
    } else if (is1x) {
      // 1X1X1X1 T: Unstable Eye — speed boost + reveal all enemies + blur
      lp.cdT = abil.cooldown;
      lp.unstableEyeTimer = abil.duration || 6;
      lp.effects.push({ type: 'unstable-eye', timer: abil.duration || 6 });
      combatLog.push({ text: '👁 Unstable Eye activated!', timer: 3, color: '#00ff66' });
      showPopup('👁 UNSTABLE EYE');
    } else if (isCricket) {
      // Cricket T: Wicket — place two wickets in a line
      lp.cdT = abil.cooldown;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      // Remove old wickets if they exist
      if (lp.wicketIds && lp.wicketIds.length > 0) {
        for (const wid of lp.wicketIds) {
          const idx = gamePlayers.findIndex(p => p.id === wid);
          if (idx >= 0) gamePlayers.splice(idx, 1);
        }
      }
      lp.wicketIds = [];
      const dist1 = GAME_TILE * 1.5;
      const dist2 = (abil.wicketDistance || 12) * GAME_TILE;
      const wHp = abil.wicketHp || 300;
      for (let wi = 0; wi < 2; wi++) {
        const wDist = wi === 0 ? dist1 : dist2;
        const wx = lp.x + aimNx * wDist;
        const wy = lp.y + aimNy * wDist;
        const wId = 'wicket-' + lp.id + '-' + wi + '-' + Date.now();
        const wicket = {
          id: wId, name: 'Wicket', color: '#c8a96e',
          x: wx, y: wy,
          hp: wHp, maxHp: wHp,
          fighter: fighter, alive: true,
          cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
          totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
          supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
          noDamageTimer: 0, healTickTimer: 0, isHealing: false,
          specialJumping: false, specialAiming: false,
          specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
          effects: [],
          blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
          chairCharges: 0, isCraftingChair: false, craftTimer: 0,
          isEatingChair: false, eatTimer: 0, eatHealPool: 0,
          summonId: null, boiledOneActive: false, boiledOneTimer: 0,
          poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
          gearUpTimer: 0, wicketIds: [], driveReflectTimer: 0, wicketOwner: lp.id,
          deerFearTimer: 0, deerFearTargetX: 0, deerFearTargetY: 0,
          deerSeerTimer: 0, deerRobotId: null, iglooX: 0, iglooY: 0, iglooTimer: 0,
          isSummon: true, summonOwner: lp.id, summonType: 'wicket',
          summonSpeed: 0, summonDamage: 0, summonStunDur: 0, summonAttackCD: 0, summonAttackTimer: 0,
        };
        gamePlayers.push(wicket);
        lp.wicketIds.push(wId);
      }
      lp.effects.push({ type: 'wicket-place', timer: 0.5 });
      combatLog.push({ text: '🏏 Wickets placed!', timer: 3, color: '#c8a96e' });
    } else if (isDeer) {
      // Deer T: Deer's Spear — antler stab, kills summons instantly, stuns 3s
      if (lp.deerSeerTimer > 0) return; // cannot attack during Seer
      lp.cdT = abil.cooldown;
      const range = (abil.range || 1.2) * GAME_TILE;
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
        if (target.isSummon) {
          dealDamage(lp, target, target.hp);
        } else {
          dealDamage(lp, target, baseDmg);
          target.stunned = Math.max(target.stunned, abil.stunDuration || 3);
          target.effects.push({ type: 'stun', timer: abil.stunDuration || 3 });
        }
      }
      lp.effects.push({ type: 'deer-spear', timer: 0.25, aimNx, aimNy });
    } else if (isNoli) {
      // Noli T: Observant — charge for 2s then teleport to opposite side (max 3 uses)
      if (lp.noliVoidRushActive || lp.noliVoidStarAiming) return;
      if (lp.noliObservantCharging > 0) return; // already charging
      if (lp.noliObservantUses >= (abil.maxUses || 3)) {
        combatLog.push({ text: '❌ No Observant charges left!', timer: 2, color: '#666' });
        lp.cdT = 0; // refund cooldown
        return;
      }
      lp.noliObservantUses++;
      lp.cdT = abil.cooldown;
      // Start 2-second charge (teleport executes in tick loop)
      const chargeTime = abil.chargeTime || 2;
      lp.noliObservantCharging = chargeTime;
      lp.noliObservantChargeMax = chargeTime;
      combatLog.push({ text: '👁 Observant charging...', timer: chargeTime + 0.5, color: '#a020f0' });
    } else if (isHitman) {
      // Hitman T: Switch Weapon — cycle Pistol → AKM → Sniper → Pistol
      if (lp.hitmanConcealTimer > 0) { lp.cdT = 0; return; }
      if (lp.hitmanEquipping) { lp.cdT = 0; return; }
      const weapons = ['pistol', 'akm', 'sniper'];
      const curIdx = weapons.indexOf(lp.hitmanWeapon || 'pistol');
      const nextIdx = (curIdx + 1) % weapons.length;
      lp.hitmanWeapon = weapons[nextIdx];
      lp.hitmanEquipping = true;
      lp.hitmanEquipTimer = abil.equipTime || 5;
      lp.hitmanReloading = false;
      lp.hitmanReloadTimer = 0;
      const wDefs = lp.fighter.abilities[0].weapons || {};
      const newWDef = wDefs[lp.hitmanWeapon];
      combatLog.push({ text: '🔫 Switching to ' + (newWDef ? newWDef.label : lp.hitmanWeapon) + '... (5s equip)', timer: 5, color: '#f5c842' });
      lp.effects.push({ type: 'hitman-switch', timer: abil.equipTime || 5 });
    } else if (isCat) {
      // Exploding Cat T: Steal — copy opponent's Move 3
      if (lp.catNopeTimer > 0 && lp.catNopeAbility === 'T') {
        combatLog.push({ text: '🚫 Noped! Can\'t use Steal!', timer: 2, color: '#e94560' });
        return;
      }
      lp.cdT = abil.cooldown;
      if (lp.catStolenReady && lp.catStolenAbil) {
        // Fire the stolen ability (costs 1 cat card)
        if ((lp.catCards || 0) < 1) {
          combatLog.push({ text: '🐱 Need a Cat card to fire stolen ability!', timer: 2, color: '#e94560' });
          lp.cdT = 0;
          return;
        }
        lp.catCards--;
        const stolenFighter = getFighter(lp.catStolenAbil.fighterId);
        const stolenAbil = stolenFighter.abilities[lp.catStolenAbil.abilIndex];
        const range = (stolenAbil.range || 1.5) * GAME_TILE;
        let baseDmg = stolenAbil.damage || 100;
        if (lp.supportBuff > 0) baseDmg *= 1.5;
        if (lp.intimidated > 0) baseDmg *= 0.5;
        // Compute aim direction for visual effect
        const fireCw = gameCanvas.width; const fireCh = gameCanvas.height;
        const fireCamX = lp.x - fireCw / 2; const fireCamY = lp.y - fireCh / 2;
        const fireAimX = mouseX + fireCamX; const fireAimY = mouseY + fireCamY;
        const fireAimDx = fireAimX - lp.x; const fireAimDy = fireAimY - lp.y;
        const fireAimDist = Math.sqrt(fireAimDx * fireAimDx + fireAimDy * fireAimDy) || 1;
        const fireAimNx = fireAimDx / fireAimDist; const fireAimNy = fireAimDy / fireAimDist;
        if (stolenAbil.type === 'buff') {
          // Stolen buff: apply supportBuff to self + slow nearby enemies
          lp.supportBuff = stolenAbil.duration || 7;
          if (stolenAbil.slowRange) {
            const slowRange = (stolenAbil.slowRange || 8) * GAME_TILE;
            const slowDur = stolenAbil.slowDuration || 7;
            for (const target of gamePlayers) {
              if (target.id === lp.id || !target.alive || (target.isSummon && target.summonOwner === lp.id)) continue;
              const sdx = target.x - lp.x, sdy = target.y - lp.y;
              if (Math.sqrt(sdx * sdx + sdy * sdy) < slowRange) target.buffSlowed = slowDur;
            }
          }
        } else if (stolenAbil.type === 'debuff') {
          // Stolen debuff: intimidate nearby enemies
          const sightRange = (stolenAbil.range || 10) * GAME_TILE;
          for (const target of gamePlayers) {
            if (target.id === lp.id || !target.alive || (target.isSummon && target.summonOwner === lp.id)) continue;
            const sdx = target.x - lp.x, sdy = target.y - lp.y;
            if (Math.sqrt(sdx * sdx + sdy * sdy) < sightRange) {
              target.intimidated = stolenAbil.duration || 10;
              target.intimidatedBy = lp.id;
            }
          }
        } else if (stolenAbil.type === 'self') {
          // Stolen self-buff: give cat a generic damage boost (supportBuff)
          lp.supportBuff = stolenAbil.duration || 5;
        } else if (stolenAbil.type === 'summon' && stolenAbil.companions) {
          // Stolen summon: spawn a temporary companion (like Oddity Overthrow)
          if (!lp.summonId) {
            const companionKeys = Object.keys(stolenAbil.companions);
            const pick = companionKeys[Math.floor(Math.random() * companionKeys.length)];
            const compDef = stolenAbil.companions[pick];
            const summonId = 'summon-' + lp.id + '-' + Date.now();
            const summon = {
              id: summonId, name: compDef.name,
              color: pick === 'fleshbed' ? '#8b4513' : pick === 'macrocosms' ? '#4a0080' : '#d4af37',
              x: lp.x + (Math.random() - 0.5) * GAME_TILE * 2,
              y: lp.y + (Math.random() - 0.5) * GAME_TILE * 2,
              hp: compDef.hp, maxHp: compDef.hp,
              fighter: lp.fighter, alive: true,
              cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
              totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
              supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
              noDamageTimer: 0, healTickTimer: 0, isHealing: false,
              specialJumping: false, specialAiming: false,
              specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
              effects: [],
              blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
              chairCharges: 0, isCraftingChair: false, craftTimer: 0,
              isEatingChair: false, eatTimer: 0, eatHealPool: 0,
              summonId: null, boiledOneActive: false, boiledOneTimer: 0,
              poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
              gearUpTimer: 0, wicketIds: [], driveReflectTimer: 0,
              deerFearTimer: 0, deerFearTargetX: 0, deerFearTargetY: 0,
              deerSeerTimer: 0, deerRobotId: null, iglooX: 0, iglooY: 0, iglooTimer: 0,
              isSummon: true, summonOwner: lp.id, summonType: pick,
              summonSpeed: compDef.speed, summonDamage: compDef.damage,
              summonStunDur: compDef.stunDuration, summonAttackCD: compDef.attackCooldown,
              summonAttackTimer: 0,
            };
            if (pick === 'obelisk') { summon.x = lp.x; summon.y = lp.y; }
            gamePlayers.push(summon);
            lp.summonId = summonId;
          }
        } else if (stolenAbil.type === 'melee') {
          const cw = gameCanvas.width; const ch = gameCanvas.height;
          const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
          const aimX = mouseX + camX; const aimY = mouseY + camY;
          const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
          const aimDist2 = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
          const aimNx = aimDx / aimDist2; const aimNy = aimDy / aimDist2;
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
        } else if (stolenAbil.projectileCount || stolenAbil.projectileSpeed) {
          const cw = gameCanvas.width; const ch = gameCanvas.height;
          const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
          const aimX = mouseX + camX; const aimY = mouseY + camY;
          const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
          const baseAngle = Math.atan2(aimDy, aimDx);
          const count = stolenAbil.projectileCount || 1;
          const spread = stolenAbil.projectileSpread || 0.15;
          for (let i = 0; i < count; i++) {
            const angle = baseAngle + (i - (count - 1) / 2) * spread;
            const spd = (stolenAbil.projectileSpeed || 8) * GAME_TILE / 10;
            projectiles.push({ x: lp.x, y: lp.y, vx: Math.cos(angle) * spd, vy: Math.sin(angle) * spd, ownerId: lp.id, damage: baseDmg, timer: 0.8, type: 'chip' });
          }
        } else {
          for (const target of gamePlayers) {
            if (target.id === lp.id || !target.alive) continue;
            if (target.isSummon && target.summonOwner === lp.id) continue;
            const dx = target.x - lp.x; const dy = target.y - lp.y;
            if (Math.sqrt(dx * dx + dy * dy) < GAME_TILE * 1.5) dealDamage(lp, target, baseDmg);
          }
        }
        combatLog.push({ text: '🐱 Used stolen ' + stolenAbil.name + '!', timer: 3, color: '#ff9900' });
        lp.effects.push({ type: 'cat-steal-fire', timer: 0.3, aimNx: fireAimNx, aimNy: fireAimNy, stolenType: stolenAbil.type });
        lp.catStolenReady = false;
        lp.catStolenAbil = null;
      } else {
        // Copy a random non-M1 ability from the closest opponent (costs 1 cat card)
        if ((lp.catCards || 0) < 1) {
          combatLog.push({ text: '🐱 Need a Cat card to steal!', timer: 2, color: '#e94560' });
          lp.cdT = 0;
          return;
        }
        lp.catCards--;
        let closestDist = Infinity, closestTarget = null;
        for (const t of gamePlayers) {
          if (t.id === lp.id || !t.alive || t.isSummon) continue;
          if (t.fighter && t.fighter.id === 'explodingcat') continue;
          const d = Math.sqrt((t.x - lp.x) ** 2 + (t.y - lp.y) ** 2);
          if (d < closestDist) { closestDist = d; closestTarget = t; }
        }
        if (closestTarget && closestTarget.fighter) {
          const fid = closestTarget.fighter.id;
          const abilIdx = 3; // Always steal Move 3 (T ability)
          lp.catStolenAbil = { fighterId: fid, abilIndex: abilIdx };
          lp.catStolenReady = true;
          const stolenName = closestTarget.fighter.abilities[abilIdx].name;
          combatLog.push({ text: '🐱 Stole ' + stolenName + ' (T) from ' + closestTarget.name + '!', timer: 3, color: '#ff9900' });
          showPopup('🐱 STOLEN: ' + stolenName);
          lp.effects.push({ type: 'cat-steal', timer: 1.0 });
        } else {
          combatLog.push({ text: '🐱 No one to steal from!', timer: 2, color: '#666' });
          lp.catCards++; // refund card
          lp.cdT = 0;
        }
      }
    } else if (isNapoleon) {
      // Napoleon T: Defensive Tactics — place a 2x2 wall entity
      lp.cdT = abil.cooldown;
      // Remove old wall if exists
      if (lp.napoleonWallId) {
        const oldIdx = gamePlayers.findIndex(p => p.id === lp.napoleonWallId);
        if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers.splice(oldIdx, 1); }
        lp.napoleonWallId = null;
      }
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      const aimNx = aimDx / aimDist; const aimNy = aimDy / aimDist;
      const wallDist = GAME_TILE * 2;
      const wx = lp.x + aimNx * wallDist;
      const wy = lp.y + aimNy * wallDist;
      const wallId = 'wall-' + lp.id + '-' + Date.now();
      const wall = createPlayerState(
        { id: wallId, name: 'Wall', color: '#8b7355', fighterId: 'napoleon' },
        { r: Math.floor(wy / GAME_TILE), c: Math.floor(wx / GAME_TILE) },
        fighter
      );
      wall.x = wx;
      wall.y = wy;
      wall.hp = 999999;
      wall.maxHp = 999999;
      wall.isSummon = true;
      wall.summonOwner = lp.id;
      wall.summonType = 'napoleon-wall';
      wall.summonSpeed = 0;
      wall.summonDamage = 0;
      wall.summonAttackCD = 0;
      wall.summonAttackTimer = 0;
      wall.wallSize = abil.wallSize || 2;
      wall.wallTimer = 30;
      gamePlayers.push(wall);
      lp.napoleonWallId = wallId;
      lp.effects.push({ type: 'wall-place', timer: 0.5 });
      combatLog.push({ text: '🧱 Defensive wall placed! (30s)', timer: 3, color: '#8b7355' });
    } else if (isModerator) {
      // Moderator T: Server Reset — TP everyone back to spawn, 3 uses per game
      if (!lp.modServerResetUses) lp.modServerResetUses = 0;
      if (lp.modServerResetUses >= (abil.maxUses || 3)) {
        combatLog.push({ text: 'Server Reset used up!', timer: 2, color: '#999' });
        return;
      }
      lp.modServerResetUses++;
      const resetRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
      for (const p of gamePlayers) {
        if (!p.alive || p.isSummon) continue;
        if (p.spawnX != null && p.spawnY != null && canMoveTo(p.spawnX, p.spawnY, resetRadius)) {
          p.x = p.spawnX;
          p.y = p.spawnY;
        } else {
          // Spawn blocked (rock/water) — use a safe fallback position
          const safe = getRandomSafePosition();
          p.x = safe.x;
          p.y = safe.y;
        }
        p.effects.push({ type: 'server-reset', timer: 1.5 });
      }
      combatLog.push({ text: '🔄 SERVER RESET! Everyone returned to spawn! (' + lp.modServerResetUses + '/' + (abil.maxUses || 3) + ')', timer: 5, color: '#3498db' });
    } else if (isDnd) {
      // D&D T: Race Change — cycle Human → Elf → Dwarf → Human
      lp.cdT = abil.cooldown || 40;
      const raceOrder = ['human', 'elf', 'dwarf'].filter(r => r !== (lp.dndRace || 'human'));
      lp.dndRace = raceOrder[Math.floor(Math.random() * raceOrder.length)];
      const raceNames = { human: 'Human (1.2× speed, Sword)', elf: 'Elf (+50 dmg, Bow)', dwarf: 'Dwarf (0.8× dmg taken, Axe)' };
      lp.effects.push({ type: 'dnd-race', timer: 1.5 });
      combatLog.push({ text: '🎭 Race changed to ' + raceNames[lp.dndRace] + '!', timer: 4, color: '#daa520' });
    } else if (isIllusion) {
      // Illusion T: The Illusion Of Time — freeze everyone except self for 1.5s
      lp.cdT = abil.cooldown;
      const freezeDur = abil.freezeDuration || 1.5;
      lp.illusionTimeFreezeTimer = freezeDur;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        target.stunned = Math.max(target.stunned, freezeDur);
        target.effects.push({ type: 'illusion-frozen', timer: freezeDur });
      }
      lp.effects.push({ type: 'illusion-time', timer: freezeDur + 0.5 });
      combatLog.push({ text: '⏱ The Illusion Of Time! Everyone frozen for 1.5s!', timer: 3, color: '#7f8fa6' });
    } else if (isDragon) {
      // Dragon T: Draconic Roar — +30% speed self, +20% allies, costs 200 HP
      lp.cdT = abil.cooldown;
      lp.dragonRoarActive = true;
      lp.hp -= (abil.selfDamage || 200);
      if (lp.hp <= 0) { _handleDeath(lp); return; }
      lp.effects.push({ type: 'hit', timer: 0.3 });
      // Buff allies
      for (const p of gamePlayers) {
        if (!p.alive || p.isSummon) continue;
        if (p.id === lp.id) continue;
        if (p.team && p.team === lp.team) {
          p.dragonRoarActive = true;
        }
      }
      lp.effects.push({ type: 'dragon-roar', timer: 2.0 });
      combatLog.push({ text: '🐉 DRACONIC ROAR! +30% speed (self)! -200 HP!', timer: 4, color: '#5b8fa8' });
    } else if (isDogTooth) {
      // Dog Tooth T: A_Love_Letter — global 450 dmg to enemies, 600 self-damage
      lp.cdT = abil.cooldown;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon && target.summonOwner === lp.id) continue;
        dealDamage(lp, target, abil.damage || 300, false, true);
        target.effects.push({ type: 'hit', timer: 0.3 });
      }
      // Self-damage: Dog Tooth takes 600
      lp.hp -= (abil.boisvertDamage || 600);
      lp.noDamageTimer = 0; lp.isHealing = false;
      if (lp.hp <= 0) _handleDeath(lp);
      lp.effects.push({ type: 'love-letter', timer: 1.5 });
      combatLog.push({ text: '💌 A_Love_Letter! 450 dmg to all! You take 600!', timer: 4, color: '#aaa' });
    } else if (isOmori) {
      // Omori T: Sad Poem — 1s pause, then enemies who can see Omori get sadness debuff
      lp.cdT = abil.cooldown;
      lp.omoriSadPoemPause = abil.pauseDuration || 1;
      lp.stunned = abil.pauseDuration || 1;
      lp.effects.push({ type: 'omori-sad-poem', timer: (abil.pauseDuration || 1) + 0.5 });
      combatLog.push({ text: '📖 Sad Poem... pausing 1s...', timer: 3, color: '#6c5ce7' });
    } else if (isUnstable) {
      // Unstable Summons: summon a random character (M1 only)
      lp.cdT = abil.cooldown;
      // Kill existing summon
      if (lp.unstableSummonId) {
        const oldSum = gamePlayers.find(p => p.id === lp.unstableSummonId);
        if (oldSum && oldSum.alive) { oldSum.alive = false; oldSum.hp = 0; oldSum.effects.push({ type: 'death', timer: 2 }); }
      }
      const allIds = getAllFighterIds().filter(f => f !== 'unstable' && f !== 'moderator' && f !== 'omori');
      const sumFid = allIds[Math.floor(Math.random() * allIds.length)];
      const sumFighter = getFighter(sumFid);
      const sumId = 'unstable-summon-' + lp.id + '-' + Date.now();
      const summon = createPlayerState(
        { id: sumId, name: sumFighter.name + ' (Unstable)', color: '#ff00ff', fighterId: sumFid },
        { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) }, sumFighter
      );
      const sR = GAME_TILE * PLAYER_RADIUS_RATIO;
      const angle = Math.random() * Math.PI * 2;
      summon.x = lp.x + Math.cos(angle) * GAME_TILE * 2;
      summon.y = lp.y + Math.sin(angle) * GAME_TILE * 2;
      if (!canMoveTo(summon.x, summon.y, sR)) { const safe = getRandomSafePosition(); summon.x = safe.x; summon.y = safe.y; }
      summon.hp = sumFighter.hp; summon.maxHp = sumFighter.hp;
      summon.isSummon = true; summon.summonOwner = lp.id; summon.summonType = 'unstable-random';
      summon.summonSpeed = sumFighter.speed;
      summon.summonDamage = sumFighter.abilities[0].damage || 100;
      summon.summonAttackCD = sumFighter.abilities[0].cooldown || 1;
      summon.summonAttackTimer = 0;
      summon.isCPU = true;
      summon.illusionM1Only = true; // restrict to M1 only
      gamePlayers.push(summon);
      lp.unstableSummonId = sumId;
      lp.effects.push({ type: 'unstable-summon-spawn', timer: 1.5 });
      combatLog.push({ text: '⚡ Summoned ' + sumFighter.name + '! (M1 only)', timer: 4, color: '#ff00ff' });
    } else if (isPyro) {
      // Pyromaniac: RAIN RAIN RAIN — fire arrows rain around player
      lp.cdT = abil.cooldown;
      const rainRadius = (abil.fireRadius || 5) * GAME_TILE;
      let dmg = abil.damage || 10;
      if (lp.supportBuff > 0) dmg *= 1.5;
      if (lp.intimidated > 0) dmg *= 0.5;
      if (lp.pyroFireBuffTimer > 0) dmg *= 2;
      // Hit all enemies in the radius immediately
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
        const dx = target.x - lp.x; const dy = target.y - lp.y;
        if (Math.sqrt(dx * dx + dy * dy) < rainRadius) {
          dealDamage(lp, target, dmg);
          _applyPyroBurn(target, abil.burnDPS || 100, abil.burnDuration || 3);
          target.effects.push({ type: 'hit', timer: 0.3 });
        }
      }
      // Leave ground fire
      if (!lp.pyroFireZones) lp.pyroFireZones = [];
      lp.pyroFireZones.push({ x: lp.x, y: lp.y, timer: abil.fireDuration || 10, radius: abil.fireRadius || 5 });
      lp.pyroRainTimer = 2; // rain visual effect duration
      lp.pyroRainX = lp.x; lp.pyroRainY = lp.y;
      // Ignite gasoline in range
      for (const op of gamePlayers) {
        if (!op.pyroGasolineTrail) continue;
        for (const g of op.pyroGasolineTrail) {
          if (g.lit) continue;
          const gx = g.x - lp.x; const gy = g.y - lp.y;
          if (Math.sqrt(gx * gx + gy * gy) < rainRadius) {
            g.lit = true;
            lp.pyroFireZones.push({ x: g.x, y: g.y, timer: 10, radius: 1.5 });
          }
        }
      }
      lp.effects.push({ type: 'pyro-rain', timer: 2 });
      combatLog.push({ text: '🔥 RAIN RAIN RAIN!', timer: 3, color: '#ff4400' });
      // Grant burn immunity for 10s
      lp.pyroBurnImmuneTimer = 10;
      if (lp.pyroBurnTimers) lp.pyroBurnTimers = [];
    } else if (isHeavyRope) {
      // Heavy Rope: Rope Grab — throw rope in a straight line, grapple to obstacle/sea
      lp.cdT = abil.cooldown;
      const cw = gameCanvas.width; const ch = gameCanvas.height;
      const camX = lp.x - cw / 2; const camY = lp.y - ch / 2;
      const aimX = mouseX + camX; const aimY = mouseY + camY;
      const aimDx = aimX - lp.x; const aimDy = aimY - lp.y;
      const aimDist = Math.sqrt(aimDx * aimDx + aimDy * aimDy) || 1;
      lp.ropeGrabActive = true;
      lp.ropeGrabX = lp.x;
      lp.ropeGrabY = lp.y;
      lp.ropeGrabNx = aimDx / aimDist;
      lp.ropeGrabNy = aimDy / aimDist;
      lp.effects.push({ type: 'rope-grab-throw', timer: 0.3 });
      combatLog.push({ text: '🪢 Rope thrown!', timer: 2, color: '#8b4513' });
    } else {
      lp.cdT = abil.cooldown;
      const sightRange = CAMERA_RANGE * GAME_TILE * 2;
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        // Skip teammates in team mode
        if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
        const dist = Math.sqrt((target.x - lp.x) ** 2 + (target.y - lp.y) ** 2);
        if (dist <= sightRange) {
          target.intimidated = abil.duration;
          target.intimidatedBy = lp.id;
          if (typeof socket !== 'undefined' && socket.emit) {
            if (!isHostAuthority) socket.emit('player-debuff', { targetId: target.id, type: 'intimidation', duration: abil.duration });
          }
        }
      }
      lp.effects.push({ type: 'intimidation', timer: 1.0 });
    }
  }

  else if (key === 'SPACE') {
    if (!lp.specialUnlocked || lp.specialUsed) return;
    // Bug Fixing: check if Special (slot 4) is disabled
    if (lp.modDisabledAbilities && lp.modDisabledAbilities.includes(4)) {
      combatLog.push({ text: '🐛 Special is disabled by Bug Fixing!', timer: 2, color: '#e67e22' });
      return;
    }

    // ── Unstable: Unstablism (switch back) when swapped, or Domain when original ──
    if (lp.unstableSwapped && lp.unstableOriginalFighter) {
      // Unstablism: switch back to Unstable
      lp.specialUsed = true;
      lp.fighter = lp.unstableOriginalFighter;
      lp.maxHp = lp.fighter.hp;
      if (lp.hp > lp.maxHp) lp.hp = lp.maxHp;
      lp.cdE = 0; lp.cdR = 0; lp.cdT = 0;
      lp.unstableSwapped = false;
      lp.specialUnlocked = false;
      lp.totalDamageTaken = 0;
      lp.effects.push({ type: 'unstable-swap', timer: 2.0 });
      combatLog.push({ text: '⚡ UNSTABLE! Switched back to Unstable!', timer: 4, color: '#ff00ff' });
      return;
    }

    if (isUnstable) {
      // Unstable Domain: anyone in 10-tile radius gets character swapped with someone else
      lp.specialUsed = true;
      const domainRange = (fighter.abilities[4].radius || 10) * GAME_TILE;
      const affectedPlayers = [];
      for (const p of gamePlayers) {
        if (p.id === lp.id || !p.alive || p.isSummon) continue;
        if (gameMode === 'teams' && lp.team && p.team === lp.team) continue;
        const dx = p.x - lp.x; const dy = p.y - lp.y;
        if (Math.sqrt(dx * dx + dy * dy) <= domainRange) {
          affectedPlayers.push(p);
        }
      }
      // Shuffle fighters among affected players
      if (affectedPlayers.length >= 2) {
        const fighters = affectedPlayers.map(p => p.fighter);
        // Fisher-Yates shuffle
        for (let i = fighters.length - 1; i > 0; i--) {
          const j = Math.floor(Math.random() * (i + 1));
          [fighters[i], fighters[j]] = [fighters[j], fighters[i]];
        }
        for (let i = 0; i < affectedPlayers.length; i++) {
          affectedPlayers[i].fighter = fighters[i];
          affectedPlayers[i].maxHp = fighters[i].hp;
          if (affectedPlayers[i].hp > affectedPlayers[i].maxHp) affectedPlayers[i].hp = affectedPlayers[i].maxHp;
          affectedPlayers[i].cdE = 0; affectedPlayers[i].cdR = 0; affectedPlayers[i].cdT = 0;
          affectedPlayers[i].effects.push({ type: 'unstable-domain', timer: 2.0 });
        }
        combatLog.push({ text: '⚡ UNSTABLE DOMAIN! ' + affectedPlayers.length + ' players swapped!', timer: 5, color: '#ff00ff' });
      } else {
        combatLog.push({ text: '⚡ UNSTABLE DOMAIN! Not enough targets in range!', timer: 3, color: '#999' });
      }
      lp.effects.push({ type: 'unstable-domain', timer: 2.5 });
      showPopup('⚡ UNSTABLE DOMAIN!');
      return;
    }

    if (isPoker) {
      // Royal Flush — distance-tiered:
      //   Self: heal to full HP automatically
      //   Close (≤3 tiles): stun + execute <500hp + reset CDs/charges
      //   Medium (3–10 tiles): reset CDs/charges only
      //   Power: The Price Of Gambling — apply debt (5 hits to clear, can't damage poker while in debt)
      lp.specialUsed = true;
      lp.hp = lp.maxHp;  // Self-heal
      const stunDur = fighter.abilities[4].stunDuration || 3;
      const execThresh = fighter.abilities[4].executeThreshold || 500;
      const closeRange = 3 * GAME_TILE;
      const mediumRange = (fighter.abilities[4].range || 10) * GAME_TILE;
      const pokerHasPower = typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id);
      for (const target of gamePlayers) {
        if (target.id === lp.id || !target.alive) continue;
        if (target.isSummon) continue;
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
        // Power: The Price Of Gambling — apply debt to all affected targets
        if (pokerHasPower && target.alive) {
          target.pokerDebtTarget = lp.id;
          target.pokerDebtHits = 5;
          target.effects.push({ type: 'poker-debt', timer: 30 });
          if (target.id === localPlayerId) {
            combatLog.push({ text: '💰 THE PRICE OF GAMBLING! Deal 5 hits to clear debt!', timer: 5, color: '#ffd700' });
          }
        }
      }
      if (pokerHasPower) {
        showPopup('👑 THE PRICE OF GAMBLING!');
      } else {
        showPopup('👑 ROYAL FLUSH!');
      }
      lp.effects.push({ type: 'royal-flush', timer: 2.0 });
      // Broadcast to other clients with position for distance calc
      if (typeof socket !== 'undefined' && socket.emit) {
        if (!isHostAuthority) socket.emit('player-buff', { type: 'royal-flush', duration: stunDur, cx: lp.x, cy: lp.y });
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
      // Achievement tracking (not team mode)
      if (typeof trackBoiledOnePlayed === 'function' && gameMode !== 'teams') trackBoiledOnePlayed();
      // Broadcast to other clients
      if (typeof socket !== 'undefined' && socket.emit) {
        if (!isHostAuthority) socket.emit('player-buff', { type: 'boiled-one', duration: stunDur, cx: lp.x, cy: lp.y });
      }
      // Power: Prehistoric Emergence — spawn 3 dinosaurs
      if (typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id)) {
        // Clear old dinos
        for (let di = gamePlayers.length - 1; di >= 0; di--) {
          if (gamePlayers[di].isSummon && gamePlayers[di].summonType === 'filbus-dino' && gamePlayers[di].summonOwner === lp.id) {
            gamePlayers.splice(di, 1);
          }
        }
        lp.filbusDinoIds = [];
        for (let d = 0; d < 3; d++) {
          const dinoId = 'dino-' + lp.id + '-' + Date.now() + '-' + d;
          let dx2, dy2;
          for (let attempts = 0; attempts < 50; attempts++) {
            dx2 = (Math.floor(Math.random() * gameMap.cols) + 0.5) * GAME_TILE;
            dy2 = (Math.floor(Math.random() * gameMap.rows) + 0.5) * GAME_TILE;
            if (canMoveTo(dx2, dy2, GAME_TILE * PLAYER_RADIUS_RATIO)) break;
          }
          const dinoFighter = getFighter('filbus');
          const dino = createPlayerState(
            { id: dinoId, name: 'Dinosaur', color: '#556b2f', fighterId: 'filbus' },
            { r: Math.floor(dy2 / GAME_TILE), c: Math.floor(dx2 / GAME_TILE) }, dinoFighter
          );
          dino.x = dx2; dino.y = dy2;
          dino.hp = 2000; dino.maxHp = 2000;
          dino.isSummon = true; dino.summonOwner = lp.id; dino.summonType = 'filbus-dino';
          dino.fighter = dinoFighter;
          dino.summonSpeed = 1.0; // slow
          dino.summonDamage = 150;
          dino.summonStunDur = 0;
          dino.summonAttackCD = 3.0; // 3s cooldown
          dino.summonAttackTimer = 0;
          dino.summonBleedDps = 50; // dino attacks apply 5s bleed
          dino.summonBleedDur = 5;
          gamePlayers.push(dino);
          lp.filbusDinoIds.push(dinoId);
        }
        showPopup('🦕 PREHISTORIC EMERGENCE!');
        combatLog.push({ text: '🦕 3 Dinosaurs summoned!', timer: 4, color: '#556b2f' });
        lp.effects.push({ type: 'dino-spawn', timer: 2.0 });
      }
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
          cdM1: 0, cdE: 0, cdR: 0, cdT: 0, cdF: 0,
          totalDamageTaken: 0, specialUnlocked: false, specialUsed: false,
          supportBuff: 0, buffSlowed: 0, intimidated: 0, intimidatedBy: null, stunned: 0,
          noDamageTimer: 0, healTickTimer: 0, isHealing: false,
          specialJumping: false, specialAiming: false,
          specialAimX: 0, specialAimY: 0, specialAimTimer: 0,
          effects: [],
          blindBuff: null, blindTimer: 0, chipChangeDmg: -1, chipChangeTimer: 0,
          chairCharges: 0, isCraftingChair: false, craftTimer: 0,
          isEatingChair: false, eatTimer: 0, eatHealPool: 0,
          summonId: null, boiledOneActive: false, boiledOneTimer: 0,
          poisonTimers: [], unstableEyeTimer: 0, zombieIds: [],
          gearUpTimer: 0, wicketIds: [], driveReflectTimer: 0,
          deerFearTimer: 0, deerFearTargetX: 0, deerFearTargetY: 0,
          deerSeerTimer: 0, deerRobotId: null, iglooX: 0, iglooY: 0, iglooTimer: 0,
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
      // Power: +Slasher — spawn a fast, deadly slasher summon
      if (typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id)) {
        // Remove old slasher
        if (lp.onexSlasherId) {
          const oldIdx = gamePlayers.findIndex(p => p.id === lp.onexSlasherId);
          if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers.splice(oldIdx, 1); }
          lp.onexSlasherId = null;
        }
        const slasherId = 'slasher-' + lp.id + '-' + Date.now();
        let sx, sy;
        for (let attempts = 0; attempts < 50; attempts++) {
          sx = (Math.floor(Math.random() * gameMap.cols) + 0.5) * GAME_TILE;
          sy = (Math.floor(Math.random() * gameMap.rows) + 0.5) * GAME_TILE;
          if (canMoveTo(sx, sy, GAME_TILE * PLAYER_RADIUS_RATIO)) break;
        }
        const slasherFighter = getFighter('onexonexonex');
        const slasher = createPlayerState(
          { id: slasherId, name: 'Slasher', color: '#8b0000', fighterId: 'onexonexonex' },
          { r: Math.floor(sy / GAME_TILE), c: Math.floor(sx / GAME_TILE) }, slasherFighter
        );
        slasher.x = sx; slasher.y = sy;
        slasher.hp = 1300; slasher.maxHp = 1300;
        slasher.isSummon = true; slasher.summonOwner = lp.id; slasher.summonType = 'slasher';
        slasher.fighter = slasherFighter;
        slasher.summonSpeed = 4.0; // fast
        slasher.summonDamage = 150;
        slasher.summonStunDur = 0;
        slasher.summonAttackCD = 0.5; // very fast attacks
        slasher.summonAttackTimer = 0;
        gamePlayers.push(slasher);
        lp.onexSlasherId = slasherId;
        showPopup('🔪 +SLASHER!');
        lp.effects.push({ type: 'slasher-spawn', timer: 2.0 });
        combatLog.push({ text: '🔪 Slasher summoned!', timer: 4, color: '#8b0000' });
      }
    } else if (isCricket) {
      // Cricket SPACE: SIXER — same aim mechanic as Fighter's special jump
      lp.specialUsed = true;
      lp.specialJumping = false; // Cricket doesn't jump, they hit a ball
      lp.specialAiming = true;
      lp.specialAimX = lp.x;
      lp.specialAimY = lp.y;
      const aimTime = lp.fighter.abilities[4].aimTime || 5;
      lp.specialAimTimer = aimTime;
      lp.effects.push({ type: 'sixer-aim', timer: aimTime + 2 });
      combatLog.push({ text: '🏏 SIXER! Aim the ball!', timer: 3, color: '#f5a623' });
    } else if (isDeer) {
      // Deer SPACE: Igloo — aim where to build it
      lp.specialUsed = true;
      lp.specialJumping = false;
      lp.specialAiming = true;
      lp.specialAimX = lp.x;
      lp.specialAimY = lp.y;
      const aimTime = lp.fighter.abilities[4].aimTime || 5;
      lp.specialAimTimer = aimTime;
      lp.effects.push({ type: 'igloo-aim', timer: aimTime + 2 });
      combatLog.push({ text: '🦌 IGLOO! Aim where to build!', timer: 3, color: '#87ceeb' });
    } else if (isHitman) {
      // Hitman SPACE: Locking In — all 3 weapons auto-fire simultaneously toward mouse for 20s
      lp.specialUsed = true;
      lp.hitmanLockingIn = true;
      lp.hitmanLockingInTimer = 20;
      lp.hitmanReloading = false;
      lp.hitmanReloadTimer = 0;
      lp.hitmanLockingFireTimer = 0; // immediate first fire
      lp.effects.push({ type: 'hitman-lockin', timer: 99 });
      combatLog.push({ text: '🔒 LOCKING IN! All weapons auto-firing for 20s!', timer: 4, color: '#ff4400' });
    } else if (isNoli) {
      // Noli SPACE: Hallucinations — clone the closest fighter as CPU ally
      lp.specialUsed = true;
      if (lp.noliCloneId) {
        const oldIdx = gamePlayers.findIndex(x => x.id === lp.noliCloneId);
        if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers.splice(oldIdx, 1); }
        lp.noliCloneId = null;
      }
      // Find target to clone
      let closestDist = Infinity, closestTarget = null;
      const candidates = gamePlayers.filter(t => t.id !== lp.id && t.alive && !t.isSummon);
      if (gameMode === 'training' && candidates.length > 0) {
        closestTarget = candidates[Math.floor(Math.random() * candidates.length)];
      } else {
        for (const t of candidates) {
          const d = Math.sqrt((t.x - lp.x) ** 2 + (t.y - lp.y) ** 2);
          if (d < closestDist) { closestDist = d; closestTarget = t; }
        }
      }
      if (!closestTarget) return;
      // Clone the target
      const clonedFighter = closestTarget.fighter;
      const cloneId = 'noli-clone-' + lp.id + '-' + Date.now();
      // Determine clone color: cloning 1x = half green/purple, cloning noli = white, else purple
      let cloneColor = '#a020f0';
      if (clonedFighter.id === 'onexonexonex') cloneColor = '#50a070';
      else if (clonedFighter.id === 'noli') cloneColor = '#ffffff';
      const clone = createPlayerState(
        { id: cloneId, name: closestTarget.name, color: cloneColor, fighterId: clonedFighter.id },
        { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
        clonedFighter
      );
      clone.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 2;
      clone.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 2;
      clone.isSummon = true;
      clone.summonOwner = lp.id;
      clone.summonType = 'noli-clone';
      clone.isCPU = true;
      clone.noCloneHeal = true; // clone cannot heal
      clone.difficulty = 'hard';
      clone.aiState = {
        moveTarget: null, attackTarget: null, thinkTimer: 0, abilityTimer: 0,
        lastSeenPositions: {}, strafeDir: Math.random() < 0.5 ? 1 : -1, retreating: false,
      };
      clone.hp = closestTarget.maxHp;
      clone.maxHp = closestTarget.maxHp;
      gamePlayers.push(clone);
      lp.noliCloneId = cloneId;
      lp.effects.push({ type: 'hallucination', timer: 2.0 });
      combatLog.push({ text: '👻 Hallucination: ' + closestTarget.name + '!', timer: 3, color: '#a020f0' });
      // Power: Guest666 — spawn a giant 2x2 black/red beast
      if (typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id)) {
        // Remove old guest666
        if (lp.noliGuest666Id) {
          const oldG = gamePlayers.findIndex(p => p.id === lp.noliGuest666Id);
          if (oldG >= 0) { gamePlayers[oldG].alive = false; gamePlayers.splice(oldG, 1); }
          lp.noliGuest666Id = null;
        }
        const guestId = 'guest666-' + lp.id + '-' + Date.now();
        const guestFighter = getFighter('noli');
        const guest = createPlayerState(
          { id: guestId, name: 'Guest666', color: '#1a0000', fighterId: 'noli' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) }, guestFighter
        );
        guest.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 3;
        guest.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 3;
        const gR = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(guest.x, guest.y, gR)) { guest.x = lp.x; guest.y = lp.y; }
        guest.hp = 2000; guest.maxHp = 2000;
        guest.isSummon = true; guest.summonOwner = lp.id; guest.summonType = 'guest666';
        guest.fighter = guestFighter;
        guest.summonSpeed = 3.5; // fast
        guest.summonDamage = 400;
        guest.summonStunDur = 3; // lacerates for 3s stun
        guest.summonAttackCD = 5.0;
        guest.summonAttackTimer = 0;
        guest.summonBleedDps = 100; // 100dmg worth of bleeding over time
        guest.summonBleedDur = 3;
        guest.summonJumpCD = 8.0; // jump ability cooldown
        guest.summonJumpTimer = 0;
        gamePlayers.push(guest);
        lp.noliGuest666Id = guestId;
        showPopup('👹 GUEST666!');
        lp.effects.push({ type: 'guest666-spawn', timer: 2.0 });
        combatLog.push({ text: '👹 Guest666 has arrived! (2000HP, 400dmg, lacerates!)', timer: 5, color: '#8b0000' });
      }
    } else if (isCat) {
      // Exploding Cat SPACE: Exploding Kitten — spawn 4 kittens
      lp.specialUsed = true;
      const sAbil = fighter.abilities[4];
      const count = sAbil.kittenCount || 4;
      lp.catKittenIds = [];
      for (let i = 0; i < count; i++) {
        const kitId = 'kitten-' + lp.id + '-' + i + '-' + Date.now();
        const kitten = createPlayerState(
          { id: kitId, name: 'Kitten', color: '#111', fighterId: 'explodingcat' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
          fighter
        );
        kitten.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 3;
        kitten.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 3;
        // Nudge out of obstacles
        const kitRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(kitten.x, kitten.y, kitRadius)) {
          kitten.x = lp.x;
          kitten.y = lp.y;
        }
        kitten.hp = sAbil.kittenHp || 400;
        kitten.maxHp = sAbil.kittenHp || 400;
        kitten.isSummon = true;
        kitten.summonOwner = lp.id;
        kitten.summonType = 'exploding-kitten';
        kitten.summonSpeed = sAbil.kittenSpeed || 2.5;
        kitten.summonDamage = sAbil.damage || 1200;
        kitten.summonStunDur = 0;
        kitten.summonAttackCD = 0;
        kitten.summonAttackTimer = 0;
        gamePlayers.push(kitten);
        lp.catKittenIds.push(kitId);
      }
      lp.effects.push({ type: 'cat-explode-spawn', timer: 2.0 });
      combatLog.push({ text: '💣 Exploding Kittens unleashed!', timer: 3, color: '#ff4444' });
      // Power: Imploding Kitten — spawn a black hole kitten
      if (typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id)) {
        // Remove old imploding kitten
        if (lp.catImplodingKittenId) {
          const oldIK = gamePlayers.findIndex(p => p.id === lp.catImplodingKittenId);
          if (oldIK >= 0) { gamePlayers[oldIK].alive = false; gamePlayers.splice(oldIK, 1); }
          lp.catImplodingKittenId = null;
        }
        const ikId = 'imploding-kitten-' + lp.id + '-' + Date.now();
        const ikFighter = getFighter('explodingcat');
        const ik = createPlayerState(
          { id: ikId, name: 'Imploding Kitten', color: '#0a0a0a', fighterId: 'explodingcat' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) }, ikFighter
        );
        ik.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 2;
        ik.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 2;
        const ikR = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(ik.x, ik.y, ikR)) { ik.x = lp.x; ik.y = lp.y; }
        ik.hp = 800; ik.maxHp = 800;
        ik.isSummon = true; ik.summonOwner = lp.id; ik.summonType = 'imploding-kitten';
        ik.fighter = ikFighter;
        ik.summonSpeed = 0; // stationary
        ik.summonDamage = 900; // 900 dmg on detonation
        ik.summonAttackCD = 0; ik.summonAttackTimer = 0;
        ik.kittenTimer = 3.0; // 3s as a cute blue kitten before imploding
        ik.blackHoleTimer = 6.0; // 6s black hole countdown after kitten phase
        ik.blackHoleRadius = 8 * GAME_TILE; // 8-tile outer suction radius
        ik.blackHoleMidRadius = 6 * GAME_TILE; // 6-tile mid zone
        ik.blackHoleInnerRadius = 4 * GAME_TILE; // 4-tile inescapable zone
        ik.blackHoleActive = false; // starts as kitten, not black hole
        gamePlayers.push(ik);
        lp.catImplodingKittenId = ikId;
        showPopup('🐱 IMPLODING KITTEN!');
        lp.effects.push({ type: 'imploding-kitten-spawn', timer: 2.0 });
        combatLog.push({ text: '🐱 Imploding Kitten spawned! Implodes in 3s...', timer: 5, color: '#4a9fff' });
      }
    } else if (isNapoleon) {
      // Napoleon SPACE: The Grande Armée — spawn 12 infantrymen
      lp.specialUsed = true;
      const sAbil = fighter.abilities[4];
      const count = sAbil.infantryCount || 12;
      if (!lp.napoleonInfantryIds) lp.napoleonInfantryIds = [];
      for (let i = 0; i < count; i++) {
        const infId = 'infantry-' + lp.id + '-' + i + '-' + Date.now();
        const inf = createPlayerState(
          { id: infId, name: 'Infantryman', color: '#2c3e50', fighterId: 'napoleon' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
          fighter
        );
        inf.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 4;
        inf.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 4;
        const infRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(inf.x, inf.y, infRadius)) { inf.x = lp.x; inf.y = lp.y; }
        inf.hp = sAbil.infantryHp || 50;
        inf.maxHp = sAbil.infantryHp || 50;
        inf.isSummon = true;
        inf.summonOwner = lp.id;
        inf.summonType = 'napoleon-infantry';
        inf.summonSpeed = sAbil.infantrySpeed || 2.0;
        inf.summonDamage = sAbil.damage || 100;
        inf.summonAttackCD = sAbil.infantryFireCD || 1;
        inf.summonAttackTimer = 0;
        inf.summonProjectileSpeed = sAbil.infantryProjectileSpeed || 38;
        inf.summonProjectileRange = sAbil.infantryRange || 0.8;
        gamePlayers.push(inf);
        lp.napoleonInfantryIds.push(infId);
      }
      lp.effects.push({ type: 'grande-armee', timer: 2.0 });
      combatLog.push({ text: '⚔ The Grande Armée has arrived!', timer: 4, color: '#2c3e50' });
      // Power: Full Power — also spawn 5 cannons and 3 cavalry
      if (typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id)) {
        // Remove old power cannons
        for (let ci = gamePlayers.length - 1; ci >= 0; ci--) {
          if (gamePlayers[ci].isSummon && gamePlayers[ci].summonType === 'napoleon-power-cannon' && gamePlayers[ci].summonOwner === lp.id) {
            gamePlayers.splice(ci, 1);
          }
        }
        if (!lp.napoleonPowerCannonIds) lp.napoleonPowerCannonIds = [];
        lp.napoleonPowerCannonIds = [];
        // Spawn 5 cannons
        for (let c = 0; c < 5; c++) {
          const cId = 'power-cannon-' + lp.id + '-' + c + '-' + Date.now();
          const cannon = createPlayerState(
            { id: cId, name: 'Cannon', color: '#555', fighterId: 'napoleon' },
            { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) }, fighter
          );
          cannon.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 6;
          cannon.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 6;
          const cR = GAME_TILE * PLAYER_RADIUS_RATIO;
          if (!canMoveTo(cannon.x, cannon.y, cR)) { cannon.x = lp.x; cannon.y = lp.y; }
          cannon.hp = 600; cannon.maxHp = 600;
          cannon.isSummon = true; cannon.summonOwner = lp.id;
          cannon.summonType = 'napoleon-power-cannon';
          cannon.summonSpeed = 0;
          cannon.summonDamage = 700;
          cannon.summonAttackCD = 5; cannon.summonAttackTimer = 0;
          cannon.summonProjectileSpeed = 30;
          gamePlayers.push(cannon);
          lp.napoleonPowerCannonIds.push(cId);
        }
        // Remove old cavalry summons
        for (let ci = gamePlayers.length - 1; ci >= 0; ci--) {
          if (gamePlayers[ci].isSummon && gamePlayers[ci].summonType === 'napoleon-cavalry' && gamePlayers[ci].summonOwner === lp.id) {
            gamePlayers.splice(ci, 1);
          }
        }
        if (!lp.napoleonCavalryIds) lp.napoleonCavalryIds = [];
        lp.napoleonCavalryIds = [];
        // Spawn 3 cavalry (300HP, 400dmg, 2x dmg taken)
        for (let cv = 0; cv < 3; cv++) {
          const cvId = 'cavalry-' + lp.id + '-' + cv + '-' + Date.now();
          const cav = createPlayerState(
            { id: cvId, name: 'Cavalry', color: '#8b4513', fighterId: 'napoleon' },
            { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) }, fighter
          );
          cav.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 5;
          cav.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 5;
          const cvR = GAME_TILE * PLAYER_RADIUS_RATIO;
          if (!canMoveTo(cav.x, cav.y, cvR)) { cav.x = lp.x; cav.y = lp.y; }
          cav.hp = 300; cav.maxHp = 300;
          cav.isSummon = true; cav.summonOwner = lp.id;
          cav.summonType = 'napoleon-cavalry';
          cav.fighter = fighter;
          cav.summonSpeed = 4.0; // fast cavalry
          cav.summonDamage = 400;
          cav.summonStunDur = 0;
          cav.summonAttackCD = 2.0; cav.summonAttackTimer = 0;
          cav.napoleonCavalry = true; // takes 2x damage (reuses existing mechanic)
          gamePlayers.push(cav);
          lp.napoleonCavalryIds.push(cvId);
        }
        showPopup('⚔ FULL POWER!');
        combatLog.push({ text: '⚔ Full Power! 5 cannons + 3 cavalry deployed!', timer: 5, color: '#8b4513' });
        lp.effects.push({ type: 'napoleon-full-power', timer: 2.0 });
      }
    } else if (isModerator) {
      // Moderator SPACE: Server Update — buff all teammates + reset cooldowns
      lp.specialUsed = true;
      const sAbil = fighter.abilities[4];
      const buffDur = sAbil.buffDuration || 10;
      for (const p of gamePlayers) {
        if (!p.alive || p.isSummon) continue;
        // In MP with teams, buff teammates and self; in FFA, buff only self
        if (p.id === lp.id || (p.team && p.team === lp.team)) {
          p.modServerUpdateTimer = buffDur;
          // Reset all cooldowns
          p.cdM1 = 0; p.cdE = 0; p.cdR = 0; p.cdT = 0; p.cdF = 0;
          p.effects.push({ type: 'server-update', timer: 2.0 });
        }
      }
      // Always buff self
      lp.modServerUpdateTimer = buffDur;
      lp.cdM1 = 0; lp.cdE = 0; lp.cdR = 0; lp.cdT = 0; lp.cdF = 0;
      combatLog.push({ text: '📦 SERVER UPDATE! +50% speed, damage, defense! CDs reset!', timer: 5, color: '#2ecc71' });
      // Power: Multi Update — allow special to recharge and be used again
      if (typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id)) {
        lp.specialUsed = false;
        lp.specialUnlocked = false;
        lp.totalDamageTaken = 0;
        showPopup('📦 MULTI UPDATE!');
        combatLog.push({ text: '📦 Multi Update! Special recharging for next use!', timer: 4, color: '#00ff88' });
      }
    } else if (isDnd) {
      // D&D Campaigner SPACE: D20 Roll — buff all teammates' M1 to 1000 dmg until next death
      lp.specialUsed = true;
      lp.dndD20Active = true;
      const dndHasPower = typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id);
      // Power: Super Lucky — buff persists through next 2 deaths instead of 1
      const deathsNeeded = dndHasPower ? 2 : 0;
      lp.effects.push({ type: 'd20-roll', timer: 3.0 });
      for (const p of gamePlayers) {
        if (!p.alive || p.isSummon) continue;
        if (p.id === lp.id || (p.team && p.team === lp.team)) {
          p.dndD20Active = true;
          p.dndD20DeathsRemaining = deathsNeeded;
        }
      }
      lp.dndD20DeathsRemaining = deathsNeeded;
      if (dndHasPower) {
        showPopup('🎲 SUPER LUCKY!');
        combatLog.push({ text: '🎲 SUPER LUCKY! All allies deal 650 M1 dmg until 2 more deaths!', timer: 5, color: '#ffd700' });
      } else {
        combatLog.push({ text: '🎲 NATURAL 20! All allies deal 650 M1 dmg until next death!', timer: 5, color: '#ffd700' });
      }
    } else if (isDragon) {
      // Dragon SPACE: Power of the Evil — summon Yellow Ochre or Lich (or both with Power)
      lp.specialUsed = true;
      const dragonHasPower = typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id);
      // Kill old summon(s) if exist
      if (lp.dragonSummonId) {
        const oldS = gamePlayers.find(p => p.id === lp.dragonSummonId);
        if (oldS && oldS.alive) { oldS.alive = false; oldS.hp = 0; oldS.effects.push({ type: 'death', timer: 2 }); }
      }
      if (lp.dragonSummonId2) {
        const oldS2 = gamePlayers.find(p => p.id === lp.dragonSummonId2);
        if (oldS2 && oldS2.alive) { oldS2.alive = false; oldS2.hp = 0; oldS2.effects.push({ type: 'death', timer: 2 }); }
        lp.dragonSummonId2 = null;
      }
      const spawnOchre = dragonHasPower || Math.random() < 0.5;
      const spawnLich = dragonHasPower || !spawnOchre;
      if (spawnOchre) {
        // Yellow Ochre: 3x3 jelly, 1000HP, 50dps area + slow
        const ochreId = 'dragon-ochre-' + lp.id + '-' + Date.now();
        const ochre = createPlayerState(
          { id: ochreId, name: 'Yellow Ochre', color: '#c8a832', fighterId: 'fighter' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) }, getFighter('fighter')
        );
        const angle = Math.random() * Math.PI * 2;
        ochre.x = lp.x + Math.cos(angle) * GAME_TILE * 3;
        ochre.y = lp.y + Math.sin(angle) * GAME_TILE * 3;
        const oR = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(ochre.x, ochre.y, oR)) { const s = getRandomSafePosition(); ochre.x = s.x; ochre.y = s.y; }
        ochre.hp = 1000; ochre.maxHp = 1000;
        ochre.isSummon = true; ochre.summonOwner = lp.id;
        ochre.summonType = 'dragon-ochre';
        ochre.summonSpeed = 1.5; ochre.summonDamage = 50;
        ochre.summonAttackCD = 0; ochre.summonAttackTimer = 0;
        ochre.isCPU = true;
        gamePlayers.push(ochre);
        lp.dragonSummonId = ochreId;
        lp.effects.push({ type: 'dragon-summon', timer: 2.0 });
        combatLog.push({ text: '👹 Yellow Ochre summoned! (3×3 jelly, 1000HP)', timer: 4, color: '#c8a832' });
      }
      if (spawnLich) {
        // Lich: 700HP, 100dmg lightning, 0.4s CD, fast autoheal
        const lichId = 'dragon-lich-' + lp.id + '-' + Date.now();
        const lich = createPlayerState(
          { id: lichId, name: 'Lich', color: '#6a0dad', fighterId: 'fighter' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) }, getFighter('fighter')
        );
        const angle = Math.random() * Math.PI * 2;
        lich.x = lp.x + Math.cos(angle) * GAME_TILE * 3;
        lich.y = lp.y + Math.sin(angle) * GAME_TILE * 3;
        const lR = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(lich.x, lich.y, lR)) { const s = getRandomSafePosition(); lich.x = s.x; lich.y = s.y; }
        lich.hp = 700; lich.maxHp = 700;
        lich.isSummon = true; lich.summonOwner = lp.id;
        lich.summonType = 'dragon-lich';
        lich.summonSpeed = 2.0; lich.summonDamage = 100;
        lich.summonAttackCD = 0.4; lich.summonAttackTimer = 0;
        lich.lichKillCount = 0;
        lich.isCPU = true;
        gamePlayers.push(lich);
        if (dragonHasPower) {
          lp.dragonSummonId2 = lichId;
        } else {
          lp.dragonSummonId = lichId;
        }
        lp.effects.push({ type: 'dragon-summon', timer: 2.0 });
        combatLog.push({ text: '💀 Lich summoned! (700HP, lightning, autoheal)', timer: 4, color: '#6a0dad' });
      }
      if (dragonHasPower) {
        showPopup('🐉 DOUBLE TROUBLE!');
        combatLog.push({ text: '🐉 Double Trouble! Both villains summoned!', timer: 5, color: '#ff4444' });
      }
    } else if (isIllusion) {
      // Illusion SPACE: The Illusions Of Everything — spawn 3 illusion copies, turn invisible until all killed
      lp.specialUsed = true;
      lp.illusionSpecialInvis = true;
      lp.illusionSpecialCopyIds = [];
      const sAbil = fighter.abilities[4];
      const illusionHasPower = typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id);
      const count = illusionHasPower ? 5 : (sAbil.illusionCount || 3);
      const copyHp = 500 + Math.floor(Math.random() * 101);
      for (let i = 0; i < count; i++) {
        const copyId = 'illusion-special-' + lp.id + '-' + i + '-' + Date.now();
        const copy = createPlayerState(
          { id: copyId, name: lp.name, color: lp.color || '#7f8fa6', fighterId: 'illusion' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
          fighter
        );
        copy.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 4;
        copy.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 4;
        const copyRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(copy.x, copy.y, copyRadius)) { copy.x = lp.x; copy.y = lp.y; }
        copy.hp = copyHp;
        copy.maxHp = copyHp;
        copy.isSummon = true;
        copy.summonOwner = lp.id;
        copy.summonType = 'illusion-special-copy';
        copy.isCPU = true;
        copy.difficulty = 'hard';
        copy.noCloneHeal = true;
        copy.illusionM1Only = true;
        copy.aiState = {
          moveTarget: null, attackTarget: null, thinkTimer: 0, abilityTimer: 0,
          lastSeenPositions: {}, strafeDir: Math.random() < 0.5 ? 1 : -1, retreating: false,
        };
        gamePlayers.push(copy);
        lp.illusionSpecialCopyIds.push(copyId);
      }
      lp.effects.push({ type: 'illusion-everything', timer: 2.0 });
      // Power: and more — stun everyone for 3s (time pause) + disillusion (see through grass)
      if (illusionHasPower) {
        const pauseDur = 3;
        for (const target of gamePlayers) {
          if (!target.alive || target.isSummon) continue;
          if (target.id === lp.id) continue;
          if (gameMode === 'teams' && lp.team && target.team === lp.team) continue;
          target.stunned = pauseDur;
          target.effects.push({ type: 'stun', timer: pauseDur });
        }
        // Give disillusion (see through grass)
        lp.illusionSeeGrassTimer = 10;
        if (gameMode === 'teams' && lp.team) {
          for (const ally of gamePlayers) {
            if (ally.id === lp.id || !ally.alive || ally.isSummon || ally.team !== lp.team) continue;
            ally.illusionSeeGrassTimer = 10;
          }
        }
        showPopup('👻 ...AND MORE!');
        combatLog.push({ text: '👻 ...and more! 5 illusions + time paused + disillusion!', timer: 5, color: '#7f8fa6' });
      } else {
        combatLog.push({ text: '👻 The Illusions Of Everything! Kill all ' + count + ' to reveal Illusion!', timer: 4, color: '#7f8fa6' });
      }
    } else if (isDogTooth) {
      // Dog Tooth SPACE: 50% Puppet God, 50% Moon — instant random pick
      const dogHasPower = typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id);
      if (lp.dogtoothForceMoon) {
        // Power: second use forced to Moon
        lp.specialUsed = true;
        lp.dogtoothForceMoon = false;
        lp.dogtoothSpecialChoice = 'moon';
        lp.dogtoothMoonUsed = true;
        const moonAbil = lp.fighter.abilities[4];
        const moonRadius = (moonAbil.moonRadius || 10) * GAME_TILE;
        const moonDelay = moonAbil.moonDelay || 3;
        lp.dogtoothMoonX = lp.x;
        lp.dogtoothMoonY = lp.y;
        lp.dogtoothMoonTimer = moonDelay;
        lp.dogtoothMoonRadius = moonRadius;
        lp.dogtoothMoonDmg = moonAbil.damage || 1200;
        lp.effects.push({ type: 'moon-shadow', timer: moonDelay + 1 });
        showPopup('🌙 THE MOON WOKE UP!');
        combatLog.push({ text: '🌙 The Moon Woke Up! Impact in 3s!', timer: 4, color: '#ffeeaa' });
      } else if (!lp.dogtoothSpecialChoice) {
        lp.specialUsed = true;
        if (Math.random() < 0.5) {
          // Kill The Puppet God
          lp.dogtoothSpecialChoice = 'puppet';
          lp.dogtoothPuppetGod = true;
          combatLog.push({ text: '💀 Kill The Puppet God', timer: 4, color: '#aaa' });
          combatLog.push({ text: '(On death → revive half HP, take 1.5× damage)', t