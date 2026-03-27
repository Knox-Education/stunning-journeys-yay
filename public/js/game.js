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

// Training dummy respawn timer
let dummyRespawnTimer = 0;

// Apple tree state
let appleTree = null; // {col, row, hp, maxHp, alive, regrowTimer, appleTimer, apples:[{col,row}]}

// Game mode: 'training' | 'fight' | undefined (multiplayer)
let gameMode = undefined;

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

// ═══════════════════════════════════════════════════════════════
// START GAME
// ═══════════════════════════════════════════════════════════════
function startGame(mapIndex, players, myId, mode) {
  gameCanvas = document.querySelector('#game-canvas');
  gameCtx = gameCanvas.getContext('2d');
  gameMap = MAPS[mapIndex];
  localPlayerId = myId;
  gameMode = mode;
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

  // Reset projectiles and network state
  projectiles = [];
  combatLog = [];
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
    const botFighters = getAllFighterIds().filter(f => f !== localPlayer.fighter.id && f !== 'moderator');
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
    const allFighters = getAllFighterIds().filter(f => f !== 'moderator');
    const difficulties = gameMode === 'fight-hard'
      ? ['expert', 'expert', 'expert', 'expert']
      : ['easy', 'medium', 'hard', 'hard'];
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
    spawnX: (spawn.c + 0.5) * GAME_TILE,
    spawnY: (spawn.r + 0.5) * GAME_TILE,
    // Team (multiplayer teams mode)
    team: p.team || null,
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
    cdF: 0,
    move4Uses: 0,
    // Ability state
    totalDamageTaken: 0,
    specialUnlocked: false,
    specialUsed: false,
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
          && localPlayer.fighter.id !== 'explodingcat') {
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
      if (!gameLoop._lastPosSend || now - gameLoop._lastPosSend > 20) {
        gameLoop._lastPosSend = now;
        socket.emit('player-position', { x: localPlayer.x, y: localPlayer.y });
      }
    }
    if (isHostAuthority) {
      // HOST: broadcast full game state snapshot every ~33ms (30 Hz)
      if (!gameLoop._lastBroadcast || now - gameLoop._lastBroadcast > 33) {
        gameLoop._lastBroadcast = now;
        const snapshot = buildGameStateSnapshot();
        socket.emit('game-state', snapshot);
      }
    } else if (gameMode === undefined || gameMode === 'teams') {
      // NON-HOST: send ability inputs throttled to ~50 Hz (every 20ms)
      if (!gameLoop._lastInputSend || now - gameLoop._lastInputSend > 20) {
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

  requestAnimationFrame(gameLoop);
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
        && !localPlayer.noliVoidRushActive && !localPlayer.noliVoidStarAiming) {
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
        p.x += (p._targetX - p.x) * 0.25;
        p.y += (p._targetY - p.y) * 0.25;
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

    // Zone damage: hurt players outside the safe zone
    if (p.alive && zoneInset > 0 && !p.isSummon) {
      // Skip backrooms players — they're in another dimension
      if (p.inBackrooms) continue;
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
          if (target.inBackrooms) continue; // backrooms players immune
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
      if (p.hp <= 0 && p.alive) {
        p.hp = 0;
        p.alive = false;
        p.effects.push({ type: 'death', timer: 2 });
        if (p.id === localPlayerId) { freeCamX = p.x; freeCamY = p.y; spectateIndex = -1; deathOverlayTimer = 0; }
      }
    }

    // Tick Unstable Eye timer
    if (p.unstableEyeTimer > 0) {
      p.unstableEyeTimer = Math.max(0, p.unstableEyeTimer - wallDt);
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
            if (p.hp <= 0) {
              p.hp = 0;
              p.alive = false;
              p.effects.push({ type: 'death', timer: 2 });
            }
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
          // Cone-shaped: 60 degree spread
          for (const target of gamePlayers) {
            if (target.id === p.id || !target.alive) continue;
            if (target.isSummon && target.summonOwner === p.id) continue;
            const tx = target.x - p.x; const ty = target.y - p.y;
            const tdist = Math.sqrt(tx * tx + ty * ty);
            if (tdist > range || tdist < 1) continue;
            const dot = (tx * nx + ty * ny) / tdist;
            if (dot > 0.5) { // ~60 degree cone
              const dmgAmt = dps * wallDt;
              if (dmgAmt > 0 && isFinite(dmgAmt)) dealDamage(p, target, dmgAmt, false);
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
        // Steer with WASD / arrow keys
        let steerDx = 0, steerDy = 0;
        if (keys['ArrowUp']    || keys['w'] || keys['W']) steerDy -= 1;
        if (keys['ArrowDown']  || keys['s'] || keys['S']) steerDy += 1;
        if (keys['ArrowLeft']  || keys['a'] || keys['A']) steerDx -= 1;
        if (keys['ArrowRight'] || keys['d'] || keys['D']) steerDx += 1;
        if (steerDx !== 0 || steerDy !== 0) {
          const steerLen = Math.sqrt(steerDx * steerDx + steerDy * steerDy);
          const wantNx = steerDx / steerLen;
          const wantNy = steerDy / steerLen;
          const curSpeed = Math.sqrt(p.noliVoidRushVx * p.noliVoidRushVx + p.noliVoidRushVy * p.noliVoidRushVy) || 1;
          const curNx = p.noliVoidRushVx / curSpeed;
          const curNy = p.noliVoidRushVy / curSpeed;
          const blendAmt = Math.min(1, steerRate * wallDt);
          const newNx = curNx + (wantNx - curNx) * blendAmt;
          const newNy = curNy + (wantNy - curNy) * blendAmt;
          const newDist = Math.sqrt(newNx * newNx + newNy * newNy) || 1;
          p.noliVoidRushVx = (newNx / newDist) * curSpeed;
          p.noliVoidRushVy = (newNy / newDist) * curSpeed;
        }
      } else if (isHostAuthority && !p.isCPU) {
        // Host: steer remote player's Void Rush using their relayed keys
        const rk = remoteInputs[p.id] && remoteInputs[p.id].keys;
        if (rk) {
          let steerDx = 0, steerDy = 0;
          if (rk.up || rk.w) steerDy -= 1;
          if (rk.down || rk.s) steerDy += 1;
          if (rk.left || rk.a) steerDx -= 1;
          if (rk.right || rk.d) steerDx += 1;
          if (steerDx !== 0 || steerDy !== 0) {
            const steerLen = Math.sqrt(steerDx * steerDx + steerDy * steerDy);
            const wantNx = steerDx / steerLen;
            const wantNy = steerDy / steerLen;
            const curSpeed = Math.sqrt(p.noliVoidRushVx * p.noliVoidRushVx + p.noliVoidRushVy * p.noliVoidRushVy) || 1;
            const curNx = p.noliVoidRushVx / curSpeed;
            const curNy = p.noliVoidRushVy / curSpeed;
            const blendAmt = Math.min(1, steerRate * wallDt);
            const newNx = curNx + (wantNx - curNx) * blendAmt;
            const newNy = curNy + (wantNy - curNy) * blendAmt;
            const newDist = Math.sqrt(newNx * newNx + newNy * newNy) || 1;
            p.noliVoidRushVx = (newNx / newDist) * curSpeed;
            p.noliVoidRushVy = (newNy / newDist) * curSpeed;
          }
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
          // Achievement: Noli Void Rush kills in MP
          if (_vrTargetWasAlive && !t.alive && p.id === localPlayerId && gameMode !== 'training' && gameMode !== 'fight' && gameMode !== 'fight-hard') {
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
        // Self-stun after throwing
        const selfStun = abil ? abil.selfStun || 2 : 2;
        p.stunned = Math.max(p.stunned, selfStun);
        p.effects.push({ type: 'void-star-throw', timer: 0.5 });
        p.effects.push({ type: 'stun', timer: selfStun });
        combatLog.push({ text: '⭐ Void Star thrown!', timer: 2, color: '#a020f0' });
      }
    }
    // Noli: check if clone is still alive
    if (p.noliCloneId) {
      const clone = gamePlayers.find(x => x.id === p.noliCloneId);
      if (!clone || !clone.alive) {
        if (clone) {
          const idx = gamePlayers.findIndex(x => x.id === p.noliCloneId);
          if (idx >= 0) gamePlayers.splice(idx, 1);
        }
        p.noliCloneId = null;
      }
    }

    // Cricket: check if wickets are still alive (both must survive)
    if (p.wicketIds && p.wicketIds.length === 2) {
      const w0 = gamePlayers.find(x => x.id === p.wicketIds[0]);
      const w1 = gamePlayers.find(x => x.id === p.wicketIds[1]);
      if (!w0 || !w0.alive || !w1 || !w1.alive) {
        // One wicket died, remove both
        for (const wid of p.wicketIds) {
          const idx = gamePlayers.findIndex(x => x.id === wid);
          if (idx >= 0) { gamePlayers[idx].alive = false; gamePlayers.splice(idx, 1); }
        }
        p.wicketIds = [];
      }
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
      if (inp.mouseDown && p.cdM1 <= 0) applyRemoteAbility(p, 'M1', inp);
      // Dragon breath: stop when remote player releases mouse
      if (p.dragonBreathActive && !inp.mouseDown) {
        p.dragonBreathActive = false;
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
    p.backroomsTimer -= dt;
    // 10 DPS while trapped in backrooms
    const brDmg = Math.round(10 * wallDt);
    if (brDmg > 0) dealDamage(null, p, brDmg);
    // Check if reached door
    const doorDx = p.x - p.backroomsDoorX;
    const doorDy = p.y - p.backroomsDoorY;
    if (Math.sqrt(doorDx * doorDx + doorDy * doorDy) < GAME_TILE * 1.2) {
      _exitBackrooms(p, 'escaped');
      continue;
    }
    // Auto-escape after 30s
    if (p.backroomsTimer <= 0) {
      _exitBackrooms(p, 'timeout');
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
  if (localPlayer.alive && mouseDown && localPlayer.cdM1 <= 0) {
    const _m1NonHost = (gameMode === undefined || gameMode === 'teams') && !isHostAuthority;
    if (!_m1NonHost) useAbility('M1');
    // Non-host M1 is relayed via mouseDown in player-input, host runs it
  }
  // Dragon breath: stop when mouse released
  if (localPlayer.dragonBreathActive && !mouseDown) {
    localPlayer.dragonBreathActive = false;
    // No cooldown — just fuel-gated
  }

  // CPU AI update (use wallDt for consistent timer behaviour with player)
  if (gameMode === 'fight' || gameMode === 'fight-hard') {
    updateCPUs(wallDt);
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
  // Unstable Eye: 30% speed boost
  if (localPlayer.unstableEyeTimer > 0) speed *= 1.3;
  // Napoleon Cavalry: 2.5x speed boost
  if (localPlayer.napoleonCavalry) speed *= 2.5;
  // Moderator Server Update: 50% speed buff
  if (localPlayer.modServerUpdateTimer > 0) speed *= 1.5;
  // Moderator Fear: 2x speed when running away from source
  if (localPlayer.modFearTimer > 0 && localPlayer.modFearSourceId) {
    const src = gamePlayers.find(p => p.id === localPlayer.modFearSourceId);
    if (src && src.alive) {
      const fdx = localPlayer.x - src.x; const fdy = localPlayer.y - src.y;
      const mdx = (keysDown.d || keysDown.ArrowRight ? 1 : 0) - (keysDown.a || keysDown.ArrowLeft ? 1 : 0);
      const mdy = (keysDown.s || keysDown.ArrowDown ? 1 : 0) - (keysDown.w || keysDown.ArrowUp ? 1 : 0);
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
  if (localPlayer.dragonBeamCharging || localPlayer.dragonBeamRecovery > 0) speed = 0;
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
          // Tiles stay as GROUND — isStumpTile() handles blocking movement
          // Push any players standing on the stump to a safe position nearby
          const stumpCenterX = (appleTree.col + 1) * GAME_TILE;
          const stumpCenterY = (appleTree.row + 1) * GAME_TILE;
          const pr = GAME_TILE * PLAYER_RADIUS_RATIO;
          for (const pl of gamePlayers) {
            if (!pl.alive) continue;
            // Check if player overlaps the 2x2 stump area
            const pCol = Math.floor(pl.x / GAME_TILE);
            const pRow = Math.floor(pl.y / GAME_TILE);
            if (pCol >= appleTree.col && pCol <= appleTree.col + 1 &&
                pRow >= appleTree.row && pRow <= appleTree.row + 1) {
              // Push outward from stump center to nearest safe position
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
              // If direct push failed, try 8 compass directions
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
              // Last resort: random safe position
              if (!placed) {
                const safe = getRandomSafePosition();
                pl.x = safe.x; pl.y = safe.y;
              }
            }
          }
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
              if (t2.id === p.ownerId || !t2.alive || t2.inBackrooms) continue;
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
          // Achievement: Cat kitten kills
          if (_kitTargetWasAlive && !bestTarget.alive && owner && owner.id === localPlayerId && !bestTarget.isSummon) {
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
        // Gamble-style random damage: 100-1000
        const roll = Math.random();
        let dmg;
        if (roll < 0.5) dmg = 100 + Math.floor(Math.random() * 200);       // 100-300
        else if (roll < 0.8) dmg = 300 + Math.floor(Math.random() * 200);   // 300-500
        else if (roll < 0.95) dmg = 500 + Math.floor(Math.random() * 300);  // 500-800
        else dmg = 800 + Math.floor(Math.random() * 200);                   // 800-1000
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
        // Touch = instant kill
        if (dist < radius * 2 && s.summonAttackTimer <= 0) {
          dealDamage(owner || s, prey, s.summonDamage, true);
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
      // Room (Boisvert): chase its specific target + constant 40 DPS regardless of distance
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
        // Move toward target but stop at firing range
        const fireRange = 6 * GAME_TILE;
        if (dist > fireRange) {
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
    }

    // Clean up summon if owner died or left the game entirely
    if (!owner || !owner.alive) {
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
  hard:   { thinkDelay: 0.18, aimError: 0.04, abilityDelay: 0.5, aggroRange: 16, retreatHp: 0.35, reactionTime: 0.10 },
  expert: { thinkDelay: 0.12, aimError: 0.02, abilityDelay: 0.35, aggroRange: 20, retreatHp: 0.40, reactionTime: 0.06 },
};

function updateCPUs(dt) {
  for (const cpu of gamePlayers) {
    if (!cpu.isCPU || !cpu.alive || cpu.stunned > 0) continue;
    // Skip summons handled by updateSummons (only noli-clone uses full CPU AI)
    if (cpu.isSummon && cpu.summonType !== 'noli-clone') continue;
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
      if (score < bestScore) {
        bestScore = score;
        bestDist = dist;
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
  // Unstable Eye: 30% speed boost
  if (cpu.unstableEyeTimer > 0) speed *= 1.3;
  // Napoleon Cavalry: 2.5x speed boost
  if (cpu.napoleonCavalry) speed *= 2.5;
  // Gear Up: speed penalty
  if (cpu.gearUpTimer > 0) speed *= (cpu.fighter.abilities[2].speedPenalty || 0.6);
  // D&D Human: 1.2x speed
  if (cpu.dndRace === 'human') speed *= 1.2;
  // Dragon: roar speed buff, fly speed, beam immobilization, breath slow
  if (cpu.dragonRoarActive) speed *= 1.3;
  if (cpu.dragonFlying) speed *= 2.5; // same as Napoleon cavalry
  if (cpu.dragonBreathActive) speed *= 0.5;
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

  // Retreat if low HP
  ai.retreating = cpu.hp / cpu.maxHp < params.retreatHp;

  let goalX, goalY;

  if (ai.attackTarget && ai.attackTarget.alive) {
    const target = ai.attackTarget;
    const dx = target.x - cpu.x; const dy = target.y - cpu.y;
    const dist = Math.sqrt(dx * dx + dy * dy);

    if (ai.retreating) {
      // Run away from target
      if (cpu.difficulty === 'expert' && appleTree && appleTree.apples.length > 0) {
        // Expert retreat: run toward nearest apple for healing
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
      // Approach to ideal range based on fighter type
      const idealRange = cpu.fighter.id === 'poker' ? 5 * GAME_TILE : cpu.fighter.id === 'filbus' ? 1.5 * GAME_TILE : cpu.fighter.id === 'cricket' ? 1.0 * GAME_TILE : cpu.fighter.id === 'deer' ? 1.0 * GAME_TILE : 1.2 * GAME_TILE;
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
    const isExpert = cpu.difficulty === 'expert';
    const centerX = (gameMap.cols / 2) * GAME_TILE;
    const centerY = (gameMap.rows / 2) * GAME_TILE;

    // Expert: seek apples or apple tree area when idle
    if (isExpert && appleTree) {
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
    if (isExpert) {
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
      if (cpu.difficulty === 'expert') {
        // Expert: soft pull toward center (0.7 blend) — allows zone entry to avoid worse outcomes
        moveX = moveX * 0.3 + toCenterX * 0.7;
        moveY = moveY * 0.3 + toCenterY * 0.7;
      } else {
        // Others: hard override to center
        moveX = toCenterX;
        moveY = toCenterY;
      }
    }
    // Expert: preemptive zone awareness — avoid moving INTO the zone edge
    if (cpu.difficulty === 'expert') {
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
    } else if (isCricket) {
      if (dist < 10 * GAME_TILE) {
        cpuUseSpecialCricket(cpu, target);
        return;
      }
    } else if (isDeer) {
      if (dist < 10 * GAME_TILE) {
        cpuUseSpecialDeer(cpu, target);
        return;
      }
    } else if (isNoli) {
      // Clone closest fighter
      cpuUseSpecialNoli(cpu);
      return;
    } else if (isCat) {
      // Exploding Kitten: spawn kittens when enemy nearby
      if (dist < 10 * GAME_TILE) {
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
      // D20: buff self (CPU solo — no teammates to buff)
      cpu.specialUsed = true;
      cpu.dndD20Active = true;
      cpu.effects.push({ type: 'd20-roll', timer: 3.0 });
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
    } else if (isCricket) {
      // Drive: melee hit + projectile reflect
      if (dist < 2 * GAME_TILE) {
        cpuCricketDrive(cpu, target, aimNx, aimNy);
        return;
      }
    } else if (isDeer) {
      // Deer's Fear: speed buff when moving away
      if (cpu.deerFearTimer <= 0 && dist < 5 * GAME_TILE) {
        cpu.cdE = fighter.abilities[1].cooldown;
        cpu.deerFearTimer = fighter.abilities[1].duration || 5;
        cpu.deerFearTargetX = target.x;
        cpu.deerFearTargetY = target.y;
        cpu.effects.push({ type: 'deer-fear', timer: fighter.abilities[1].duration || 5 });
        return;
      }
    } else if (isNoli) {
      // Void Rush: dash toward target
      if (!cpu.noliVoidRushActive && !cpu.noliVoidStarAiming && dist < 8 * GAME_TILE) {
        cpuNoliVoidRush(cpu, target);
        return;
      }
    } else if (isCat) {
      // Draw: use whenever available
      cpuCatDraw(cpu);
      return;
    } else if (isNapoleon) {
      // Cavalry: toggle mount if not already mounted
      if (!cpu.napoleonCavalry) {
        cpu.napoleonCavalry = true;
        cpu.effects.push({ type: 'cavalry-mount', timer: 1.5 });
      }
      return;
    } else if (isModerator) {
      // Scare: TP random enemy to self, stun, apply fear
      const enemies = gamePlayers.filter(p => p.alive && !p.isSummon && p.id !== cpu.id);
      if (enemies.length > 0) {
        const pick = enemies[Math.floor(Math.random() * enemies.length)];
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
      // Questing: spawn orc that chases self (CPU spawns orcs to farm GP)
      const abil = fighter.abilities[1];
      if (cpu.dndOrcIds.length < 3) {
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
      // Dragon Ride: fly when low HP or to close distance
      if (!cpu.dragonFlying && !cpu.dragonBeamCharging && !cpu.dragonBeamFiring) {
        const shouldFly = cpu.hp < cpu.maxHp * 0.3 || dist > 8 * GAME_TILE;
        if (shouldFly) {
          cpu.cdE = fighter.abilities[1].cooldown;
          cpu.dragonFlying = true;
          cpu.dragonFlyTimer = fighter.abilities[1].flyDuration || 5;
          cpu.effects.push({ type: 'dragon-fly', timer: 1.5 });
          return;
        }
      }
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
    } else if (isCricket) {
      // Gear Up: use when enemy nearby and not already active
      if (cpu.gearUpTimer <= 0 && dist < 4 * GAME_TILE) {
        cpu.cdR = fighter.abilities[2].cooldown;
        cpu.gearUpTimer = fighter.abilities[2].duration || 10;
        cpu.effects.push({ type: 'gear-up', timer: 1.5 });
        return;
      }
    } else if (isDeer) {
      // Deer's Seer: dodge state
      if (cpu.deerSeerTimer <= 0 && dist < 4 * GAME_TILE && cpu.hp < cpu.maxHp * 0.5) {
        cpu.cdR = fighter.abilities[2].cooldown;
        cpu.deerSeerTimer = fighter.abilities[2].duration || 5;
        cpu.effects.push({ type: 'deer-seer', timer: fighter.abilities[2].duration || 5 });
        return;
      }
    } else if (isNoli) {
      // Void Star: aimed area attack
      if (!cpu.noliVoidRushActive && !cpu.noliVoidStarAiming && dist < 8 * GAME_TILE) {
        cpuNoliVoidStar(cpu, target);
        return;
      }
    } else if (isCat) {
      // Attack buff when close to enemy
      if (cpu.catAttackBuff <= 0 && dist < 3 * GAME_TILE) {
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
      // Buy/Use: spend GP based on amount
      const gp = cpu.dndGP || 0;
      if (gp >= 1) {
        cpu.cdR = fighter.abilities[2].cooldown || 1;
        if (gp >= 8 && !cpu.dndCharm) {
          // Buy charm + M1 buff
          cpu.dndGP = 0;
          cpu.dndCharm = true;
          cpu.dndWeaponBonus = (cpu.dndWeaponBonus || 0) + 50;
        } else if (gp >= 5) {
          // Buy weapon upgrade
          cpu.dndGP = 0;
          cpu.dndWeaponBonus = (cpu.dndWeaponBonus || 0) + 50;
        } else if (gp >= 2) {
          // Random spell
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
      // Dragon Beam: fire at medium range when not already charging/flying
      if (!cpu.dragonBeamCharging && !cpu.dragonBeamFiring && cpu.dragonBeamRecovery <= 0 && !cpu.dragonFlying) {
        if (dist < 12 * GAME_TILE && dist > 3 * GAME_TILE) {
          cpu.cdR = fighter.abilities[2].cooldown;
          cpu.dragonBeamCharging = true;
          cpu.dragonBeamChargeTimer = fighter.abilities[2].chargeTime || 3;
          cpu.dragonBeamAimNx = aimNx;
          cpu.dragonBeamAimNy = aimNy;
          cpu.effects.push({ type: 'dragon-beam-charge', timer: fighter.abilities[2].chargeTime || 3 });
          return;
        }
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
      // Unstable Eye: use when enemy is nearby
      if (cpu.unstableEyeTimer <= 0 && dist < 6 * GAME_TILE) {
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
      // Deer T: Deer's Spear — antler stab + stun
      if (cpu.deerSeerTimer <= 0 && dist < (fighter.abilities[3].range || 1.2) * GAME_TILE) {
        cpuDeerSpear(cpu, target, aimNx, aimNy);
        return;
      }
    } else if (isNoli) {
      // Observant: teleport when low HP
      if (cpu.noliObservantUses < (fighter.abilities[3].maxUses || 3) && cpu.hp < cpu.maxHp * 0.3) {
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
      // Race Change: cycle races
      cpu.cdT = fighter.abilities[3].cooldown;
      const races = ['human', 'elf', 'dwarf'].filter(r => r !== (cpu.dndRace || 'human'));
      cpu.dndRace = races[Math.floor(Math.random() * races.length)];
      cpu.effects.push({ type: 'race-change', timer: 1.5 });
      return;
    } else if (isDragon) {
      // Draconic Roar: +30% speed self, +20% allies, -200HP, use once
      if (!cpu.dragonRoarActive && cpu.hp > 300) {
        cpu.cdT = fighter.abilities[3].cooldown;
        cpu.dragonRoarActive = true;
        cpu.hp -= (fighter.abilities[3].selfDamage || 200);
        if (cpu.hp <= 0) cpu.hp = 1;
        cpu.effects.push({ type: 'dragon-roar', timer: 2 });
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
  // Queen Bee Unicorn: blocks M1 attacks while alive (except creator)
  const cpuQueenBee = gamePlayers.find(p => p.alive && p.isSummon && p.summonType === 'queenbee-unicorn');
  const cpuQueenBeeBlocked = cpuQueenBee && cpuQueenBee.summonOwner !== cpu.id;
  if (cpu.cdM1 <= 0 && !cpuQueenBeeBlocked) {
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
    if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers.splice(oldIdx, 1); }
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
    if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers.splice(oldIdx, 1); }
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
  dealDamage(target, dmg, cpu);
  cpu.effects.push({ type: 'cat-scratch', timer: 0.3 });
}

function cpuCatDraw(cpu) {
  const abil = cpu.fighter.abilities[1];
  cpu.cdE = abil.cooldown;
  const roll = Math.random();
  if (roll < 0.25) {
    cpu.catCards = (cpu.catCards || 0) + 1;
    cpu.effects.push({ type: 'cat-draw-cat', timer: 1.0 });
  } else if (roll < 0.5) {
    // Shuffle: rotate positions
    const alive = gamePlayers.filter(p => p.alive && !p.isSummon);
    if (alive.length >= 2) {
      const positions = alive.map(p => ({ x: p.x, y: p.y }));
      const last = positions.pop();
      positions.unshift(last);
      const pr = GAME_TILE * PLAYER_RADIUS_RATIO;
      alive.forEach((p, i) => {
        let nx = positions[i].x, ny = positions[i].y;
        if (!canMoveTo(nx, ny, pr)) {
          for (let att = 0; att < 20; att++) {
            nx = positions[i].x + (Math.random() - 0.5) * GAME_TILE * 2;
            ny = positions[i].y + (Math.random() - 0.5) * GAME_TILE * 2;
            if (canMoveTo(nx, ny, pr)) break;
          }
          if (!canMoveTo(nx, ny, pr)) { nx = p.x; ny = p.y; }
        }
        p.x = nx; p.y = ny;
      });
    }
    cpu.effects.push({ type: 'cat-draw-shuffle', timer: 1.0 });
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
    // Copy a random non-M1 ability from the target (costs 1 cat card, skip cats, Filbus only Oddity Overthrow)
    if ((cpu.catCards || 0) < 1) { cpu.cdT = 0; return; }
    if (target.fighter && target.fighter.id === 'explodingcat') return;
    cpu.catCards--;
    const fid = target.fighter.id;
    const abilIdx = (fid === 'filbus') ? 3 : [1, 2, 3][Math.floor(Math.random() * 3)];
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
    if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers.splice(oldIdx, 1); }
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
    if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers.splice(oldIdx, 1); }
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
      lp.effects.push({ type: 'cat-scratch', timer: 0.2, aimNx, aimNy });
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
            // Tiles stay as GROUND — isStumpTile() handles blocking movement
            // Push any players standing on the stump to a safe position nearby
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
            combatLog.push({ text: '🪓 Apple tree chopped down!', timer: 4, color: '#e67e22' });
          }
        }
      }
    }
  }

  else if (key === 'E') {
    if (lp.cdE > 0) return;
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
        // Shuffle — everyone swaps positions
        const alivePlayers = gamePlayers.filter(p => p.alive && !p.isSummon);
        if (alivePlayers.length >= 2) {
          const positions = alivePlayers.map(p => ({ x: p.x, y: p.y }));
          const pr = GAME_TILE * PLAYER_RADIUS_RATIO;
          for (let i = 0; i < alivePlayers.length; i++) {
            const nextPos = positions[(i + 1) % positions.length];
            let nx = nextPos.x, ny = nextPos.y;
            // Ensure new position is not inside an obstacle
            if (!canMoveTo(nx, ny, pr)) {
              for (let att = 0; att < 20; att++) {
                nx = nextPos.x + (Math.random() - 0.5) * GAME_TILE * 2;
                ny = nextPos.y + (Math.random() - 0.5) * GAME_TILE * 2;
                if (canMoveTo(nx, ny, pr)) break;
              }
              if (!canMoveTo(nx, ny, pr)) { nx = alivePlayers[i].x; ny = alivePlayers[i].y; }
            }
            alivePlayers[i].x = nx;
            alivePlayers[i].y = ny;
          }
        }
        combatLog.push({ text: '🔀 Shuffle! Everyone swapped!', timer: 3, color: '#ff9900' });
        showPopup('🔀 SHUFFLE!');
        lp.effects.push({ type: 'cat-draw-shuffle', timer: 1.5 });
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
    } else if (isDragon) {
      // Dragon E: Dragon Ride — fly over obstacles for 5s
      lp.cdE = abil.cooldown;
      lp.dragonFlying = true;
      lp.dragonFlyTimer = abil.flyDuration || 5;
      lp.effects.push({ type: 'dragon-fly', timer: (abil.flyDuration || 5) + 0.5 });
      combatLog.push({ text: '🐉 Dragon Ride! Flying for 5s!', timer: 3, color: '#5b8fa8' });
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
      // Noli T: Observant — teleport to opposite side of map (max 3 uses)
      if (lp.noliVoidRushActive || lp.noliVoidStarAiming) return;
      if (lp.noliObservantUses >= (abil.maxUses || 3)) {
        combatLog.push({ text: '❌ No Observant charges left!', timer: 2, color: '#666' });
        lp.cdT = 0; // refund cooldown
        return;
      }
      lp.noliObservantUses++;
      lp.cdT = abil.cooldown;
      // Clear any lingering stun from previous abilities
      lp.stunned = 0;
      // Teleport to opposite side
      const mapW = gameMap.cols * GAME_TILE, mapH = gameMap.rows * GAME_TILE;
      let newX = mapW - lp.x, newY = mapH - lp.y;
      // Clamp to valid position
      const pr = GAME_TILE * PLAYER_RADIUS_RATIO;
      newX = Math.max(pr, Math.min(mapW - pr, newX));
      newY = Math.max(pr, Math.min(mapH - pr, newY));
      // Find nearest valid tile (checks all 4 corners for obstacles)
      if (!canMoveTo(newX, newY, pr)) {
        let foundValid = false;
        for (let attempts = 0; attempts < 30; attempts++) {
          const tryX = newX + (Math.random() - 0.5) * GAME_TILE * 3;
          const tryY = newY + (Math.random() - 0.5) * GAME_TILE * 3;
          const cx = Math.max(pr, Math.min(mapW - pr, tryX));
          const cy = Math.max(pr, Math.min(mapH - pr, tryY));
          if (canMoveTo(cx, cy, pr)) { newX = cx; newY = cy; foundValid = true; break; }
        }
        if (!foundValid) {
          newX = (gameMap.cols / 2 + 0.5) * GAME_TILE;
          newY = (gameMap.rows / 2 + 0.5) * GAME_TILE;
        }
      }
      lp.x = newX; lp.y = newY;
      lp.effects.push({ type: 'observant-tp', timer: 1.0 });
      combatLog.push({ text: '👁 Observant! (' + ((abil.maxUses || 3) - lp.noliObservantUses) + ' left)', timer: 3, color: '#a020f0' });
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
          const abilIdx = (fid === 'filbus') ? 3 : [1, 2, 3][Math.floor(Math.random() * 3)];
          lp.catStolenAbil = { fighterId: fid, abilIndex: abilIdx };
          lp.catStolenReady = true;
          const stolenName = closestTarget.fighter.abilities[abilIdx].name;
          combatLog.push({ text: '🐱 Stole ' + stolenName + ' from ' + closestTarget.name + '!', timer: 3, color: '#ff9900' });
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
    } else if (isDragon) {
      // Dragon T: Draconic Roar — +30% speed self, +20% allies, costs 200 HP
      lp.cdT = abil.cooldown;
      lp.dragonRoarActive = true;
      lp.hp -= (abil.selfDamage || 200);
      if (lp.hp <= 0) { lp.hp = 0; lp.alive = false; lp.effects.push({ type: 'death', timer: 2 }); return; }
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
      // Achievement tracking
      if (typeof trackBoiledOnePlayed === 'function') trackBoiledOnePlayed();
      // Broadcast to other clients
      if (typeof socket !== 'undefined' && socket.emit) {
        if (!isHostAuthority) socket.emit('player-buff', { type: 'boiled-one', duration: stunDur, cx: lp.x, cy: lp.y });
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
    } else if (isNoli) {
      // Noli SPACE: Hallucinations — clone the closest fighter as CPU ally
      lp.specialUsed = true;
      // Remove existing clone
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
    } else if (isDnd) {
      // D&D Campaigner SPACE: D20 Roll — buff all teammates' M1 to 1000 dmg until next death
      lp.specialUsed = true;
      lp.dndD20Active = true;
      lp.effects.push({ type: 'd20-roll', timer: 3.0 });
      for (const p of gamePlayers) {
        if (!p.alive || p.isSummon) continue;
        if (p.id === lp.id || (p.team && p.team === lp.team)) {
          p.dndD20Active = true;
        }
      }
      combatLog.push({ text: '🎲 NATURAL 20! All allies deal 650 M1 dmg until next death!', timer: 5, color: '#ffd700' });
    } else if (isDragon) {
      // Dragon SPACE: Power of the Evil — summon Yellow Ochre or Lich
      lp.specialUsed = true;
      // Kill old summon if exists
      if (lp.dragonSummonId) {
        const oldS = gamePlayers.find(p => p.id === lp.dragonSummonId);
        if (oldS && oldS.alive) { oldS.alive = false; oldS.hp = 0; oldS.effects.push({ type: 'death', timer: 2 }); }
      }
      const roll = Math.random();
      if (roll < 0.5) {
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
      } else {
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
        lp.dragonSummonId = lichId;
        lp.effects.push({ type: 'dragon-summon', timer: 2.0 });
        combatLog.push({ text: '💀 Lich summoned! (700HP, lightning, autoheal)', timer: 4, color: '#6a0dad' });
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

  // ── Move 4 (F) — achievement-unlocked abilities ───────────
  else if (key === 'F') {
    if (lp.isCPU) return; // CPU never uses Move 4
    if (lp.fighter.abilities.length <= 5) return; // no F ability
    const fAbil = lp.fighter.abilities[5];
    // Check if unlocked via achievement
    if (typeof isMove4Unlocked === 'function' && !isMove4Unlocked(lp.fighter.id)) return;
    // Max 3 uses per game
    if (lp.move4Uses >= 3) return;
    if (lp.cdF > 0) return;

    if (isPoker) {
      // Full House: next move guaranteed best option
      lp.move4Uses++;
      lp.pokerFullHouseActive = true;
      lp.cdF = fAbil.cooldown;
      lp.effects.push({ type: 'full-house', timer: 2.0 });
      combatLog.push({ text: '🃏 Full House! Next move = best option.', timer: 3, color: '#f5a623' });
    } else if (isFilbus) {
      // Analogus: randomly pick Backrooms, Alternate, or Boisvert
      // Block if only 2 alive non-summon players remain
      const aliveNonSummon = gamePlayers.filter(p => p.alive && !p.isSummon);
      if (aliveNonSummon.length <= 2) {
        combatLog.push({ text: '❌ Cannot use Analogus with only 2 players left!', timer: 2, color: '#999' });
        return;
      }
      // With exactly 3 players: the third player (not Filbus, not the target) must have >50% HP
      if (aliveNonSummon.length === 3) {
        // Find closest enemy first to determine who the target would be
        let checkClosestDist = Infinity, checkClosestTarget = null;
        for (const t of gamePlayers) {
          if (t.id === lp.id || !t.alive || t.isSummon) continue;
          const d = Math.sqrt((t.x - lp.x) ** 2 + (t.y - lp.y) ** 2);
          if (d < checkClosestDist) { checkClosestDist = d; checkClosestTarget = t; }
        }
        if (checkClosestTarget) {
          const thirdPlayer = aliveNonSummon.find(p => p.id !== lp.id && p.id !== checkClosestTarget.id);
          if (thirdPlayer && thirdPlayer.hp <= thirdPlayer.maxHp * 0.5) {
            combatLog.push({ text: '❌ Cannot use Analogus — remaining player is too weak!', timer: 2, color: '#999' });
            return;
          }
        }
      }
      // Find closest enemy
      let closestDist = Infinity, closestTarget = null;
      for (const t of gamePlayers) {
        if (t.id === lp.id || !t.alive || t.isSummon) continue;
        const d = Math.sqrt((t.x - lp.x) ** 2 + (t.y - lp.y) ** 2);
        if (d < closestDist) { closestDist = d; closestTarget = t; }
      }
      if (!closestTarget) {
        combatLog.push({ text: '❌ No targets for Analogus!', timer: 2, color: '#999' });
        return;
      }
      lp.move4Uses++;
      lp.cdF = fAbil.cooldown;

      // Cleanup: if target already in backrooms, exit them first
      if (closestTarget.inBackrooms) {
        _exitBackrooms(closestTarget, 'new-analogus');
      }
      // Cleanup: if target already has an alternate, kill it
      if (closestTarget.hasAlternate && closestTarget.alternateId) {
        const oldAlt = gamePlayers.find(a => a.id === closestTarget.alternateId);
        if (oldAlt && oldAlt.alive) { oldAlt.alive = false; oldAlt.hp = 0; oldAlt.effects.push({ type: 'death', timer: 2 }); }
        closestTarget.hasAlternate = false;
        closestTarget.alternateId = null;
      }

      const roll = Math.random();
      if (roll < 0.33) {
        // ── BACKROOMS ──
        // Place door at a random walkable tile far from the target
        const mapW = gameMap.cols, mapH = gameMap.rows;
        let bestDoorR = -1, bestDoorC = -1, bestDoorDist = 0;
        for (let attempt = 0; attempt < 40; attempt++) {
          const rr = Math.floor(Math.random() * mapH);
          const cc = Math.floor(Math.random() * mapW);
          if (gameMap.tiles[rr] && gameMap.tiles[rr][cc] !== undefined
              && gameMap.tiles[rr][cc] !== TILE.WATER && gameMap.tiles[rr][cc] !== TILE.ROCK) {
            const dd = Math.sqrt((rr - Math.floor(closestTarget.y / GAME_TILE)) ** 2 +
                                 (cc - Math.floor(closestTarget.x / GAME_TILE)) ** 2);
            if (dd > bestDoorDist) { bestDoorDist = dd; bestDoorR = rr; bestDoorC = cc; }
          }
        }
        if (bestDoorR < 0) { bestDoorR = 1; bestDoorC = 1; }
        closestTarget.inBackrooms = true;
        closestTarget.backroomsDoorX = (bestDoorC + 0.5) * GAME_TILE;
        closestTarget.backroomsDoorY = (bestDoorR + 0.5) * GAME_TILE;
        closestTarget.backroomsTimer = 30; // 30s max
        // Spawn chaser entity
        const chaserId = 'br-chaser-' + closestTarget.id + '-' + Date.now();
        const chaserFighter = getFighter('fighter'); // use basic fighter stats
        const chaser = createPlayerState(
          { id: chaserId, name: '???', color: '#8b8000', fighterId: 'fighter' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
          chaserFighter
        );
        // Place chaser at Filbus position — verify it's walkable, otherwise use safe position
        const chaserRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (canMoveTo(lp.x, lp.y, chaserRadius)) {
          chaser.x = lp.x;
          chaser.y = lp.y;
        } else {
          const safeChaserPos = getRandomSafePosition();
          chaser.x = safeChaserPos.x;
          chaser.y = safeChaserPos.y;
        }
        chaser.hp = 999999;
        chaser.maxHp = 999999;
        chaser.isSummon = true;
        chaser.summonOwner = lp.id;
        chaser.summonType = 'backrooms-chaser';
        chaser.summonSpeed = closestTarget.fighter.speed * 0.7; // noticeably slower than the player
        chaser.summonDamage = 999999; // instant kill on touch
        chaser.summonAttackCD = 0.5;
        chaser.summonAttackTimer = 0;
        chaser.summonTargetId = closestTarget.id; // only chases this player
        chaser.isCPU = true;
        chaser.noCloneHeal = true;
        gamePlayers.push(chaser);
        closestTarget.backroomsChaserId = chaserId;
        closestTarget.effects.push({ type: 'backrooms-enter', timer: 2.0 });
        lp.effects.push({ type: 'analogus-cast', timer: 1.5 });
        combatLog.push({ text: '🚪 Analogus: ' + closestTarget.name + ' sent to the Backrooms!', timer: 4, color: '#8b8000' });
        if (closestTarget.id === localPlayerId) {
          combatLog.push({ text: '⚠️ You are in the Backrooms! Find the door to escape! (10 DPS, no healing)', timer: 5, color: '#ff4444' });
        }
      } else if (roll < 0.66) {
        // ── ALTERNATE ──
        const altId = 'alternate-' + closestTarget.id + '-' + Date.now();
        const altFighter = closestTarget.fighter;
        const alt = createPlayerState(
          { id: altId, name: closestTarget.name, color: closestTarget.color, fighterId: altFighter.id },
          { r: Math.floor(closestTarget.y / GAME_TILE), c: Math.floor(closestTarget.x / GAME_TILE) },
          altFighter
        );
        // Spawn alternate 6-8 tiles away in a random direction, ensuring safe position
        const altRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
        let altPlaced = false;
        for (let attempt = 0; attempt < 20; attempt++) {
          const angle = Math.random() * Math.PI * 2;
          const dist = GAME_TILE * (6 + Math.random() * 2); // 6-8 tiles away
          const tryX = closestTarget.x + Math.cos(angle) * dist;
          const tryY = closestTarget.y + Math.sin(angle) * dist;
          if (canMoveTo(tryX, tryY, altRadius)) {
            alt.x = tryX; alt.y = tryY; altPlaced = true; break;
          }
        }
        if (!altPlaced) {
          const safeAltPos = getRandomSafePosition();
          alt.x = safeAltPos.x; alt.y = safeAltPos.y;
        }
        alt.hp = 500;
        alt.maxHp = 500;
        alt.isSummon = true;
        alt.summonOwner = lp.id;
        alt.summonType = 'alternate';
        alt.summonSpeed = closestTarget.fighter.speed * 0.9; // slightly slower
        alt.summonDamage = 999999; // instant kill on touch
        alt.summonAttackCD = 0.5;
        alt.summonAttackTimer = 0;
        alt.summonTargetId = closestTarget.id; // only chases the original
        alt.isCPU = true;
        alt.noCloneHeal = true;
        gamePlayers.push(alt);
        closestTarget.hasAlternate = true;
        closestTarget.alternateId = altId;
        closestTarget.effects.push({ type: 'alternate-spawn', timer: 2.0 });
        lp.effects.push({ type: 'analogus-cast', timer: 1.5 });
        combatLog.push({ text: '👤 Analogus: ' + closestTarget.name + '\'s Alternate has appeared!', timer: 4, color: '#6a0dad' });
        if (closestTarget.id === localPlayerId) {
          combatLog.push({ text: '⚠️ Your Alternate is hunting you! You can\'t see others or heal! (10 DPS)', timer: 5, color: '#ff4444' });
        }
      } else {
        // ── BOISVERT ──
        // Spawn a "Room" entity for each non-Filbus alive player
        lp.effects.push({ type: 'analogus-cast', timer: 1.5 });
        let roomCount = 0;
        for (const target of gamePlayers) {
          if (target.id === lp.id || !target.alive || target.isSummon) continue;
          const roomId = 'room-' + target.id + '-' + Date.now();
          const roomFighter = getFighter('fighter');
          const room = createPlayerState(
            { id: roomId, name: 'Room', color: '#000', fighterId: 'fighter' },
            { r: Math.floor(target.y / GAME_TILE), c: Math.floor(target.x / GAME_TILE) },
            roomFighter
          );
          // Spawn near the target — ensure safe position
          const roomRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
          let roomPlaced = false;
          for (let ra = 0; ra < 16; ra++) {
            const angle = Math.random() * Math.PI * 2;
            const dist = GAME_TILE * (2 + Math.random() * 2);
            const tryX = target.x + Math.cos(angle) * dist;
            const tryY = target.y + Math.sin(angle) * dist;
            if (canMoveTo(tryX, tryY, roomRadius)) {
              room.x = tryX; room.y = tryY; roomPlaced = true; break;
            }
          }
          if (!roomPlaced) {
            const safeRoomPos = getRandomSafePosition();
            room.x = safeRoomPos.x; room.y = safeRoomPos.y;
          }
          room.hp = 500;
          room.maxHp = 500;
          room.isSummon = true;
          room.summonOwner = lp.id;
          room.summonType = 'room';
          room.summonSpeed = 2.5;
          room.summonDamage = 0; // damage via DPS aura, not touch
          room.summonAttackCD = 1;
          room.summonAttackTimer = 0;
          room.summonTargetId = target.id; // only targets this player
          room.roomDPS = 50; // constant 50 DPS regardless of distance
          room.isCPU = true;
          room.noCloneHeal = true;
          gamePlayers.push(room);
          roomCount++;
          if (target.id === localPlayerId) {
            combatLog.push({ text: '⚠️ A Room has appeared! It deals 50 DPS until killed!', timer: 5, color: '#333' });
          }
        }
        combatLog.push({ text: '🏚️ Boisvert: ' + roomCount + ' Room(s) spawned!', timer: 4, color: '#333' });
      }
    } else if (is1x) {
      // Forsaken Help: spawn c00lkidd
      if (lp.coolkiddId) {
        // Dismiss existing
        const sIdx = gamePlayers.findIndex(p => p.id === lp.coolkiddId);
        if (sIdx >= 0) {
          gamePlayers[sIdx].alive = false;
          gamePlayers[sIdx].hp = 0;
          gamePlayers[sIdx].effects.push({ type: 'death', timer: 2 });
        }
        lp.coolkiddId = null;
        lp.cdF = 5;
        combatLog.push({ text: '👋 c00lkidd dismissed', timer: 2, color: '#999' });
      } else {
        const summonId = 'coolkidd-' + lp.id + '-' + Date.now();
        lp.move4Uses++;
        const summon = createPlayerState(
          { id: summonId, name: 'c00lkidd', color: '#ff0000', fighterId: 'onexonexonex' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
          fighter
        );
        summon.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 2;
        summon.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 2;
        summon.hp = fAbil.summonHp || 500;
        summon.maxHp = fAbil.summonHp || 500;
        summon.isSummon = true;
        summon.summonOwner = lp.id;
        summon.summonType = 'coolkidd';
        summon.summonSpeed = 0;
        summon.summonDamage = 0;
        summon.summonAttackCD = fAbil.summonFireCD || 4;
        summon.summonAttackTimer = 0;
        summon.summonProjectileSpeed = fAbil.projectileSpeed || 30;
        gamePlayers.push(summon);
        lp.coolkiddId = summonId;
        lp.cdF = fAbil.cooldown;
        lp.effects.push({ type: 'coolkidd-spawn', timer: 1.5 });
        combatLog.push({ text: '🔴 c00lkidd summoned!', timer: 3, color: '#ff0000' });
      }
    } else if (isCricket) {
      // Bowler: spawn a bowler
      if (lp.bowlerId) {
        const sIdx = gamePlayers.findIndex(p => p.id === lp.bowlerId);
        if (sIdx >= 0) {
          gamePlayers[sIdx].alive = false;
          gamePlayers[sIdx].hp = 0;
          gamePlayers[sIdx].effects.push({ type: 'death', timer: 2 });
        }
        lp.bowlerId = null;
        lp.cdF = 5;
        combatLog.push({ text: '👋 Bowler dismissed', timer: 2, color: '#999' });
      } else {
        const summonId = 'bowler-' + lp.id + '-' + Date.now();
        lp.move4Uses++;
        const summon = createPlayerState(
          { id: summonId, name: 'Bowler', color: '#228b22', fighterId: 'cricket' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
          fighter
        );
        summon.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 2;
        summon.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 2;
        summon.hp = fAbil.summonHp || 300;
        summon.maxHp = fAbil.summonHp || 300;
        summon.isSummon = true;
        summon.summonOwner = lp.id;
        summon.summonType = 'bowler';
        summon.summonSpeed = 0;
        summon.summonDamage = fAbil.damage || 200;
        summon.summonAttackCD = fAbil.summonFireCD || 5;
        summon.summonAttackTimer = 0;
        gamePlayers.push(summon);
        lp.bowlerId = summonId;
        lp.cdF = fAbil.cooldown;
        lp.effects.push({ type: 'bowler-spawn', timer: 1.5 });
        combatLog.push({ text: '🏏 Bowler summoned!', timer: 3, color: '#228b22' });
      }
    } else if (isDeer) {
      // YOU HAVE CRABS: spawn 5 crabs
      lp.move4Uses++;
      lp.cdF = fAbil.cooldown;
      const count = fAbil.crabCount || 5;
      if (!lp.crabIds) lp.crabIds = [];
      for (let i = 0; i < count; i++) {
        const crabId = 'crab-' + lp.id + '-' + i + '-' + Date.now();
        const crab = createPlayerState(
          { id: crabId, name: 'Crab', color: '#ff6347', fighterId: 'deer' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
          fighter
        );
        crab.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 3;
        crab.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 3;
        const crabRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(crab.x, crab.y, crabRadius)) { crab.x = lp.x; crab.y = lp.y; }
        crab.hp = fAbil.crabHp || 400;
        crab.maxHp = fAbil.crabHp || 400;
        crab.isSummon = true;
        crab.summonOwner = lp.id;
        crab.summonType = 'crab';
        crab.summonSpeed = fAbil.crabSpeed || 2.0;
        crab.summonDamage = fAbil.damage || 200;
        crab.summonAttackCD = fAbil.crabAttackCD || 1;
        crab.summonAttackTimer = 0;
        gamePlayers.push(crab);
        lp.crabIds.push(crabId);
      }
      lp.effects.push({ type: 'crab-spawn', timer: 2.0 });
      combatLog.push({ text: '🦀 YOU HAVE CRABS!', timer: 3, color: '#ff6347' });
    } else if (isNoli) {
      // Forsaken Help: spawn John Doe on map edge
      lp.move4Uses++;
      // Remove existing John Doe if any
      if (lp.johnDoeId) {
        const oldIdx = gamePlayers.findIndex(x => x.id === lp.johnDoeId);
        if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers[oldIdx].hp = 0; gamePlayers[oldIdx].effects.push({ type: 'death', timer: 2 }); }
        lp.johnDoeId = null;
      }
      // Pick a random walkable edge tile
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
      const summonId = 'johndoe-' + lp.id + '-' + Date.now();
      const summon = createPlayerState(
        { id: summonId, name: 'John Doe', color: '#8b0000', fighterId: 'noli' },
        edgeSpawn,
        fighter
      );
      summon.hp = fAbil.summonHp || 500;
      summon.maxHp = fAbil.summonHp || 500;
      summon.isSummon = true;
      summon.summonOwner = lp.id;
      summon.summonType = 'johndoe';
      summon.summonSpeed = 0;
      summon.summonDamage = fAbil.damage || 500;
      summon.summonAttackCD = fAbil.summonFireCD || 10;
      summon.summonAttackTimer = fAbil.summonFireCD || 10; // starts on cooldown
      summon.spikeDuration = fAbil.spikeDuration || 5;
      summon.touchDPS = fAbil.touchDPS || 100;
      gamePlayers.push(summon);
      lp.johnDoeId = summonId;
      lp.cdF = fAbil.cooldown;
      lp.effects.push({ type: 'johndoe-spawn', timer: 1.5 });
      combatLog.push({ text: '🗡️ John Doe summoned on the edge!', timer: 3, color: '#8b0000' });
    } else if (isCat) {
      // Unstable Unicorns: summon a random unicorn
      // Remove existing unicorn if any
      if (lp.catUnicornId) {
        const oldIdx = gamePlayers.findIndex(x => x.id === lp.catUnicornId);
        if (oldIdx >= 0) { gamePlayers[oldIdx].alive = false; gamePlayers.splice(oldIdx, 1); }
        lp.catUnicornId = null;
      }
      // Pick random unicorn type (1/3 each)
      const uniRoll = Math.random();
      let uniType, uniName, uniColor, uniLog;
      if (uniRoll < 0.33) {
        uniType = 'destructive-unicorn';
        uniName = 'Extremely Destructive Unicorn';
        uniColor = '#ff2200';
        uniLog = '💥 Extremely Destructive Unicorn summoned! It will explode on contact for 999 damage!';
      } else if (uniRoll < 0.66) {
        uniType = 'queenbee-unicorn';
        uniName = 'Queen Bee Unicorn';
        uniColor = '#ffd700';
        uniLog = '👑 Queen Bee Unicorn summoned! Enemies cannot use M1 until it\'s killed!';
      } else {
        uniType = 'seductive-unicorn';
        uniName = 'Seductive Unicorn';
        uniColor = '#ff69b4';
        uniLog = '💖 Seductive Unicorn summoned! You are invulnerable until it dies!';
      }
      const uniId = 'unicorn-' + lp.id + '-' + Date.now();
      const uniFighter = getFighter('fighter');
      const uni = createPlayerState(
        { id: uniId, name: uniName, color: uniColor, fighterId: 'fighter' },
        { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
        uniFighter
      );
      uni.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 3;
      uni.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 3;
      uni.hp = 500;
      uni.maxHp = 500;
      uni.isSummon = true;
      uni.summonOwner = lp.id;
      uni.summonType = uniType;
      uni.summonSpeed = 3.0;
      uni.summonDamage = uniType === 'destructive-unicorn' ? 999 : 0;
      uni.summonAttackCD = 0.5;
      uni.summonAttackTimer = 0;
      uni.isCPU = true;
      uni.noCloneHeal = true;
      gamePlayers.push(uni);
      lp.catUnicornId = uniId;
      lp.move4Uses++;
      lp.cdF = fAbil.cooldown;
      lp.effects.push({ type: 'unicorn-spawn', timer: 1.5 });
      combatLog.push({ text: uniLog, timer: 4, color: uniColor });
    } else if (isNapoleon) {
      // Napoleon F: Light Infantry — spawn 3 infantrymen
      lp.move4Uses++;
      lp.cdF = fAbil.cooldown;
      const count = fAbil.infantryCount || 3;
      if (!lp.napoleonInfantryIds) lp.napoleonInfantryIds = [];
      for (let i = 0; i < count; i++) {
        const infId = 'infantry-' + lp.id + '-f-' + i + '-' + Date.now();
        const inf = createPlayerState(
          { id: infId, name: 'Infantryman', color: '#2c3e50', fighterId: 'napoleon' },
          { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) },
          fighter
        );
        inf.x = lp.x + (Math.random() - 0.5) * GAME_TILE * 3;
        inf.y = lp.y + (Math.random() - 0.5) * GAME_TILE * 3;
        const infRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
        if (!canMoveTo(inf.x, inf.y, infRadius)) { inf.x = lp.x; inf.y = lp.y; }
        inf.hp = fAbil.infantryHp || 50;
        inf.maxHp = fAbil.infantryHp || 50;
        inf.isSummon = true;
        inf.summonOwner = lp.id;
        inf.summonType = 'napoleon-infantry';
        inf.summonSpeed = fAbil.infantrySpeed || 2.0;
        inf.summonDamage = fAbil.damage || 100;
        inf.summonAttackCD = fAbil.infantryFireCD || 1;
        inf.summonAttackTimer = 0;
        inf.summonProjectileSpeed = fAbil.infantryProjectileSpeed || 38;
        inf.summonProjectileRange = fAbil.infantryRange || 0.8;
        gamePlayers.push(inf);
        lp.napoleonInfantryIds.push(infId);
      }
      lp.effects.push({ type: 'infantry-spawn', timer: 1.5 });
      combatLog.push({ text: '🎖 Light Infantry deployed!', timer: 3, color: '#2c3e50' });
    } else if (isModerator) {
      // Moderator F: Firewall — invincible + invisible for 5s
      lp.move4Uses++;
      lp.cdF = fAbil.cooldown;
      lp.modFirewallTimer = fAbil.duration || 5;
      lp.effects.push({ type: 'firewall', timer: (fAbil.duration || 5) + 0.5 });
      combatLog.push({ text: '🛡 Firewall active! Invincible + invisible for 5s!', timer: 3, color: '#e74c3c' });
    } else if (isDnd) {
      // D&D F: Sidekick — spawn a clone of yourself with half max HP
      // Kill old sidekick if exists
      if (lp.dndSidekickId) {
        const oldSk = gamePlayers.find(p => p.id === lp.dndSidekickId);
        if (oldSk && oldSk.alive) { oldSk.alive = false; oldSk.hp = 0; oldSk.effects.push({ type: 'death', timer: 2 }); }
      }
      lp.move4Uses++;
      lp.cdF = fAbil.cooldown;
      const skId = 'dnd-sidekick-' + lp.id + '-' + Date.now();
      const skFighter = lp.fighter;
      const sk = createPlayerState(
        { id: skId, name: lp.name + "'s Sidekick", color: lp.color || '#daa520', fighterId: 'dnd' },
        { r: Math.floor(lp.y / GAME_TILE), c: Math.floor(lp.x / GAME_TILE) }, skFighter
      );
      const skRadius = GAME_TILE * PLAYER_RADIUS_RATIO;
      const angle = Math.random() * Math.PI * 2;
      sk.x = lp.x + Math.cos(angle) * GAME_TILE * 2;
      sk.y = lp.y + Math.sin(angle) * GAME_TILE * 2;
      if (!canMoveTo(sk.x, sk.y, skRadius)) { const safe = getRandomSafePosition(); sk.x = safe.x; sk.y = safe.y; }
      sk.hp = Math.floor(lp.maxHp / 2); sk.maxHp = Math.floor(lp.maxHp / 2);
      sk.isSummon = true; sk.summonOwner = lp.id;
      sk.summonType = 'dnd-sidekick';
      sk.dndRace = lp.dndRace || 'human';
      sk.summonSpeed = 3.0; sk.summonDamage = 100 + (lp.dndWeaponBonus || 0);
      sk.summonAttackCD = sk.dndRace === 'dwarf' ? 2 : 0.5;
      sk.summonAttackTimer = 0;
      sk.isCPU = true;
      gamePlayers.push(sk);
      lp.dndSidekickId = skId;
      lp.effects.push({ type: 'dnd-sidekick-spawn', timer: 1.5 });
      combatLog.push({ text: '🛡 Sidekick summoned!', timer: 3, color: '#daa520' });
    } else {
      // Fighter: Potion — heal 300 over 3s
      lp.move4Uses++;
      lp.cdF = fAbil.cooldown;
      lp.potionHealPool = fAbil.healAmount || 300;
      lp.potionHealTimer = fAbil.healDuration || 3;
      lp.effects.push({ type: 'potion', timer: (fAbil.healDuration || 3) + 0.5 });
      combatLog.push({ text: '🧪 Potion! Healing ' + (fAbil.healAmount || 300) + ' HP...', timer: 3, color: '#2ecc71' });
    }
  }
}

function executeSpecialLanding() {
  const lp = localPlayer;
  const abil = lp.fighter.abilities[4]; // Special
  const isCricketSpecial = lp.fighter.id === 'cricket';
  const isDeerSpecial = lp.fighter.id === 'deer';
  lp.specialAiming = false;
  lp.specialJumping = false;
  lp.specialUsed = true;
  lp.effects = lp.effects.filter((fx) => fx.type !== 'jump' && fx.type !== 'sixer-aim' && fx.type !== 'igloo-aim');

  const landX = lp.specialAimX;
  const landY = lp.specialAimY;

  if (isDeerSpecial) {
    // Deer Igloo: place igloo at aimed location, damage over time handled in updateGame
    lp.iglooX = landX;
    lp.iglooY = landY;
    lp.iglooTimer = abil.duration || 5;
    lp.effects.push({ type: 'igloo', timer: (abil.duration || 5) + 1 });
    combatLog.push({ text: '🏔 Igloo built!', timer: 3, color: '#87ceeb' });
    return;
  }

  // Check if hit any enemy within 1 tile of landing
  const hitRange = GAME_TILE * 1.2;
  let hitSomeone = false;

  for (const target of gamePlayers) {
    if (target.id === lp.id || !target.alive) continue;
    const dist = Math.sqrt((target.x - landX) ** 2 + (target.y - landY) ** 2);
    if (dist <= hitRange) {
      const wasAlive = target.alive;
      dealDamage(lp, target, abil.damage);
      // Achievement: Fighter special kills
      if (wasAlive && !target.alive && lp.id === localPlayerId && lp.fighter.id === 'fighter' && !target.isSummon) {
        _fighterSpecialKillsThisGame++;
        if (_fighterSpecialKillsThisGame >= 2 && typeof trackFighterSpecialAch === 'function') {
          trackFighterSpecialAch();
        }
      }
      hitSomeone = true;
    }
  }

  // Move player to landing position (Cricket stays in place — ball lands there instead)
  if (!isCricketSpecial) {
    lp.x = landX;
    lp.y = landY;
  }

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

function _exitBackrooms(p, reason) {
  p.inBackrooms = false;
  p.backroomsTimer = 0;
  // Kill chaser
  if (p.backroomsChaserId) {
    const chaser = gamePlayers.find(c => c.id === p.backroomsChaserId);
    if (chaser) {
      chaser.alive = false;
      chaser.hp = 0;
      chaser.effects.push({ type: 'death', timer: 2 });
    }
    p.backroomsChaserId = null;
  }
  p.effects.push({ type: 'backrooms-exit', timer: 1.5 });
  if (p.id === localPlayerId) {
    if (reason === 'escaped') {
      combatLog.push({ text: '🚪 You escaped the Backrooms!', timer: 4, color: '#2ecc71' });
    } else {
      combatLog.push({ text: '🚪 Backrooms timed out — you\'re free!', timer: 4, color: '#f5a623' });
    }
  }
}

function dealDamage(attacker, target, amount, viaSummon) {
  if (!target.alive) return;
  // Team friendly fire prevention: same-team players/summons can't hurt each other
  if (attacker && attacker !== target && gameMode === 'teams') {
    const attackerTeam = attacker.isSummon
      ? (gamePlayers.find(o => o.id === attacker.summonOwner) || {}).team
      : attacker.team;
    const targetTeam = target.isSummon
      ? (gamePlayers.find(o => o.id === target.summonOwner) || {}).team
      : target.team;
    if (attackerTeam && targetTeam && attackerTeam === targetTeam) return;
  }
  // Obelisk and backrooms chaser are invincible
  if (target.isSummon && (target.summonType === 'obelisk' || target.summonType === 'backrooms-chaser')) return;
  // Backrooms: players in backrooms can't be damaged by normal attacks (only the chaser)
  if (target.inBackrooms && attacker && attacker.summonType !== 'backrooms-chaser') return;
  // Backrooms: players outside backrooms can't be hit by backrooms entities
  if (!target.inBackrooms && attacker && attacker.summonType === 'backrooms-chaser') return;
  // Backrooms: player IN backrooms cannot attack players in the normal dimension
  if (attacker && attacker.inBackrooms && !target.inBackrooms && target.summonType !== 'backrooms-chaser') return;
  // Alternate: player being hunted by an alternate can only attack the alternate, not other players
  if (attacker && attacker.hasAlternate && !target.isSummon) return;
  if (attacker && attacker.hasAlternate && target.isSummon && target.summonType !== 'alternate') return;
  // Seductive Unicorn: owner is invulnerable while their seductive unicorn is alive
  if (!target.isSummon) {
    const seductiveUnicorn = gamePlayers.find(p => p.alive && p.isSummon && p.summonType === 'seductive-unicorn' && p.summonOwner === target.id);
    if (seductiveUnicorn) return;
  }
  // Moderator Firewall: invincible
  if (target.modFirewallTimer > 0) return;
  // Moderator Server Update: 50% damage reduction (defense buff)
  if (target.modServerUpdateTimer > 0) amount = Math.round(amount * 0.5);
  // Moderator Server Update: 50% damage increase (attack buff)
  if (attacker && attacker.modServerUpdateTimer > 0) amount = Math.round(amount * 1.5);
  // Deer Seer: dodge by jumping to the side
  if (target.deerSeerTimer > 0 && target.fighter && target.fighter.id === 'deer') {
    const r = GAME_TILE * PLAYER_RADIUS_RATIO;
    // Jump perpendicular to attacker direction
    let jx = 0, jy = 0;
    if (attacker && attacker.alive) {
      const adx = target.x - attacker.x; const ady = target.y - attacker.y;
      const ad = Math.sqrt(adx * adx + ady * ady) || 1;
      // Perpendicular (randomly left or right)
      const side = Math.random() < 0.5 ? 1 : -1;
      jx = (-ady / ad) * side; jy = (adx / ad) * side;
    } else {
      const angle = Math.random() * Math.PI * 2;
      jx = Math.cos(angle); jy = Math.sin(angle);
    }
    const jumpDist = GAME_TILE * 2;
    for (let s = 10; s >= 1; s--) {
      const tryX = target.x + jx * jumpDist * (s / 10);
      const tryY = target.y + jy * jumpDist * (s / 10);
      if (canMoveTo(tryX, tryY, r)) { target.x = tryX; target.y = tryY; break; }
    }
    target.effects.push({ type: 'deer-dodge', timer: 0.4 });
    return; // damage fully dodged
  }
  // Cat Seer (Reveal the Future): dodge by jumping, same as deer
  if (target.catSeerTimer > 0 && target.fighter && target.fighter.id === 'explodingcat') {
    const r = GAME_TILE * PLAYER_RADIUS_RATIO;
    let jx = 0, jy = 0;
    if (attacker && attacker.alive) {
      const adx = target.x - attacker.x; const ady = target.y - attacker.y;
      const ad = Math.sqrt(adx * adx + ady * ady) || 1;
      const side = Math.random() < 0.5 ? 1 : -1;
      jx = (-ady / ad) * side; jy = (adx / ad) * side;
    } else {
      const angle = Math.random() * Math.PI * 2;
      jx = Math.cos(angle); jy = Math.sin(angle);
    }
    const jumpDist = GAME_TILE * 2;
    for (let s = 10; s >= 1; s--) {
      const tryX = target.x + jx * jumpDist * (s / 10);
      const tryY = target.y + jy * jumpDist * (s / 10);
      if (canMoveTo(tryX, tryY, r)) { target.x = tryX; target.y = tryY; break; }
    }
    target.effects.push({ type: 'cat-dodge', timer: 0.4 });
    return; // damage fully dodged
  }
  // Blinds modifier (Poker)
  if (target.blindBuff === 'small') amount = Math.round(amount * 0.5);
  else if (target.blindBuff === 'big') amount = Math.round(amount * 1.5);
  // Napoleon Cavalry: 2x damage received while mounted
  if (target.napoleonCavalry) amount = Math.round(amount * 2);
  // D&D Dwarf: 0.8x damage taken
  if (target.dndRace === 'dwarf') amount = Math.round(amount * 0.8);
  // D&D Elf attacker: +50 damage bonus
  if (attacker && attacker.dndRace === 'elf') amount += 50;
  // Napoleon Defensive Tactics wall: invincible — absorbs no damage itself
  if (target.isSummon && target.summonType === 'napoleon-wall') return;
  // Napoleon Defensive Tactics: anyone inside a wall area takes half damage
  if (!target.isSummon) {
    const walls = gamePlayers.filter(w => w.alive && w.summonType === 'napoleon-wall');
    for (const wall of walls) {
      const ws = (wall.wallSize || 2) * GAME_TILE / 2;
      if (Math.abs(target.x - wall.x) < ws && Math.abs(target.y - wall.y) < ws) {
        amount = Math.round(amount * 0.5);
        break;
      }
    }
  }
  // Cricket Gear Up: 80% damage reduction
  if (target.gearUpTimer > 0) {
    const originalAmount = amount;
    amount = Math.round(amount * 0.2);
    // Achievement: Gear Up absorption tracking (Cricket in SP)
    if (target.id === localPlayerId && target.fighter && target.fighter.id === 'cricket' && (gameMode === 'fight' || gameMode === 'fight-hard')) {
      const absorbed = originalAmount - amount;
      _gearDmgAbsorbedRemainder += absorbed;
      if (_gearDmgAbsorbedRemainder >= 10 && typeof trackGearDmgAbsorbed === 'function') {
        trackGearDmgAbsorbed(_gearDmgAbsorbedRemainder);
        _gearDmgAbsorbedRemainder = _gearDmgAbsorbedRemainder % 10;
      }
    }
  }
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

  // Broadcast damage to other clients (skip in host-authoritative — snapshot handles it)
  if (typeof socket !== 'undefined' && socket.emit && attacker && attacker.id === localPlayerId && !isHostAuthority) {
    socket.emit('player-damage', { targetId: target.id, amount, attackerId: attacker.id });
  }

  if (target.hp <= 0) {
    target.hp = 0;
    target.alive = false;
    target.effects.push({ type: 'death', timer: 2 });
    // Achievement: summon kill in multiplayer
    if (viaSummon && attacker && attacker.id === localPlayerId && !target.isSummon && gameMode !== 'training' && gameMode !== 'fight' && gameMode !== 'fight-hard') {
      if (typeof trackSummonKillMP === 'function') trackSummonKillMP();
      // Filbus oddity kill in MP
      if (attacker.fighter && attacker.fighter.id === 'filbus' && typeof trackFilbusOddityKill === 'function') {
        trackFilbusOddityKill();
      }
    }
    // Achievement: 1X kill tracking
    if (attacker && attacker.id === localPlayerId && attacker.fighter && attacker.fighter.id === 'onexonexonex' && !target.isSummon && target.fighter) {
      // Kill Noli in MP
      if (target.fighter.id === 'noli' && gameMode !== 'training' && gameMode !== 'fight' && gameMode !== 'fight-hard') {
        if (typeof trackOnexKilledNoliMP === 'function') trackOnexKilledNoliMP();
      }
      // Kill Cat in SP
      if (target.fighter.id === 'explodingcat' && (gameMode === 'fight' || gameMode === 'fight-hard')) {
        if (typeof trackOnexKilledCatSP === 'function') trackOnexKilledCatSP();
      }
    }
    // Achievement: Deer water kill
    if (attacker && attacker.id === localPlayerId && attacker.fighter && attacker.fighter.id === 'deer' && !target.isSummon) {
      const aTileR = Math.floor(attacker.y / GAME_TILE);
      const aTileC = Math.floor(attacker.x / GAME_TILE);
      let nearWater = false;
      for (let dr = -1; dr <= 1 && !nearWater; dr++) {
        for (let dc = -1; dc <= 1 && !nearWater; dc++) {
          const r = aTileR + dr, c = aTileC + dc;
          if (r >= 0 && r < gameMap.rows && c >= 0 && c < gameMap.cols && gameMap.tiles[r][c] === TILE.WATER) {
            nearWater = true;
          }
        }
      }
      if (nearWater && typeof trackDeerWaterKill === 'function') trackDeerWaterKill();
    }
    // Achievement: Napoleon unlock — M1 kills (any fighter, not via summon or special)
    if (attacker && attacker.id === localPlayerId && !target.isSummon && _lastDealDamageWasM1) {
      if (typeof trackNapoleonM1Kill === 'function') trackNapoleonM1Kill();
    }
    // Achievement: Napoleon unlock — track summon kills for win-with-summon
    if (viaSummon && attacker && attacker.id === localPlayerId && !target.isSummon) {
      _hadSummonKillThisGame = true;
    }
    // Achievement: Filbus boiled one kills
    if (attacker && attacker.id === localPlayerId && attacker.fighter && attacker.fighter.id === 'filbus' && attacker.boiledOneActive && !target.isSummon) {
      _filbusBoiledKillsThisGame++;
      if (_filbusBoiledKillsThisGame >= 2 && typeof trackFilbusBoiledKill === 'function') {
        trackFilbusBoiledKill();
      }
    }
    // Achievement: Dragon Beam kills in a single game
    if (attacker && attacker.id === localPlayerId && attacker.fighter && attacker.fighter.id === 'dragon' && attacker.dragonBeamFiring && !target.isSummon) {
      _dragonBeamKillsThisGame++;
      if (_dragonBeamKillsThisGame >= 2 && typeof trackDragonBeamAch === 'function') {
        trackDragonBeamAch();
      }
    }
    // Init spectator camera if local player died
    if (target.id === localPlayerId) {
      freeCamX = target.x;
      freeCamY = target.y;
      spectateIndex = -1;
      deathOverlayTimer = 0;
    }
    // Clean up backrooms if target was in backrooms
    if (target.inBackrooms) {
      _exitBackrooms(target, 'died');
    }
    // Clean up alternate if target had one
    if (target.hasAlternate && target.alternateId) {
      const alt = gamePlayers.find(a => a.id === target.alternateId);
      if (alt && alt.alive) {
        alt.alive = false; alt.hp = 0;
        alt.effects.push({ type: 'death', timer: 2 });
      }
      target.hasAlternate = false;
      target.alternateId = null;
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
      // Deer robot death: clear reference, apply 30s M1 cooldown
      if (target.summonType === 'deer-robot' && owner) {
        if (owner.deerRobotId === target.id) owner.deerRobotId = null;
        owner.cdM1 = 30;
        combatLog.push({ text: '🤖 Robot died!', timer: 3, color: '#ff4444' });
      }
      // Coolkidd death: clear reference
      if (target.summonType === 'coolkidd' && owner) {
        if (owner.coolkiddId === target.id) owner.coolkiddId = null;
      }
      // Bowler death: clear reference
      if (target.summonType === 'bowler' && owner) {
        if (owner.bowlerId === target.id) owner.bowlerId = null;
      }
      // Crab death: clear from owner's crabIds array
      if (target.summonType === 'crab' && owner && owner.crabIds) {
        const cidx = owner.crabIds.indexOf(target.id);
        if (cidx >= 0) owner.crabIds.splice(cidx, 1);
      }
      // John Doe death: clear reference
      if (target.summonType === 'johndoe' && owner) {
        if (owner.johnDoeId === target.id) owner.johnDoeId = null;
      }
      // Unicorn death: clear catUnicornId
      if ((target.summonType === 'destructive-unicorn' || target.summonType === 'queenbee-unicorn' || target.summonType === 'seductive-unicorn') && owner) {
        if (owner.catUnicornId === target.id) owner.catUnicornId = null;
      }
      // Alternate death: free the original player
      if (target.summonType === 'alternate') {
        const prey = target.summonTargetId ? gamePlayers.find(t => t.id === target.summonTargetId) : null;
        if (prey) {
          prey.hasAlternate = false;
          prey.alternateId = null;
          prey.effects.push({ type: 'alternate-end', timer: 1.5 });
          if (prey.id === localPlayerId) {
            combatLog.push({ text: '✅ Your Alternate was destroyed! You are visible again.', timer: 4, color: '#2ecc71' });
          }
        }
      }
      // Backrooms chaser death: shouldn't normally happen (invincible) but clean up
      if (target.summonType === 'backrooms-chaser') {
        const prey = target.summonTargetId ? gamePlayers.find(t => t.id === target.summonTargetId) : null;
        if (prey && prey.inBackrooms) {
          _exitBackrooms(prey, 'escaped');
        }
      }
      // D&D Orc death: GP only if killed by the owner; stolen if another campaigner kills it
      if (target.summonType === 'dnd-orc' && owner) {
        if (owner.dndOrcIds) {
          const idx = owner.dndOrcIds.indexOf(target.id);
          if (idx >= 0) owner.dndOrcIds.splice(idx, 1);
        }
        if (attacker && attacker.id === owner.id) {
          // Owner killed their own orc — award GP
          owner.dndGP = (owner.dndGP || 0) + 1;
          if (owner.id === localPlayerId) {
            combatLog.push({ text: '🪙 +1 GP! (Total: ' + owner.dndGP + ')', timer: 3, color: '#ffd700' });
          }
        } else if (attacker && !attacker.isSummon && attacker.fighter && attacker.fighter.id === 'dnd') {
          // Another D&D Campaigner killed the orc — they steal the GP
          attacker.dndGP = (attacker.dndGP || 0) + 1;
          if (attacker.id === localPlayerId) {
            combatLog.push({ text: '🪙 Quest stolen from ' + (owner.name || 'enemy') + '! +1 GP! (Total: ' + attacker.dndGP + ')', timer: 4, color: '#ffd700' });
          }
          if (owner.id === localPlayerId) {
            combatLog.push({ text: '⚠️ Quest was stolen by ' + (attacker.name || 'enemy') + '!', timer: 4, color: '#ff4444' });
          }
        } else {
          // Someone else (not a campaigner) killed the orc — no GP
          if (owner.id === localPlayerId) {
            combatLog.push({ text: "⚠️ You couldn't finish the quest!", timer: 4, color: '#ff4444' });
          }
        }
      }
      // D&D Zombie death: clear from gamePlayers (no GP reward)
      if (target.summonType === 'dnd-zombie') {
        // No special cleanup needed — just dies
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
    // Napoleon death: immediately kill all Napoleon summons
    if (target.napoleonCannonId) {
      const c = gamePlayers.find(p => p.id === target.napoleonCannonId);
      if (c && c.alive) { c.alive = false; c.hp = 0; c.effects.push({ type: 'death', timer: 2 }); }
      target.napoleonCannonId = null;
    }
    if (target.napoleonWallId) {
      const w = gamePlayers.find(p => p.id === target.napoleonWallId);
      if (w && w.alive) { w.alive = false; w.hp = 0; w.effects.push({ type: 'death', timer: 2 }); }
      target.napoleonWallId = null;
    }
    if (target.napoleonInfantryIds && target.napoleonInfantryIds.length > 0) {
      for (const iid of target.napoleonInfantryIds) {
        const inf = gamePlayers.find(p => p.id === iid);
        if (inf && inf.alive) { inf.alive = false; inf.hp = 0; inf.effects.push({ type: 'death', timer: 2 }); }
      }
      target.napoleonInfantryIds = [];
    }
    // D&D death: kill orcs/zombies/sidekick owned by the dead player
    if (target.dndOrcIds && target.dndOrcIds.length > 0) {
      for (const oid of target.dndOrcIds) {
        const orc = gamePlayers.find(p => p.id === oid);
        if (orc && orc.alive) { orc.alive = false; orc.hp = 0; orc.effects.push({ type: 'death', timer: 2 }); }
      }
      target.dndOrcIds = [];
    }
    if (target.dndSidekickId) {
      const sk = gamePlayers.find(p => p.id === target.dndSidekickId);
      if (sk && sk.alive) { sk.alive = false; sk.hp = 0; sk.effects.push({ type: 'death', timer: 2 }); }
      target.dndSidekickId = null;
    }
    // Dragon death: kill summon
    if (target.dragonSummonId) {
      const ds = gamePlayers.find(p => p.id === target.dragonSummonId);
      if (ds && ds.alive) { ds.alive = false; ds.hp = 0; ds.effects.push({ type: 'death', timer: 2 }); }
      target.dragonSummonId = null;
    }
    // Dragon/Draconic Roar: ANY death clears roar buffs for ALL players
    for (const dp of gamePlayers) {
      if (dp.dragonRoarActive) {
        dp.dragonRoarActive = false;
        if (dp.id === localPlayerId) {
          combatLog.push({ text: '🐉 Roar buff ended — someone died!', timer: 3, color: '#5b8fa8' });
        }
      }
    }
    // D&D D20: ANY death clears the D20 buff for ALL players
    for (const dp of gamePlayers) {
      if (dp.dndD20Active) {
        dp.dndD20Active = false;
        if (dp.id === localPlayerId) {
          combatLog.push({ text: '🎲 D20 buff ended — someone died!', timer: 3, color: '#ff6600' });
        }
      }
    }
    // Moderator Bug Fixing: clear disabled abilities on all players when someone dies
    for (const p of gamePlayers) {
      if (p.modDisabledAbilities && p.modDisabledAbilities.length > 0) {
        p.modDisabledAbilities = [];
        if (p.id === localPlayerId) {
          combatLog.push({ text: '🔧 Bug fixes cleared — someone died!', timer: 3, color: '#2ecc71' });
        }
      }
    }
    // Tell server this player died (only host in authoritative mode, or singleplayer)
    if (typeof socket !== 'undefined' && socket.emit) {
      // In host-authoritative, only the host should emit deaths to avoid duplicate server tracking
      if (isHostAuthority || (gameMode !== undefined && gameMode !== 'teams')) {
        socket.emit('player-died', { playerId: target.id });
      }
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
  // Interrupt channels on the local player when hit by remote attacker
  if (target.id === localPlayerId) {
    if (target.isCraftingChair) {
      target.isCraftingChair = false;
      target.craftTimer = 0;
      combatLog.push({ text: '🪑 Chair crafting interrupted!', timer: 2, color: '#e94560' });
    }
    if (target.isEatingChair) {
      target.isEatingChair = false;
      target.eatTimer = 0;
      target.eatHealPool = 0;
      combatLog.push({ text: '🪑 Chair eating interrupted!', timer: 2, color: '#e94560' });
    }
  }
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
      deathOverlayTimer = 0;
    }
  }
}

function onRemoteKnockback(targetId, x, y) {
  const target = gamePlayers.find((p) => p.id === targetId);
  if (target) {
    target.x = x; target.y = y;
    // Also snap the interpolation target so it doesn't lerp back to old position
    target._targetX = x; target._targetY = y;
  }
}

function onZoneSync(newInset, newTimer) {
  zoneInset = newInset;
  zoneTimer = newTimer;
  // Back-calculate what zonePhaseStart would be for this timer value
  zonePhaseStart = Date.now() - (ZONE_INTERVAL - newTimer) * 1000;
}

function onGameOver(winnerId, winnerName, winningTeam) {
  gameRunning = false;
  const cw = gameCanvas.width;
  const ch = gameCanvas.height;
  gameCtx.fillStyle = 'rgba(0, 0, 0, 0.7)';
  gameCtx.fillRect(0, 0, cw, ch);

  // Team mode win
  if (winningTeam) {
    const myTeam = localPlayer ? localPlayer.team : null;
    const isMyTeam = myTeam === winningTeam;
    gameCtx.fillStyle = isMyTeam ? '#2ecc71' : '#e94560';
    gameCtx.font = 'bold 36px "Press Start 2P", monospace';
    gameCtx.textAlign = 'center';
    gameCtx.fillText(isMyTeam ? 'TEAM VICTORY!' : 'TEAM DEFEATED', cw / 2, ch / 2 - 20);
    gameCtx.fillStyle = '#fff';
    gameCtx.font = 'bold 16px "Press Start 2P", monospace';
    gameCtx.fillText('Team ' + winningTeam + ' wins!', cw / 2, ch / 2 + 30);
    if (isMyTeam && typeof trackMPWin === 'function') {
      trackMPWin(localPlayer ? localPlayer.fighter.id : selectedFighterId);
    }
    return;
  }

  if (winnerId) {
    const isMe = winnerId === localPlayerId;
    gameCtx.fillStyle = isMe ? '#2ecc71' : '#e94560';
    gameCtx.font = 'bold 36px "Press Start 2P", monospace';
    gameCtx.textAlign = 'center';
    gameCtx.fillText(isMe ? 'VICTORY!' : 'DEFEATED', cw / 2, ch / 2 - 20);
    gameCtx.fillStyle = '#fff';
    gameCtx.font = 'bold 16px "Press Start 2P", monospace';
    gameCtx.fillText((winnerName || 'Someone') + ' wins!', cw / 2, ch / 2 + 30);
    // Achievement tracking: multiplayer win
    if (isMe && typeof trackMPWin === 'function') {
      trackMPWin(localPlayer ? localPlayer.fighter.id : selectedFighterId);
      // Check deer restricted win (only M1, T/Spear, SPACE/IGLOO used)
      if (localPlayer && localPlayer.fighter.id === 'deer' && typeof trackDeerRestrictedWin === 'function') {
        const forbidden = new Set(['E', 'R']);
        let usedForbidden = false;
        for (const k of usedAbilityKeys) {
          if (forbidden.has(k)) { usedForbidden = true; break; }
        }
        if (!usedForbidden) trackDeerRestrictedWin();
      }
      // Poker: win without using special
      if (localPlayer && localPlayer.fighter.id === 'poker' && !localPlayer.specialUsed && typeof trackPokerNoSpecialWin === 'function') {
        trackPokerNoSpecialWin();
      }
      // Napoleon unlock: win a battle with a summon
      if (_hadSummonKillThisGame && typeof trackNapoleonSummonWin === 'function') {
        trackNapoleonSummonWin();
      }
      // Moderator achievement: win one game as moderator
      if (localPlayer && localPlayer.fighter.id === 'moderator' && typeof trackModWin === 'function') {
        trackModWin();
      }
      // D&D achievement: track race win
      if (localPlayer && localPlayer.fighter.id === 'dnd' && typeof trackDndRaceWin === 'function') {
        trackDndRaceWin(localPlayer.dndRace || 'human');
      }
    }
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

  // ── Apple Tree rendering ──────────────────────────────────
  if (appleTree) {
    const treeScreenX = appleTree.col * GAME_TILE - camX;
    const treeScreenY = appleTree.row * GAME_TILE - camY;
    const ts = GAME_TILE; // tile size
    const tw = ts * 2;    // tree width (2 tiles)
    const th = ts * 2;    // tree height (2 tiles)

    if (appleTree.alive) {
      // ── Trunk ──
      const trunkW = tw * 0.22;
      const trunkH = th * 0.45;
      const trunkX = treeScreenX + tw / 2 - trunkW / 2;
      const trunkY = treeScreenY + th - trunkH;

      // Trunk shadow
      gameCtx.fillStyle = 'rgba(0,0,0,0.18)';
      gameCtx.beginPath();
      gameCtx.ellipse(treeScreenX + tw / 2, treeScreenY + th - 2, tw * 0.35, th * 0.08, 0, 0, Math.PI * 2);
      gameCtx.fill();

      // Trunk body
      gameCtx.fillStyle = '#6b3e26';
      gameCtx.fillRect(trunkX, trunkY, trunkW, trunkH);
      // Bark texture lines
      gameCtx.strokeStyle = '#4a2a18';
      gameCtx.lineWidth = 1;
      for (let i = 0; i < 4; i++) {
        const bx = trunkX + trunkW * (0.2 + Math.random() * 0.6);
        gameCtx.beginPath();
        gameCtx.moveTo(bx, trunkY + trunkH * 0.1 + i * trunkH * 0.2);
        gameCtx.lineTo(bx + (Math.random() - 0.5) * 3, trunkY + trunkH * 0.3 + i * trunkH * 0.2);
        gameCtx.stroke();
      }
      // Trunk highlight
      gameCtx.fillStyle = '#8b5a3a';
      gameCtx.fillRect(trunkX + trunkW * 0.6, trunkY, trunkW * 0.15, trunkH);

      // ── Canopy (multiple layered circles for a full, bushy look) ──
      const cx = treeScreenX + tw / 2;
      const cy = treeScreenY + th * 0.35;
      const canopyR = tw * 0.42;

      // Dark shadow layer
      gameCtx.fillStyle = '#1e6b1e';
      gameCtx.beginPath();
      gameCtx.arc(cx, cy + canopyR * 0.15, canopyR * 1.05, 0, Math.PI * 2);
      gameCtx.fill();

      // Main canopy
      gameCtx.fillStyle = '#2d8c2d';
      gameCtx.beginPath();
      gameCtx.arc(cx, cy, canopyR, 0, Math.PI * 2);
      gameCtx.fill();

      // Leaf clusters (overlapping arcs for depth)
      gameCtx.fillStyle = '#3aad3a';
      const clusters = [
        { dx: -canopyR * 0.45, dy: -canopyR * 0.2, r: canopyR * 0.55 },
        { dx: canopyR * 0.4, dy: -canopyR * 0.15, r: canopyR * 0.5 },
        { dx: -canopyR * 0.2, dy: -canopyR * 0.5, r: canopyR * 0.45 },
        { dx: canopyR * 0.15, dy: -canopyR * 0.45, r: canopyR * 0.4 },
        { dx: 0, dy: canopyR * 0.25, r: canopyR * 0.5 },
      ];
      for (const cl of clusters) {
        gameCtx.beginPath();
        gameCtx.arc(cx + cl.dx, cy + cl.dy, cl.r, 0, Math.PI * 2);
        gameCtx.fill();
      }

      // Bright highlights (top)
      gameCtx.fillStyle = '#4fc44f';
      gameCtx.beginPath();
      gameCtx.arc(cx - canopyR * 0.15, cy - canopyR * 0.45, canopyR * 0.3, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.beginPath();
      gameCtx.arc(cx + canopyR * 0.25, cy - canopyR * 0.35, canopyR * 0.22, 0, Math.PI * 2);
      gameCtx.fill();

      // Canopy outline
      gameCtx.strokeStyle = 'rgba(0,0,0,0.2)';
      gameCtx.lineWidth = 1.5;
      gameCtx.beginPath();
      gameCtx.arc(cx, cy, canopyR * 1.02, 0, Math.PI * 2);
      gameCtx.stroke();

      // ── Tree HP bar ──
      if (appleTree.hp < appleTree.maxHp) {
        const barW = tw * 0.7;
        const barH = 5;
        const barX = treeScreenX + tw / 2 - barW / 2;
        const barY = treeScreenY - 10;
        gameCtx.fillStyle = 'rgba(0,0,0,0.5)';
        gameCtx.fillRect(barX - 1, barY - 1, barW + 2, barH + 2);
        gameCtx.fillStyle = '#555';
        gameCtx.fillRect(barX, barY, barW, barH);
        const hpFrac = appleTree.hp / appleTree.maxHp;
        gameCtx.fillStyle = hpFrac > 0.5 ? '#2ecc71' : hpFrac > 0.25 ? '#f1c40f' : '#e74c3c';
        gameCtx.fillRect(barX, barY, barW * hpFrac, barH);
      }
    } else {
      // ── Dead tree: stump (centered in the 2x2 area) ──
      const centerX = treeScreenX + tw / 2;
      const centerY = treeScreenY + th / 2;
      const stumpW = tw * 0.3;
      const stumpH = th * 0.25;
      const stumpX = centerX - stumpW / 2;
      const stumpY = centerY - stumpH / 2;

      // Stump shadow
      gameCtx.fillStyle = 'rgba(0,0,0,0.15)';
      gameCtx.beginPath();
      gameCtx.ellipse(centerX, stumpY + stumpH + 2, tw * 0.2, th * 0.05, 0, 0, Math.PI * 2);
      gameCtx.fill();

      // Stump body
      gameCtx.fillStyle = '#5a3420';
      gameCtx.fillRect(stumpX, stumpY, stumpW, stumpH);
      // Stump top (rings)
      gameCtx.fillStyle = '#7a5035';
      gameCtx.beginPath();
      gameCtx.ellipse(centerX, stumpY, stumpW / 2, stumpH * 0.25, 0, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.strokeStyle = '#4a2a18';
      gameCtx.lineWidth = 0.8;
      gameCtx.beginPath();
      gameCtx.ellipse(centerX, stumpY, stumpW * 0.3, stumpH * 0.15, 0, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.beginPath();
      gameCtx.ellipse(centerX, stumpY, stumpW * 0.15, stumpH * 0.08, 0, 0, Math.PI * 2);
      gameCtx.stroke();

      // Regrow timer
      if (appleTree.regrowTimer > 0) {
        gameCtx.fillStyle = 'rgba(255,255,255,0.8)';
        gameCtx.font = 'bold 10px "Press Start 2P", monospace';
        gameCtx.textAlign = 'center';
        gameCtx.fillText(Math.ceil(appleTree.regrowTimer) + 's', centerX, stumpY - 8);
        gameCtx.textAlign = 'left';
      }
    }

    // ── Render apples ──
    for (const apple of appleTree.apples) {
      const ax = (apple.col + 0.5) * GAME_TILE - camX;
      const ay = (apple.row + 0.5) * GAME_TILE - camY;
      const ar = GAME_TILE * 0.25;

      // Apple body
      gameCtx.fillStyle = '#e74c3c';
      gameCtx.beginPath();
      gameCtx.arc(ax, ay, ar, 0, Math.PI * 2);
      gameCtx.fill();
      // Apple highlight
      gameCtx.fillStyle = '#ff6b6b';
      gameCtx.beginPath();
      gameCtx.arc(ax - ar * 0.25, ay - ar * 0.3, ar * 0.35, 0, Math.PI * 2);
      gameCtx.fill();
      // Stem
      gameCtx.strokeStyle = '#5a3420';
      gameCtx.lineWidth = 1.5;
      gameCtx.beginPath();
      gameCtx.moveTo(ax, ay - ar);
      gameCtx.lineTo(ax + 1, ay - ar - 4);
      gameCtx.stroke();
      // Leaf on stem
      gameCtx.fillStyle = '#2ecc71';
      gameCtx.beginPath();
      gameCtx.ellipse(ax + 3, ay - ar - 3, 3, 1.5, 0.5, 0, Math.PI * 2);
      gameCtx.fill();
    }
  }

  // ── Backrooms visual overlay (yellowed map for trapped player) ──
  if (localPlayer.inBackrooms) {
    // Yellow-sepia overlay on entire screen
    gameCtx.fillStyle = 'rgba(180, 160, 60, 0.35)';
    gameCtx.fillRect(0, 0, cw, ch);
    // Render the door
    const doorSX = localPlayer.backroomsDoorX - camX;
    const doorSY = localPlayer.backroomsDoorY - camY;
    if (doorSX > -50 && doorSX < cw + 50 && doorSY > -50 && doorSY < ch + 50) {
      const doorW = GAME_TILE * 0.7;
      const doorH = GAME_TILE * 1.2;
      // Door frame
      gameCtx.fillStyle = '#4a2800';
      gameCtx.fillRect(doorSX - doorW / 2 - 3, doorSY - doorH / 2 - 3, doorW + 6, doorH + 6);
      // Door body
      gameCtx.fillStyle = '#8b5a2b';
      gameCtx.fillRect(doorSX - doorW / 2, doorSY - doorH / 2, doorW, doorH);
      // Door handle
      gameCtx.fillStyle = '#ffd700';
      gameCtx.beginPath();
      gameCtx.arc(doorSX + doorW * 0.25, doorSY, 2.5, 0, Math.PI * 2);
      gameCtx.fill();
      // EXIT label above door
      gameCtx.fillStyle = '#ffd700';
      gameCtx.font = 'bold 9px "Press Start 2P", monospace';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('EXIT', doorSX, doorSY - doorH / 2 - 8);
      gameCtx.textAlign = 'left';
      // Pulsing glow around door
      const doorPulse = 0.5 + 0.5 * Math.sin(Date.now() * 0.005);
      gameCtx.strokeStyle = `rgba(255, 215, 0, ${0.4 + doorPulse * 0.4})`;
      gameCtx.lineWidth = 3;
      gameCtx.strokeRect(doorSX - doorW / 2 - 5, doorSY - doorH / 2 - 5, doorW + 10, doorH + 10);
    }
    // Timer display
    gameCtx.fillStyle = '#ff4444';
    gameCtx.font = 'bold 16px "Press Start 2P", monospace';
    gameCtx.textAlign = 'center';
    gameCtx.fillText('BACKROOMS: ' + Math.ceil(localPlayer.backroomsTimer) + 's', cw / 2, 30);
    gameCtx.textAlign = 'left';
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

    // ── Backrooms visibility: player in backrooms is invisible to others ──
    if (p.inBackrooms && p.id !== localPlayerId) continue;
    // Backrooms chaser: only visible to the trapped player
    if (p.summonType === 'backrooms-chaser' && p.summonTargetId !== localPlayerId) continue;

    // ── Alternate visibility: the real player is invisible to everyone except themselves ──
    if (p.hasAlternate && p.id !== localPlayerId) continue;
    // Player being hunted by alternate can only see themselves and their alternate
    if (localPlayer && localPlayer.hasAlternate && p.id !== localPlayerId
        && p.id !== localPlayer.alternateId && !p.isSummon) continue;

    // ── Room visibility: only visible to its target player ──
    if (p.summonType === 'room' && p.summonTargetId !== localPlayerId) continue;

    // ── Moderator Firewall: invisible to enemies while active ──
    if (p.modFirewallTimer > 0 && p.id !== localPlayerId) continue;

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
      } else if (p.summonType === 'deer-robot') {
        // Deer Robot: metallic gray square body
        gameCtx.fillStyle = isDying ? '#8b0000' : '#708090';
        const rSize = radius * 0.8;
        gameCtx.fillRect(sx - rSize, sy - rSize, rSize * 2, rSize * 2);
        gameCtx.strokeStyle = '#4a5568';
        gameCtx.lineWidth = 2;
        gameCtx.strokeRect(sx - rSize, sy - rSize, rSize * 2, rSize * 2);
        // Antenna
        gameCtx.strokeStyle = '#a0aec0';
        gameCtx.lineWidth = 1.5;
        gameCtx.beginPath();
        gameCtx.moveTo(sx, sy - rSize);
        gameCtx.lineTo(sx, sy - rSize - 5);
        gameCtx.stroke();
        gameCtx.fillStyle = '#f56565';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - rSize - 5, 2, 0, Math.PI * 2);
        gameCtx.fill();
        // Eyes
        gameCtx.fillStyle = '#00ff66';
        gameCtx.beginPath();
        gameCtx.arc(sx - 3, sy - 2, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + 3, sy - 2, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'wicket') {
        // Wicket: three vertical stumps
        gameCtx.fillStyle = isDying ? '#8b0000' : '#c8a96e';
        const stumpW = 2, stumpH = radius * 1.5;
        for (let wi = -1; wi <= 1; wi++) {
          gameCtx.fillRect(sx + wi * 4 - stumpW / 2, sy - stumpH / 2, stumpW, stumpH);
        }
        // Bails on top
        gameCtx.fillStyle = '#a0522d';
        gameCtx.fillRect(sx - 5, sy - stumpH / 2 - 2, 4, 2);
        gameCtx.fillRect(sx + 1, sy - stumpH / 2 - 2, 4, 2);
      } else if (p.summonType === 'noli-clone') {
        // Noli Hallucination clone: colored dot with ghostly purple overlay
        gameCtx.fillStyle = isDying ? '#8b0000' : p.color;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        // Purple translucent overlay
        gameCtx.fillStyle = 'rgba(160, 32, 240, 0.25)';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        // Pulsing purple outline
        const clonePulse = 0.5 + 0.5 * Math.sin(Date.now() * 0.006);
        gameCtx.strokeStyle = `rgba(160, 32, 240, ${0.5 + clonePulse * 0.4})`;
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 1, 0, Math.PI * 2);
        gameCtx.stroke();
        // Ghost icon — small "👻" indicator
        gameCtx.fillStyle = 'rgba(160, 32, 240, 0.7)';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - radius - 5, 3, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'exploding-kitten') {
        // Exploding Kitten: black dot with cat ears and orange danger glow
        gameCtx.fillStyle = isDying ? '#8b0000' : '#111';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        // Pulsing orange danger glow
        const kittenPulse = 0.5 + 0.5 * Math.sin(Date.now() * 0.008);
        gameCtx.strokeStyle = `rgba(255, 120, 0, ${0.5 + kittenPulse * 0.5})`;
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 1, 0, Math.PI * 2);
        gameCtx.stroke();
        // Cat ears (two triangles on top)
        gameCtx.fillStyle = isDying ? '#8b0000' : '#111';
        gameCtx.beginPath();
        gameCtx.moveTo(sx - radius * 0.7, sy - radius * 0.3);
        gameCtx.lineTo(sx - radius * 0.3, sy - radius * 1.3);
        gameCtx.lineTo(sx - radius * 0.0, sy - radius * 0.5);
        gameCtx.closePath();
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.moveTo(sx + radius * 0.7, sy - radius * 0.3);
        gameCtx.lineTo(sx + radius * 0.3, sy - radius * 1.3);
        gameCtx.lineTo(sx + radius * 0.0, sy - radius * 0.5);
        gameCtx.closePath();
        gameCtx.fill();
        // Inner ear pink
        gameCtx.fillStyle = '#ff6600';
        gameCtx.beginPath();
        gameCtx.moveTo(sx - radius * 0.55, sy - radius * 0.4);
        gameCtx.lineTo(sx - radius * 0.35, sy - radius * 1.0);
        gameCtx.lineTo(sx - radius * 0.1, sy - radius * 0.55);
        gameCtx.closePath();
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.moveTo(sx + radius * 0.55, sy - radius * 0.4);
        gameCtx.lineTo(sx + radius * 0.35, sy - radius * 1.0);
        gameCtx.lineTo(sx + radius * 0.1, sy - radius * 0.55);
        gameCtx.closePath();
        gameCtx.fill();
        // Eyes — angry slits
        gameCtx.fillStyle = '#ff4400';
        gameCtx.beginPath();
        gameCtx.ellipse(sx - 3, sy - 1, 2, 1, 0, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.ellipse(sx + 3, sy - 1, 2, 1, 0, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'johndoe') {
        // John Doe: Circular Obelisk of Enlightenment — black circle with red eye
        gameCtx.fillStyle = isDying ? '#8b0000' : '#000';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        // Subtle dark outline
        gameCtx.strokeStyle = '#222';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.stroke();
        // Pulsing red eye
        const enPulse = 0.5 + 0.5 * Math.sin(Date.now() * 0.004);
        gameCtx.fillStyle = `rgba(255, 0, 0, ${0.7 + enPulse * 0.3})`;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - 1, 2.5, 0, Math.PI * 2);
        gameCtx.fill();
        // Red eye glow
        gameCtx.fillStyle = `rgba(255, 0, 0, ${0.1 + enPulse * 0.15})`;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - 1, 5, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'coolkidd') {
        // c00lkidd: Blood-red circle with black dot eyes and wide smile
        gameCtx.fillStyle = isDying ? '#8b0000' : '#cc0000';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = '#990000';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.stroke();
        // Black dot eyes
        gameCtx.fillStyle = '#000';
        gameCtx.beginPath();
        gameCtx.arc(sx - 3, sy - 2, 1.8, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + 3, sy - 2, 1.8, 0, Math.PI * 2);
        gameCtx.fill();
        // Wide smile
        gameCtx.strokeStyle = '#000';
        gameCtx.lineWidth = 1.5;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy + 1, radius * 0.5, 0.15, Math.PI - 0.15);
        gameCtx.stroke();
      } else if (p.summonType === 'bowler') {
        // Bowler: green circle with bowling ball look
        gameCtx.fillStyle = isDying ? '#8b0000' : '#228b22';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = '#145214';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.stroke();
        // Three bowling ball dots
        gameCtx.fillStyle = '#0a3a0a';
        gameCtx.beginPath();
        gameCtx.arc(sx - 2, sy - 3, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + 2, sy - 3, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - 0.5, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'crab') {
        // Crab: aqua blue circle with crab claw icons
        gameCtx.fillStyle = isDying ? '#8b0000' : '#00ced1';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 0.85, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#600' : '#008b8b';
        gameCtx.lineWidth = 1.5;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 0.85, 0, Math.PI * 2);
        gameCtx.stroke();
        // Left crab claw
        gameCtx.strokeStyle = isDying ? '#600' : '#008b8b';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx - radius * 1.05, sy, radius * 0.35, -0.7, 0.7);
        gameCtx.stroke();
        gameCtx.beginPath();
        gameCtx.arc(sx - radius * 1.05, sy - radius * 0.15, radius * 0.2, -1.2, -0.1);
        gameCtx.stroke();
        gameCtx.beginPath();
        gameCtx.arc(sx - radius * 1.05, sy + radius * 0.15, radius * 0.2, 0.1, 1.2);
        gameCtx.stroke();
        // Right crab claw
        gameCtx.beginPath();
        gameCtx.arc(sx + radius * 1.05, sy, radius * 0.35, Math.PI - 0.7, Math.PI + 0.7);
        gameCtx.stroke();
        gameCtx.beginPath();
        gameCtx.arc(sx + radius * 1.05, sy - radius * 0.15, radius * 0.2, Math.PI + 0.1, Math.PI + 1.2);
        gameCtx.stroke();
        gameCtx.beginPath();
        gameCtx.arc(sx + radius * 1.05, sy + radius * 0.15, radius * 0.2, Math.PI - 1.2, Math.PI - 0.1);
        gameCtx.stroke();
        // Small dot eyes
        gameCtx.fillStyle = '#000';
        gameCtx.beginPath();
        gameCtx.arc(sx - 2, sy - radius * 0.35, 1.2, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + 2, sy - radius * 0.35, 1.2, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'backrooms-chaser') {
        // Backrooms chaser: yellow-brown menacing figure
        const brPulse = 0.5 + 0.5 * Math.sin(Date.now() * 0.006);
        gameCtx.fillStyle = isDying ? '#8b0000' : '#8b8000';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 1.1, 0, Math.PI * 2);
        gameCtx.fill();
        // Distortion glow
        gameCtx.strokeStyle = `rgba(139, 128, 0, ${0.4 + brPulse * 0.4})`;
        gameCtx.lineWidth = 3;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 1.3, 0, Math.PI * 2);
        gameCtx.stroke();
        // Dark hollow eyes
        gameCtx.fillStyle = '#000';
        gameCtx.beginPath();
        gameCtx.arc(sx - 3, sy - 2, 2, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + 3, sy - 2, 2, 0, Math.PI * 2);
        gameCtx.fill();
        // Distorted mouth
        gameCtx.strokeStyle = '#000';
        gameCtx.lineWidth = 1.5;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy + 3, 4, 0.3, Math.PI - 0.3);
        gameCtx.stroke();
      } else if (p.summonType === 'alternate') {
        // Alternate: looks like the target player but with a dark glitch overlay
        gameCtx.fillStyle = isDying ? '#8b0000' : p.color;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        // Dark purple distortion overlay
        const altPulse = 0.5 + 0.5 * Math.sin(Date.now() * 0.005);
        gameCtx.fillStyle = `rgba(50, 0, 80, ${0.2 + altPulse * 0.15})`;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        // Glitchy edge
        gameCtx.strokeStyle = `rgba(106, 13, 173, ${0.5 + altPulse * 0.3})`;
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 1, 0, Math.PI * 2);
        gameCtx.stroke();
      } else if (p.summonType === 'room') {
        // Room (Boisvert): black circle with a wide black triangle on top
        gameCtx.fillStyle = isDying ? '#8b0000' : '#000';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        // Wide triangle on head (party hat shape)
        gameCtx.fillStyle = isDying ? '#8b0000' : '#000';
        gameCtx.beginPath();
        gameCtx.moveTo(sx, sy - radius * 1.8);
        gameCtx.lineTo(sx - radius * 1.0, sy - radius * 0.3);
        gameCtx.lineTo(sx + radius * 1.0, sy - radius * 0.3);
        gameCtx.closePath();
        gameCtx.fill();
        // Subtle dark outline
        gameCtx.strokeStyle = '#333';
        gameCtx.lineWidth = 1.5;
        gameCtx.stroke();
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.stroke();
      } else if (p.summonType === 'destructive-unicorn') {
        // Extremely Destructive Unicorn: red circle with horn and fire glow
        const uniPulse = 0.5 + 0.5 * Math.sin(Date.now() * 0.008);
        gameCtx.fillStyle = isDying ? '#8b0000' : '#ff2200';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        // Pulsing danger glow
        gameCtx.strokeStyle = `rgba(255, 100, 0, ${0.5 + uniPulse * 0.5})`;
        gameCtx.lineWidth = 3;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 2, 0, Math.PI * 2);
        gameCtx.stroke();
        // Horn (golden triangle on top)
        gameCtx.fillStyle = '#ffd700';
        gameCtx.beginPath();
        gameCtx.moveTo(sx, sy - radius * 2.0);
        gameCtx.lineTo(sx - radius * 0.25, sy - radius * 0.6);
        gameCtx.lineTo(sx + radius * 0.25, sy - radius * 0.6);
        gameCtx.closePath();
        gameCtx.fill();
        // Eyes — white dots
        gameCtx.fillStyle = '#fff';
        gameCtx.beginPath();
        gameCtx.arc(sx - 3, sy - 2, 2, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + 3, sy - 2, 2, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'queenbee-unicorn') {
        // Queen Bee Unicorn: gold circle with crown and horn
        const qbPulse = 0.5 + 0.5 * Math.sin(Date.now() * 0.005);
        gameCtx.fillStyle = isDying ? '#8b0000' : '#ffd700';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        // Royal glow
        gameCtx.strokeStyle = `rgba(255, 215, 0, ${0.4 + qbPulse * 0.4})`;
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 2, 0, Math.PI * 2);
        gameCtx.stroke();
        // Horn
        gameCtx.fillStyle = '#fff';
        gameCtx.beginPath();
        gameCtx.moveTo(sx, sy - radius * 2.0);
        gameCtx.lineTo(sx - radius * 0.2, sy - radius * 0.6);
        gameCtx.lineTo(sx + radius * 0.2, sy - radius * 0.6);
        gameCtx.closePath();
        gameCtx.fill();
        // Crown points on top
        gameCtx.fillStyle = '#ff8c00';
        const crownY = sy - radius * 0.5;
        for (let ci = -1; ci <= 1; ci++) {
          gameCtx.beginPath();
          gameCtx.moveTo(sx + ci * radius * 0.4, crownY - radius * 0.6);
          gameCtx.lineTo(sx + ci * radius * 0.4 - 2, crownY);
          gameCtx.lineTo(sx + ci * radius * 0.4 + 2, crownY);
          gameCtx.closePath();
          gameCtx.fill();
        }
        // Eyes
        gameCtx.fillStyle = '#000';
        gameCtx.beginPath();
        gameCtx.arc(sx - 3, sy - 1, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + 3, sy - 1, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'seductive-unicorn') {
        // Seductive Unicorn: pink circle with horn and hearts
        const sedPulse = 0.5 + 0.5 * Math.sin(Date.now() * 0.006);
        gameCtx.fillStyle = isDying ? '#8b0000' : '#ff69b4';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        // Pink glow
        gameCtx.strokeStyle = `rgba(255, 105, 180, ${0.4 + sedPulse * 0.4})`;
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 2, 0, Math.PI * 2);
        gameCtx.stroke();
        // Horn (white)
        gameCtx.fillStyle = '#fff';
        gameCtx.beginPath();
        gameCtx.moveTo(sx, sy - radius * 2.0);
        gameCtx.lineTo(sx - radius * 0.2, sy - radius * 0.6);
        gameCtx.lineTo(sx + radius * 0.2, sy - radius * 0.6);
        gameCtx.closePath();
        gameCtx.fill();
        // Heart shape near top
        gameCtx.fillStyle = '#ff1493';
        gameCtx.beginPath();
        gameCtx.arc(sx - 2, sy - radius * 1.2, 2, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + 2, sy - radius * 1.2, 2, 0, Math.PI * 2);
        gameCtx.fill();
        // Eyes
        gameCtx.fillStyle = '#fff';
        gameCtx.beginPath();
        gameCtx.arc(sx - 3, sy - 1, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + 3, sy - 1, 1.5, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'napoleon-cannon') {
        // ── Napoleon Cannon: wheeled cannon render ──
        const cW = radius * 2.2;
        const cH = radius * 1.2;
        // Barrel
        gameCtx.fillStyle = isDying ? '#8b0000' : '#444';
        gameCtx.beginPath();
        gameCtx.moveTo(sx - cW * 0.1, sy - cH * 0.35);
        gameCtx.lineTo(sx + cW * 0.6, sy - cH * 0.2);
        gameCtx.lineTo(sx + cW * 0.65, sy - cH * 0.05);
        gameCtx.lineTo(sx + cW * 0.6, sy + cH * 0.1);
        gameCtx.lineTo(sx - cW * 0.1, sy + cH * 0.05);
        gameCtx.closePath();
        gameCtx.fill();
        // Barrel muzzle ring
        gameCtx.strokeStyle = '#888';
        gameCtx.lineWidth = 1.5;
        gameCtx.beginPath();
        gameCtx.arc(sx + cW * 0.62, sy - cH * 0.05, cH * 0.18, 0, Math.PI * 2);
        gameCtx.stroke();
        // Carriage body
        gameCtx.fillStyle = isDying ? '#600' : '#5c3a1e';
        gameCtx.fillRect(sx - cW * 0.3, sy - cH * 0.1, cW * 0.4, cH * 0.5);
        // Left wheel
        gameCtx.strokeStyle = '#333';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx - cW * 0.2, sy + cH * 0.5, cH * 0.3, 0, Math.PI * 2);
        gameCtx.stroke();
        // Wheel spokes
        for (let i = 0; i < 4; i++) {
          const a = (i / 4) * Math.PI * 2;
          gameCtx.beginPath();
          gameCtx.moveTo(sx - cW * 0.2, sy + cH * 0.5);
          gameCtx.lineTo(sx - cW * 0.2 + Math.cos(a) * cH * 0.3, sy + cH * 0.5 + Math.sin(a) * cH * 0.3);
          gameCtx.stroke();
        }
        // Right wheel
        gameCtx.beginPath();
        gameCtx.arc(sx + cW * 0.05, sy + cH * 0.5, cH * 0.3, 0, Math.PI * 2);
        gameCtx.stroke();
        for (let i = 0; i < 4; i++) {
          const a = (i / 4) * Math.PI * 2;
          gameCtx.beginPath();
          gameCtx.moveTo(sx + cW * 0.05, sy + cH * 0.5);
          gameCtx.lineTo(sx + cW * 0.05 + Math.cos(a) * cH * 0.3, sy + cH * 0.5 + Math.sin(a) * cH * 0.3);
          gameCtx.stroke();
        }
        // HP bar above
        const cHpFrac = Math.max(0, p.hp / p.maxHp);
        gameCtx.fillStyle = '#600';
        gameCtx.fillRect(sx - cW * 0.4, sy - cH * 0.8, cW * 0.8, 3);
        gameCtx.fillStyle = '#0f0';
        gameCtx.fillRect(sx - cW * 0.4, sy - cH * 0.8, cW * 0.8 * cHpFrac, 3);
      } else if (p.summonType === 'napoleon-infantry') {
        // ── Napoleon Infantry: small musketeer soldier ──
        gameCtx.fillStyle = isDying ? '#8b0000' : '#1a3a6b';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 0.8, 0, Math.PI * 2);
        gameCtx.fill();
        // Shako hat (tall cylindrical)
        gameCtx.fillStyle = '#111';
        gameCtx.fillRect(sx - radius * 0.45, sy - radius * 1.8, radius * 0.9, radius * 1.0);
        // Hat plume (red)
        gameCtx.fillStyle = '#cc0000';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - radius * 1.85, radius * 0.25, 0, Math.PI * 2);
        gameCtx.fill();
        // Musket (diagonal line)
        gameCtx.strokeStyle = '#5c3a1e';
        gameCtx.lineWidth = 1.5;
        gameCtx.beginPath();
        gameCtx.moveTo(sx + radius * 0.3, sy - radius * 0.2);
        gameCtx.lineTo(sx + radius * 1.5, sy - radius * 1.2);
        gameCtx.stroke();
        // Bayonet tip
        gameCtx.strokeStyle = '#aaa';
        gameCtx.lineWidth = 1;
        gameCtx.beginPath();
        gameCtx.moveTo(sx + radius * 1.5, sy - radius * 1.2);
        gameCtx.lineTo(sx + radius * 1.7, sy - radius * 1.5);
        gameCtx.stroke();
        // White cross belt
        gameCtx.strokeStyle = '#ddd';
        gameCtx.lineWidth = 1;
        gameCtx.beginPath();
        gameCtx.moveTo(sx - radius * 0.5, sy - radius * 0.4);
        gameCtx.lineTo(sx + radius * 0.5, sy + radius * 0.4);
        gameCtx.moveTo(sx + radius * 0.5, sy - radius * 0.4);
        gameCtx.lineTo(sx - radius * 0.5, sy + radius * 0.4);
        gameCtx.stroke();
      } else if (p.summonType === 'napoleon-wall') {
        // ── Defensive Tactics Wall: 2x2 tile outline (gold dashed border, no fill) ──
        const ws = (p.wallSize || 2) * GAME_TILE;
        const wx = sx - ws / 2;
        const wy = sy - ws / 2;
        gameCtx.strokeStyle = isDying ? '#8b0000' : '#d4af37';
        gameCtx.lineWidth = 2.5;
        gameCtx.setLineDash([6, 4]);
        gameCtx.strokeRect(wx, wy, ws, ws);
        gameCtx.setLineDash([]);
        // Corner decorations (fleur-de-lis style dots)
        gameCtx.fillStyle = '#d4af37';
        const corners = [[wx, wy], [wx + ws, wy], [wx, wy + ws], [wx + ws, wy + ws]];
        for (const [cx, cy] of corners) {
          gameCtx.beginPath();
          gameCtx.arc(cx, cy, 3, 0, Math.PI * 2);
          gameCtx.fill();
        }
        // "Defended" text above
        gameCtx.fillStyle = '#d4af37';
        gameCtx.font = 'bold 8px sans-serif';
        gameCtx.textAlign = 'center';
        gameCtx.fillText('⚜', sx, wy - 4);
        // Timer indicator (wall is invincible, shows remaining seconds)
        if (p.wallTimer !== undefined) {
          const tSec = Math.ceil(p.wallTimer);
          const tFrac = Math.max(0, p.wallTimer / 30);
          gameCtx.fillStyle = '#333';
          gameCtx.fillRect(wx, wy - 10, ws, 3);
          gameCtx.fillStyle = '#d4af37';
          gameCtx.fillRect(wx, wy - 10, ws * tFrac, 3);
          gameCtx.fillStyle = '#d4af37';
          gameCtx.font = 'bold 7px sans-serif';
          gameCtx.textAlign = 'center';
          gameCtx.fillText(tSec + 's', sx, wy - 13);
        }
      } else if (p.summonType === 'dnd-orc') {
        // ── D&D Orc: green-brown circle with tusks + axe ──
        gameCtx.fillStyle = isDying ? '#8b0000' : '#4a6b2a';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 0.9, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#500' : '#2d4a1a';
        gameCtx.lineWidth = 1.5;
        gameCtx.stroke();
        // Tusks (two small white triangles at bottom)
        gameCtx.fillStyle = '#eee';
        gameCtx.beginPath();
        gameCtx.moveTo(sx - radius * 0.3, sy + radius * 0.3);
        gameCtx.lineTo(sx - radius * 0.15, sy + radius * 0.9);
        gameCtx.lineTo(sx - radius * 0.05, sy + radius * 0.3);
        gameCtx.closePath();
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.moveTo(sx + radius * 0.3, sy + radius * 0.3);
        gameCtx.lineTo(sx + radius * 0.15, sy + radius * 0.9);
        gameCtx.lineTo(sx + radius * 0.05, sy + radius * 0.3);
        gameCtx.closePath();
        gameCtx.fill();
        // Angry eyes (red dots)
        gameCtx.fillStyle = '#ff3333';
        gameCtx.beginPath();
        gameCtx.arc(sx - radius * 0.25, sy - radius * 0.15, radius * 0.15, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + radius * 0.25, sy - radius * 0.15, radius * 0.15, 0, Math.PI * 2);
        gameCtx.fill();
        // Crude axe on top
        gameCtx.strokeStyle = '#5c3a1e';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.moveTo(sx, sy - radius * 0.5);
        gameCtx.lineTo(sx, sy - radius * 1.4);
        gameCtx.stroke();
        gameCtx.fillStyle = '#888';
        gameCtx.beginPath();
        gameCtx.moveTo(sx - radius * 0.35, sy - radius * 1.4);
        gameCtx.lineTo(sx + radius * 0.35, sy - radius * 1.4);
        gameCtx.lineTo(sx + radius * 0.2, sy - radius * 1.05);
        gameCtx.lineTo(sx - radius * 0.2, sy - radius * 1.05);
        gameCtx.closePath();
        gameCtx.fill();
      } else if (p.summonType === 'dnd-zombie') {
        // ── D&D Zombie: sickly green circle with stagger lines ──
        gameCtx.fillStyle = isDying ? '#8b0000' : '#3d5a1e';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 0.85, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#500' : '#2a3d10';
        gameCtx.lineWidth = 1.5;
        gameCtx.stroke();
        // Ragged arms (short lines out to sides)
        gameCtx.strokeStyle = '#4a6b2a';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.moveTo(sx - radius * 0.7, sy);
        gameCtx.lineTo(sx - radius * 1.3, sy + radius * 0.4);
        gameCtx.stroke();
        gameCtx.beginPath();
        gameCtx.moveTo(sx + radius * 0.7, sy);
        gameCtx.lineTo(sx + radius * 1.3, sy + radius * 0.4);
        gameCtx.stroke();
        // Dead eyes (X marks)
        gameCtx.strokeStyle = '#111';
        gameCtx.lineWidth = 1.5;
        const eyeOff = radius * 0.25;
        // Left eye X
        gameCtx.beginPath();
        gameCtx.moveTo(sx - eyeOff - 2, sy - radius * 0.15 - 2);
        gameCtx.lineTo(sx - eyeOff + 2, sy - radius * 0.15 + 2);
        gameCtx.moveTo(sx - eyeOff + 2, sy - radius * 0.15 - 2);
        gameCtx.lineTo(sx - eyeOff - 2, sy - radius * 0.15 + 2);
        gameCtx.stroke();
        // Right eye X
        gameCtx.beginPath();
        gameCtx.moveTo(sx + eyeOff - 2, sy - radius * 0.15 - 2);
        gameCtx.lineTo(sx + eyeOff + 2, sy - radius * 0.15 + 2);
        gameCtx.moveTo(sx + eyeOff + 2, sy - radius * 0.15 - 2);
        gameCtx.lineTo(sx + eyeOff - 2, sy - radius * 0.15 + 2);
        gameCtx.stroke();
      } else if (p.summonType === 'dnd-sidekick') {
        // ── D&D Sidekick: looks like the owner's race dot but with a glow border ──
        const skRace = p.dndRace || 'human';
        const baseColor = isDying ? '#8b0000' : (skRace === 'elf' ? '#228b22' : skRace === 'dwarf' ? '#d2691e' : '#4169e1');
        // Glow ring
        gameCtx.strokeStyle = '#ffd700';
        gameCtx.lineWidth = 3;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 1.1, 0, Math.PI * 2);
        gameCtx.stroke();
        // Base circle
        gameCtx.fillStyle = baseColor;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#500' : '#222';
        gameCtx.lineWidth = 1.5;
        gameCtx.stroke();
        // Race-specific weapon (simplified)
        if (skRace === 'elf') {
          // Small bow
          gameCtx.strokeStyle = '#654321';
          gameCtx.lineWidth = 2;
          gameCtx.beginPath();
          gameCtx.arc(sx + radius * 0.8, sy, radius * 0.5, -Math.PI * 0.4, Math.PI * 0.4);
          gameCtx.stroke();
        } else if (skRace === 'dwarf') {
          // Small axe
          gameCtx.strokeStyle = '#5c3a1e';
          gameCtx.lineWidth = 2;
          gameCtx.beginPath();
          gameCtx.moveTo(sx + radius * 0.4, sy - radius * 0.1);
          gameCtx.lineTo(sx + radius * 1.1, sy - radius * 0.1);
          gameCtx.stroke();
          gameCtx.fillStyle = '#888';
          gameCtx.beginPath();
          gameCtx.arc(sx + radius * 1.1, sy - radius * 0.1, radius * 0.25, 0, Math.PI * 2);
          gameCtx.fill();
        } else {
          // Small sword
          gameCtx.strokeStyle = '#ccc';
          gameCtx.lineWidth = 2;
          gameCtx.beginPath();
          gameCtx.moveTo(sx + radius * 0.4, sy);
          gameCtx.lineTo(sx + radius * 1.2, sy);
          gameCtx.stroke();
        }
        // "SK" label
        gameCtx.fillStyle = '#fff';
        gameCtx.font = 'bold ' + Math.max(8, radius * 0.6) + 'px monospace';
        gameCtx.textAlign = 'center';
        gameCtx.textBaseline = 'middle';
        gameCtx.fillText('SK', sx, sy);
      } else if (p.summonType === 'dragon-ochre') {
        // ── Yellow Ochre: 3x3 golden jelly blob ──
        const jR = radius * 3.0; // bigger than normal (3x3)
        gameCtx.fillStyle = isDying ? '#8b0000' : '#c8a832';
        gameCtx.beginPath();
        // Blobby shape using overlapping circles
        gameCtx.arc(sx - jR * 0.3, sy - jR * 0.2, jR * 0.7, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + jR * 0.3, sy - jR * 0.1, jR * 0.65, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx, sy + jR * 0.3, jR * 0.6, 0, Math.PI * 2);
        gameCtx.fill();
        // Glossy highlight
        gameCtx.fillStyle = 'rgba(255, 255, 200, 0.3)';
        gameCtx.beginPath();
        gameCtx.arc(sx - jR * 0.15, sy - jR * 0.35, jR * 0.25, 0, Math.PI * 2);
        gameCtx.fill();
        // Eyes (simple dark dots)
        gameCtx.fillStyle = '#333';
        gameCtx.beginPath();
        gameCtx.arc(sx - jR * 0.2, sy - jR * 0.1, jR * 0.08, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + jR * 0.15, sy - jR * 0.1, jR * 0.08, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (p.summonType === 'dragon-lich') {
        // ── Lich: dark purple robed figure with green glow ──
        gameCtx.fillStyle = isDying ? '#8b0000' : '#3a0066';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 0.9, 0, Math.PI * 2);
        gameCtx.fill();
        // Purple robe outline
        gameCtx.strokeStyle = isDying ? '#500' : '#6a0dad';
        gameCtx.lineWidth = 2;
        gameCtx.stroke();
        // Hood (darker top arc)
        gameCtx.fillStyle = '#200040';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - radius * 0.2, radius * 0.6, Math.PI, 0);
        gameCtx.closePath();
        gameCtx.fill();
        // Glowing green eyes
        gameCtx.fillStyle = '#00ff44';
        gameCtx.beginPath();
        gameCtx.arc(sx - radius * 0.2, sy - radius * 0.2, radius * 0.12, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.beginPath();
        gameCtx.arc(sx + radius * 0.2, sy - radius * 0.2, radius * 0.12, 0, Math.PI * 2);
        gameCtx.fill();
        // Staff
        gameCtx.strokeStyle = '#8b6508';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.moveTo(sx + radius * 0.5, sy + radius * 0.5);
        gameCtx.lineTo(sx + radius * 0.3, sy - radius * 1.2);
        gameCtx.stroke();
        // Staff orb
        gameCtx.fillStyle = '#aa00ff';
        gameCtx.beginPath();
        gameCtx.arc(sx + radius * 0.3, sy - radius * 1.2, radius * 0.15, 0, Math.PI * 2);
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
    } else if (p.fighter && p.fighter.id === 'noli' && !p.isSummon) {
      // ── Noli: Purple version of 1X1X1X1 skin ──
      gameCtx.fillStyle = isDying ? '#8b0000' : '#111';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
      gameCtx.fill();
      // Glitchy neon purple edge fragments
      gameCtx.strokeStyle = '#a020f0';
      gameCtx.lineWidth = 2;
      const nSegments = 8;
      for (let i = 0; i < nSegments; i++) {
        const a1 = (i / nSegments) * Math.PI * 2;
        const a2 = ((i + 0.6) / nSegments) * Math.PI * 2;
        const jitter = ((i * 7 + 3) % 5) * 0.5 - 1;
        const rr = radius + jitter;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, rr, a1, a2);
        gameCtx.stroke();
      }
      // Purple glitch streaks
      gameCtx.strokeStyle = '#a020f0';
      gameCtx.lineWidth = 1.2;
      gameCtx.globalAlpha = 0.7;
      gameCtx.beginPath();
      gameCtx.moveTo(sx - radius * 0.6, sy - radius * 0.3);
      gameCtx.lineTo(sx - radius * 0.2, sy - radius * 0.1);
      gameCtx.moveTo(sx + radius * 0.1, sy + radius * 0.2);
      gameCtx.lineTo(sx + radius * 0.6, sy + radius * 0.1);
      gameCtx.moveTo(sx - radius * 0.3, sy + radius * 0.4);
      gameCtx.lineTo(sx + radius * 0.1, sy + radius * 0.55);
      gameCtx.stroke();
      gameCtx.globalAlpha = 1.0;
      // Purple inner glow
      gameCtx.fillStyle = 'rgba(160, 32, 240, 0.08)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius * 0.8, 0, Math.PI * 2);
      gameCtx.fill();
      // Purple eye
      gameCtx.fillStyle = 'rgba(160, 32, 240, 0.25)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy - radius * 0.15, 6, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.fillStyle = '#1a0030';
      gameCtx.beginPath();
      gameCtx.ellipse(sx, sy - radius * 0.15, 5, 3, 0, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.fillStyle = '#a020f0';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy - radius * 0.15, 2.5, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.fillStyle = '#000';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy - radius * 0.15, 1, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.fillStyle = 'rgba(200, 130, 255, 0.8)';
      gameCtx.beginPath();
      gameCtx.arc(sx + 1, sy - radius * 0.15 - 1, 0.7, 0, Math.PI * 2);
      gameCtx.fill();
      // Clone indicator
      if (p.noliCloneId) {
        gameCtx.fillStyle = '#a020f0';
        gameCtx.beginPath();
        gameCtx.arc(sx + radius + 3, sy - radius - 3, 3, 0, Math.PI * 2);
        gameCtx.fill();
      }
    } else if (p.fighter && p.fighter.id === 'moderator') {
      // Moderator: the dot IS a terminal window
      const tw = radius * 2;
      const th = radius * 2;
      const txOff = sx - tw / 2;
      const tyOff = sy - th / 2;
      const cr = radius * 0.25;
      // Terminal background (rounded rect)
      gameCtx.fillStyle = isDying ? '#3a0000' : '#0c0c0c';
      gameCtx.beginPath();
      gameCtx.moveTo(txOff + cr, tyOff); gameCtx.lineTo(txOff + tw - cr, tyOff);
      gameCtx.quadraticCurveTo(txOff + tw, tyOff, txOff + tw, tyOff + cr);
      gameCtx.lineTo(txOff + tw, tyOff + th - cr);
      gameCtx.quadraticCurveTo(txOff + tw, tyOff + th, txOff + tw - cr, tyOff + th);
      gameCtx.lineTo(txOff + cr, tyOff + th);
      gameCtx.quadraticCurveTo(txOff, tyOff + th, txOff, tyOff + th - cr);
      gameCtx.lineTo(txOff, tyOff + cr);
      gameCtx.quadraticCurveTo(txOff, tyOff, txOff + cr, tyOff);
      gameCtx.closePath();
      gameCtx.fill();
      // Title bar
      const tbH = th * 0.2;
      gameCtx.fillStyle = isDying ? '#5a0000' : '#2d2d2d';
      gameCtx.beginPath();
      gameCtx.moveTo(txOff + cr, tyOff); gameCtx.lineTo(txOff + tw - cr, tyOff);
      gameCtx.quadraticCurveTo(txOff + tw, tyOff, txOff + tw, tyOff + cr);
      gameCtx.lineTo(txOff + tw, tyOff + tbH);
      gameCtx.lineTo(txOff, tyOff + tbH);
      gameCtx.lineTo(txOff, tyOff + cr);
      gameCtx.quadraticCurveTo(txOff, tyOff, txOff + cr, tyOff);
      gameCtx.closePath();
      gameCtx.fill();
      // Title bar dots (red/yellow/green)
      const dotSz = Math.max(1.2, radius * 0.12);
      const dotGap = dotSz * 2.8;
      const dotYPos = tyOff + tbH * 0.5;
      gameCtx.fillStyle = '#ff5f56'; gameCtx.beginPath(); gameCtx.arc(txOff + dotGap, dotYPos, dotSz, 0, Math.PI * 2); gameCtx.fill();
      gameCtx.fillStyle = '#ffbd2e'; gameCtx.beginPath(); gameCtx.arc(txOff + dotGap * 2, dotYPos, dotSz, 0, Math.PI * 2); gameCtx.fill();
      gameCtx.fillStyle = '#27c93f'; gameCtx.beginPath(); gameCtx.arc(txOff + dotGap * 3, dotYPos, dotSz, 0, Math.PI * 2); gameCtx.fill();
      // Green terminal text
      if (!isDying) {
        gameCtx.fillStyle = '#00ff41';
        const fontSize = Math.max(5, radius * 0.55);
        gameCtx.font = 'bold ' + fontSize + 'px monospace';
        gameCtx.textAlign = 'left';
        gameCtx.textBaseline = 'middle';
        gameCtx.fillText('> mod_', txOff + 2, sy + th * 0.12);
      }
      // Green border glow
      gameCtx.strokeStyle = isDying ? '#8b0000' : '#00ff41';
      gameCtx.lineWidth = 1.2;
      gameCtx.beginPath();
      gameCtx.moveTo(txOff + cr, tyOff); gameCtx.lineTo(txOff + tw - cr, tyOff);
      gameCtx.quadraticCurveTo(txOff + tw, tyOff, txOff + tw, tyOff + cr);
      gameCtx.lineTo(txOff + tw, tyOff + th - cr);
      gameCtx.quadraticCurveTo(txOff + tw, tyOff + th, txOff + tw - cr, tyOff + th);
      gameCtx.lineTo(txOff + cr, tyOff + th);
      gameCtx.quadraticCurveTo(txOff, tyOff + th, txOff, tyOff + th - cr);
      gameCtx.lineTo(txOff, tyOff + cr);
      gameCtx.quadraticCurveTo(txOff, tyOff, txOff + cr, tyOff);
      gameCtx.closePath();
      gameCtx.stroke();
    } else if (p.fighter && p.fighter.id === 'dnd') {
      // D&D Campaigner: race-dependent dot with weapon + shield
      const race = p.dndRace || 'human';

      if (race === 'elf') {
        // ── Elf: green dot with pointy ears, sword + shield ──
        const bodyCol = isDying ? '#8b0000' : '#2ecc71';
        // Body circle
        gameCtx.fillStyle = bodyCol;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#500' : 'rgba(0,0,0,0.4)';
        gameCtx.lineWidth = 1.5;
        gameCtx.stroke();
        // Elf ears (two pointed triangles)
        gameCtx.fillStyle = isDying ? '#a00' : '#27ae60';
        // Left ear
        gameCtx.beginPath();
        gameCtx.moveTo(sx - radius * 0.7, sy - radius * 0.5);
        gameCtx.lineTo(sx - radius * 1.4, sy - radius * 1.2);
        gameCtx.lineTo(sx - radius * 0.3, sy - radius * 0.8);
        gameCtx.closePath();
        gameCtx.fill();
        // Right ear
        gameCtx.beginPath();
        gameCtx.moveTo(sx + radius * 0.7, sy - radius * 0.5);
        gameCtx.lineTo(sx + radius * 1.4, sy - radius * 1.2);
        gameCtx.lineTo(sx + radius * 0.3, sy - radius * 0.8);
        gameCtx.closePath();
        gameCtx.fill();
        // Shield (left side)
        const shX = sx - radius * 0.9;
        const shY = sy + radius * 0.1;
        const shW = radius * 0.7;
        const shH = radius * 0.9;
        gameCtx.fillStyle = isDying ? '#600' : '#1a7a3a';
        gameCtx.beginPath();
        gameCtx.moveTo(shX, shY - shH * 0.5);
        gameCtx.lineTo(shX + shW * 0.5, shY - shH * 0.5);
        gameCtx.lineTo(shX + shW * 0.5, shY + shH * 0.2);
        gameCtx.lineTo(shX + shW * 0.25, shY + shH * 0.5);
        gameCtx.lineTo(shX, shY + shH * 0.2);
        gameCtx.closePath();
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#400' : '#145a2a';
        gameCtx.lineWidth = 1;
        gameCtx.stroke();
        // Sword (right side, angled up-right)
        const swX = sx + radius * 0.6;
        const swY = sy - radius * 0.2;
        gameCtx.strokeStyle = isDying ? '#888' : '#c0c0c0';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.moveTo(swX, swY + radius * 0.5);
        gameCtx.lineTo(swX + radius * 0.3, swY - radius * 0.9);
        gameCtx.stroke();
        // Sword tip
        gameCtx.fillStyle = '#e0e0e0';
        gameCtx.beginPath();
        gameCtx.moveTo(swX + radius * 0.3, swY - radius * 0.9);
        gameCtx.lineTo(swX + radius * 0.35, swY - radius * 1.1);
        gameCtx.lineTo(swX + radius * 0.2, swY - radius * 0.85);
        gameCtx.closePath();
        gameCtx.fill();
        // Crossguard
        gameCtx.strokeStyle = isDying ? '#666' : '#d4af37';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.moveTo(swX - radius * 0.15, swY + radius * 0.1);
        gameCtx.lineTo(swX + radius * 0.45, swY + radius * 0.1);
        gameCtx.stroke();
      } else if (race === 'dwarf') {
        // ── Dwarf: orange dot with axe + shield ──
        const bodyCol = isDying ? '#8b0000' : '#e67e22';
        // Body circle (slightly smaller to look stocky)
        gameCtx.fillStyle = bodyCol;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#500' : 'rgba(0,0,0,0.4)';
        gameCtx.lineWidth = 1.5;
        gameCtx.stroke();
        // Beard (brown arc below)
        gameCtx.fillStyle = isDying ? '#600' : '#8b5e3c';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy + radius * 0.3, radius * 0.7, 0, Math.PI);
        gameCtx.fill();
        // Shield (left side — round/wide dwarven shield)
        const shX = sx - radius * 0.9;
        const shY = sy;
        const shR = radius * 0.55;
        gameCtx.fillStyle = isDying ? '#600' : '#b5651d';
        gameCtx.beginPath();
        gameCtx.arc(shX, shY, shR, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#400' : '#8b4513';
        gameCtx.lineWidth = 1.5;
        gameCtx.stroke();
        // Shield boss (center dot)
        gameCtx.fillStyle = isDying ? '#888' : '#d4af37';
        gameCtx.beginPath();
        gameCtx.arc(shX, shY, shR * 0.3, 0, Math.PI * 2);
        gameCtx.fill();
        // Axe (right side)
        const axX = sx + radius * 0.7;
        const axY = sy;
        // Axe handle
        gameCtx.strokeStyle = isDying ? '#555' : '#8b4513';
        gameCtx.lineWidth = 2.5;
        gameCtx.beginPath();
        gameCtx.moveTo(axX, axY + radius * 0.7);
        gameCtx.lineTo(axX, axY - radius * 0.9);
        gameCtx.stroke();
        // Axe head (two curved blades)
        gameCtx.fillStyle = isDying ? '#888' : '#aaa';
        gameCtx.beginPath();
        gameCtx.moveTo(axX, axY - radius * 0.9);
        gameCtx.quadraticCurveTo(axX + radius * 0.7, axY - radius * 0.7, axX + radius * 0.5, axY - radius * 0.3);
        gameCtx.lineTo(axX, axY - radius * 0.4);
        gameCtx.closePath();
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#666' : '#777';
        gameCtx.lineWidth = 1;
        gameCtx.stroke();
        // Second blade (left side of axe)
        gameCtx.fillStyle = isDying ? '#888' : '#aaa';
        gameCtx.beginPath();
        gameCtx.moveTo(axX, axY - radius * 0.9);
        gameCtx.quadraticCurveTo(axX - radius * 0.7, axY - radius * 0.7, axX - radius * 0.5, axY - radius * 0.3);
        gameCtx.lineTo(axX, axY - radius * 0.4);
        gameCtx.closePath();
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#666' : '#777';
        gameCtx.lineWidth = 1;
        gameCtx.stroke();
      } else {
        // ── Human: blue dot with sword + shield ──
        const bodyCol = isDying ? '#8b0000' : '#3498db';
        // Body circle
        gameCtx.fillStyle = bodyCol;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#500' : 'rgba(0,0,0,0.4)';
        gameCtx.lineWidth = 1.5;
        gameCtx.stroke();
        // Shield (left side — kite shield shape)
        const shX = sx - radius * 0.9;
        const shY = sy + radius * 0.1;
        const shW = radius * 0.7;
        const shH = radius * 1.0;
        gameCtx.fillStyle = isDying ? '#600' : '#2c3e80';
        gameCtx.beginPath();
        gameCtx.moveTo(shX, shY - shH * 0.5);
        gameCtx.lineTo(shX + shW * 0.5, shY - shH * 0.5);
        gameCtx.lineTo(shX + shW * 0.5, shY + shH * 0.15);
        gameCtx.lineTo(shX + shW * 0.25, shY + shH * 0.5);
        gameCtx.lineTo(shX, shY + shH * 0.15);
        gameCtx.closePath();
        gameCtx.fill();
        gameCtx.strokeStyle = isDying ? '#400' : '#1a2555';
        gameCtx.lineWidth = 1;
        gameCtx.stroke();
        // Shield cross emblem
        gameCtx.strokeStyle = isDying ? '#888' : '#d4af37';
        gameCtx.lineWidth = 1.5;
        gameCtx.beginPath();
        gameCtx.moveTo(shX + shW * 0.25, shY - shH * 0.3);
        gameCtx.lineTo(shX + shW * 0.25, shY + shH * 0.3);
        gameCtx.stroke();
        gameCtx.beginPath();
        gameCtx.moveTo(shX + shW * 0.05, shY - shH * 0.1);
        gameCtx.lineTo(shX + shW * 0.45, shY - shH * 0.1);
        gameCtx.stroke();
        // Sword (right side, angled up-right)
        const swX = sx + radius * 0.6;
        const swY = sy - radius * 0.2;
        gameCtx.strokeStyle = isDying ? '#888' : '#c0c0c0';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.moveTo(swX, swY + radius * 0.5);
        gameCtx.lineTo(swX + radius * 0.3, swY - radius * 0.9);
        gameCtx.stroke();
        // Sword tip
        gameCtx.fillStyle = '#e0e0e0';
        gameCtx.beginPath();
        gameCtx.moveTo(swX + radius * 0.3, swY - radius * 0.9);
        gameCtx.lineTo(swX + radius * 0.35, swY - radius * 1.1);
        gameCtx.lineTo(swX + radius * 0.2, swY - radius * 0.85);
        gameCtx.closePath();
        gameCtx.fill();
        // Crossguard
        gameCtx.strokeStyle = isDying ? '#666' : '#d4af37';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.moveTo(swX - radius * 0.15, swY + radius * 0.1);
        gameCtx.lineTo(swX + radius * 0.45, swY + radius * 0.1);
        gameCtx.stroke();
      }
      // GP indicator (gold text above)
      if (p.dndGP > 0) {
        gameCtx.fillStyle = '#ffd700';
        gameCtx.font = 'bold ' + Math.max(5, radius * 0.45) + 'px sans-serif';
        gameCtx.textAlign = 'center';
        gameCtx.textBaseline = 'bottom';
        gameCtx.fillText(p.dndGP + 'GP', sx, sy - radius - 2);
      }
      // D20 glow when active
      if (p.dndD20Active) {
        gameCtx.strokeStyle = '#ffd700';
        gameCtx.lineWidth = 2;
        gameCtx.setLineDash([3, 3]);
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 4, 0, Math.PI * 2);
        gameCtx.stroke();
        gameCtx.setLineDash([]);
      }
    } else if (p.fighter && p.fighter.id === 'dragon' && !p.isSummon) {
      // ── Dragon of Icespire: icy blue dragon dot ──
      // Base: dark icy blue circle
      gameCtx.fillStyle = isDying ? '#8b0000' : '#1a3a5c';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius, 0, Math.PI * 2);
      gameCtx.fill();
      // Icy crystalline edge
      gameCtx.strokeStyle = isDying ? '#500' : '#5bb8e8';
      gameCtx.lineWidth = 2.5;
      gameCtx.stroke();
      // Dragon wing shapes (left and right)
      if (!isDying) {
        gameCtx.fillStyle = 'rgba(91, 184, 232, 0.4)';
        // Left wing
        gameCtx.beginPath();
        gameCtx.moveTo(sx - radius * 0.7, sy - radius * 0.2);
        gameCtx.lineTo(sx - radius * 1.6, sy - radius * 0.8);
        gameCtx.lineTo(sx - radius * 1.3, sy + radius * 0.1);
        gameCtx.lineTo(sx - radius * 0.7, sy + radius * 0.3);
        gameCtx.closePath();
        gameCtx.fill();
        // Right wing
        gameCtx.beginPath();
        gameCtx.moveTo(sx + radius * 0.7, sy - radius * 0.2);
        gameCtx.lineTo(sx + radius * 1.6, sy - radius * 0.8);
        gameCtx.lineTo(sx + radius * 1.3, sy + radius * 0.1);
        gameCtx.lineTo(sx + radius * 0.7, sy + radius * 0.3);
        gameCtx.closePath();
        gameCtx.fill();
      }
      // Icy eyes
      gameCtx.fillStyle = '#00ddff';
      gameCtx.beginPath();
      gameCtx.arc(sx - radius * 0.25, sy - radius * 0.15, radius * 0.15, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.beginPath();
      gameCtx.arc(sx + radius * 0.25, sy - radius * 0.15, radius * 0.15, 0, Math.PI * 2);
      gameCtx.fill();
      // Tiny horns
      gameCtx.strokeStyle = '#7fafc4';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.moveTo(sx - radius * 0.35, sy - radius * 0.7);
      gameCtx.lineTo(sx - radius * 0.5, sy - radius * 1.2);
      gameCtx.stroke();
      gameCtx.beginPath();
      gameCtx.moveTo(sx + radius * 0.35, sy - radius * 0.7);
      gameCtx.lineTo(sx + radius * 0.5, sy - radius * 1.2);
      gameCtx.stroke();
      // Flying indicator
      if (p.dragonFlying) {
        gameCtx.strokeStyle = 'rgba(200, 240, 255, 0.6)';
        gameCtx.lineWidth = 2;
        gameCtx.setLineDash([4, 4]);
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 1.4, 0, Math.PI * 2);
        gameCtx.stroke();
        gameCtx.setLineDash([]);
      }
      // Roar glow
      if (p.dragonRoarActive) {
        gameCtx.strokeStyle = '#5b8fa8';
        gameCtx.lineWidth = 3;
        gameCtx.globalAlpha = 0.5 + Math.sin(Date.now() / 200) * 0.3;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 1.3, 0, Math.PI * 2);
        gameCtx.stroke();
        gameCtx.globalAlpha = 1;
      }
      // Beam charging indicator (aim moves slowly)
      if (p.dragonBeamCharging) {
        const chargeProgress = 1 - (p.dragonBeamChargeTimer / 3);
        gameCtx.strokeStyle = '#00ccff';
        gameCtx.lineWidth = 3;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius * 1.5, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * chargeProgress);
        gameCtx.stroke();
        // Show beam direction — long preview so player can see where it aims
        const bLen = GAME_TILE * 12;
        const bW = (p.fighter.abilities[2].beamWidth || 2) * GAME_TILE;
        gameCtx.strokeStyle = 'rgba(0, 204, 255, ' + (0.15 + 0.2 * chargeProgress) + ')';
        gameCtx.lineWidth = bW * (0.3 + 0.7 * chargeProgress);
        gameCtx.beginPath();
        gameCtx.moveTo(sx, sy);
        gameCtx.lineTo(sx + p.dragonBeamAimNx * bLen, sy + p.dragonBeamAimNy * bLen);
        gameCtx.stroke();
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
    } else if (p.fighter && p.fighter.id === 'cricket') {
      // Cricket: bat icon on the dot
      const batAngle = -Math.PI / 4;
      const batLen = radius * 1.4;
      const batBaseX = sx + Math.cos(batAngle) * radius * 0.3;
      const batBaseY = sy + Math.sin(batAngle) * radius * 0.3;
      const batTipX = batBaseX + Math.cos(batAngle) * batLen;
      const batTipY = batBaseY + Math.sin(batAngle) * batLen;
      // Handle
      gameCtx.strokeStyle = '#8b4513';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.moveTo(batBaseX, batBaseY);
      gameCtx.lineTo(batBaseX + Math.cos(batAngle) * batLen * 0.4, batBaseY + Math.sin(batAngle) * batLen * 0.4);
      gameCtx.stroke();
      // Blade (wider part)
      gameCtx.strokeStyle = '#c8a96e';
      gameCtx.lineWidth = 6;
      gameCtx.beginPath();
      gameCtx.moveTo(batBaseX + Math.cos(batAngle) * batLen * 0.4, batBaseY + Math.sin(batAngle) * batLen * 0.4);
      gameCtx.lineTo(batTipX, batTipY);
      gameCtx.stroke();
      // Gear Up indicator
      if (p.gearUpTimer > 0) {
        gameCtx.fillStyle = 'rgba(52, 152, 219, 0.3)';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 4, 0, Math.PI * 2);
        gameCtx.fill();
        // Helmet shape on top
        gameCtx.fillStyle = '#3498db';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy - radius * 0.5, radius * 0.5, Math.PI, 0);
        gameCtx.fill();
      }
    } else if (p.fighter && p.fighter.id === 'deer') {
      // Deer: dual antlers icon on the dot
      const antlerLen = radius * 1.2;
      // Left antler
      gameCtx.strokeStyle = '#8b6914';
      gameCtx.lineWidth = 2.5;
      gameCtx.beginPath();
      gameCtx.moveTo(sx - radius * 0.2, sy - radius * 0.3);
      gameCtx.lineTo(sx - radius * 0.5, sy - radius * 0.3 - antlerLen * 0.7);
      gameCtx.lineTo(sx - radius * 0.8, sy - radius * 0.3 - antlerLen);
      gameCtx.stroke();
      // Left antler branch
      gameCtx.beginPath();
      gameCtx.moveTo(sx - radius * 0.5, sy - radius * 0.3 - antlerLen * 0.5);
      gameCtx.lineTo(sx - radius * 0.9, sy - radius * 0.3 - antlerLen * 0.5);
      gameCtx.stroke();
      // Right antler
      gameCtx.beginPath();
      gameCtx.moveTo(sx + radius * 0.2, sy - radius * 0.3);
      gameCtx.lineTo(sx + radius * 0.5, sy - radius * 0.3 - antlerLen * 0.7);
      gameCtx.lineTo(sx + radius * 0.8, sy - radius * 0.3 - antlerLen);
      gameCtx.stroke();
      // Right antler branch
      gameCtx.beginPath();
      gameCtx.moveTo(sx + radius * 0.5, sy - radius * 0.3 - antlerLen * 0.5);
      gameCtx.lineTo(sx + radius * 0.9, sy - radius * 0.3 - antlerLen * 0.5);
      gameCtx.stroke();
      // Seer glow
      if (p.deerSeerTimer > 0) {
        gameCtx.fillStyle = 'rgba(221, 160, 221, 0.25)';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 5, 0, Math.PI * 2);
        gameCtx.fill();
      }
      // Fear speed lines
      if (p.deerFearTimer > 0) {
        gameCtx.strokeStyle = 'rgba(143, 188, 143, 0.6)';
        gameCtx.lineWidth = 1.5;
        for (let i = 0; i < 3; i++) {
          const a = (i / 3) * Math.PI * 2 + Date.now() * 0.003;
          gameCtx.beginPath();
          gameCtx.moveTo(sx + Math.cos(a) * (radius + 2), sy + Math.sin(a) * (radius + 2));
          gameCtx.lineTo(sx + Math.cos(a) * (radius + 8), sy + Math.sin(a) * (radius + 8));
          gameCtx.stroke();
        }
      }
      // Robot indicator
      if (p.deerRobotId) {
        gameCtx.fillStyle = '#708090';
        gameCtx.beginPath();
        gameCtx.arc(sx + radius + 3, sy - radius - 3, 3, 0, Math.PI * 2);
        gameCtx.fill();
      }
    } else if (p.fighter && p.fighter.id === 'explodingcat') {
      // Exploding Cat: cat ears on the dot + claw marks
      const earH = radius * 1.1;
      // Left ear
      gameCtx.fillStyle = isDying ? '#8b0000' : '#222';
      gameCtx.beginPath();
      gameCtx.moveTo(sx - radius * 0.7, sy - radius * 0.2);
      gameCtx.lineTo(sx - radius * 0.3, sy - radius * 0.2 - earH);
      gameCtx.lineTo(sx, sy - radius * 0.4);
      gameCtx.closePath();
      gameCtx.fill();
      // Right ear
      gameCtx.beginPath();
      gameCtx.moveTo(sx + radius * 0.7, sy - radius * 0.2);
      gameCtx.lineTo(sx + radius * 0.3, sy - radius * 0.2 - earH);
      gameCtx.lineTo(sx, sy - radius * 0.4);
      gameCtx.closePath();
      gameCtx.fill();
      // Inner ear pink
      gameCtx.fillStyle = '#ff69b4';
      gameCtx.beginPath();
      gameCtx.moveTo(sx - radius * 0.55, sy - radius * 0.3);
      gameCtx.lineTo(sx - radius * 0.35, sy - radius * 0.3 - earH * 0.6);
      gameCtx.lineTo(sx - radius * 0.1, sy - radius * 0.45);
      gameCtx.closePath();
      gameCtx.fill();
      gameCtx.beginPath();
      gameCtx.moveTo(sx + radius * 0.55, sy - radius * 0.3);
      gameCtx.lineTo(sx + radius * 0.35, sy - radius * 0.3 - earH * 0.6);
      gameCtx.lineTo(sx + radius * 0.1, sy - radius * 0.45);
      gameCtx.closePath();
      gameCtx.fill();
      // Claw scratch marks (three diagonal lines)
      gameCtx.strokeStyle = '#ff4444';
      gameCtx.lineWidth = 1.5;
      gameCtx.globalAlpha = 0.7;
      for (let ci = -1; ci <= 1; ci++) {
        gameCtx.beginPath();
        gameCtx.moveTo(sx + ci * 3 + radius * 0.6, sy - radius * 0.3);
        gameCtx.lineTo(sx + ci * 3 + radius * 1.0, sy + radius * 0.3);
        gameCtx.stroke();
      }
      gameCtx.globalAlpha = 1.0;
      // Attack buff glow
      if (p.catAttackBuff > 0) {
        gameCtx.fillStyle = 'rgba(255, 68, 68, 0.25)';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 5, 0, Math.PI * 2);
        gameCtx.fill();
      }
      // Seer glow (reveal the future)
      if (p.catSeerTimer > 0) {
        gameCtx.fillStyle = 'rgba(255, 215, 0, 0.2)';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 4, 0, Math.PI * 2);
        gameCtx.fill();
      }
      // Nope indicator
      if (p.catNopeTimer > 0) {
        gameCtx.strokeStyle = 'rgba(255, 0, 0, 0.6)';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 3, 0, Math.PI * 2);
        gameCtx.stroke();
        // X mark
        gameCtx.strokeStyle = 'rgba(255, 0, 0, 0.5)';
        gameCtx.lineWidth = 1.5;
        gameCtx.beginPath();
        gameCtx.moveTo(sx - 4, sy - radius - 6);
        gameCtx.lineTo(sx + 4, sy - radius - 14);
        gameCtx.moveTo(sx + 4, sy - radius - 6);
        gameCtx.lineTo(sx - 4, sy - radius - 14);
        gameCtx.stroke();
      }
      // Cat card count indicator
      if (p.catCards > 0) {
        gameCtx.fillStyle = '#ffcc00';
        gameCtx.font = 'bold 8px monospace';
        gameCtx.textAlign = 'center';
        gameCtx.fillText(p.catCards + '', sx, sy + radius + 10);
      }
    } else if (p.fighter && p.fighter.id === 'napoleon') {
      // Napoleon: grand bicorne hat covering the whole head
      const hatW = radius * 2.2;
      const hatH = radius * 1.1;
      const hatY = sy - radius * 0.45;
      // Hat body (dark navy bicorne — large and grand)
      gameCtx.fillStyle = '#0a0a1a';
      gameCtx.beginPath();
      // Left upswept brim — dramatic sweep
      gameCtx.moveTo(sx - hatW * 0.55, hatY + hatH * 0.1);
      gameCtx.quadraticCurveTo(sx - hatW * 0.5, hatY - hatH * 0.7, sx - hatW * 0.08, hatY - hatH * 0.35);
      // Top crest — tall peak
      gameCtx.quadraticCurveTo(sx, hatY - hatH * 0.5, sx + hatW * 0.08, hatY - hatH * 0.35);
      // Right upswept brim — dramatic sweep
      gameCtx.quadraticCurveTo(sx + hatW * 0.5, hatY - hatH * 0.7, sx + hatW * 0.55, hatY + hatH * 0.1);
      // Bottom curve wrapping around head
      gameCtx.quadraticCurveTo(sx + hatW * 0.25, hatY + hatH * 0.35, sx, hatY + hatH * 0.25);
      gameCtx.quadraticCurveTo(sx - hatW * 0.25, hatY + hatH * 0.35, sx - hatW * 0.55, hatY + hatH * 0.1);
      gameCtx.closePath();
      gameCtx.fill();
      // Outer edge highlight
      gameCtx.strokeStyle = '#1a1a3a';
      gameCtx.lineWidth = 1;
      gameCtx.stroke();
      // Gold trim band — thick and prominent
      gameCtx.strokeStyle = '#d4af37';
      gameCtx.lineWidth = 2.5;
      gameCtx.beginPath();
      gameCtx.moveTo(sx - hatW * 0.48, hatY + hatH * 0.08);
      gameCtx.quadraticCurveTo(sx - hatW * 0.2, hatY + hatH * 0.3, sx, hatY + hatH * 0.22);
      gameCtx.quadraticCurveTo(sx + hatW * 0.2, hatY + hatH * 0.3, sx + hatW * 0.48, hatY + hatH * 0.08);
      gameCtx.stroke();
      // Second gold trim line at brim tips
      gameCtx.lineWidth = 1.5;
      gameCtx.beginPath();
      gameCtx.moveTo(sx - hatW * 0.52, hatY + hatH * 0.05);
      gameCtx.quadraticCurveTo(sx - hatW * 0.45, hatY - hatH * 0.55, sx - hatW * 0.1, hatY - hatH * 0.3);
      gameCtx.stroke();
      gameCtx.beginPath();
      gameCtx.moveTo(sx + hatW * 0.52, hatY + hatH * 0.05);
      gameCtx.quadraticCurveTo(sx + hatW * 0.45, hatY - hatH * 0.55, sx + hatW * 0.1, hatY - hatH * 0.3);
      gameCtx.stroke();
      // Cockade (tricolor rosette — larger)
      gameCtx.fillStyle = '#003399';
      gameCtx.beginPath(); gameCtx.arc(sx, hatY + hatH * 0.05, 4.5, 0, Math.PI * 2); gameCtx.fill();
      gameCtx.fillStyle = '#fff';
      gameCtx.beginPath(); gameCtx.arc(sx, hatY + hatH * 0.05, 3, 0, Math.PI * 2); gameCtx.fill();
      gameCtx.fillStyle = '#cc0000';
      gameCtx.beginPath(); gameCtx.arc(sx, hatY + hatH * 0.05, 1.8, 0, Math.PI * 2); gameCtx.fill();
      // Gold button center
      gameCtx.fillStyle = '#d4af37';
      gameCtx.beginPath(); gameCtx.arc(sx, hatY + hatH * 0.05, 0.8, 0, Math.PI * 2); gameCtx.fill();
      // White plume feather curving from left tip
      gameCtx.strokeStyle = '#fff';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.moveTo(sx - hatW * 0.5, hatY - hatH * 0.5);
      gameCtx.quadraticCurveTo(sx - hatW * 0.6, hatY - hatH * 0.9, sx - hatW * 0.35, hatY - hatH * 1.0);
      gameCtx.stroke();
      gameCtx.lineWidth = 1.2;
      gameCtx.beginPath();
      gameCtx.moveTo(sx - hatW * 0.48, hatY - hatH * 0.55);
      gameCtx.quadraticCurveTo(sx - hatW * 0.55, hatY - hatH * 0.85, sx - hatW * 0.3, hatY - hatH * 0.95);
      gameCtx.stroke();
      // Cavalry glow when mounted
      if (p.napoleonCavalry) {
        gameCtx.strokeStyle = 'rgba(200, 169, 110, 0.6)';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 4, 0, Math.PI * 2);
        gameCtx.stroke();
        // Speed lines
        gameCtx.strokeStyle = 'rgba(200, 169, 110, 0.4)';
        gameCtx.lineWidth = 1.5;
        for (let i = 0; i < 3; i++) {
          const a = (i / 3) * Math.PI * 2 + Date.now() * 0.005;
          gameCtx.beginPath();
          gameCtx.moveTo(sx + Math.cos(a) * (radius + 3), sy + Math.sin(a) * (radius + 3));
          gameCtx.lineTo(sx + Math.cos(a) * (radius + 10), sy + Math.sin(a) * (radius + 10));
          gameCtx.stroke();
        }
      }
      // Cannon indicator
      if (p.napoleonCannonId) {
        gameCtx.fillStyle = '#555';
        gameCtx.beginPath();
        gameCtx.arc(sx + radius + 3, sy - radius - 3, 3, 0, Math.PI * 2);
        gameCtx.fill();
      }
    } else if (p.fighter && p.fighter.id === 'moderator') {
      // Moderator: terminal screen on head
      const termW = radius * 1.4, termH = radius * 1.0;
      const termX = sx - termW / 2, termY = sy - radius * 1.1;
      gameCtx.fillStyle = '#0c0c0c';
      gameCtx.fillRect(termX, termY, termW, termH);
      gameCtx.strokeStyle = '#333';
      gameCtx.lineWidth = 1;
      gameCtx.strokeRect(termX, termY, termW, termH);
      // Green cursor blink
      gameCtx.fillStyle = '#0f0';
      gameCtx.font = 'bold 6px monospace';
      gameCtx.textAlign = 'left';
      gameCtx.fillText('>', termX + 2, termY + termH - 3);
      gameCtx.textAlign = 'left';
      // Firewall glow when active
      if (p.modFirewallTimer > 0) {
        gameCtx.strokeStyle = 'rgba(0, 200, 255, 0.6)';
        gameCtx.lineWidth = 2;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 5, 0, Math.PI * 2);
        gameCtx.stroke();
      }
      // Server Update glow when buffed
      if (p.modServerUpdateTimer > 0) {
        gameCtx.strokeStyle = 'rgba(50, 255, 100, 0.5)';
        gameCtx.lineWidth = 1.5;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 3, 0, Math.PI * 2);
        gameCtx.stroke();
      }
      // Fear indicator on feared players
      if (p.modFearTimer > 0) {
        gameCtx.fillStyle = '#ff4444';
        gameCtx.font = 'bold 8px sans-serif';
        gameCtx.textAlign = 'center';
        gameCtx.fillText('😱 ' + Math.ceil(p.modFearTimer) + 's', sx, sy - radius - 10);
      }
      // Disabled ability indicator
      if (p.modDisabledAbilities && p.modDisabledAbilities.length > 0 && p.id === localPlayerId) {
        gameCtx.fillStyle = '#e67e22';
        gameCtx.font = 'bold 8px sans-serif';
        gameCtx.textAlign = 'center';
        gameCtx.fillText('🐛 ' + p.modDisabledAbilities.length + ' disabled', sx, sy + radius + 10);
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

    // Neon red aura when special is ready (visible to all players)
    if (!p.isSummon && p.specialUnlocked && !p.specialUsed && p.alive && !isDying) {
      const pulse = 0.5 + 0.5 * Math.sin(Date.now() * 0.005);
      gameCtx.strokeStyle = `rgba(255, 20, 20, ${0.5 + pulse * 0.4})`;
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 8 + pulse * 3, 0, Math.PI * 2);
      gameCtx.stroke();
      // Outer glow
      gameCtx.strokeStyle = `rgba(255, 20, 20, ${0.15 + pulse * 0.15})`;
      gameCtx.lineWidth = 6;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 12 + pulse * 3, 0, Math.PI * 2);
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
    gameCtx.fillStyle = isDying ? '#8b0000' : '#fff';
    gameCtx.font = 'bold 11px sans-serif';
    gameCtx.textAlign = 'center';
    const nameLabel = (gameMode === 'teams' && p.team) ? '[T' + p.team + '] ' + p.name : p.name;
    gameCtx.fillText(nameLabel, sx, sy - radius - 14);

    // HP bar above dot
    if (p.alive) {
      const barW = radius * 2.2;
      const barH = 4;
      const barX = sx - barW / 2;
      const barY = sy - radius - 10;
      gameCtx.fillStyle = '#333';
      gameCtx.fillRect(barX, barY, barW, barH);
      const hpFrac = Math.max(0, Math.min(1, (p.hp || 0) / (p.maxHp || 1)));
      gameCtx.fillStyle = hpFrac >= 0.7 ? '#2ecc71' : hpFrac >= 0.4 ? '#f5a623' : '#e94560';
      gameCtx.fillRect(barX, barY, barW * hpFrac, barH);
    }

    // Dragon breath fuel bar (only visible to the player using breath)
    if (p.id === localPlayerId && p.dragonBreathActive && p.fighter && p.fighter.id === 'dragon') {
      const maxFuel = p.fighter.abilities[0].maxFuel || 5;
      const fuelFrac = Math.max(0, (p.dragonBreathFuel || 0) / maxFuel);
      const fBarW = radius * 2.8;
      const fBarH = 3;
      const fBarX = sx - fBarW / 2;
      const fBarY = sy - radius - 5;
      gameCtx.fillStyle = '#222';
      gameCtx.fillRect(fBarX, fBarY, fBarW, fBarH);
      gameCtx.fillStyle = fuelFrac > 0.3 ? '#00aaff' : '#ff4444';
      gameCtx.fillRect(fBarX, fBarY, fBarW * fuelFrac, fBarH);
    }

    // Team heal/buff range indicator (visible to local player in team mode when healing)
    if (p.id === localPlayerId && gameMode === 'teams' && p.team && p.isHealing && p.alive && !p.isSummon && p.fighter && p.fighter.id !== 'filbus') {
      const rangeR = TEAM_HEAL_RANGE * GAME_TILE;
      gameCtx.save();
      gameCtx.strokeStyle = 'rgba(46, 204, 113, 0.35)';
      gameCtx.lineWidth = 1.5;
      gameCtx.setLineDash([6, 4]);
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, rangeR, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.setLineDash([]);
      gameCtx.restore();
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

    // Moderator: Ban Hammer swing effect (red arc, directional)
    const banFx = p.effects.find((fx) => fx.type === 'ban-hammer');
    if (banFx) {
      const swLen = GAME_TILE * 1.5;
      const aRad = Math.atan2(banFx.aimNy || 0, banFx.aimNx || 1);
      // Hammer handle
      gameCtx.strokeStyle = '#8b4513';
      gameCtx.lineWidth = 4;
      gameCtx.beginPath();
      gameCtx.moveTo(sx, sy);
      gameCtx.lineTo(sx + Math.cos(aRad) * swLen * 0.7, sy + Math.sin(aRad) * swLen * 0.7);
      gameCtx.stroke();
      // Hammer head
      gameCtx.fillStyle = '#ff4444';
      const hx = sx + Math.cos(aRad) * swLen * 0.75;
      const hy = sy + Math.sin(aRad) * swLen * 0.75;
      gameCtx.fillRect(hx - 8, hy - 5, 16, 10);
      gameCtx.strokeStyle = '#cc0000';
      gameCtx.lineWidth = 2;
      gameCtx.strokeRect(hx - 8, hy - 5, 16, 10);
      // Red sweep arc
      gameCtx.strokeStyle = 'rgba(255, 68, 68, 0.6)';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, swLen, aRad - 0.5, aRad + 0.5);
      gameCtx.stroke();
    }
    // Moderator: Ban Teleport flash on target
    if (p.effects.some((fx) => fx.type === 'ban-teleport')) {
      gameCtx.fillStyle = 'rgba(255, 0, 0, 0.3)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 15, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.fillStyle = '#ff0000';
      gameCtx.font = 'bold 10px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('BANNED!', sx, sy - radius - 12);
    }
    // Moderator: Scare TP flash (purple burst on victim)
    if (p.effects.some((fx) => fx.type === 'scare-tp')) {
      gameCtx.fillStyle = 'rgba(155, 89, 182, 0.35)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 18, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.strokeStyle = '#9b59b6';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 18, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.fillStyle = '#9b59b6';
      gameCtx.font = 'bold 11px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('😱 SCARED!', sx, sy - radius - 16);
    }
    // Moderator: Bug Fix effect
    if (p.effects.some((fx) => fx.type === 'bug-fix')) {
      gameCtx.strokeStyle = '#e67e22';
      gameCtx.lineWidth = 2;
      gameCtx.setLineDash([3, 3]);
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 8, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.setLineDash([]);
      gameCtx.fillStyle = '#e67e22';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('🐛 BUG FIX', sx, sy - radius - 12);
    }
    // Moderator: Server Reset flash (blue pulse)
    if (p.effects.some((fx) => fx.type === 'server-reset')) {
      gameCtx.fillStyle = 'rgba(52, 152, 219, 0.25)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 20, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.strokeStyle = '#3498db';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 20, 0, Math.PI * 2);
      gameCtx.stroke();
    }
    // Moderator: Server Update buff glow (green pulsing ring)
    if (p.effects.some((fx) => fx.type === 'server-update')) {
      gameCtx.fillStyle = 'rgba(46, 204, 113, 0.2)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 14, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.strokeStyle = '#2ecc71';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 14, 0, Math.PI * 2);
      gameCtx.stroke();
    }
    // Moderator: Firewall activation flash (bright cyan ring)
    if (p.effects.some((fx) => fx.type === 'firewall')) {
      gameCtx.strokeStyle = 'rgba(0, 200, 255, 0.7)';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 10, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.fillStyle = 'rgba(0, 200, 255, 0.15)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 10, 0, Math.PI * 2);
      gameCtx.fill();
    }

    // D&D Axe swing effect (orange arc, wider)
    const dndAxeFx = p.effects.find((fx) => fx.type === 'dnd-axe');
    if (dndAxeFx) {
      const swLen = GAME_TILE * 1.4;
      gameCtx.strokeStyle = '#e67e22';
      gameCtx.lineWidth = 5;
      gameCtx.beginPath();
      const aRad = Math.atan2(dndAxeFx.aimNy, dndAxeFx.aimNx);
      gameCtx.arc(sx, sy, swLen, aRad - 0.7, aRad + 0.7);
      gameCtx.stroke();
      // Inner lighter arc
      gameCtx.strokeStyle = 'rgba(230, 126, 34, 0.4)';
      gameCtx.lineWidth = 8;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, swLen * 0.8, aRad - 0.5, aRad + 0.5);
      gameCtx.stroke();
    }

    // D&D Bow shot effect (green flash line in aim direction)
    const dndBowFx = p.effects.find((fx) => fx.type === 'dnd-bow');
    if (dndBowFx) {
      gameCtx.strokeStyle = '#2ecc71';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.moveTo(sx, sy);
      gameCtx.lineTo(sx + dndBowFx.aimNx * GAME_TILE * 1.5, sy + dndBowFx.aimNy * GAME_TILE * 1.5);
      gameCtx.stroke();
      // Bow string pull effect (small arc behind player)
      gameCtx.strokeStyle = 'rgba(46, 204, 113, 0.5)';
      gameCtx.lineWidth = 1.5;
      const bRad = Math.atan2(dndBowFx.aimNy, dndBowFx.aimNx);
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius * 1.2, bRad + Math.PI - 0.4, bRad + Math.PI + 0.4);
      gameCtx.stroke();
    }

    // Dragon Breath effect (icy wind cone)
    if (p.dragonBreathActive) {
      const range = (p.fighter && p.fighter.abilities[0].range || 4) * GAME_TILE;
      const nx = p.dragonBreathAimNx || 0;
      const ny = p.dragonBreathAimNy || 0;
      const angle = Math.atan2(ny, nx);
      // Draw multiple semi-transparent icy blue + white wisps
      for (let i = 0; i < 10; i++) {
        const spread = (Math.random() - 0.5) * 0.6;
        const dist = range * (0.3 + Math.random() * 0.7);
        const ex = sx + Math.cos(angle + spread) * dist;
        const ey = sy + Math.sin(angle + spread) * dist;
        const alpha = 0.2 + Math.random() * 0.3;
        // Alternate between icy blue and white wisps
        if (i % 2 === 0) {
          gameCtx.strokeStyle = 'rgba(80, 180, 255, ' + alpha + ')';
        } else {
          gameCtx.strokeStyle = 'rgba(220, 240, 255, ' + alpha + ')';
        }
        gameCtx.lineWidth = 3 + Math.random() * 6;
        gameCtx.beginPath();
        gameCtx.moveTo(sx + Math.cos(angle + spread * 0.3) * radius, sy + Math.sin(angle + spread * 0.3) * radius);
        gameCtx.lineTo(ex, ey);
        gameCtx.stroke();
      }
      // Core bright blue-white beam
      gameCtx.strokeStyle = 'rgba(100, 200, 255, 0.35)';
      gameCtx.lineWidth = 10;
      gameCtx.beginPath();
      gameCtx.moveTo(sx, sy);
      gameCtx.lineTo(sx + Math.cos(angle) * range * 0.6, sy + Math.sin(angle) * range * 0.6);
      gameCtx.stroke();
      // Inner white glow
      gameCtx.strokeStyle = 'rgba(255, 255, 255, 0.25)';
      gameCtx.lineWidth = 4;
      gameCtx.beginPath();
      gameCtx.moveTo(sx, sy);
      gameCtx.lineTo(sx + Math.cos(angle) * range * 0.5, sy + Math.sin(angle) * range * 0.5);
      gameCtx.stroke();
    }

    // Dragon Beam fire effect (wide icy beam)
    const beamFx = p.effects.find((fx) => fx.type === 'dragon-beam-fire');
    if (beamFx) {
      const beamWidth = (p.fighter && p.fighter.abilities[2] ? p.fighter.abilities[2].beamWidth || 2 : 2) * GAME_TILE;
      const beamLen = Math.max(gameCanvas.width, gameCanvas.height) * 2;
      const nx = beamFx.aimNx || 0; const ny = beamFx.aimNy || 0;
      gameCtx.save();
      gameCtx.globalAlpha = 0.6 * Math.min(1, beamFx.timer / 0.3);
      gameCtx.fillStyle = '#00ccff';
      // Draw beam rectangle along aim direction
      const perpX = -ny; const perpY = nx;
      gameCtx.beginPath();
      gameCtx.moveTo(sx + perpX * beamWidth / 2, sy + perpY * beamWidth / 2);
      gameCtx.lineTo(sx + perpX * beamWidth / 2 + nx * beamLen, sy + perpY * beamWidth / 2 + ny * beamLen);
      gameCtx.lineTo(sx - perpX * beamWidth / 2 + nx * beamLen, sy - perpY * beamWidth / 2 + ny * beamLen);
      gameCtx.lineTo(sx - perpX * beamWidth / 2, sy - perpY * beamWidth / 2);
      gameCtx.closePath();
      gameCtx.fill();
      // Bright center
      gameCtx.fillStyle = 'rgba(255, 255, 255, 0.4)';
      gameCtx.beginPath();
      gameCtx.moveTo(sx + perpX * beamWidth / 4, sy + perpY * beamWidth / 4);
      gameCtx.lineTo(sx + perpX * beamWidth / 4 + nx * beamLen, sy + perpY * beamWidth / 4 + ny * beamLen);
      gameCtx.lineTo(sx - perpX * beamWidth / 4 + nx * beamLen, sy - perpY * beamWidth / 4 + ny * beamLen);
      gameCtx.lineTo(sx - perpX * beamWidth / 4, sy - perpY * beamWidth / 4);
      gameCtx.closePath();
      gameCtx.fill();
      gameCtx.restore();
    }

    // Lich lightning effect
    const lichFx = p.effects.find((fx) => fx.type === 'lich-lightning');
    if (lichFx && lichFx.targetX !== undefined) {
      const tx = lichFx.targetX - camX; const ty = lichFx.targetY - camY;
      gameCtx.strokeStyle = '#aa00ff';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.moveTo(sx, sy);
      // Zigzag lightning
      const ldx = tx - sx; const ldy = ty - sy;
      const steps = 6;
      for (let i = 1; i <= steps; i++) {
        const t = i / steps;
        const jx = (Math.random() - 0.5) * 15;
        const jy = (Math.random() - 0.5) * 15;
        if (i === steps) gameCtx.lineTo(tx, ty);
        else gameCtx.lineTo(sx + ldx * t + jx, sy + ldy * t + jy);
      }
      gameCtx.stroke();
      // Bright glow at target
      gameCtx.fillStyle = 'rgba(170, 0, 255, 0.4)';
      gameCtx.beginPath();
      gameCtx.arc(tx, ty, GAME_TILE * 0.4, 0, Math.PI * 2);
      gameCtx.fill();
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

    // Cricket bat swing effect
    const batFx = p.effects.find((fx) => fx.type === 'bat-swing');
    if (batFx) {
      const swLen = GAME_TILE * 1.0;
      gameCtx.strokeStyle = '#c8a96e';
      gameCtx.lineWidth = 5;
      gameCtx.beginPath();
      const aRad = Math.atan2(batFx.aimNy, batFx.aimNx);
      gameCtx.arc(sx, sy, swLen, aRad - 0.6, aRad + 0.6);
      gameCtx.stroke();
    }

    // Cricket Drive effect
    const driveFx = p.effects.find((fx) => fx.type === 'drive');
    if (driveFx) {
      const swLen = GAME_TILE * 1.8;
      gameCtx.strokeStyle = '#f5a623';
      gameCtx.lineWidth = 4;
      gameCtx.beginPath();
      const aRad = Math.atan2(driveFx.aimNy, driveFx.aimNx);
      gameCtx.arc(sx, sy, swLen, aRad - 0.4, aRad + 0.4);
      gameCtx.stroke();
      gameCtx.fillStyle = 'rgba(245, 166, 35, 0.15)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, swLen, aRad - 0.4, aRad + 0.4);
      gameCtx.lineTo(sx, sy);
      gameCtx.fill();
    }

    // Cricket Gear Up ring
    if (p.gearUpTimer > 0) {
      gameCtx.strokeStyle = '#3498db';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 6, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.fillStyle = '#3498db';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('GEAR ' + Math.ceil(p.gearUpTimer) + 's', sx, sy + radius + 16);
    }

    // Deer Spear effect (antler stab arc)
    const deerSpearFx = p.effects.find((fx) => fx.type === 'deer-spear');
    if (deerSpearFx) {
      const swLen = GAME_TILE * 1.0;
      gameCtx.strokeStyle = '#8b6914';
      gameCtx.lineWidth = 4;
      const aRad = Math.atan2(deerSpearFx.aimNy, deerSpearFx.aimNx);
      gameCtx.beginPath();
      gameCtx.moveTo(sx, sy);
      gameCtx.lineTo(sx + Math.cos(aRad) * swLen, sy + Math.sin(aRad) * swLen);
      gameCtx.stroke();
      // Prongs
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.moveTo(sx + Math.cos(aRad) * swLen * 0.7, sy + Math.sin(aRad) * swLen * 0.7);
      gameCtx.lineTo(sx + Math.cos(aRad - 0.3) * swLen, sy + Math.sin(aRad - 0.3) * swLen);
      gameCtx.moveTo(sx + Math.cos(aRad) * swLen * 0.7, sy + Math.sin(aRad) * swLen * 0.7);
      gameCtx.lineTo(sx + Math.cos(aRad + 0.3) * swLen, sy + Math.sin(aRad + 0.3) * swLen);
      gameCtx.stroke();
    }

    // Deer dodge flash
    if (p.effects.some((fx) => fx.type === 'deer-dodge')) {
      gameCtx.fillStyle = 'rgba(221, 160, 221, 0.4)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 4, 0, Math.PI * 2);
      gameCtx.fill();
    }

    // Deer Seer state indicator
    if (p.deerSeerTimer > 0) {
      gameCtx.strokeStyle = '#dda0dd';
      gameCtx.lineWidth = 2;
      gameCtx.setLineDash([4, 4]);
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 8, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.setLineDash([]);
      gameCtx.fillStyle = '#dda0dd';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('SEER ' + Math.ceil(p.deerSeerTimer) + 's', sx, sy + radius + 16);
    }

    // Deer Fear indicator
    if (p.deerFearTimer > 0) {
      gameCtx.fillStyle = '#8fbc8f';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('FEAR ' + Math.ceil(p.deerFearTimer) + 's', sx, sy - radius - 8);
    }

    // Noli Tendril Stab effect (purple slash)
    const tendrilFx = p.effects.find((fx) => fx.type === 'tendril-stab');
    if (tendrilFx) {
      const swLen = GAME_TILE * 1.2;
      const aRad = Math.atan2(tendrilFx.aimNy, tendrilFx.aimNx);
      gameCtx.strokeStyle = '#a020f0';
      gameCtx.lineWidth = 3;
      gameCtx.shadowColor = '#a020f0';
      gameCtx.shadowBlur = 6;
      gameCtx.beginPath();
      gameCtx.moveTo(sx, sy);
      gameCtx.lineTo(sx + Math.cos(aRad) * swLen, sy + Math.sin(aRad) * swLen);
      gameCtx.stroke();
      gameCtx.shadowBlur = 0;
    }

    // Noli Void Rush speed trail (purple afterimages behind player)
    if (p._voidRushTrail && p._voidRushTrail.length > 0) {
      for (const pt of p._voidRushTrail) {
        const ptSx = pt.x - camX, ptSy = pt.y - camY;
        const alpha = Math.max(0, pt.t / 0.3) * 0.4;
        const trailR = radius * (0.5 + alpha);
        gameCtx.fillStyle = 'rgba(160, 32, 240, ' + alpha.toFixed(2) + ')';
        gameCtx.beginPath();
        gameCtx.arc(ptSx, ptSy, trailR, 0, Math.PI * 2);
        gameCtx.fill();
      }
    }

    // Noli Void Rush aura — grows with chain count
    if (p.noliVoidRushActive) {
      const rushChain = p.noliVoidRushChain || 0;
      const rushRadius = radius + 4 + rushChain * 2;
      const rushAlpha = Math.min(0.5, 0.25 + rushChain * 0.05);
      gameCtx.fillStyle = 'rgba(160, 32, 240, ' + rushAlpha + ')';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, rushRadius, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.strokeStyle = '#a020f0';
      gameCtx.lineWidth = 1.5 + rushChain * 0.5;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, rushRadius, 0, Math.PI * 2);
      gameCtx.stroke();
    }

    // Noli Void Rush chain indicator
    if (p.noliVoidRushChainTimer > 0 && p.noliVoidRushChain > 0) {
      gameCtx.fillStyle = '#a020f0';
      gameCtx.font = 'bold ' + Math.min(16, 10 + p.noliVoidRushChain) + 'px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('CHAIN ' + p.noliVoidRushChain + '!', sx, sy - radius - 12);
    }

    // Noli Void Star aiming indicator
    if (p.noliVoidStarAiming) {
      const aimSx = p.noliVoidStarAimX - camX, aimSy = p.noliVoidStarAimY - camY;
      const starAbil = p.fighter && p.fighter.abilities[2];
      const starR = ((starAbil ? starAbil.radius : 1.5) || 1.5) * GAME_TILE;
      gameCtx.fillStyle = 'rgba(160, 32, 240, 0.15)';
      gameCtx.beginPath();
      gameCtx.arc(aimSx, aimSy, starR, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.strokeStyle = '#a020f0';
      gameCtx.lineWidth = 2;
      gameCtx.setLineDash([4, 4]);
      gameCtx.beginPath();
      gameCtx.arc(aimSx, aimSy, starR, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.setLineDash([]);
      // Star shape in center
      gameCtx.fillStyle = '#a020f0';
      gameCtx.font = 'bold 14px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('⭐', aimSx, aimSy + 5);
      gameCtx.fillStyle = '#a020f0';
      gameCtx.font = 'bold 9px sans-serif';
      gameCtx.fillText(Math.ceil(p.noliVoidStarTimer) + 's', aimSx, aimSy - starR - 6);
    }

    // Noli Observant teleport flash
    if (p.effects.some((fx) => fx.type === 'observant-tp')) {
      gameCtx.fillStyle = 'rgba(160, 32, 240, 0.5)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 10, 0, Math.PI * 2);
      gameCtx.fill();
    }

    // Noli Hallucination summon flash
    if (p.effects.some((fx) => fx.type === 'hallucination')) {
      gameCtx.strokeStyle = '#a020f0';
      gameCtx.lineWidth = 3;
      gameCtx.shadowColor = '#a020f0';
      gameCtx.shadowBlur = 10;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 12, 0, Math.PI * 2);
      gameCtx.stroke();
      gameCtx.shadowBlur = 0;
    }

    // Hit flash
    if (p.effects.some((fx) => fx.type === 'hit')) {
      gameCtx.fillStyle = 'rgba(255,0,0,0.3)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 2, 0, Math.PI * 2);
      gameCtx.fill();
    }

    // Apple heal glow
    if (p.effects.some((fx) => fx.type === 'apple-heal')) {
      gameCtx.fillStyle = 'rgba(46, 204, 113, 0.35)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 6, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.fillStyle = '#2ecc71';
      gameCtx.font = 'bold 10px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('+300', sx, sy - radius - 8);
      gameCtx.textAlign = 'left';
    }

    // Team heal glow (green pulse)
    if (p.effects.some((fx) => fx.type === 'team-heal')) {
      gameCtx.fillStyle = 'rgba(46, 204, 113, 0.25)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 5, 0, Math.PI * 2);
      gameCtx.fill();
    }

    // Team buff glow (gold pulse)
    if (p.effects.some((fx) => fx.type === 'team-buff')) {
      gameCtx.fillStyle = 'rgba(245, 166, 35, 0.3)';
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, radius + 5, 0, Math.PI * 2);
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

    // 1X1X1X1: Mass Infection close-range slash (dramatic green burst, distinct from M1)
    const miSlashFx = p.effects.find((fx) => fx.type === 'mass-infection-slash');
    if (miSlashFx) {
      const aRad = Math.atan2(miSlashFx.aimNy, miSlashFx.aimNx);
      // Filled green wedge — much more dramatic than the thin M1 arc
      const wedgeR = GAME_TILE * 2;
      gameCtx.save();
      gameCtx.globalAlpha = 0.5;
      gameCtx.fillStyle = '#00ff66';
      gameCtx.beginPath();
      gameCtx.moveTo(sx, sy);
      gameCtx.arc(sx, sy, wedgeR, aRad - Math.PI / 3, aRad + Math.PI / 3);
      gameCtx.closePath();
      gameCtx.fill();
      gameCtx.globalAlpha = 1.0;
      // Bright outline arc
      gameCtx.strokeStyle = '#00ff66';
      gameCtx.lineWidth = 5;
      gameCtx.beginPath();
      gameCtx.arc(sx, sy, wedgeR, aRad - Math.PI / 3, aRad + Math.PI / 3);
      gameCtx.stroke();
      gameCtx.restore();
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

    // Exploding Cat: Scratch claw marks effect (3 red claw arcs)
    const clawFx = p.effects.find((fx) => fx.type === 'cat-scratch');
    if (clawFx) {
      const clawLen = GAME_TILE * 0.9;
      const aRad = Math.atan2(clawFx.aimNy || 0, clawFx.aimNx || 1);
      gameCtx.strokeStyle = '#ff4444';
      gameCtx.lineWidth = 2.5;
      gameCtx.lineCap = 'round';
      for (let ci = -1; ci <= 1; ci++) {
        const offset = ci * 0.25;
        const startA = aRad - 0.35 + offset;
        const endA = aRad + 0.35 + offset;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, clawLen + ci * 2, startA, endA);
        gameCtx.stroke();
      }
      // Claw tip marks (sharp ends)
      gameCtx.strokeStyle = '#ff6666';
      gameCtx.lineWidth = 1.5;
      for (let ci = -1; ci <= 1; ci++) {
        const tipA = aRad + 0.35 + ci * 0.25;
        const tipR = clawLen + ci * 2;
        const tx = sx + Math.cos(tipA) * tipR;
        const ty = sy + Math.sin(tipA) * tipR;
        gameCtx.beginPath();
        gameCtx.moveTo(tx, ty);
        gameCtx.lineTo(tx + Math.cos(tipA) * 4, ty + Math.sin(tipA) * 4);
        gameCtx.stroke();
      }
    }

    // Cat Steal-Fire effect: orange slash/ring depending on stolen ability type
    const stealFireFx = p.effects.find((fx) => fx.type === 'cat-steal-fire');
    if (stealFireFx) {
      const aRad = Math.atan2(stealFireFx.aimNy || 0, stealFireFx.aimNx || 1);
      const sType = stealFireFx.stolenType;
      if (sType === 'melee') {
        // Orange directional arc
        const swLen = GAME_TILE * 1.2;
        gameCtx.strokeStyle = '#ff9900';
        gameCtx.lineWidth = 4;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, swLen, aRad - 0.5, aRad + 0.5);
        gameCtx.stroke();
      } else if (sType === 'ranged' || sType === 'projectile') {
        // Orange line in aim direction
        const lineLen = GAME_TILE * 1.5;
        gameCtx.strokeStyle = '#ff9900';
        gameCtx.lineWidth = 3;
        gameCtx.beginPath();
        gameCtx.moveTo(sx, sy);
        gameCtx.lineTo(sx + Math.cos(aRad) * lineLen, sy + Math.sin(aRad) * lineLen);
        gameCtx.stroke();
      } else if (sType === 'buff' || sType === 'self') {
        // Orange glow ring (self-buff)
        gameCtx.strokeStyle = '#ff9900';
        gameCtx.lineWidth = 3;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 8, 0, Math.PI * 2);
        gameCtx.stroke();
        gameCtx.fillStyle = 'rgba(255, 153, 0, 0.15)';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 8, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (sType === 'debuff') {
        // Purple pulse ring (debuff applied)
        gameCtx.strokeStyle = '#9b59b6';
        gameCtx.lineWidth = 3;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 10, 0, Math.PI * 2);
        gameCtx.stroke();
        gameCtx.fillStyle = 'rgba(155, 89, 182, 0.15)';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 10, 0, Math.PI * 2);
        gameCtx.fill();
      } else if (sType === 'summon') {
        // Gold summon flash
        gameCtx.fillStyle = 'rgba(212, 175, 55, 0.25)';
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 12, 0, Math.PI * 2);
        gameCtx.fill();
        gameCtx.strokeStyle = '#d4af37';
        gameCtx.lineWidth = 3;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 12, 0, Math.PI * 2);
        gameCtx.stroke();
      } else {
        // Default: orange ring
        gameCtx.strokeStyle = '#ff9900';
        gameCtx.lineWidth = 3;
        gameCtx.beginPath();
        gameCtx.arc(sx, sy, radius + 6, 0, Math.PI * 2);
        gameCtx.stroke();
      }
    }

    // Cat Draw card text (visible to all players via synced effects)
    const drawCatFx = p.effects.find((fx) => fx.type === 'cat-draw-cat');
    const drawShuffleFx = p.effects.find((fx) => fx.type === 'cat-draw-shuffle');
    const drawNopeFx = p.effects.find((fx) => fx.type === 'cat-draw-nope');
    const drawRevealFx = p.effects.find((fx) => fx.type === 'cat-draw-reveal');
    if (drawCatFx || drawShuffleFx || drawNopeFx || drawRevealFx) {
      gameCtx.font = 'bold 11px sans-serif';
      gameCtx.textAlign = 'center';
      let drawText, drawColor;
      if (drawCatFx) { drawText = '🐱 CAT!'; drawColor = '#ff9900'; }
      else if (drawShuffleFx) { drawText = '🔀 SHUFFLE!'; drawColor = '#ff9900'; }
      else if (drawNopeFx) { drawText = '🚫 NOPE!'; drawColor = '#e94560'; }
      else { drawText = '🔮 REVEAL!'; drawColor = '#dda0dd'; }
      gameCtx.fillStyle = '#000';
      gameCtx.fillText(drawText, sx + 1, sy - radius - 11);
      gameCtx.fillStyle = drawColor;
      gameCtx.fillText(drawText, sx, sy - radius - 12);
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

    // Moderator Fear indicator (on any player)
    if (p.modFearTimer > 0 && !(p.fighter && p.fighter.id === 'moderator')) {
      gameCtx.fillStyle = '#ff4444';
      gameCtx.font = 'bold 8px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('😱 FEAR ' + Math.ceil(p.modFearTimer) + 's', sx, sy - radius - 10);
    }

    // Moderator Bug Fix disabled abilities (on any player)
    if (p.modDisabledAbilities && p.modDisabledAbilities.length > 0 && p.id === localPlayerId && !(p.fighter && p.fighter.id === 'moderator')) {
      gameCtx.fillStyle = '#e67e22';
      gameCtx.font = 'bold 8px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('🐛 ' + p.modDisabledAbilities.length + ' move(s) disabled', sx, sy + radius + 10);
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
      // Tether line to owner (but not for wickets — they have their own line)
      if (p.summonType !== 'wicket') {
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
    }

    // Cricket: draw wicket line between two wickets
    if (p.wicketIds && p.wicketIds.length === 2) {
      const w0 = gamePlayers.find(x => x.id === p.wicketIds[0]);
      const w1 = gamePlayers.find(x => x.id === p.wicketIds[1]);
      if (w0 && w0.alive && w1 && w1.alive) {
        const w0x = w0.x - camX, w0y = w0.y - camY;
        const w1x = w1.x - camX, w1y = w1.y - camY;
        // Dashed green line between wickets
        gameCtx.strokeStyle = 'rgba(200, 169, 110, 0.5)';
        gameCtx.lineWidth = 3;
        gameCtx.setLineDash([8, 6]);
        gameCtx.beginPath();
        gameCtx.moveTo(w0x, w0y);
        gameCtx.lineTo(w1x, w1y);
        gameCtx.stroke();
        gameCtx.setLineDash([]);
      }
    }

    // Deer: draw igloo dome
    if (p.iglooTimer > 0) {
      const ix = p.iglooX - camX, iy = p.iglooY - camY;
      const iglooAbil = p.fighter && p.fighter.abilities[4];
      const ir = ((iglooAbil ? iglooAbil.radius : 2.5) || 2.5) * GAME_TILE;
      // Ice dome fill
      gameCtx.fillStyle = 'rgba(135, 206, 235, 0.15)';
      gameCtx.beginPath();
      gameCtx.arc(ix, iy, ir, 0, Math.PI * 2);
      gameCtx.fill();
      // Ice dome border
      gameCtx.strokeStyle = 'rgba(135, 206, 235, 0.6)';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(ix, iy, ir, 0, Math.PI * 2);
      gameCtx.stroke();
      // Ice blocks pattern
      gameCtx.strokeStyle = 'rgba(200, 230, 255, 0.3)';
      gameCtx.lineWidth = 1;
      for (let a = 0; a < 6; a++) {
        const angle = (a / 6) * Math.PI * 2;
        gameCtx.beginPath();
        gameCtx.moveTo(ix, iy);
        gameCtx.lineTo(ix + Math.cos(angle) * ir, iy + Math.sin(angle) * ir);
        gameCtx.stroke();
      }
      // Timer text
      gameCtx.fillStyle = '#87ceeb';
      gameCtx.font = 'bold 11px sans-serif';
      gameCtx.textAlign = 'center';
      gameCtx.fillText('IGLOO ' + Math.ceil(p.iglooTimer) + 's', ix, iy - ir - 6);
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
    } else if (proj.type === 'shockwave') {
      // Subtle green ripple so the shockwave is visible but not overwhelming
      gameCtx.save();
      gameCtx.globalAlpha = Math.min(0.6, proj.timer * 0.3);
      const angle = Math.atan2(proj.vy, proj.vx);
      gameCtx.strokeStyle = '#00ff66';
      gameCtx.lineWidth = 3;
      gameCtx.beginPath();
      gameCtx.arc(px, py, 6, angle - 0.6, angle + 0.6);
      gameCtx.stroke();
      gameCtx.globalAlpha = 1.0;
      gameCtx.restore();
    } else if (proj.type === 'coolkidd-ball') {
      gameCtx.fillStyle = proj.color || '#ff0000';
      gameCtx.beginPath();
      gameCtx.arc(px, py, 6, 0, Math.PI * 2);
      gameCtx.fill();
    } else if (proj.type === 'bowler-ball') {
      gameCtx.fillStyle = proj.color || '#228b22';
      gameCtx.beginPath();
      gameCtx.arc(px, py, 5, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.strokeStyle = '#fff';
      gameCtx.lineWidth = 1;
      gameCtx.stroke();
    } else if (proj.type === 'cannonball') {
      // ── Napoleon Cannonball: dark iron sphere with smoke trail ──
      // Smoke trail
      gameCtx.fillStyle = 'rgba(120, 120, 120, 0.3)';
      for (let i = 1; i <= 3; i++) {
        const tx = px - proj.vx * i * 0.3;
        const ty = py - proj.vy * i * 0.3;
        gameCtx.beginPath();
        gameCtx.arc(tx, ty, 4 - i * 0.8, 0, Math.PI * 2);
        gameCtx.fill();
      }
      // Main cannonball
      gameCtx.fillStyle = '#222';
      gameCtx.beginPath();
      gameCtx.arc(px, py, 5, 0, Math.PI * 2);
      gameCtx.fill();
      // Metallic highlight
      gameCtx.fillStyle = 'rgba(200, 200, 200, 0.35)';
      gameCtx.beginPath();
      gameCtx.arc(px - 1.5, py - 1.5, 2, 0, Math.PI * 2);
      gameCtx.fill();
    } else if (proj.type === 'infantry-bullet') {
      // ── Napoleon Infantry Bullet: small bright musket ball ──
      gameCtx.fillStyle = '#ffcc44';
      gameCtx.beginPath();
      gameCtx.arc(px, py, 2.5, 0, Math.PI * 2);
      gameCtx.fill();
      // Muzzle flash glow
      gameCtx.fillStyle = 'rgba(255, 200, 60, 0.25)';
      gameCtx.beginPath();
      gameCtx.arc(px, py, 5, 0, Math.PI * 2);
      gameCtx.fill();
    } else if (proj.type === 'dnd-arrow') {
      // ── D&D Elf Arrow: brown shaft with white tip ──
      gameCtx.save();
      const angle = Math.atan2(proj.vy, proj.vx);
      gameCtx.translate(px, py);
      gameCtx.rotate(angle);
      // Shaft
      gameCtx.strokeStyle = '#8b4513';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.moveTo(-10, 0);
      gameCtx.lineTo(6, 0);
      gameCtx.stroke();
      // Arrowhead
      gameCtx.fillStyle = '#ddd';
      gameCtx.beginPath();
      gameCtx.moveTo(10, 0);
      gameCtx.lineTo(5, -3);
      gameCtx.lineTo(5, 3);
      gameCtx.closePath();
      gameCtx.fill();
      // Fletching
      gameCtx.fillStyle = '#2ecc71';
      gameCtx.beginPath();
      gameCtx.moveTo(-10, 0);
      gameCtx.lineTo(-8, -3);
      gameCtx.lineTo(-6, 0);
      gameCtx.closePath();
      gameCtx.fill();
      gameCtx.beginPath();
      gameCtx.moveTo(-10, 0);
      gameCtx.lineTo(-8, 3);
      gameCtx.lineTo(-6, 0);
      gameCtx.closePath();
      gameCtx.fill();
      gameCtx.restore();
    } else if (proj.type === 'dnd-fireball') {
      // ── D&D Fireball: large 3×3 orange-red ball with flame trail ──
      const fbR = (proj.aoeRadius || 1.5 * GAME_TILE) * 0.5;
      // Flame trail
      for (let i = 1; i <= 6; i++) {
        const tx = px - proj.vx * i * 0.12;
        const ty = py - proj.vy * i * 0.12;
        gameCtx.fillStyle = 'rgba(255, ' + (80 + i * 25) + ', 0, ' + (0.35 - i * 0.05) + ')';
        gameCtx.beginPath();
        gameCtx.arc(tx, ty, fbR * (1 - i * 0.12), 0, Math.PI * 2);
        gameCtx.fill();
      }
      // Outer glow
      gameCtx.fillStyle = 'rgba(255, 69, 0, 0.25)';
      gameCtx.beginPath();
      gameCtx.arc(px, py, fbR * 1.15, 0, Math.PI * 2);
      gameCtx.fill();
      // Main ball
      gameCtx.fillStyle = '#ff4500';
      gameCtx.beginPath();
      gameCtx.arc(px, py, fbR * 0.7, 0, Math.PI * 2);
      gameCtx.fill();
      // Inner bright core
      gameCtx.fillStyle = '#ffcc00';
      gameCtx.beginPath();
      gameCtx.arc(px, py, fbR * 0.3, 0, Math.PI * 2);
      gameCtx.fill();
    } else if (proj.type === 'dnd-blur-bolt') {
      // ── D&D Blur Bolt: purple spinning bolt ──
      gameCtx.save();
      const angle = Math.atan2(proj.vy, proj.vx) + (Date.now() / 150);
      gameCtx.translate(px, py);
      gameCtx.rotate(angle);
      gameCtx.fillStyle = '#9b59b6';
      gameCtx.beginPath();
      gameCtx.moveTo(8, 0);
      gameCtx.lineTo(0, -5);
      gameCtx.lineTo(-8, 0);
      gameCtx.lineTo(0, 5);
      gameCtx.closePath();
      gameCtx.fill();
      // Glow
      gameCtx.fillStyle = 'rgba(155, 89, 182, 0.3)';
      gameCtx.beginPath();
      gameCtx.arc(0, 0, 8, 0, Math.PI * 2);
      gameCtx.fill();
      gameCtx.restore();
    }
  }

  // Render spike entities (John Doe)
  if (window._spikeEntities && window._spikeEntities.length > 0) {
    for (const spike of window._spikeEntities) {
      const sx = spike.x - camX;
      const sy = spike.y - camY;
      if (sx < -50 || sx > cw + 50 || sy < -50 || sy > ch + 50) continue;
      const alpha = Math.min(1, spike.timer / 2);
      gameCtx.fillStyle = 'rgba(139, 0, 0, ' + (alpha * 0.6) + ')';
      gameCtx.fillRect(sx - GAME_TILE / 2, sy - GAME_TILE / 2, GAME_TILE, GAME_TILE);
      // Draw spike cross
      gameCtx.strokeStyle = 'rgba(255, 50, 50, ' + alpha + ')';
      gameCtx.lineWidth = 2;
      gameCtx.beginPath();
      gameCtx.moveTo(sx - 8, sy - 8); gameCtx.lineTo(sx + 8, sy + 8);
      gameCtx.moveTo(sx + 8, sy - 8); gameCtx.lineTo(sx - 8, sy + 8);
      gameCtx.stroke();
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

  // Unstable Eye overlay: heavy blur + green tint (only visible to the 1x player, overridden by Boiled One)
  if (localPlayer && localPlayer.unstableEyeTimer > 0 && localPlayer.fighter.id === 'onexonexonex' && !anyBoiledOne) {
    // Heavy blur pass - redraw canvas onto itself with blur filter to smear colours together
    gameCtx.save();
    gameCtx.filter = 'blur(14px)';
    gameCtx.drawImage(gameCanvas, 0, 0);
    gameCtx.filter = 'none';
    gameCtx.restore();
    // Second lighter blur pass for extra smear
    gameCtx.save();
    gameCtx.filter = 'blur(8px)';
    gameCtx.globalAlpha = 0.6;
    gameCtx.drawImage(gameCanvas, 0, 0);
    gameCtx.filter = 'none';
    gameCtx.globalAlpha = 1.0;
    gameCtx.restore();
    // Green colour wash to further obscure
    gameCtx.fillStyle = 'rgba(0, 50, 10, 0.25)';
    gameCtx.fillRect(0, 0, cw, ch);
    // Subtle green outlines on enemies (reveal effect, but hard to see through blur)
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

  // D&D Blur overlay: heavy blur + purple tint (applied by blur bolt spell)
  if (localPlayer && localPlayer.dndBlurTimer > 0) {
    gameCtx.save();
    gameCtx.filter = 'blur(12px)';
    gameCtx.drawImage(gameCanvas, 0, 0);
    gameCtx.filter = 'none';
    gameCtx.restore();
    gameCtx.save();
    gameCtx.filter = 'blur(6px)';
    gameCtx.globalAlpha = 0.5;
    gameCtx.drawImage(gameCanvas, 0, 0);
    gameCtx.filter = 'none';
    gameCtx.globalAlpha = 1.0;
    gameCtx.restore();
    // Purple colour wash
    gameCtx.fillStyle = 'rgba(80, 0, 120, 0.2)';
    gameCtx.fillRect(0, 0, cw, ch);
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
    // "YOU DIED" fades out after 5 seconds
    if (deathOverlayTimer < 5) {
      const fadeAlpha = deathOverlayTimer < 4 ? 1.0 : 1.0 - (deathOverlayTimer - 4);
      // Slight dark overlay
      gameCtx.fillStyle = 'rgba(0,0,0,' + (0.15 * fadeAlpha) + ')';
      gameCtx.fillRect(0, 0, cw, ch);
      // "YOU DIED" text
      gameCtx.globalAlpha = fadeAlpha;
      gameCtx.font = 'bold 36px "Press Start 2P", monospace';
      gameCtx.textAlign = 'center';
      const deathMsg = diedInOtherWorld ? 'YOU DIED IN ANOTHER WORLD' : 'YOU DIED';
      gameCtx.fillStyle = '#000';
      gameCtx.fillText(deathMsg, cw / 2 + 2, ch / 2 - 40 + 2);
      gameCtx.fillStyle = diedInOtherWorld ? '#4a0080' : '#8b0000';
      gameCtx.fillText(deathMsg, cw / 2, ch / 2 - 40);
      gameCtx.globalAlpha = 1.0;
    }
    // Spectator hint (always visible)
    gameCtx.font = 'bold 12px "Press Start 2P", monospace';
    gameCtx.textAlign = 'center';
    gameCtx.fillStyle = '#ccc';
    if (spectateIndex >= 0 && gamePlayers[spectateIndex]) {
      gameCtx.fillText('Spectating: ' + gamePlayers[spectateIndex].name, cw / 2, ch - 40);
    }
    gameCtx.fillText('TAB = cycle players | WASD = free cam | ESC = free cam', cw / 2, ch - 20);
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
    gameCtx.fillText('💪 Buff ' + Math.ceil(lp.supportBuff) + 's', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#2ecc71';
    gameCtx.fillText('💪 Buff ' + Math.ceil(lp.supportBuff) + 's', cw / 2, logY);
    logY += 20;
  }
  if (lp.intimidated > 0) {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('😨 Intimidated ' + Math.ceil(lp.intimidated) + 's', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#9b59b6';
    gameCtx.fillText('😨 Intimidated ' + Math.ceil(lp.intimidated) + 's', cw / 2, logY);
    logY += 20;
  }
  if (lp.buffSlowed > 0) {
    gameCtx.fillStyle = '#000';
    gameCtx.fillText('🐌 Slowed ' + Math.ceil(lp.buffSlowed) + 's', cw / 2 + 1, logY + 1);
    gameCtx.fillStyle = '#e67e22';
    gameCtx.fillText('🐌 Slowed ' + Math.ceil(lp.buffSlowed) + 's', cw / 2, logY);
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
  const hasF = fighter.abilities.length > 5;
  const keys = hasF ? ['M1', 'E', 'R', 'T', 'F', 'SPC'] : ['M1', 'E', 'R', 'T', 'SPC'];
  const nameMap = {};
  fighter.abilities.forEach(a => { nameMap[a.key === 'SPACE' ? 'SPC' : a.key] = a.name; });
  keys.forEach((k) => {
    const n = nameMap[k] || k;
    const shortName = n.length > 7 ? n.substring(0, 6) + '.' : n;
    const div = document.createElement('div');
    div.className = 'hud-ability ready';
    div.id = 'hud-ab-' + k;
    div.innerHTML = `<span class="key-label">${k}</span>`;
    div.title = shortName;
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
  // Add F ability cooldown if fighter has it
  if (lp.fighter.abilities.length > 5) {
    const fAbil = lp.fighter.abilities[5];
    const fUnlocked = typeof isMove4Unlocked === 'function' && isMove4Unlocked(lp.fighter.id);
    const fMaxUsed = lp.move4Uses >= 3;
    cds.push({ id: 'F', cd: fUnlocked ? (fMaxUsed ? 999 : lp.cdF) : 999, max: fAbil.cooldown || 10 });
  }

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
      } else if (c.id === 'F' && c.cd >= 999) {
        ov.textContent = lp.move4Uses >= 3 ? '✓' : '🔒';
      } else {
        ov.textContent = (c.cd < 1 ? c.cd.toFixed(1) : Math.ceil(c.cd)) + 's';
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
  if (gameMode === 'fight' || gameMode === 'fight-hard') {
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
        // Achievement tracking: singleplayer win
        if (typeof trackSPWin === 'function') {
          trackSPWin(localPlayer.fighter.id);
        }
        // Check deer restricted win (only M1, T/Spear, SPACE/IGLOO used)
        if (localPlayer.fighter.id === 'deer' && typeof trackDeerRestrictedWin === 'function') {
          const forbidden = new Set(['E', 'R']);
          let usedForbidden = false;
          for (const k of usedAbilityKeys) {
            if (forbidden.has(k)) { usedForbidden = true; break; }
          }
          if (!usedForbidden) trackDeerRestrictedWin();
        }
        // Poker: win without using special
        if (localPlayer.fighter.id === 'poker' && !localPlayer.specialUsed && typeof trackPokerNoSpecialWin === 'function') {
          trackPokerNoSpecialWin();
        }
        // Flush remaining gear damage absorbed
        if (_gearDmgAbsorbedRemainder >= 1 && typeof trackGearDmgAbsorbed === 'function') {
          trackGearDmgAbsorbed(_gearDmgAbsorbedRemainder);
          _gearDmgAbsorbedRemainder = 0;
        }
        // Napoleon unlock: win a battle with a summon
        if (_hadSummonKillThisGame && typeof trackNapoleonSummonWin === 'function') {
          trackNapoleonSummonWin();
        }
        // Moderator achievement: win one game as moderator
        if (localPlayer && localPlayer.fighter.id === 'moderator' && typeof trackModWin === 'function') {
          trackModWin();
        }
        // D&D achievement: track race win
        if (localPlayer && localPlayer.fighter.id === 'dnd' && typeof trackDndRaceWin === 'function') {
          trackDndRaceWin(localPlayer.dndRace || 'human');
        }
        // Dragon achievement: track dragon win
        if (localPlayer && localPlayer.fighter.id === 'dragon' && typeof trackDragonBeamAch === 'function') {
          // Beam achievement tracked separately in dealDamage; no per-win tracking needed here
        }
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
  } else if (type === 'boiled-one') {
    // Remote Filbus activated The Boiled One Phenomenon
    const caster = gamePlayers.find((p) => p.id === casterId);
    if (caster && caster.alive) {
      caster.boiledOneActive = true;
      caster.boiledOneTimer = duration;
      caster.effects.push({ type: 'boiled-one', timer: duration + 1 });
      // Stun all non-Filbus players
      for (const target of gamePlayers) {
        if (!target.alive || target.isSummon) continue;
        if (target.id === casterId) continue;
        target.stunned = duration;
        target.effects.push({ type: 'stun', timer: duration });
      }
      showPopup('\ud83e\ude78 THE BOILED ONE PHENOMENON');
      combatLog.push({ text: '\ud83e\ude78 Phen 228 has entered...', timer: 5, color: '#8b0000' });
    }
  }
}

function onRemoteDebuff(casterId, targetId, type, duration) {
  if (type === 'intimidation') {
    const target = gamePlayers.find((p) => p.id === targetId);
    if (target) {
      target.intimidated = duration;
      target.intimidatedBy = casterId;
    }
  } else if (type === 'stun') {
    const target = gamePlayers.find((p) => p.id === targetId);
    if (target && target.alive) {
      target.stunned = duration;
      target.effects.push({ type: 'stun', timer: duration });
    }
  } else if (type === 'poison') {
    const target = gamePlayers.find((p) => p.id === targetId);
    if (target && target.alive) {
      if (!target.poisonTimers) target.poisonTimers = [];
      target.poisonTimers.push({ sourceId: casterId, dps: 50, remaining: duration });
      target.effects.push({ type: 'poison', timer: duration });
    }
  }
}

function onRemoteProjectiles(ownerId, projs) {
  // Legacy: Add visual-only projectiles (used as fallback only)
  for (const p of projs) {
    projectiles.push({
      x: p.x, y: p.y, vx: p.vx, vy: p.vy,
      ownerId: ownerId, damage: 0,
      timer: p.timer, type: p.type,
    });
  }
}

// ── HOST-AUTHORITATIVE MULTIPLAYER ────────────────────────────

// Build a serialisable snapshot of the full game state for broadcast
function buildGameStateSnapshot() {
  const players = gamePlayers.map(p => ({
    id: p.id,
    name: p.name, color: p.color,
    x: p.x, y: p.y,
    hp: p.hp, maxHp: p.maxHp,
    alive: p.alive,
    stunned: p.stunned,
    // cooldowns
    cdM1: p.cdM1, cdE: p.cdE, cdR: p.cdR, cdT: p.cdT, cdF: p.cdF || 0,
    // summon identity
    isSummon: p.isSummon || false,
    summonOwner: p.summonOwner || null,
    summonType: p.summonType || null,
    // buffs/debuffs
    supportBuff: p.supportBuff,
    buffSlowed: p.buffSlowed || 0,
    intimidated: p.intimidated,
    intimidatedBy: p.intimidatedBy || null,
    poisonTimers: p.poisonTimers || [],
    unstableEyeTimer: p.unstableEyeTimer || 0,
    zombieIds: p.zombieIds || [],
    boiledOneActive: p.boiledOneActive || false,
    boiledOneTimer: p.boiledOneTimer || 0,
    specialUnlocked: p.specialUnlocked,
    specialUsed: p.specialUsed,
    totalDamageTaken: p.totalDamageTaken,
    // Auto-heal state
    noDamageTimer: p.noDamageTimer || 0,
    healTickTimer: p.healTickTimer || 0,
    isHealing: p.isHealing || false,
    // Fighter special aim state
    specialAiming: p.specialAiming || false,
    specialAimX: p.specialAimX || 0,
    specialAimY: p.specialAimY || 0,
    specialAimTimer: p.specialAimTimer || 0,
    // Poker state
    blindBuff: p.blindBuff || null,
    blindTimer: p.blindTimer || 0,
    chipChangeDmg: p.chipChangeDmg != null ? p.chipChangeDmg : -1,
    chipChangeTimer: p.chipChangeTimer || 0,
    // Team
    team: p.team || null,
    // Filbus
    chairCharges: p.chairCharges || 0,
    isCraftingChair: p.isCraftingChair || false,
    isEatingChair: p.isEatingChair || false,
    craftTimer: p.craftTimer || 0,
    eatTimer: p.eatTimer || 0,
    eatHealPool: p.eatHealPool || 0,
    summonId: p.summonId || null,
    // Cricket
    gearUpTimer: p.gearUpTimer || 0,
    driveReflectTimer: p.driveReflectTimer || 0,
    wicketIds: p.wicketIds || [],
    // Deer
    deerFearTimer: p.deerFearTimer || 0,
    deerFearTargetX: p.deerFearTargetX || 0,
    deerFearTargetY: p.deerFearTargetY || 0,
    deerSeerTimer: p.deerSeerTimer || 0,
    deerRobotId: p.deerRobotId || null,
    deerBuildSlowTimer: p.deerBuildSlowTimer || 0,
    iglooX: p.iglooX || 0,
    iglooY: p.iglooY || 0,
    iglooTimer: p.iglooTimer || 0,
    // Noli
    noliVoidRushActive: p.noliVoidRushActive || false,
    noliVoidRushTimer: p.noliVoidRushTimer || 0,
    noliVoidRushVx: p.noliVoidRushVx || 0,
    noliVoidRushVy: p.noliVoidRushVy || 0,
    noliVoidRushChain: p.noliVoidRushChain || 0,
    noliVoidRushChainTimer: p.noliVoidRushChainTimer || 0,
    noliVoidRushLastHitId: p.noliVoidRushLastHitId || null,
    noliVoidStarAiming: p.noliVoidStarAiming || false,
    noliVoidStarAimX: p.noliVoidStarAimX || 0,
    noliVoidStarAimY: p.noliVoidStarAimY || 0,
    noliVoidStarTimer: p.noliVoidStarTimer || 0,
    noliObservantUses: p.noliObservantUses || 0,
    noliCloneId: p.noliCloneId || null,
    // Exploding Cat
    catCards: p.catCards || 0,
    catStolenAbil: p.catStolenAbil || null,
    catStolenReady: p.catStolenReady || false,
    catAttackBuff: p.catAttackBuff || 0,
    catSeerTimer: p.catSeerTimer || 0,
    catNopeTimer: p.catNopeTimer || 0,
    catNopeAbility: p.catNopeAbility || null,
    catKittenIds: p.catKittenIds || [],
    catUnicornId: p.catUnicornId || null,
    // Move 4 F ability state
    move4Uses: p.move4Uses || 0,
    pokerFullHouseActive: p.pokerFullHouseActive || false,
    potionHealPool: p.potionHealPool || 0,
    potionHealTimer: p.potionHealTimer || 0,
    coolkiddId: p.coolkiddId || null,
    bowlerId: p.bowlerId || null,
    crabIds: p.crabIds || [],
    johnDoeId: p.johnDoeId || null,
    // Filbus Analogus state
    inBackrooms: p.inBackrooms || false,
    backroomsDoorX: p.backroomsDoorX || 0,
    backroomsDoorY: p.backroomsDoorY || 0,
    backroomsChaserId: p.backroomsChaserId || null,
    backroomsTimer: p.backroomsTimer || 0,
    hasAlternate: p.hasAlternate || false,
    alternateId: p.alternateId || null,
    // Summon target tracking (for backrooms-chaser, alternate, and room)
    summonTargetId: p.summonTargetId || null,
    roomDPS: p.roomDPS || 0,
    // Moderator state
    modFirewallTimer: p.modFirewallTimer || 0,
    modServerUpdateTimer: p.modServerUpdateTimer || 0,
    modFearTimer: p.modFearTimer || 0,
    modFearSourceId: p.modFearSourceId || null,
    modServerResetUses: p.modServerResetUses || 0,
    modDisabledAbilities: p.modDisabledAbilities || [],
    // Napoleon state
    napoleonCavalry: p.napoleonCavalry || false,
    napoleonCannonId: p.napoleonCannonId || null,
    napoleonWallId: p.napoleonWallId || null,
    napoleonInfantryIds: p.napoleonInfantryIds || [],
    // D&D Campaigner state
    dndGP: p.dndGP || 0,
    dndRace: p.dndRace || 'human',
    dndWeaponBonus: p.dndWeaponBonus || 0,
    dndCharm: p.dndCharm || false,
    dndD20Active: p.dndD20Active || false,
    dndBlurTimer: p.dndBlurTimer || 0,
    dndHealPool: p.dndHealPool || 0,
    dndHealTimer: p.dndHealTimer || 0,
    dndOrcIds: p.dndOrcIds || [],
    dndSidekickId: p.dndSidekickId || null,
    // Dragon of Icespire state
    dragonBreathFuel: p.dragonBreathFuel != null ? p.dragonBreathFuel : 5,
    dragonBreathActive: p.dragonBreathActive || false,
    dragonBreathAimNx: p.dragonBreathAimNx || 0,
    dragonBreathAimNy: p.dragonBreathAimNy || 0,
    dragonBreathWindup: p.dragonBreathWindup || 0,
    dragonBreathRegenDelay: p.dragonBreathRegenDelay || 0,
    dragonFlying: p.dragonFlying || false,
    dragonFlyTimer: p.dragonFlyTimer || 0,
    dragonBeamCharging: p.dragonBeamCharging || false,
    dragonBeamChargeTimer: p.dragonBeamChargeTimer || 0,
    dragonBeamFiring: p.dragonBeamFiring || false,
    dragonBeamRecovery: p.dragonBeamRecovery || 0,
    dragonBeamAimNx: p.dragonBeamAimNx || 0,
    dragonBeamAimNy: p.dragonBeamAimNy || 0,
    dragonRoarActive: p.dragonRoarActive || false,
    dragonSummonId: p.dragonSummonId || null,
    // Movement state for non-host position correction
    specialJumping: p.specialJumping || false,
    // visual effects (include aimNx/aimNy for directional rendering, stolenType for cat-steal-fire)
    effects: (p.effects || []).map(fx => ({ type: fx.type, timer: fx.timer, aimNx: fx.aimNx, aimNy: fx.aimNy, stolenType: fx.stolenType })),
    // fighter id so client knows what it is
    fighterId: p.fighter ? p.fighter.id : null,
  }));
  const projs = projectiles.map(p => ({
    x: p.x, y: p.y, vx: p.vx, vy: p.vy,
    type: p.type, timer: p.timer, ownerId: p.ownerId,
  }));
  return {
    players, projectiles: projs, zoneInset, zoneTimer,
    appleTree: appleTree ? {
      col: appleTree.col, row: appleTree.row,
      hp: appleTree.hp, maxHp: appleTree.maxHp,
      alive: appleTree.alive,
      regrowTimer: appleTree.regrowTimer,
      appleTimer: appleTree.appleTimer,
      apples: appleTree.apples.slice(),
    } : null,
  };
}

// Non-host client: receive full state snapshot from host and apply it
function onRemoteGameState(snapshot) {
  if (isHostAuthority) return; // host doesn't process its own broadcast

  // Sync zone
  zoneInset = snapshot.zoneInset;
  zoneTimer = snapshot.zoneTimer;

  // Sync players (including summons)
  const incomingIds = new Set(snapshot.players.map(p => p.id));
  // Remove players/summons that no longer exist on host
  for (let i = gamePlayers.length - 1; i >= 0; i--) {
    if (!incomingIds.has(gamePlayers[i].id)) gamePlayers.splice(i, 1);
  }
  for (const sp of snapshot.players) {
    let p = gamePlayers.find(x => x.id === sp.id);
    if (!p) {
      // New player or summon — create a minimal state
      const fighter = getFighter(sp.fighterId || 'fighter');
      p = createPlayerState(
        { id: sp.id, name: sp.name || sp.id, color: sp.color || '#fff', fighterId: sp.fighterId || 'fighter' },
        { r: 1, c: 1 }, fighter
      );
      gamePlayers.push(p);
    }
    // Update name/color from snapshot
    if (sp.name) p.name = sp.name;
    if (sp.color) p.color = sp.color;
    // For local player: DON'T overwrite position — local prediction handles movement.
    // Exception: when the host controls movement (stunned, dashing, knocked back, dead)
    // accept the host's position to prevent desync during non-predicted states.
    // For remote players: set interpolation target so movement is smooth
    if (sp.id !== localPlayerId) {
      p._targetX = sp.x; p._targetY = sp.y;
      // If first snapshot or teleported far, snap immediately
      const dx = sp.x - p.x, dy = sp.y - p.y;
      if (dx * dx + dy * dy > 10000) { p.x = sp.x; p.y = sp.y; }
    } else {
      // Local player: accept host position when in non-predicted states
      if (sp.stunned > 0 || !sp.alive || sp.noliVoidRushActive || sp.specialJumping) {
        p.x = sp.x; p.y = sp.y;
      } else {
        // Soft correction: gently pull local prediction toward host position to prevent drift
        const dx = sp.x - p.x, dy = sp.y - p.y;
        const distSq = dx * dx + dy * dy;
        if (distSq > (GAME_TILE * 3) * (GAME_TILE * 3)) {
          // Teleport snap if very far (>3 tiles away from host)
          p.x = sp.x; p.y = sp.y;
        } else if (distSq > (GAME_TILE * 0.5) * (GAME_TILE * 0.5)) {
          // Gentle correction toward host position (prevents slow drift)
          p.x += dx * 0.1;
          p.y += dy * 0.1;
        }
      }
    }
    // Detect death transition for local player (init spectator camera)
    if (sp.id === localPlayerId && p.alive && !sp.alive) {
      freeCamX = p.x; freeCamY = p.y;
      spectateIndex = -1;
      deathOverlayTimer = 0;
    }
    p.hp = sp.hp; p.maxHp = sp.maxHp;
    p.alive = sp.alive;
    p.stunned = sp.stunned;
    p.cdM1 = sp.cdM1; p.cdE = sp.cdE; p.cdR = sp.cdR; p.cdT = sp.cdT; p.cdF = sp.cdF || 0;
    p.isSummon = sp.isSummon; p.summonOwner = sp.summonOwner; p.summonType = sp.summonType;
    p.supportBuff = sp.supportBuff;
    p.buffSlowed = sp.buffSlowed || 0;
    p.intimidated = sp.intimidated;
    p.intimidatedBy = sp.intimidatedBy || null;
    p.poisonTimers = sp.poisonTimers || [];
    p.unstableEyeTimer = sp.unstableEyeTimer || 0;
    p.zombieIds = sp.zombieIds || [];
    p.boiledOneActive = sp.boiledOneActive || false;
    p.boiledOneTimer = sp.boiledOneTimer || 0;
    p.specialUnlocked = sp.specialUnlocked;
    p.specialUsed = sp.specialUsed;
    p.totalDamageTaken = sp.totalDamageTaken;
    // Auto-heal state
    p.noDamageTimer = sp.noDamageTimer || 0;
    p.healTickTimer = sp.healTickTimer || 0;
    p.isHealing = sp.isHealing || false;
    // Fighter special aim state
    p.specialAiming = sp.specialAiming || false;
    p.specialAimX = sp.specialAimX || 0;
    p.specialAimY = sp.specialAimY || 0;
    p.specialAimTimer = sp.specialAimTimer || 0;
    // Poker state
    p.blindBuff = sp.blindBuff || null;
    p.blindTimer = sp.blindTimer || 0;
    p.chipChangeDmg = sp.chipChangeDmg != null ? sp.chipChangeDmg : -1;
    p.chipChangeTimer = sp.chipChangeTimer || 0;
    // Team
    p.team = sp.team || null;
    p.chairCharges = sp.chairCharges || 0;
    p.isCraftingChair = sp.isCraftingChair || false;
    p.isEatingChair = sp.isEatingChair || false;
    p.craftTimer = sp.craftTimer || 0;
    p.eatTimer = sp.eatTimer || 0;
    p.eatHealPool = sp.eatHealPool || 0;
    p.summonId = sp.summonId || null;
    p.gearUpTimer = sp.gearUpTimer || 0;
    p.driveReflectTimer = sp.driveReflectTimer || 0;
    p.wicketIds = sp.wicketIds || [];
    // Deer
    p.deerFearTimer = sp.deerFearTimer || 0;
    p.deerFearTargetX = sp.deerFearTargetX || 0;
    p.deerFearTargetY = sp.deerFearTargetY || 0;
    p.deerSeerTimer = sp.deerSeerTimer || 0;
    p.deerRobotId = sp.deerRobotId || null;
    p.deerBuildSlowTimer = sp.deerBuildSlowTimer || 0;
    p.iglooX = sp.iglooX || 0;
    p.iglooY = sp.iglooY || 0;
    p.iglooTimer = sp.iglooTimer || 0;
    // Noli
    p.noliVoidRushActive = sp.noliVoidRushActive || false;
    p.noliVoidRushTimer = sp.noliVoidRushTimer || 0;
    p.noliVoidRushVx = sp.noliVoidRushVx || 0;
    p.noliVoidRushVy = sp.noliVoidRushVy || 0;
    p.noliVoidRushChain = sp.noliVoidRushChain || 0;
    p.noliVoidRushChainTimer = sp.noliVoidRushChainTimer || 0;
    p.noliVoidRushLastHitId = sp.noliVoidRushLastHitId || null;
    p.noliVoidStarAiming = sp.noliVoidStarAiming || false;
    p.noliVoidStarAimX = sp.noliVoidStarAimX || 0;
    p.noliVoidStarAimY = sp.noliVoidStarAimY || 0;
    p.noliVoidStarTimer = sp.noliVoidStarTimer || 0;
    p.noliObservantUses = sp.noliObservantUses || 0;
    p.noliCloneId = sp.noliCloneId || null;
    // Exploding Cat
    p.catCards = sp.catCards || 0;
    p.catStolenAbil = sp.catStolenAbil || null;
    p.catStolenReady = sp.catStolenReady || false;
    p.catAttackBuff = sp.catAttackBuff || 0;
    p.catSeerTimer = sp.catSeerTimer || 0;
    p.catNopeTimer = sp.catNopeTimer || 0;
    p.catNopeAbility = sp.catNopeAbility || null;
    p.catKittenIds = sp.catKittenIds || [];
    p.catUnicornId = sp.catUnicornId || null;
    // Move 4 F ability state
    p.move4Uses = sp.move4Uses || 0;
    p.pokerFullHouseActive = sp.pokerFullHouseActive || false;
    p.potionHealPool = sp.potionHealPool || 0;
    p.potionHealTimer = sp.potionHealTimer || 0;
    p.coolkiddId = sp.coolkiddId || null;
    p.bowlerId = sp.bowlerId || null;
    p.crabIds = sp.crabIds || [];
    p.johnDoeId = sp.johnDoeId || null;
    // Filbus Analogus state — detect transitions for combat log on non-host target
    const wasInBackrooms = p.inBackrooms;
    const hadAlternate = p.hasAlternate;
    p.inBackrooms = sp.inBackrooms || false;
    p.backroomsDoorX = sp.backroomsDoorX || 0;
    p.backroomsDoorY = sp.backroomsDoorY || 0;
    p.backroomsChaserId = sp.backroomsChaserId || null;
    p.backroomsTimer = sp.backroomsTimer || 0;
    p.hasAlternate = sp.hasAlternate || false;
    p.alternateId = sp.alternateId || null;
    // Show combat log warnings for the local player entering backrooms/alternate
    if (p.id === localPlayerId && !isHostAuthority) {
      if (!wasInBackrooms && p.inBackrooms) {
        combatLog.push({ text: '⚠️ You are in the Backrooms! Find the door to escape! (10 DPS, no healing)', timer: 5, color: '#ff4444' });
      }
      if (!hadAlternate && p.hasAlternate) {
        combatLog.push({ text: "⚠️ Your Alternate is hunting you! You can't see others or heal! (10 DPS)", timer: 5, color: '#ff4444' });
      }
    }
    p.summonTargetId = sp.summonTargetId || null;
    p.roomDPS = sp.roomDPS || 0;
    // Moderator
    p.modFirewallTimer = sp.modFirewallTimer || 0;
    p.modServerUpdateTimer = sp.modServerUpdateTimer || 0;
    p.modFearTimer = sp.modFearTimer || 0;
    p.modFearSourceId = sp.modFearSourceId || null;
    p.modServerResetUses = sp.modServerResetUses || 0;
    p.modDisabledAbilities = sp.modDisabledAbilities || [];
    // Napoleon
    p.napoleonCavalry = sp.napoleonCavalry || false;
    p.napoleonCannonId = sp.napoleonCannonId || null;
    p.napoleonWallId = sp.napoleonWallId || null;
    p.napoleonInfantryIds = sp.napoleonInfantryIds || [];
    // D&D Campaigner
    p.dndGP = sp.dndGP || 0;
    p.dndRace = sp.dndRace || 'human';
    p.dndWeaponBonus = sp.dndWeaponBonus || 0;
    p.dndCharm = sp.dndCharm || false;
    p.dndD20Active = sp.dndD20Active || false;
    p.dndBlurTimer = sp.dndBlurTimer || 0;
    p.dndHealPool = sp.dndHealPool || 0;
    p.dndHealTimer = sp.dndHealTimer || 0;
    p.dndOrcIds = sp.dndOrcIds || [];
    p.dndSidekickId = sp.dndSidekickId || null;
    // Dragon of Icespire
    p.dragonBreathFuel = sp.dragonBreathFuel != null ? sp.dragonBreathFuel : 5;
    p.dragonBreathActive = sp.dragonBreathActive || false;
    p.dragonBreathAimNx = sp.dragonBreathAimNx || 0;
    p.dragonBreathAimNy = sp.dragonBreathAimNy || 0;
    p.dragonBreathWindup = sp.dragonBreathWindup || 0;
    p.dragonBreathRegenDelay = sp.dragonBreathRegenDelay || 0;
    p.dragonFlying = sp.dragonFlying || false;
    p.dragonFlyTimer = sp.dragonFlyTimer || 0;
    p.dragonBeamCharging = sp.dragonBeamCharging || false;
    p.dragonBeamChargeTimer = sp.dragonBeamChargeTimer || 0;
    p.dragonBeamFiring = sp.dragonBeamFiring || false;
    p.dragonBeamRecovery = sp.dragonBeamRecovery || 0;
    p.dragonBeamAimNx = sp.dragonBeamAimNx || 0;
    p.dragonBeamAimNy = sp.dragonBeamAimNy || 0;
    p.dragonRoarActive = sp.dragonRoarActive || false;
    p.dragonSummonId = sp.dragonSummonId || null;
    p.specialJumping = sp.specialJumping || false;
    if (sp.effects) p.effects = sp.effects;
  }

  // Sync projectiles (replace entirely with host's list)
  projectiles = snapshot.projectiles.map(sp => ({
    x: sp.x, y: sp.y, vx: sp.vx, vy: sp.vy,
    type: sp.type, timer: sp.timer, ownerId: sp.ownerId,
    damage: 0, // client doesn't resolve damage — host does
  }));

  // Sync apple tree state
  if (snapshot.appleTree) {
    if (!appleTree) appleTree = {};
    appleTree.col = snapshot.appleTree.col;
    appleTree.row = snapshot.appleTree.row;
    appleTree.hp = snapshot.appleTree.hp;
    appleTree.maxHp = snapshot.appleTree.maxHp;
    appleTree.alive = snapshot.appleTree.alive;
    appleTree.regrowTimer = snapshot.appleTree.regrowTimer;
    appleTree.appleTimer = snapshot.appleTree.appleTimer;
    appleTree.apples = snapshot.appleTree.apples || [];
    // Sync map tiles for dead tree (stump = ROCK)
    if (!appleTree.alive) {
      for (let dr = 0; dr < 2; dr++) {
        for (let dc = 0; dc < 2; dc++) {
          gameMap.tiles[appleTree.row + dr][appleTree.col + dc] = TILE.ROCK;
        }
      }
    } else {
      for (let dr = 0; dr < 2; dr++) {
        for (let dc = 0; dc < 2; dc++) {
          if (gameMap.tiles[appleTree.row + dr][appleTree.col + dc] === TILE.ROCK) {
            gameMap.tiles[appleTree.row + dr][appleTree.col + dc] = TILE.GROUND;
          }
        }
      }
    }
  }

  // Re-bind localPlayer reference (could have been replaced above)
  localPlayer = gamePlayers.find(p => p.id === localPlayerId);
}

// Host: receive input from a non-host client and store it
function onRemoteInput(input) {
  if (!isHostAuthority) return;
  const { playerId, aimWorldX: awx, aimWorldY: awy, mouseDown: md, pendingAbilities: pa, keys: k } = input;
  if (!remoteInputs[playerId]) remoteInputs[playerId] = { aimWorldX: 0, aimWorldY: 0, mouseDown: false, pendingAbilities: [], keys: {} };
  const ri = remoteInputs[playerId];
  ri.aimWorldX = awx || 0;
  ri.aimWorldY = awy || 0;
  ri.mouseDown = md || false;
  if (k) ri.keys = k;
  // Append pending abilities (don't overwrite, accumulate between frames)
  if (pa && pa.length) ri.pendingAbilities.push(...pa);
}

// Receive a player's world position (relay from server — all clients send their own position)
function onRemotePosition(data) {
  const { id, x, y } = data;
  if (id === localPlayerId) return; // never rewrite own position
  const p = gamePlayers.find(pl => pl.id === id);
  if (!p) return;
  if (isHostAuthority) {
    // Host: directly update remote player's position for authoritative combat resolution
    p.x = x; p.y = y;
  }
  // Non-host: ignore position relay — remote positions come from host snapshot only
  // This prevents two conflicting position sources from causing jitter
}

// Apply movement from a remote input object to a player (host-side)
function applyRemoteMovement(p, inp, dt) {
  if (!p.alive || p.stunned > 0 || p.isCraftingChair || p.isEatingChair || p.specialAiming) return;
  let dx = 0, dy = 0;
  const k = inp.keys || {};
  if (k['ArrowUp']   || k['w'] || k['W']) dy -= 1;
  if (k['ArrowDown'] || k['s'] || k['S']) dy += 1;
  if (k['ArrowLeft'] || k['a'] || k['A']) dx -= 1;
  if (k['ArrowRight']|| k['d'] || k['D']) dx += 1;
  if (dx === 0 && dy === 0) return;
  if (dx !== 0 && dy !== 0) { const len = Math.sqrt(2); dx /= len; dy /= len; }
  let speed = p.fighter.speed;
  if (p.unstableEyeTimer > 0) speed *= 1.3;
  // Cricket: Gear Up speed penalty
  if (p.gearUpTimer > 0) speed *= (p.fighter.abilities[2].speedPenalty || 0.6);
  // Deer: Fear speed boost (when moving away from feared enemy)
  if (p.deerFearTimer > 0 && p.fighter.id === 'deer') {
    const awayX = p.x - p.deerFearTargetX, awayY = p.y - p.deerFearTargetY;
    const dot = dx * awayX + dy * awayY;
    if (dot > 0) speed *= (p.fighter.abilities[1].speedBoost || 1.5);
  }
  // Deer: slower while building robot
  if (p.deerBuildSlowTimer > 0 && p.fighter && p.fighter.id === 'deer') {
    speed *= 0.6;
  }
  // Igloo slow: severely slow anyone inside an enemy igloo
  for (const owner of gamePlayers) {
    if (owner.iglooTimer > 0 && owner.id !== p.id) {
      const iglooAbil = owner.fighter && owner.fighter.abilities[4];
      const ir = ((iglooAbil ? iglooAbil.radius : 4.5) || 4.5) * GAME_TILE;
      const dxI = p.x - owner.iglooX, dyI = p.y - owner.iglooY;
      if (Math.sqrt(dxI * dxI + dyI * dyI) < ir) { speed *= 0.35; break; }
    }
  }
  // Cricket: wicket line speed boost
  if (p.wicketIds && p.wicketIds.length === 2) {
    const w0 = gamePlayers.find(pl => pl.id === p.wicketIds[0]);
    const w1 = gamePlayers.find(pl => pl.id === p.wicketIds[1]);
    if (w0 && w0.alive && w1 && w1.alive) {
      const lx = w1.x - w0.x, ly = w1.y - w0.y;
      const ll = lx * lx + ly * ly;
      if (ll > 0) {
        const t = Math.max(0, Math.min(1, ((p.x - w0.x) * lx + (p.y - w0.y) * ly) / ll));
        const cx = w0.x + t * lx, cy = w0.y + t * ly;
        const dd = Math.sqrt((p.x - cx) ** 2 + (p.y - cy) ** 2);
        if (dd < 1.5 * GAME_TILE) speed *= (p.fighter.abilities[3].speedBoost || 1.5);
      }
    }
  }
  const move = speed * dt * 60;
  const radius = GAME_TILE * PLAYER_RADIUS_RATIO;
  const newX = p.x + dx * move;
  const newY = p.y + dy * move;
  const prevX = p.x, prevY = p.y;
  if (canMoveTo(newX, p.y, radius)) p.x = newX;
  if (canMoveTo(p.x, newY, radius)) p.y = newY;

  // Igloo containment removed — igloo is now freely walkable (slow applied in speed calc)
}

// Apply an ability for a remote player (host-side) — swaps localPlayer context temporarily
function applyRemoteAbility(p, abilKey, inp) {
  // Temporarily swap localPlayer so useAbility() works for this player
  const savedLocal = localPlayer;
  const savedLocalId = localPlayerId;
  const savedMouseX = mouseX;
  const savedMouseY = mouseY;
  const savedMouseDown = mouseDown;
  localPlayer = p;
  localPlayerId = p.id;
  // Convert world-space aim coords to screen-space for useAbility
  const cw = gameCanvas.width, ch = gameCanvas.height;
  const camX = p.x - cw / 2, camY = p.y - ch / 2;
  mouseX = (inp.aimWorldX || 0) - camX;
  mouseY = (inp.aimWorldY || 0) - camY;
  mouseDown = inp.mouseDown || false;
  try { useAbility(abilKey); } catch(e) { /* ignore errors from remote ability */ }
  localPlayer = savedLocal;
  localPlayerId = savedLocalId;
  mouseX = savedMouseX;
  mouseY = savedMouseY;
  mouseDown = savedMouseDown;
}

function onPlayerMove(id, x, y, hp) {
  // Legacy handler — only used if host-authoritative is not active
  if (isHostAuthority) return;
  const p = gamePlayers.find((pl) => pl.id === id);
  if (p && p.id !== localPlayerId) {
    p.x = x; p.y = y;
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
