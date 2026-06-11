// ═════════════════════════════════════════════════════════════
// CONSTANTS
// ═══════════════════════════════════════════════════════════════
const ADV_TILE = 80; // pixels per tile
const ADV_MAP_COLS = 20;
const ADV_MAP_ROWS = 15;
const ADV_ENEMY_SIGHT_RANGE = 6; // tiles — enemies start chasing when player is within this
const ADV_ENEMY_CHASE_SPEED = 3; // tiles per second (slower than player)

// Tile types
const ADV_TILES = {
  GRASS: 0,
  PATH: 1,
  WATER: 2,
  HOUSE: 3,
  TREE: 4,
  FENCE: 5,
  DOOR: 6,
  FLOWER: 7,
};

// North route map (20x15) — forest path with clearing for boss
const ADV_NORTH_MAP = [
  [4,4,4,4,4,4,0,0,0,0,0,0,0,0,4,4,4,4,4,4],
  [4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4],
  [4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4],
  [4,0,0,0,4,0,0,0,0,0,0,0,0,0,0,4,0,0,0,4],
  [4,0,0,4,4,0,0,0,0,0,0,0,0,0,0,4,4,0,0,4],
  [4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4],
  [4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4],
  [4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4],
  [4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4],
  [4,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,4],
  [4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4],
  [4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4],
  [4,4,4,0,0,0,0,0,0,1,1,0,0,0,0,0,0,4,4,4],
  [4,4,4,4,0,0,0,0,1,1,1,1,0,0,0,0,4,4,4,4],
  [4,4,4,4,4,0,0,0,1,1,1,1,0,0,0,4,4,4,4,4],
];

// Enemy definitions for north map
const ADV_NORTH_ENEMIES = [
  { id: 'enemy1', name: 'Shadow', x: 6, y: 5, patrol: [{x:6,y:5},{x:6,y:8}], isEnemy: true },
  { id: 'enemy2', name: 'Shadow', x: 13, y: 6, patrol: [{x:13,y:6},{x:13,y:9}], isEnemy: true },
  { id: 'enemy3', name: 'Dark Scout', x: 10, y: 3, patrol: [{x:8,y:3},{x:12,y:3}], isEnemy: true },
  { id: 'boss', name: 'GOREMAW', x: 10, y: 6, patrol: null, isEnemy: true, isBoss: true },
];

// Village map (20x15) — Pokemon GBA style town
const ADV_VILLAGE_MAP = [
  [4,4,4,4,4,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4],
  [4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4],
  [4,0,3,3,3,0,7,0,0,0,0,0,0,7,0,3,3,3,0,4],
  [4,0,3,3,3,0,0,0,0,0,0,0,0,0,0,3,3,3,0,4],
  [4,0,3,6,3,0,0,0,0,0,0,0,0,0,0,3,6,3,0,4],
  [4,0,0,1,0,0,7,0,0,0,0,0,0,7,0,0,1,0,0,4],
  [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
  [0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0],
  [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
  [4,0,0,1,0,0,7,0,0,0,0,0,0,7,0,0,1,0,0,4],
  [4,0,3,3,3,0,0,0,0,0,0,0,0,0,0,3,3,3,0,4],
  [4,0,3,3,3,0,0,0,0,0,0,0,0,0,0,3,3,3,0,4],
  [4,0,3,6,3,0,7,0,0,0,0,0,0,7,0,3,6,3,0,4],
  [4,4,0,1,0,0,0,0,0,2,2,0,0,0,0,0,1,0,4,4],
  [4,4,4,4,4,0,0,0,2,2,2,2,0,0,0,0,4,4,4,4],
];

// Tile colors (Pokemon GBA palette)
const ADV_TILE_COLORS = {
  [ADV_TILES.GRASS]:  '#58a858',
  [ADV_TILES.PATH]:   '#c8b878',
  [ADV_TILES.WATER]:  '#3890d8',
  [ADV_TILES.HOUSE]:  '#e8d8c0',
  [ADV_TILES.TREE]:   '#286828',
  [ADV_TILES.FENCE]:  '#c8b878',
  [ADV_TILES.DOOR]:   '#e8d8c0',
  [ADV_TILES.FLOWER]: '#58a858',
};

// ═══════════════════════════════════════════════════════════════
// PIXEL SPRITE GENERATION (detailed 32x32 retro humans)
// ═══════════════════════════════════════════════════════════════

// Each sprite is a 32x32 pixel grid
// Colors: 0=transparent, 1=skin, 2=hair, 3=shirt, 4=pants, 5=shoes, 6=outline/eyes
//         7=shirt shadow, 8=skin shadow, 9=hair highlight, A=belt

const SKIN_PALETTES = [
  '#f5c6a0', '#e8b090', '#d4956a', '#b07848', '#8b5e3c',
];
const HAIR_PALETTES = [
  '#3a2a1a', '#6b4423', '#c8a040', '#d44000', '#1a1a2a', '#f0e0c0',
];
const SHIRT_PALETTES = [
  '#4060c0', '#c04040', '#40a040', '#a040a0', '#e08020', '#20a0a0', '#e0e040',
];
const PANTS_PALETTES = [
  '#2a3a6a', '#4a3a2a', '#3a3a3a', '#1a4a1a', '#5a3a5a',
];

function darkenColor(hex, amount) {
  const r = Math.max(0, parseInt(hex.slice(1, 3), 16) - amount);
  const g = Math.max(0, parseInt(hex.slice(3, 5), 16) - amount);
  const b = Math.max(0, parseInt(hex.slice(5, 7), 16) - amount);
  return `rgb(${r},${g},${b})`;
}

function lightenColor(hex, amount) {
  const r = Math.min(255, parseInt(hex.slice(1, 3), 16) + amount);
  const g = Math.min(255, parseInt(hex.slice(3, 5), 16) + amount);
  const b = Math.min(255, parseInt(hex.slice(5, 7), 16) + amount);
  return `rgb(${r},${g},${b})`;
}

function generateNPCSprite(direction, palette, frame) {
  const canvas = document.createElement('canvas');
  canvas.width = 32;
  canvas.height = 32;
  const ctx = canvas.getContext('2d');

  const skin = palette.skin;
  const skinShd = darkenColor(palette.skin, 35);
  const hair = palette.hair;
  const hairHi = lightenColor(palette.hair, 50);
  const shirt = palette.shirt;
  const shirtShd = darkenColor(palette.shirt, 45);
  const shirtHi = lightenColor(palette.shirt, 35);
  const pants = palette.pants;
  const pantsShd = darkenColor(palette.pants, 35);
  const shoes = palette.shoes || '#2a2a2a';
  const outline = '#2a2a3a';
  const white = '#ffffff';
  const eyeColor = '#1a1a2a';

  const p = (x, y, w, h, color) => { ctx.fillStyle = color; ctx.fillRect(x, y, w, h); };

  if (direction === 'down') {
    // === LARGE HEAD (Pokemon chibi style) ===
    // Hair outline/volume
    p(8, 0, 16, 2, hair);
    p(7, 1, 18, 2, hair);
    p(6, 3, 20, 3, hair);
    p(7, 5, 18, 2, hair);
    // Hair highlight
    p(9, 1, 4, 2, hairHi);
    p(18, 2, 3, 2, hairHi);
    // Face
    p(8, 6, 16, 10, skin);
    p(7, 7, 18, 8, skin);
    // Forehead shadow
    p(8, 6, 16, 1, skinShd);
    // Eyes (large, Pokemon style: white + iris + pupil + shine)
    p(9, 8, 5, 5, white);
    p(18, 8, 5, 5, white);
    // Iris
    p(10, 9, 4, 4, '#3060a0');
    p(19, 9, 4, 4, '#3060a0');
    // Pupil
    p(11, 10, 2, 3, eyeColor);
    p(20, 10, 2, 3, eyeColor);
    // Eye shine
    p(12, 9, 1, 1, white);
    p(21, 9, 1, 1, white);
    // Nose
    p(15, 12, 2, 1, skinShd);
    // Mouth
    p(14, 14, 4, 1, darkenColor(palette.skin, 50));
    // Ears
    p(6, 9, 2, 3, skin);
    p(24, 9, 2, 3, skin);

    // === BODY (small/compact) ===
    // Neck
    p(14, 16, 4, 1, skin);
    // Torso
    p(10, 17, 12, 6, shirt);
    p(11, 17, 10, 2, shirtHi);
    p(10, 21, 12, 2, shirtShd);
    // Collar V
    p(14, 17, 4, 2, darkenColor(palette.shirt, 25));
    // Arms
    p(8, 18, 3, 5, shirt);
    p(21, 18, 3, 5, shirt);
    // Hands
    p(8, 22, 3, 2, skin);
    p(21, 22, 3, 2, skin);
    // Pants
    p(11, 23, 4, 4, pants);
    p(17, 23, 4, 4, pants);
    // Leg gap
    p(15, 24, 2, 3, 'rgba(0,0,0,0)');
    ctx.clearRect(15, 24, 2, 3);
    // Shoes
    if (frame === 1) {
      p(11, 27, 4, 3, pants);
      p(17, 23, 4, 3, pants);
      p(11, 29, 4, 2, shoes);
      p(17, 26, 4, 2, shoes);
    } else {
      p(11, 27, 4, 2, shoes);
      p(17, 27, 4, 2, shoes);
      p(10, 28, 5, 2, shoes);
      p(17, 28, 5, 2, shoes);
    }
  } else if (direction === 'up') {
    // Hair back (covers head)
    p(8, 0, 16, 2, hair);
    p(7, 1, 18, 2, hair);
    p(6, 3, 20, 5, hair);
    p(7, 7, 18, 5, hair);
    p(8, 11, 16, 4, hair);
    // Highlight
    p(9, 1, 4, 2, hairHi);
    p(19, 3, 3, 2, hairHi);
    // Ears
    p(6, 9, 2, 3, skin);
    p(24, 9, 2, 3, skin);
    // Neck
    p(14, 15, 4, 2, skin);
    // Torso
    p(10, 17, 12, 6, shirt);
    p(11, 17, 10, 2, shirtHi);
    p(10, 21, 12, 2, shirtShd);
    // Arms
    p(8, 18, 3, 5, shirt);
    p(21, 18, 3, 5, shirt);
    p(8, 22, 3, 2, skin);
    p(21, 22, 3, 2, skin);
    // Pants
    p(11, 23, 4, 4, pants);
    p(17, 23, 4, 4, pants);
    ctx.clearRect(15, 24, 2, 3);
    // Shoes
    if (frame === 1) {
      p(11, 23, 4, 5, pants);
      p(17, 23, 4, 3, pants);
      p(11, 28, 4, 2, shoes);
      p(17, 26, 4, 2, shoes);
    } else {
      p(11, 27, 4, 2, shoes);
      p(17, 27, 4, 2, shoes);
      p(10, 28, 5, 2, shoes);
      p(17, 28, 5, 2, shoes);
    }
  } else if (direction === 'left') {
    // Hair (side view, extends back)
    p(11, 0, 12, 2, hair);
    p(10, 1, 14, 2, hair);
    p(9, 3, 15, 4, hair);
    p(10, 6, 14, 2, hair);
    p(11, 1, 3, 2, hairHi);
    // Face (side profile)
    p(8, 6, 12, 10, skin);
    p(7, 8, 2, 5, skin);
    // Eye (one visible)
    p(9, 8, 4, 4, white);
    p(9, 9, 3, 3, '#3060a0');
    p(9, 10, 2, 2, eyeColor);
    p(11, 8, 1, 1, white);
    // Nose
    p(7, 11, 2, 2, skinShd);
    // Mouth
    p(9, 14, 3, 1, skinShd);
    // Ear
    p(20, 9, 2, 3, skin);
    // Neck
    p(13, 16, 4, 1, skin);
    // Torso
    p(10, 17, 10, 6, shirt);
    p(11, 17, 8, 2, shirtHi);
    p(10, 21, 10, 2, shirtShd);
    // Arm (in front)
    p(8, 18, 3, 5, shirt);
    p(8, 22, 3, 2, skin);
    // Pants
    p(11, 23, 8, 4, pants);
    p(11, 25, 8, 2, pantsShd);
    if (frame === 1) {
      p(11, 23, 4, 5, pants);
      p(15, 23, 4, 3, pants);
      p(11, 28, 4, 2, shoes);
      p(15, 26, 4, 2, shoes);
    } else {
      p(11, 27, 4, 2, shoes);
      p(15, 27, 4, 2, shoes);
    }
  } else { // right
    // Hair (side mirrored)
    p(9, 0, 12, 2, hair);
    p(8, 1, 14, 2, hair);
    p(8, 3, 15, 4, hair);
    p(8, 6, 14, 2, hair);
    p(18, 1, 3, 2, hairHi);
    // Face (side)
    p(12, 6, 12, 10, skin);
    p(23, 8, 2, 5, skin);
    // Eye
    p(19, 8, 4, 4, white);
    p(20, 9, 3, 3, '#3060a0');
    p(21, 10, 2, 2, eyeColor);
    p(20, 8, 1, 1, white);
    // Nose
    p(23, 11, 2, 2, skinShd);
    // Mouth
    p(20, 14, 3, 1, skinShd);
    // Ear
    p(10, 9, 2, 3, skin);
    // Neck
    p(15, 16, 4, 1, skin);
    // Torso
    p(12, 17, 10, 6, shirt);
    p(13, 17, 8, 2, shirtHi);
    p(12, 21, 10, 2, shirtShd);
    // Arm (in front)
    p(21, 18, 3, 5, shirt);
    p(21, 22, 3, 2, skin);
    // Pants
    p(13, 23, 8, 4, pants);
    p(13, 25, 8, 2, pantsShd);
    if (frame === 1) {
      p(17, 23, 4, 5, pants);
      p(13, 23, 4, 3, pants);
      p(17, 28, 4, 2, shoes);
      p(13, 26, 4, 2, shoes);
    } else {
      p(13, 27, 4, 2, shoes);
      p(17, 27, 4, 2, shoes);
    }
  }

  return canvas;
}

// ═══════════════════════════════════════════════════════════════
// NPC DEFINITIONS  
// ═══════════════════════════════════════════════════════════════

function createNPC(id, name, x, y, patrol, dialogue) {
  const skinIdx = Math.floor(Math.random() * SKIN_PALETTES.length);
  const hairIdx = Math.floor(Math.random() * HAIR_PALETTES.length);
  const shirtIdx = Math.floor(Math.random() * SHIRT_PALETTES.length);
  const pantsIdx = Math.floor(Math.random() * PANTS_PALETTES.length);

  return {
    id,
    name,
    x, y,
    startX: x, startY: y,
    direction: 'down',
    frame: 0,
    frameTimer: 0,
    patrol, // array of {x,y} waypoints, or null for stationary
    patrolIndex: 0, // current waypoint target
    patrolForward: true, // moving forward through waypoints
    pauseTimer: 0, // brief pause at endpoints
    moveProgress: 0,
    moving: false,
    targetX: x, targetY: y,
    palette: {
      skin: SKIN_PALETTES[skinIdx],
      hair: HAIR_PALETTES[hairIdx],
      shirt: SHIRT_PALETTES[shirtIdx],
      pants: PANTS_PALETTES[pantsIdx],
      shoes: '#2a2a2a',
    },
    dialogue: dialogue || "Hello, traveler!",
    sprites: null, // cached after first draw
  };
}

const ADV_NPCS_TEMPLATE = [
  { id: 'elder', name: 'Village Elder', x: 9, y: 7, patrol: null, dialogue: "A terrible monster guards the road to the north... It appeared one night and hasn't left since. I wonder... who could possibly defeat it?" },
  { id: 'merchant', name: 'Merchant', x: 5, y: 7, patrol: [{x:5,y:7},{x:5,y:5},{x:5,y:7},{x:8,y:7}], dialogue: "Business has been slow since that thing showed up to the north. Nobody dares to travel anymore." },
  { id: 'guard', name: 'Guard', x: 14, y: 7, patrol: [{x:14,y:7},{x:14,y:5},{x:14,y:7},{x:17,y:7}], dialogue: "I've seen the monster to the north... it's massive. I wouldn't go up there if I were you." },
  { id: 'child1', name: 'Kid', x: 9, y: 9, patrol: [{x:9,y:9},{x:11,y:9},{x:11,y:11},{x:9,y:11}], dialogue: "There's a scawy monster up north! Mommy says I can't go there!" },
  { id: 'farmer', name: 'Farmer', x: 6, y: 12, patrol: [{x:6,y:12},{x:6,y:9}], dialogue: "The crops are fine this year, at least. That monster up north hasn't bothered the fields... yet." },
  { id: 'fisher', name: 'Fisher', x: 8, y: 13, patrol: null, dialogue: "Fish aren't biting today... I think even they're scared of that thing to the north." },
  { id: 'smith', name: 'Blacksmith', x: 14, y: 9, patrol: [{x:14,y:9},{x:14,y:12}], dialogue: "I could forge you a blade, but would it even scratch that monster? Doubtful." },
  { id: 'woman1', name: 'Villager', x: 12, y: 5, patrol: [{x:12,y:5},{x:14,y:5}], dialogue: "It used to be peaceful here... now everyone's afraid to leave the village." },
];

// ═══════════════════════════════════════════════════════════════
// ADVENTURE GAME STATE
// ═══════════════════════════════════════════════════════════════

let advState = null;
let advCanvas = null;
let advCtx = null;
let advAnimId = null;
let advLastTime = 0;
let advDialogueBox = null;

function initAdventure() {
  advCanvas = document.getElementById('adventure-canvas');
  if (!advCanvas) return;
  advCanvas.width = ADV_MAP_COLS * ADV_TILE;
  advCanvas.height = ADV_MAP_ROWS * ADV_TILE;
  advCtx = advCanvas.getContext('2d');
  advCtx.imageSmoothingEnabled = false;

  // Create NPCs
  const npcs = ADV_NPCS_TEMPLATE.map(t => createNPC(t.id, t.name, t.x, t.y, t.patrol, t.dialogue));

  advState = {
    player: {
      x: 10, y: 7,
      direction: 'down',
      frame: 0,
      frameTimer: 0,
      moving: false,
      moveProgress: 0,
      targetX: 10, targetY: 7,
      hp: 100,
      maxHp: 100,
      atk: 20,
      palette: {
        skin: '#f5c6a0',
        hair: '#3a2a1a',
        shirt: '#d03030',
        pants: '#2a3a6a',
        shoes: '#2a2a2a',
      },
    },
    npcs,
    keys: { up: false, down: false, left: false, right: false },
    dialogue: null, // { text, name } or null
    currentMap: 'village',
    elderTalkedTo: false,
    glowTimer: 0,
    camera: { x: 10, y: 7 }, // camera center (in tile coords)
    combat: null, // { enemy, playerHp, enemyHp, enemyMaxHp, turn, log, animTimer, state }
  };

  // Cache NPC sprites
  for (const npc of advState.npcs) {
    cacheSprites(npc);
  }

  // Input
  advCanvas.tabIndex = 0;
  advCanvas.focus();
  document.addEventListener('keydown', advKeyDown);
  document.addEventListener('keyup', advKeyUp);

  advLastTime = performance.now();
  advLoop(advLastTime);
}

function cacheSprites(entity) {
  entity.sprites = {
    down: [generateNPCSprite('down', entity.palette, 0), generateNPCSprite('down', entity.palette, 1)],
    up: [generateNPCSprite('up', entity.palette, 0), generateNPCSprite('up', entity.palette, 1)],
    left: [generateNPCSprite('left', entity.palette, 0), generateNPCSprite('left', entity.palette, 1)],
    right: [generateNPCSprite('right', entity.palette, 0), generateNPCSprite('right', entity.palette, 1)],
  };
}

function stopAdventure() {
  if (advAnimId) { cancelAnimationFrame(advAnimId); advAnimId = null; }
  document.removeEventListener('keydown', advKeyDown);
  document.removeEventListener('keyup', advKeyUp);
  advState = null;
}

// ═══════════════════════════════════════════════════════════════
// INPUT
// ═══════════════════════════════════════════════════════════════

function advKeyDown(e) {
  if (!advState) return;
  // Combat input
  if (advState.combat) {
    if (e.key === 'z' || e.key === 'Z' || e.key === 'Enter' || e.key === ' ') {
      advCombatAction();
    } else if (e.key === 'x' || e.key === 'X') {
      advCombatDefend();
    }
    return;
  }
  if (advState.dialogue) {
    if (e.key === 'Enter' || e.key === ' ' || e.key === 'Escape' || e.key === 'z' || e.key === 'Z') {
      advState.dialogue = null;
    }
    return;
  }
  switch (e.key) {
    case 'ArrowUp': case 'w': case 'W': advState.keys.up = true; break;
    case 'ArrowDown': case 's': case 'S': advState.keys.down = true; break;
    case 'ArrowLeft': case 'a': case 'A': advState.keys.left = true; break;
    case 'ArrowRight': case 'd': case 'D': advState.keys.right = true; break;
    case 'Enter': case ' ': case 'z': case 'Z': advInteract(); break;
  }
}

function advKeyUp(e) {
  if (!advState) return;
  switch (e.key) {
    case 'ArrowUp': case 'w': case 'W': advState.keys.up = false; break;
    case 'ArrowDown': case 's': case 'S': advState.keys.down = false; break;
    case 'ArrowLeft': case 'a': case 'A': advState.keys.left = false; break;
    case 'ArrowRight': case 'd': case 'D': advState.keys.right = false; break;
  }
}

function advInteract() {
  if (!advState) return;
  if (advState.combat) {
    advCombatAction();
    return;
  }
  const p = advState.player;
  let fx = p.x, fy = p.y;
  if (p.direction === 'up') fy--;
  else if (p.direction === 'down') fy++;
  else if (p.direction === 'left') fx--;
  else if (p.direction === 'right') fx++;

  for (const npc of advState.npcs) {
    if (Math.round(npc.x) === fx && Math.round(npc.y) === fy) {
      npc.direction = getOppositeDir(p.direction);
      cacheSprites(npc);
      if (npc.id === 'elder' && !advState.elderTalkedTo) {
        advState.elderTalkedTo = true;
      }
      if (npc.isEnemy) {
        startCombat(npc);
      } else {
        advState.dialogue = { name: npc.name, text: npc.dialogue };
      }
      return;
    }
  }
}

function getOppositeDir(dir) {
  if (dir === 'up') return 'down';
  if (dir === 'down') return 'up';
  if (dir === 'left') return 'right';
  return 'left';
}

// ═══════════════════════════════════════════════════════════════
// GAME LOOP
// ═══════════════════════════════════════════════════════════════

function advLoop(timestamp) {
  if (!advState) return;
  const dt = Math.min((timestamp - advLastTime) / 1000, 0.1);
  advLastTime = timestamp;

  advUpdate(dt);
  advRender();

  advAnimId = requestAnimationFrame(advLoop);
}

// ═══════════════════════════════════════════════════════════════
// UPDATE
// ═══════════════════════════════════════════════════════════════

const ADV_MOVE_SPEED = 4; // tiles per second

function getCurrentMap() {
  if (!advState) return ADV_VILLAGE_MAP;
  return advState.currentMap === 'north' ? ADV_NORTH_MAP : ADV_VILLAGE_MAP;
}

function isTileWalkable(tx, ty) {
  if (tx < 0 || tx >= ADV_MAP_COLS) return false;
  // Allow walking off top/bottom edge for map transitions
  if (ty < 0 || ty >= ADV_MAP_ROWS) return true;
  const tile = getCurrentMap()[ty][tx];
  return tile === ADV_TILES.GRASS || tile === ADV_TILES.PATH || tile === ADV_TILES.FLOWER || tile === ADV_TILES.DOOR;
}

function isTileOccupiedByNPC(tx, ty, excludeId) {
  if (!advState) return false;
  for (const npc of advState.npcs) {
    if (npc.id === excludeId) continue;
    if (Math.round(npc.x) === tx && Math.round(npc.y) === ty) return true;
    if (npc.moving && Math.round(npc.targetX) === tx && Math.round(npc.targetY) === ty) return true;
  }
  // Check player
  const p = advState.player;
  if (Math.round(p.x) === tx && Math.round(p.y) === ty) return true;
  if (p.moving && Math.round(p.targetX) === tx && Math.round(p.targetY) === ty) return true;
  return false;
}

function advUpdate(dt) {
  if (advState.combat) {
    advState.combat.animTimer -= dt;
    return;
  }
  if (advState.dialogue) return;

  // Update player movement
  updateEntityMovement(advState.player, dt);

  // Start new player movement if not moving
  if (!advState.player.moving) {
    const keys = advState.keys;
    let dx = 0, dy = 0;
    if (keys.up) { dy = -1; advState.player.direction = 'up'; }
    else if (keys.down) { dy = 1; advState.player.direction = 'down'; }
    else if (keys.left) { dx = -1; advState.player.direction = 'left'; }
    else if (keys.right) { dx = 1; advState.player.direction = 'right'; }

    if (dx !== 0 || dy !== 0) {
      const tx = Math.round(advState.player.x) + dx;
      const ty = Math.round(advState.player.y) + dy;
      if (isTileWalkable(tx, ty) && !isTileOccupiedByNPC(tx, ty, null)) {
        advState.player.moving = true;
        advState.player.targetX = tx;
        advState.player.targetY = ty;
        advState.player.moveProgress = 0;
      }
    }
  }

  // Update NPCs
  for (const npc of advState.npcs) {
    updateEntityMovement(npc, dt);
    if (npc.isEnemy && !npc.dead) {
      updateEnemyAI(npc, dt);
    } else if (npc.patrol && !npc.moving) {
      if (npc.pauseTimer > 0) {
        npc.pauseTimer -= dt;
        continue;
      }
      advancePatrol(npc);
    }
  }

  // Glow timer
  advState.glowTimer += dt;

  // Smooth camera follow
  const camSpeed = 6;
  advState.camera.x += (advState.player.x - advState.camera.x) * camSpeed * dt;
  advState.camera.y += (advState.player.y - advState.camera.y) * camSpeed * dt;

  // Map transitions
  const p = advState.player;
  if (!p.moving) {
    if (advState.currentMap === 'village' && Math.round(p.y) < 0) {
      switchMap('north', Math.round(p.x), ADV_MAP_ROWS - 1);
    } else if (advState.currentMap === 'north' && Math.round(p.y) >= ADV_MAP_ROWS) {
      switchMap('village', Math.round(p.x), 0);
    }
  }
}

// ═══════════════════════════════════════════════════════════════
// ENEMY AI
// ═══════════════════════════════════════════════════════════════

function updateEnemyAI(npc, dt) {
  if (npc.moving) return;
  if (npc.pauseTimer > 0) {
    npc.pauseTimer -= dt;
    return;
  }

  const p = advState.player;
  const px = Math.round(p.x);
  const py = Math.round(p.y);
  const nx = Math.round(npc.x);
  const ny = Math.round(npc.y);
  const dist = Math.abs(px - nx) + Math.abs(py - ny);

  // If adjacent to player, start combat!
  if (dist <= 1) {
    startCombat(npc);
    return;
  }

  // If player is within sight range, chase them
  const sightRange = npc.isBoss ? 8 : ADV_ENEMY_SIGHT_RANGE;
  if (dist <= sightRange) {
    npc.chasing = true;
    chasePlayer(npc, px, py, nx, ny);
  } else {
    npc.chasing = false;
    // Fall back to patrol
    if (npc.patrol) {
      advancePatrol(npc);
    }
  }
}

function chasePlayer(npc, px, py, nx, ny) {
  // Move one step toward the player
  let dx = 0, dy = 0;
  const diffX = px - nx;
  const diffY = py - ny;

  // Prefer the axis with greater distance
  if (Math.abs(diffX) >= Math.abs(diffY)) {
    dx = diffX > 0 ? 1 : -1;
  } else {
    dy = diffY > 0 ? 1 : -1;
  }

  let tx = nx + dx;
  let ty = ny + dy;

  // If main direction is blocked, try the other axis
  if (!isTileWalkable(tx, ty) || isTileOccupiedByNPC(tx, ty, npc.id)) {
    if (dx !== 0) {
      dx = 0;
      dy = diffY > 0 ? 1 : (diffY < 0 ? -1 : 0);
    } else {
      dy = 0;
      dx = diffX > 0 ? 1 : (diffX < 0 ? -1 : 0);
    }
    tx = nx + dx;
    ty = ny + dy;
    if (!isTileWalkable(tx, ty) || isTileOccupiedByNPC(tx, ty, npc.id)) {
      npc.pauseTimer = 0.3;
      return;
    }
  }

  if (dx === 0 && dy === 0) return;

  // Set direction
  if (dx === 1) npc.direction = 'right';
  else if (dx === -1) npc.direction = 'left';
  else if (dy === 1) npc.direction = 'down';
  else if (dy === -1) npc.direction = 'up';

  npc.moving = true;
  npc.targetX = tx;
  npc.targetY = ty;
  npc.moveProgress = 0;
  cacheSprites(npc);
}

// ═══════════════════════════════════════════════════════════════
// COMBAT SYSTEM
// ═══════════════════════════════════════════════════════════════

function startCombat(enemy) {
  const enemyHp = enemy.isBoss ? 150 : 60;
  const enemyAtk = enemy.isBoss ? 25 : 12;
  advState.combat = {
    enemy,
    enemyName: enemy.name,
    playerHp: advState.player.hp,
    playerMaxHp: advState.player.maxHp,
    enemyHp,
    enemyMaxHp: enemyHp,
    enemyAtk,
    turn: 'player', // 'player' | 'enemy' | 'victory' | 'defeat'
    log: ['A wild ' + enemy.name + ' attacks!', '[Z] Attack  [X] Defend'],
    animTimer: 0,
    shakeTimer: 0,
    defending: false,
  };
}

function advCombatAction() {
  const c = advState.combat;
  if (!c || c.animTimer > 0) return;

  if (c.turn === 'victory' || c.turn === 'defeat') {
    endCombat();
    return;
  }

  if (c.turn === 'player') {
    // Player attacks
    const dmg = advState.player.atk + Math.floor(Math.random() * 8);
    c.enemyHp -= dmg;
    c.log = ['You deal ' + dmg + ' damage!'];
    c.shakeTimer = 0.2;
    c.animTimer = 0.5;

    if (c.enemyHp <= 0) {
      c.enemyHp = 0;
      c.turn = 'victory';
      c.log.push(c.enemyName + ' is defeated!');
    } else {
      c.turn = 'enemy';
      c.log.push('Enemy\'s turn...');
    }
    c.defending = false;
  }
}

function advCombatDefend() {
  const c = advState.combat;
  if (!c || c.animTimer > 0 || c.turn !== 'player') return;
  c.defending = true;
  c.log = ['You brace yourself!'];
  c.turn = 'enemy';
  c.animTimer = 0.5;
}

function advCombatEnemyTurn() {
  const c = advState.combat;
  if (!c || c.turn !== 'enemy') return;

  let dmg = c.enemyAtk + Math.floor(Math.random() * 6);
  if (c.defending) {
    dmg = Math.floor(dmg * 0.4);
    c.log = ['You block! Only ' + dmg + ' damage taken.'];
  } else {
    c.log = [c.enemyName + ' deals ' + dmg + ' damage!'];
  }
  c.playerHp -= dmg;
  c.shakeTimer = 0.2;
  c.animTimer = 0.5;
  c.defending = false;

  if (c.playerHp <= 0) {
    c.playerHp = 0;
    c.turn = 'defeat';
    c.log.push('You were defeated...');
  } else {
    c.turn = 'player';
    c.log.push('[Z] Attack  [X] Defend');
  }
}

function endCombat() {
  const c = advState.combat;
  if (c.turn === 'victory') {
    // Remove defeated enemy
    c.enemy.dead = true;
    advState.npcs = advState.npcs.filter(n => n.id !== c.enemy.id);
    advState.player.hp = Math.min(advState.player.maxHp, advState.player.hp + 20);
  } else {
    // Defeat: respawn in village with full HP
    advState.player.hp = advState.player.maxHp;
    switchMap('village', 10, 7);
  }
  advState.combat = null;
}

function switchMap(mapName, px, py) {
  advState.currentMap = mapName;
  advState.player.x = px;
  advState.player.y = py;
  advState.player.targetX = px;
  advState.player.targetY = py;
  advState.player.moving = false;
  advState.camera.x = px;
  advState.camera.y = py;

  // Load NPCs for the new map
  if (mapName === 'north') {
    advState.npcs = ADV_NORTH_ENEMIES.map(e => {
      const npc = createNPC(e.id, e.name, e.x, e.y, e.patrol, '');
      npc.isEnemy = true;
      npc.isBoss = !!e.isBoss;
      return npc;
    });
  } else {
    advState.npcs = ADV_NPCS_TEMPLATE.map(t => createNPC(t.id, t.name, t.x, t.y, t.patrol, t.dialogue));
  }
  for (const npc of advState.npcs) {
    cacheSprites(npc);
  }
}

function updateEntityMovement(entity, dt) {
  if (!entity.moving) return;

  const speed = (entity.isEnemy && entity.chasing) ? ADV_ENEMY_CHASE_SPEED : ADV_MOVE_SPEED;
  entity.moveProgress += dt * speed;
  entity.frameTimer += dt;
  if (entity.frameTimer > 0.2) {
    entity.frame = (entity.frame + 1) % 2;
    entity.frameTimer = 0;
  }

  if (entity.moveProgress >= 1) {
    entity.x = entity.targetX;
    entity.y = entity.targetY;
    entity.moving = false;
    entity.moveProgress = 0;
  } else {
    const startX = entity.targetX - (entity.direction === 'right' ? 1 : entity.direction === 'left' ? -1 : 0);
    const startY = entity.targetY - (entity.direction === 'down' ? 1 : entity.direction === 'up' ? -1 : 0);
    entity.x = startX + (entity.targetX - startX) * entity.moveProgress;
    entity.y = startY + (entity.targetY - startY) * entity.moveProgress;
  }
}

function advancePatrol(npc) {
  const waypoints = npc.patrol;
  if (!waypoints || waypoints.length < 2) return;

  // Get current target waypoint
  const target = waypoints[npc.patrolIndex];
  const cx = Math.round(npc.x);
  const cy = Math.round(npc.y);

  // Already at target waypoint? Move to next one
  if (cx === target.x && cy === target.y) {
    // Advance patrol index
    if (npc.patrolForward) {
      npc.patrolIndex++;
      if (npc.patrolIndex >= waypoints.length) {
        npc.patrolIndex = waypoints.length - 2;
        npc.patrolForward = false;
        npc.pauseTimer = 0.6; // Pause at endpoint
        return;
      }
    } else {
      npc.patrolIndex--;
      if (npc.patrolIndex < 0) {
        npc.patrolIndex = 1;
        npc.patrolForward = true;
        npc.pauseTimer = 0.6; // Pause at endpoint
        return;
      }
    }
  }

  // Move one step toward current waypoint
  const wp = waypoints[npc.patrolIndex];
  let dx = 0, dy = 0;
  if (wp.x > cx) dx = 1;
  else if (wp.x < cx) dx = -1;
  else if (wp.y > cy) dy = 1;
  else if (wp.y < cy) dy = -1;

  if (dx === 0 && dy === 0) return;

  const tx = cx + dx;
  const ty = cy + dy;

  if (!isTileWalkable(tx, ty) || isTileOccupiedByNPC(tx, ty, npc.id)) {
    npc.pauseTimer = 0.3;
    return;
  }

  // Set direction
  if (dx === 1) npc.direction = 'right';
  else if (dx === -1) npc.direction = 'left';
  else if (dy === 1) npc.direction = 'down';
  else if (dy === -1) npc.direction = 'up';

  npc.moving = true;
  npc.targetX = tx;
  npc.targetY = ty;
  npc.moveProgress = 0;
  cacheSprites(npc);
}

// ═══════════════════════════════════════════════════════════════
// RENDER
// ═══════════════════════════════════════════════════════════════

function advRender() {
  const ctx = advCtx;
  ctx.clearRect(0, 0, advCanvas.width, advCanvas.height);

  const map = getCurrentMap();

  // Camera offset: center camera on advState.camera position
  const camTileX = advState.camera.x;
  const camTileY = advState.camera.y;
  const viewTilesX = advCanvas.width / ADV_TILE;
  const viewTilesY = advCanvas.height / ADV_TILE;
  const offsetX = advCanvas.width / 2 - camTileX * ADV_TILE - ADV_TILE / 2;
  const offsetY = advCanvas.height / 2 - camTileY * ADV_TILE - ADV_TILE / 2;

  ctx.save();
  ctx.translate(Math.round(offsetX), Math.round(offsetY));

  // Determine visible tile range (with margin)
  const startCol = Math.max(0, Math.floor(camTileX - viewTilesX / 2) - 1);
  const endCol = Math.min(ADV_MAP_COLS - 1, Math.ceil(camTileX + viewTilesX / 2) + 1);
  const startRow = Math.max(0, Math.floor(camTileY - viewTilesY / 2) - 1);
  const endRow = Math.min(ADV_MAP_ROWS - 1, Math.ceil(camTileY + viewTilesY / 2) + 1);

  // Draw tiles
  for (let y = startRow; y <= endRow; y++) {
    for (let x = startCol; x <= endCol; x++) {
      const tile = map[y][x];
      const px = x * ADV_TILE;
      const py = y * ADV_TILE;
      ctx.fillStyle = ADV_TILE_COLORS[tile];
      ctx.fillRect(px, py, ADV_TILE, ADV_TILE);

      if (tile === ADV_TILES.GRASS) adv_drawGrass(ctx, px, py);
      else if (tile === ADV_TILES.TREE) adv_drawTree(ctx, px, py);
      else if (tile === ADV_TILES.FLOWER) adv_drawFlowers(ctx, px, py);
      else if (tile === ADV_TILES.WATER) adv_drawWater(ctx, px, py);
      else if (tile === ADV_TILES.HOUSE) adv_drawHouseWall(ctx, px, py);
      else if (tile === ADV_TILES.DOOR) adv_drawDoor(ctx, px, py);
      else if (tile === ADV_TILES.FENCE) adv_drawFence(ctx, px, py);
      else if (tile === ADV_TILES.PATH) adv_drawPath(ctx, px, py);
    }
  }

  // Draw NPCs (sorted by y for depth)
  const sortedNPCs = [...advState.npcs].sort((a, b) => a.y - b.y);
  for (const npc of sortedNPCs) {
    drawEntity(ctx, npc);
  }

  // Draw player as a dot
  drawPlayerDot(ctx);

  ctx.restore();

  // HUD (drawn in screen space, not world space)
  // HP bar
  drawPlayerHUD(ctx);

  // Draw dialogue box
  if (advState.dialogue) {
    adv_drawDialogue(ctx, advState.dialogue);
  }

  // Combat overlay
  if (advState.combat) {
    drawCombatOverlay(ctx);
  }

  // Map label
  ctx.fillStyle = '#fff';
  ctx.strokeStyle = '#000';
  ctx.lineWidth = 3;
  ctx.font = '14px "Press Start 2P", monospace';
  ctx.textAlign = 'left';
  const label = advState.currentMap === 'north' ? 'Northern Road' : 'Starter Village';
  ctx.strokeText(label, 20, 24);
  ctx.fillText(label, 20, 24);
}

function drawEntity(ctx, entity) {
  const screenX = entity.x * ADV_TILE + ADV_TILE / 2;
  const screenY = entity.y * ADV_TILE + ADV_TILE / 2;
  const size = entity.id === 'child1' ? ADV_TILE * 0.4 : ADV_TILE * 0.6;

  // Elder glow effect (before first talk)
  if (entity.id === 'elder' && advState && !advState.elderTalkedTo) {
    const glow = 0.3 + 0.2 * Math.sin(advState.glowTimer * 3);
    ctx.fillStyle = `rgba(255, 220, 80, ${glow})`;
    ctx.beginPath();
    ctx.arc(screenX, screenY, size * 1.2, 0, Math.PI * 2);
    ctx.fill();
  }

  // Shadow
  ctx.fillStyle = 'rgba(0,0,0,0.2)';
  ctx.beginPath();
  ctx.ellipse(screenX, screenY + size * 0.6, size * 0.6, size * 0.2, 0, 0, Math.PI * 2);
  ctx.fill();

  // Enemies are black, NPCs are grey
  const isEnemy = entity.isEnemy;
  const isBoss = entity.isBoss;

  // Pick shape based on NPC id hash
  const shapeIdx = entity.id.charCodeAt(0) % 3;
  ctx.fillStyle = isEnemy ? '#1a1a1a' : '#606060';
  ctx.strokeStyle = isEnemy ? '#000000' : '#303030';
  ctx.lineWidth = isBoss ? 3 : 2;

  // Boss is larger
  const drawSize = isBoss ? size * 2 : size;

  if (shapeIdx === 0) {
    // Circle
    ctx.beginPath();
    ctx.arc(screenX, screenY - drawSize * 0.1, drawSize * 0.5, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
  } else if (shapeIdx === 1) {
    // Square
    const s = drawSize * 0.8;
    ctx.fillRect(screenX - s / 2, screenY - s / 2 - drawSize * 0.1, s, s);
    ctx.strokeRect(screenX - s / 2, screenY - s / 2 - drawSize * 0.1, s, s);
  } else {
    // Triangle
    ctx.beginPath();
    ctx.moveTo(screenX, screenY - drawSize * 0.6);
    ctx.lineTo(screenX - drawSize * 0.5, screenY + drawSize * 0.3);
    ctx.lineTo(screenX + drawSize * 0.5, screenY + drawSize * 0.3);
    ctx.closePath();
    ctx.fill();
    ctx.stroke();
  }

  // Boss red eyes
  if (isBoss) {
    ctx.fillStyle = '#ff0000';
    ctx.beginPath();
    ctx.arc(screenX - drawSize * 0.15, screenY - drawSize * 0.15, drawSize * 0.08, 0, Math.PI * 2);
    ctx.fill();
    ctx.beginPath();
    ctx.arc(screenX + drawSize * 0.15, screenY - drawSize * 0.15, drawSize * 0.08, 0, Math.PI * 2);
    ctx.fill();
  }


  // Draw name above
  if (entity.name) {
    ctx.fillStyle = isEnemy ? '#ff4040' : '#fff';
    ctx.strokeStyle = '#000';
    ctx.lineWidth = 3;
    ctx.font = (isBoss ? '16' : '12') + 'px "Press Start 2P", monospace';
    ctx.textAlign = 'center';
    const nameY = screenY - drawSize * 0.8;
    ctx.strokeText(entity.name, screenX, nameY);
    ctx.fillText(entity.name, screenX, nameY);
    ctx.textAlign = 'left';
  }
}

function drawPlayerDot(ctx) {
  const p = advState.player;
  const screenX = p.x * ADV_TILE + ADV_TILE / 2;
  const screenY = p.y * ADV_TILE + ADV_TILE / 2;
  const radius = ADV_TILE * 0.3;

  // Shadow
  ctx.beginPath();
  ctx.ellipse(screenX, screenY + radius * 0.7, radius * 0.8, radius * 0.3, 0, 0, Math.PI * 2);
  ctx.fillStyle = 'rgba(0,0,0,0.3)';
  ctx.fill();

  // Main dot (Fighter red)
  ctx.beginPath();
  ctx.arc(screenX, screenY - radius * 0.2, radius, 0, Math.PI * 2);
  ctx.fillStyle = '#d03030';
  ctx.fill();
  ctx.strokeStyle = '#8b1a1a';
  ctx.lineWidth = 2;
  ctx.stroke();

  // Highlight
  ctx.beginPath();
  ctx.arc(screenX - radius * 0.3, screenY - radius * 0.5, radius * 0.3, 0, Math.PI * 2);
  ctx.fillStyle = 'rgba(255,255,255,0.4)';
  ctx.fill();


}

// ── Tile detail renderers ──────────────────────────────────────
const T = () => ADV_TILE; // shorthand

function adv_drawGrass(ctx, px, py) {
  const t = T();
  // Pokemon GBA grass - subtle two-tone pattern
  ctx.fillStyle = '#48a048';
  ctx.fillRect(px, py, t * 0.5, t * 0.5);
  ctx.fillRect(px + t * 0.5, py + t * 0.5, t * 0.5, t * 0.5);
  // Lighter accent spots
  ctx.fillStyle = '#68b868';
  ctx.fillRect(px + t * 0.1, py + t * 0.15, t * 0.08, t * 0.06);
  ctx.fillRect(px + t * 0.6, py + t * 0.7, t * 0.08, t * 0.06);
  ctx.fillRect(px + t * 0.75, py + t * 0.2, t * 0.06, t * 0.06);
  ctx.fillRect(px + t * 0.3, py + t * 0.8, t * 0.06, t * 0.06);
}

function adv_drawTree(ctx, px, py) {
  const t = T();
  // Pokemon GBA tree style - round dense canopy
  // Trunk
  ctx.fillStyle = '#685830';
  ctx.fillRect(px + t * 0.35, py + t * 0.65, t * 0.3, t * 0.35);
  ctx.fillStyle = '#584820';
  ctx.fillRect(px + t * 0.38, py + t * 0.7, t * 0.08, t * 0.2);

  // Canopy - large round shape (dark outer)
  ctx.fillStyle = '#186818';
  ctx.fillRect(px + t * 0.05, py + t * 0.15, t * 0.9, t * 0.55);
  ctx.fillRect(px + t * 0.15, py + t * 0.05, t * 0.7, t * 0.15);
  ctx.fillRect(px + t * 0.15, py + t * 0.65, t * 0.7, t * 0.1);

  // Mid green
  ctx.fillStyle = '#289828';
  ctx.fillRect(px + t * 0.1, py + t * 0.15, t * 0.7, t * 0.45);
  ctx.fillRect(px + t * 0.2, py + t * 0.08, t * 0.55, t * 0.12);

  // Light top highlight
  ctx.fillStyle = '#48c048';
  ctx.fillRect(px + t * 0.15, py + t * 0.1, t * 0.35, t * 0.2);
  ctx.fillRect(px + t * 0.2, py + t * 0.06, t * 0.25, t * 0.08);

  // Dark depth patches
  ctx.fillStyle = '#105810';
  ctx.fillRect(px + t * 0.5, py + t * 0.4, t * 0.25, t * 0.15);
  ctx.fillRect(px + t * 0.15, py + t * 0.5, t * 0.2, t * 0.12);
  ctx.fillRect(px + t * 0.6, py + t * 0.55, t * 0.2, t * 0.1);
}

function adv_drawFlowers(ctx, px, py) {
  const t = T();
  // Light grass base first
  ctx.fillStyle = '#48a048';
  ctx.fillRect(px, py, t * 0.5, t * 0.5);
  ctx.fillRect(px + t * 0.5, py + t * 0.5, t * 0.5, t * 0.5);
  // Simple Pokemon-style flower dots
  const flowers = [
    { x: 0.2, y: 0.2, color: '#f86868' },
    { x: 0.6, y: 0.15, color: '#f8f868' },
    { x: 0.8, y: 0.5, color: '#f868f8' },
    { x: 0.15, y: 0.65, color: '#f8f8f8' },
    { x: 0.5, y: 0.75, color: '#f86868' },
    { x: 0.75, y: 0.8, color: '#f8f868' },
  ];
  for (const f of flowers) {
    const s = t * 0.08;
    const fx = px + f.x * t;
    const fy = py + f.y * t;
    ctx.fillStyle = f.color;
    ctx.fillRect(fx, fy, s, s);
    ctx.fillRect(fx - s * 0.5, fy + s * 0.25, s * 0.5, s * 0.5);
    ctx.fillRect(fx + s, fy + s * 0.25, s * 0.5, s * 0.5);
    ctx.fillRect(fx + s * 0.25, fy - s * 0.5, s * 0.5, s * 0.5);
    ctx.fillRect(fx + s * 0.25, fy + s, s * 0.5, s * 0.5);
    ctx.fillStyle = '#f8e838';
    ctx.fillRect(fx + s * 0.25, fy + s * 0.25, s * 0.5, s * 0.5);
  }
}

function adv_drawWater(ctx, px, py) {
  const t = T();
  // Pokemon GBA water - darker blue with animated-style highlights
  ctx.fillStyle = '#2878c0';
  ctx.fillRect(px, py, t, t);
  // Wave pattern
  ctx.fillStyle = '#3890d8';
  ctx.fillRect(px + t * 0.05, py + t * 0.1, t * 0.3, t * 0.08);
  ctx.fillRect(px + t * 0.5, py + t * 0.35, t * 0.35, t * 0.06);
  ctx.fillRect(px + t * 0.15, py + t * 0.6, t * 0.25, t * 0.06);
  ctx.fillRect(px + t * 0.6, py + t * 0.75, t * 0.3, t * 0.06);
  // Bright highlights
  ctx.fillStyle = '#68c8f8';
  ctx.fillRect(px + t * 0.1, py + t * 0.12, t * 0.12, t * 0.04);
  ctx.fillRect(px + t * 0.55, py + t * 0.37, t * 0.1, t * 0.03);
  ctx.fillRect(px + t * 0.2, py + t * 0.62, t * 0.08, t * 0.03);
  ctx.fillRect(px + t * 0.7, py + t * 0.77, t * 0.1, t * 0.03);
}

function isHouseTile(tx, ty) {
  if (tx < 0 || ty < 0 || tx >= ADV_MAP_COLS || ty >= ADV_MAP_ROWS) return false;
  const t = getCurrentMap()[ty][tx];
  return t === ADV_TILES.HOUSE || t === ADV_TILES.DOOR;
}

function adv_drawHouseWall(ctx, px, py) {
  const t = T();
  const col = Math.round(px / t);
  const row = Math.round(py / t);
  const hasAbove = isHouseTile(col, row - 1);
  const hasBelow = isHouseTile(col, row + 1);
  const hasLeft = isHouseTile(col - 1, row);
  const hasRight = isHouseTile(col + 1, row);

  // Determine building color based on position (left buildings = brown roof, right = blue)
  const isLeftBuilding = col < 10;
  const roofColor = isLeftBuilding ? '#b04818' : '#3068a8';
  const roofHi = isLeftBuilding ? '#c86030' : '#4888c8';
  const roofShd = isLeftBuilding ? '#802810' : '#204880';

  // Clean wall (cream/white like GBA)
  ctx.fillStyle = '#f0e8d8';
  ctx.fillRect(px, py, t, t);

  // Top row = Roof
  if (!hasAbove) {
    // Roof fills the tile
    ctx.fillStyle = roofColor;
    ctx.fillRect(px, py, t, t);
    // Roof highlight (top half)
    ctx.fillStyle = roofHi;
    ctx.fillRect(px, py, t, t * 0.4);
    // Roof shadow (bottom edge)
    ctx.fillStyle = roofShd;
    ctx.fillRect(px, py + t * 0.8, t, t * 0.2);
    // Roof ridge lines
    ctx.fillStyle = roofShd;
    ctx.fillRect(px, py + t * 0.35, t, t * 0.04);
    ctx.fillRect(px, py + t * 0.6, t, t * 0.03);
    // Overhang shadow below
    ctx.fillStyle = 'rgba(0,0,0,0.25)';
    ctx.fillRect(px, py + t * 0.95, t, t * 0.05);
  } else {
    // Wall body
    ctx.fillStyle = '#f0e8d8';
    ctx.fillRect(px, py, t, t);
    // Subtle wall lines (paneling)
    ctx.fillStyle = '#e0d8c0';
    ctx.fillRect(px, py + t * 0.48, t, t * 0.03);
    // Wall shadow at bottom
    ctx.fillStyle = '#d8d0b8';
    ctx.fillRect(px, py + t * 0.85, t, t * 0.15);

    // Window (centered)
    if (!hasBelow || hasAbove) {
      ctx.fillStyle = '#58a8d8';
      ctx.fillRect(px + t * 0.25, py + t * 0.15, t * 0.5, t * 0.45);
      // Window frame
      ctx.fillStyle = '#f8f0e0';
      ctx.fillRect(px + t * 0.48, py + t * 0.15, t * 0.04, t * 0.45);
      ctx.fillRect(px + t * 0.25, py + t * 0.36, t * 0.5, t * 0.03);
      // Window border
      ctx.fillStyle = '#a89878';
      ctx.fillRect(px + t * 0.23, py + t * 0.13, t * 0.54, t * 0.03);
      ctx.fillRect(px + t * 0.23, py + t * 0.59, t * 0.54, t * 0.03);
      ctx.fillRect(px + t * 0.23, py + t * 0.13, t * 0.03, t * 0.49);
      ctx.fillRect(px + t * 0.74, py + t * 0.13, t * 0.03, t * 0.49);
      // Curtain hint
      ctx.fillStyle = '#f8e8c8';
      ctx.fillRect(px + t * 0.26, py + t * 0.16, t * 0.06, t * 0.18);
      ctx.fillRect(px + t * 0.68, py + t * 0.16, t * 0.06, t * 0.18);
    }
  }

  // Side edges
  if (!hasLeft) {
    ctx.fillStyle = 'rgba(0,0,0,0.08)';
    ctx.fillRect(px, py, t * 0.03, t);
  }
  if (!hasRight) {
    ctx.fillStyle = 'rgba(0,0,0,0.05)';
    ctx.fillRect(px + t * 0.97, py, t * 0.03, t);
  }
}

function adv_drawDoor(ctx, px, py) {
  const t = T();
  const col = Math.round(px / t);
  const isLeftBuilding = col < 10;
  const roofColor = isLeftBuilding ? '#b04818' : '#3068a8';

  // Wall background
  ctx.fillStyle = '#f0e8d8';
  ctx.fillRect(px, py, t, t);
  // Wall shadow at bottom
  ctx.fillStyle = '#d8d0b8';
  ctx.fillRect(px, py + t * 0.85, t, t * 0.15);
  // Wall panel line
  ctx.fillStyle = '#e0d8c0';
  ctx.fillRect(px, py + t * 0.48, t, t * 0.03);

  // Door (centered, tall)
  ctx.fillStyle = '#684818';
  ctx.fillRect(px + t * 0.25, py + t * 0.15, t * 0.5, t * 0.75);
  // Door lighter panel
  ctx.fillStyle = '#886830';
  ctx.fillRect(px + t * 0.3, py + t * 0.2, t * 0.4, t * 0.3);
  ctx.fillRect(px + t * 0.3, py + t * 0.55, t * 0.4, t * 0.28);
  // Door frame
  ctx.fillStyle = '#483010';
  ctx.fillRect(px + t * 0.23, py + t * 0.13, t * 0.54, t * 0.03);
  ctx.fillRect(px + t * 0.23, py + t * 0.13, t * 0.03, t * 0.78);
  ctx.fillRect(px + t * 0.74, py + t * 0.13, t * 0.03, t * 0.78);
  // Handle
  ctx.fillStyle = '#f8d838';
  ctx.fillRect(px + t * 0.6, py + t * 0.5, t * 0.06, t * 0.06);
  // Small awning/overhang colored like roof
  ctx.fillStyle = roofColor;
  ctx.fillRect(px + t * 0.15, py + t * 0.08, t * 0.7, t * 0.07);
  ctx.fillStyle = 'rgba(0,0,0,0.15)';
  ctx.fillRect(px + t * 0.15, py + t * 0.14, t * 0.7, t * 0.02);
  // Step
  ctx.fillStyle = '#a89878';
  ctx.fillRect(px + t * 0.2, py + t * 0.9, t * 0.6, t * 0.05);
}

function adv_drawFence(ctx, px, py) {
  const t = T();
  // Pokemon GBA style - path border/yard with fence posts
  // Grass base
  ctx.fillStyle = '#58a858';
  ctx.fillRect(px, py, t, t);
  ctx.fillStyle = '#48a048';
  ctx.fillRect(px, py, t * 0.5, t * 0.5);
  ctx.fillRect(px + t * 0.5, py + t * 0.5, t * 0.5, t * 0.5);

  // White picket fence (3 pickets + rails)
  const pickets = [0.15, 0.42, 0.7];
  // Rails
  ctx.fillStyle = '#e8e0d0';
  ctx.fillRect(px, py + t * 0.3, t, t * 0.06);
  ctx.fillRect(px, py + t * 0.6, t, t * 0.06);
  // Rail shadow
  ctx.fillStyle = '#c8c0b0';
  ctx.fillRect(px, py + t * 0.35, t, t * 0.02);
  ctx.fillRect(px, py + t * 0.65, t, t * 0.02);
  // Pickets
  for (const xp of pickets) {
    ctx.fillStyle = '#f8f0e8';
    ctx.fillRect(px + xp * t, py + t * 0.15, t * 0.12, t * 0.6);
    // Pointed top
    ctx.fillRect(px + xp * t + t * 0.02, py + t * 0.1, t * 0.08, t * 0.06);
    // Shadow
    ctx.fillStyle = '#d0c8b8';
    ctx.fillRect(px + xp * t + t * 0.09, py + t * 0.15, t * 0.03, t * 0.6);
  }
}

function adv_drawPath(ctx, px, py) {
  const t = T();
  // Pokemon GBA style path - packed earth/gravel
  ctx.fillStyle = '#b8a868';
  ctx.fillRect(px + t * 0.05, py + t * 0.1, t * 0.15, t * 0.08);
  ctx.fillRect(px + t * 0.55, py + t * 0.05, t * 0.12, t * 0.08);
  ctx.fillRect(px + t * 0.8, py + t * 0.4, t * 0.1, t * 0.06);
  ctx.fillRect(px + t * 0.2, py + t * 0.6, t * 0.12, t * 0.06);
  ctx.fillRect(px + t * 0.7, py + t * 0.75, t * 0.12, t * 0.06);
  // Slightly darker spots
  ctx.fillStyle = '#a89858';
  ctx.fillRect(px + t * 0.3, py + t * 0.3, t * 0.08, t * 0.06);
  ctx.fillRect(px + t * 0.1, py + t * 0.75, t * 0.08, t * 0.06);
  ctx.fillRect(px + t * 0.6, py + t * 0.5, t * 0.1, t * 0.04);
  // Edge darkening
  ctx.fillStyle = '#d8c888';
  ctx.fillRect(px, py, t, t * 0.02);
  ctx.fillRect(px, py + t * 0.98, t, t * 0.02);
}

// ── Dialogue box ──────────────────────────────────────────────

function adv_drawDialogue(ctx, dialogue) {
  const boxH = 200;
  const boxY = advCanvas.height - boxH - 20;
  const boxX = 20;
  const boxW = advCanvas.width - 40;

  // Background
  ctx.fillStyle = 'rgba(0, 0, 0, 0.9)';
  ctx.fillRect(boxX, boxY, boxW, boxH);
  // Border
  ctx.strokeStyle = '#f5a623';
  ctx.lineWidth = 3;
  ctx.strokeRect(boxX, boxY, boxW, boxH);

  // Name
  ctx.fillStyle = '#f5a623';
  ctx.font = '20px "Press Start 2P", monospace';
  ctx.fillText(dialogue.name, boxX + 20, boxY + 40);

  // Text
  ctx.fillStyle = '#fff';
  ctx.font = '16px "Press Start 2P", monospace';
  // Word wrap
  const words = dialogue.text.split(' ');
  let line = '';
  let lineY = boxY + 80;
  const maxW = boxW - 40;
  for (const word of words) {
    const test = line + (line ? ' ' : '') + word;
    if (ctx.measureText(test).width > maxW) {
      ctx.fillText(line, boxX + 20, lineY);
      line = word;
      lineY += 30;
    } else {
      line = test;
    }
  }
  ctx.fillText(line, boxX + 20, lineY);

  // Prompt
  ctx.fillStyle = '#888';
  ctx.font = '12px "Press Start 2P", monospace';
  ctx.fillText('[Z / ENTER to close]', boxX + boxW - 310, boxY + boxH - 16);
}

// ── Player HUD ────────────────────────────────────────────────

function drawPlayerHUD(ctx) {
  const p = advState.player;
  const barW = 200;
  const barH = 16;
  const barX = advCanvas.width - barW - 20;
  const barY = 12;

  // Background
  ctx.fillStyle = 'rgba(0,0,0,0.5)';
  ctx.fillRect(barX - 4, barY - 4, barW + 8, barH + 8);
  // Red bar
  ctx.fillStyle = '#333';
  ctx.fillRect(barX, barY, barW, barH);
  const hpRatio = Math.max(0, p.hp / p.maxHp);
  ctx.fillStyle = hpRatio > 0.5 ? '#30c030' : hpRatio > 0.25 ? '#e0c020' : '#d03030';
  ctx.fillRect(barX, barY, barW * hpRatio, barH);
  // Border
  ctx.strokeStyle = '#fff';
  ctx.lineWidth = 1;
  ctx.strokeRect(barX, barY, barW, barH);
  // Text
  ctx.fillStyle = '#fff';
  ctx.font = '10px "Press Start 2P", monospace';
  ctx.textAlign = 'center';
  ctx.fillText('HP ' + p.hp + '/' + p.maxHp, barX + barW / 2, barY + barH - 3);
  ctx.textAlign = 'left';
}

// ── Combat overlay ────────────────────────────────────────────

function drawCombatOverlay(ctx) {
  const c = advState.combat;
  const W = advCanvas.width;
  const H = advCanvas.height;

  // Darken background
  ctx.fillStyle = 'rgba(0, 0, 0, 0.7)';
  ctx.fillRect(0, 0, W, H);

  // Combat box
  const boxW = 700;
  const boxH = 400;
  const boxX = (W - boxW) / 2;
  const boxY = (H - boxH) / 2;

  ctx.fillStyle = '#1a1a2e';
  ctx.fillRect(boxX, boxY, boxW, boxH);
  ctx.strokeStyle = '#f5a623';
  ctx.lineWidth = 3;
  ctx.strokeRect(boxX, boxY, boxW, boxH);

  // Enemy name and sprite area
  ctx.fillStyle = '#ff4040';
  ctx.font = '20px "Press Start 2P", monospace';
  ctx.textAlign = 'center';
  const shake = c.shakeTimer > 0 ? (Math.random() - 0.5) * 8 : 0;
  ctx.fillText(c.enemyName, boxX + boxW / 2 + shake, boxY + 50);

  // Enemy shape (bigger version)
  const enemyDrawX = boxX + boxW / 2;
  const enemyDrawY = boxY + 130;
  const eSize = c.enemy.isBoss ? 80 : 50;
  ctx.fillStyle = '#1a1a1a';
  ctx.strokeStyle = '#000';
  ctx.lineWidth = 3;
  const shapeIdx = c.enemy.id.charCodeAt(0) % 3;
  if (shapeIdx === 0) {
    ctx.beginPath();
    ctx.arc(enemyDrawX + shake, enemyDrawY, eSize, 0, Math.PI * 2);
    ctx.fill(); ctx.stroke();
  } else if (shapeIdx === 1) {
    ctx.fillRect(enemyDrawX - eSize + shake, enemyDrawY - eSize, eSize * 2, eSize * 2);
    ctx.strokeRect(enemyDrawX - eSize + shake, enemyDrawY - eSize, eSize * 2, eSize * 2);
  } else {
    ctx.beginPath();
    ctx.moveTo(enemyDrawX + shake, enemyDrawY - eSize);
    ctx.lineTo(enemyDrawX - eSize + shake, enemyDrawY + eSize);
    ctx.lineTo(enemyDrawX + eSize + shake, enemyDrawY + eSize);
    ctx.closePath();
    ctx.fill(); ctx.stroke();
  }
  if (c.enemy.isBoss) {
    ctx.fillStyle = '#ff0000';
    ctx.beginPath();
    ctx.arc(enemyDrawX - eSize * 0.25 + shake, enemyDrawY - eSize * 0.1, eSize * 0.1, 0, Math.PI * 2);
    ctx.fill();
    ctx.beginPath();
    ctx.arc(enemyDrawX + eSize * 0.25 + shake, enemyDrawY - eSize * 0.1, eSize * 0.1, 0, Math.PI * 2);
    ctx.fill();
  }

  // Enemy HP bar
  const eBarW = 300;
  const eBarH = 18;
  const eBarX = boxX + (boxW - eBarW) / 2;
  const eBarY = boxY + 180;
  ctx.fillStyle = '#333';
  ctx.fillRect(eBarX, eBarY, eBarW, eBarH);
  const eHpRatio = Math.max(0, c.enemyHp / c.enemyMaxHp);
  ctx.fillStyle = '#d03030';
  ctx.fillRect(eBarX, eBarY, eBarW * eHpRatio, eBarH);
  ctx.strokeStyle = '#fff';
  ctx.lineWidth = 1;
  ctx.strokeRect(eBarX, eBarY, eBarW, eBarH);
  ctx.fillStyle = '#fff';
  ctx.font = '10px "Press Start 2P", monospace';
  ctx.fillText(c.enemyHp + '/' + c.enemyMaxHp, boxX + boxW / 2, eBarY + eBarH - 3);

  // Player section
  // Player dot
  const pDrawX = boxX + 100;
  const pDrawY = boxY + boxH - 100;
  ctx.beginPath();
  ctx.arc(pDrawX, pDrawY, 20, 0, Math.PI * 2);
  ctx.fillStyle = '#d03030';
  ctx.fill();
  ctx.strokeStyle = '#8b1a1a';
  ctx.lineWidth = 2;
  ctx.stroke();
  ctx.beginPath();
  ctx.arc(pDrawX - 6, pDrawY - 8, 6, 0, Math.PI * 2);
  ctx.fillStyle = 'rgba(255,255,255,0.4)';
  ctx.fill();

  // Player HP bar
  const pBarX = pDrawX + 40;
  const pBarY = pDrawY - 10;
  const pBarW = 250;
  const pBarH = 18;
  ctx.fillStyle = '#333';
  ctx.fillRect(pBarX, pBarY, pBarW, pBarH);
  const pHpRatio = Math.max(0, c.playerHp / c.playerMaxHp);
  ctx.fillStyle = pHpRatio > 0.5 ? '#30c030' : pHpRatio > 0.25 ? '#e0c020' : '#d03030';
  ctx.fillRect(pBarX, pBarY, pBarW * pHpRatio, pBarH);
  ctx.strokeStyle = '#fff';
  ctx.lineWidth = 1;
  ctx.strokeRect(pBarX, pBarY, pBarW, pBarH);
  ctx.fillStyle = '#fff';
  ctx.font = '10px "Press Start 2P", monospace';
  ctx.textAlign = 'center';
  ctx.fillText('HP ' + c.playerHp + '/' + c.playerMaxHp, pBarX + pBarW / 2, pBarY + pBarH - 3);

  // Combat log
  ctx.font = '14px "Press Start 2P", monospace';
  ctx.textAlign = 'center';
  for (let i = 0; i < c.log.length; i++) {
    ctx.fillStyle = i === 0 ? '#fff' : '#aaa';
    ctx.fillText(c.log[i], boxX + boxW / 2, boxY + 240 + i * 28);
  }

  ctx.textAlign = 'left';

  // Process enemy turn automatically after anim timer
  if (c.turn === 'enemy' && c.animTimer <= 0) {
    advCombatEnemyTurn();
  }
}
