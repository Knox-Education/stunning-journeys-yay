/**
 * mantis.js – Mantis card game logic + renderer + SP controller.
 * Colors on cards, score 10 (or 15 in 2-player) to win.
 */

// ── Mantis Constants ─────────────────────────────────────────
const MANTIS_COLORS = ['red', 'blue', 'green', 'yellow', 'purple', 'orange'];
const MANTIS_COLOR_HEX = {
  red: '#e94560',
  blue: '#3498db',
  green: '#2ecc71',
  yellow: '#f5a623',
  purple: '#9b59b6',
  orange: '#e67e22',
};
const MANTIS_COLOR_EMOJI = {
  red: '🔴',
  blue: '🔵',
  green: '🟢',
  yellow: '🟡',
  purple: '🟣',
  orange: '🟠',
};

// ── Deck Builder ─────────────────────────────────────────────
function buildMantisDeck() {
  const deck = [];
  // 10 cards of each color = 60 cards total
  for (const color of MANTIS_COLORS) {
    for (let i = 0; i < 10; i++) {
      // Each card has a front color and 3 hint colors on the back (one is the real color)
      const hints = generateHints(color);
      deck.push({ color, hints });
    }
  }
  return shuffleMantisDeck(deck);
}

function generateHints(realColor) {
  const hints = new Set([realColor]);
  while (hints.size < 3) {
    hints.add(MANTIS_COLORS[Math.floor(Math.random() * MANTIS_COLORS.length)]);
  }
  // Shuffle the hints array
  return [...hints].sort(() => Math.random() - 0.5);
}

function shuffleMantisDeck(deck) {
  for (let i = deck.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [deck[i], deck[j]] = [deck[j], deck[i]];
  }
  return deck;
}

// ── Mantis Game State ────────────────────────────────────────
class MantisGame {
  constructor(players) {
    this.players = players; // [{id, name, isCPU}]
    this.tanks = {}; // id -> [card]
    this.scores = {}; // id -> [card]
    this.drawPile = [];
    this.currentPlayerIdx = 0;
    this.winner = null;
    this.winTarget = players.length === 2 ? 15 : 10;
    this.lastAction = null; // for display: {type, playerId, targetId, color, success}
    this.extraTurn = false;
    this.log = [];
  }

  setup() {
    this.drawPile = buildMantisDeck();
    this.players.forEach(p => {
      this.tanks[p.id] = [];
      this.scores[p.id] = [];
      // Deal 4 cards face-up to each tank
      for (let i = 0; i < 4; i++) {
        if (this.drawPile.length > 0) {
          this.tanks[p.id].push(this.drawPile.pop());
        }
      }
    });
    this.addLog('Game started!');
  }

  get currentPlayer() {
    return this.players[this.currentPlayerIdx];
  }

  addLog(msg) {
    this.log.push(msg);
    if (this.log.length > 30) this.log.shift();
  }

  // Score action: draw and try to match own tank
  score(playerId) {
    if (this.winner) return { success: false, reason: 'Game over' };
    if (this.currentPlayer.id !== playerId) return { success: false, reason: 'Not your turn' };
    if (this.drawPile.length === 0) return { success: false, reason: 'Deck empty' };

    const card = this.drawPile.pop();
    const tank = this.tanks[playerId];
    const matchCount = tank.filter(c => c.color === card.color).length;

    if (matchCount > 0) {
      // Match! Move all of that color + the drawn card to score pile
      const matched = tank.filter(c => c.color === card.color);
      this.tanks[playerId] = tank.filter(c => c.color !== card.color);
      this.scores[playerId].push(card, ...matched);
      this.addLog(`${this.getPlayerName(playerId)} scored ${matchCount + 1} ${card.color} cards!`);
      this.lastAction = { type: 'score', playerId, color: card.color, success: true, count: matchCount + 1 };
      this.checkWin(playerId);
      if (!this.winner) this.advanceTurn();
      return { success: true, matched: true, color: card.color, count: matchCount + 1, card };
    } else {
      // No match — card stays in tank
      this.tanks[playerId].push(card);
      this.addLog(`${this.getPlayerName(playerId)} drew ${card.color} — no match, added to tank.`);
      this.lastAction = { type: 'score', playerId, color: card.color, success: false };
      this.advanceTurn();
      return { success: true, matched: false, color: card.color, card };
    }
  }

  // Steal action: draw and try to match an opponent's tank
  steal(playerId, targetId) {
    if (this.winner) return { success: false, reason: 'Game over' };
    if (this.currentPlayer.id !== playerId) return { success: false, reason: 'Not your turn' };
    if (targetId === playerId) return { success: false, reason: "Can't steal from yourself" };
    if (this.drawPile.length === 0) return { success: false, reason: 'Deck empty' };

    const card = this.drawPile.pop();
    const targetTank = this.tanks[targetId];
    const matchCount = targetTank.filter(c => c.color === card.color).length;

    if (matchCount > 0) {
      // Successful steal! Take all matching cards from target's tank + the drawn card into your tank
      const stolen = targetTank.filter(c => c.color === card.color);
      this.tanks[targetId] = targetTank.filter(c => c.color !== card.color);
      this.tanks[playerId].push(card, ...stolen);
      this.addLog(`${this.getPlayerName(playerId)} stole ${matchCount + 1} ${card.color} cards from ${this.getPlayerName(targetId)}!`);
      this.lastAction = { type: 'steal', playerId, targetId, color: card.color, success: true, count: matchCount + 1 };
      // 2-player: successful steal grants extra turn
      if (this.players.length === 2) {
        this.extraTurn = true;
      }
      if (!this.extraTurn) this.advanceTurn();
      else this.extraTurn = false; // consume the extra turn (stay on same player)
      return { success: true, matched: true, color: card.color, count: matchCount + 1, card };
    } else {
      // Failed steal — card goes into target's tank
      this.tanks[targetId].push(card);
      this.addLog(`${this.getPlayerName(playerId)} failed to steal — gave ${this.getPlayerName(targetId)} a ${card.color} card.`);
      this.lastAction = { type: 'steal', playerId, targetId, color: card.color, success: false };
      this.advanceTurn();
      return { success: true, matched: false, color: card.color, card };
    }
  }

  advanceTurn() {
    if (this.winner) return;
    this.currentPlayerIdx = (this.currentPlayerIdx + 1) % this.players.length;
  }

  checkWin(playerId) {
    if (this.scores[playerId].length >= this.winTarget) {
      this.winner = this.players.find(p => p.id === playerId);
      this.addLog(`🎉 ${this.winner.name} wins with ${this.scores[playerId].length} scored cards!`);
    }
  }

  getPlayerName(id) {
    const p = this.players.find(p => p.id === id);
    return p ? p.name : 'Unknown';
  }

  // Get next card's back hints (visible to current player making a decision)
  peekNextCardHints() {
    if (this.drawPile.length === 0) return null;
    return this.drawPile[this.drawPile.length - 1].hints;
  }
}

// ── Mantis AI ────────────────────────────────────────────────
class MantisAI {
  static decide(game, playerId) {
    const tank = game.tanks[playerId];
    const hints = game.peekNextCardHints();
    if (!hints) return { action: 'score' }; // deck empty edge case

    const myColors = new Set(tank.map(c => c.color));
    const myColorCounts = {};
    tank.forEach(c => { myColorCounts[c.color] = (myColorCounts[c.color] || 0) + 1; });

    // Check which hint colors match my tank
    const matchesMyTank = hints.filter(h => myColors.has(h));
    // Check opponents for steal targets
    const opponents = game.players.filter(p => p.id !== playerId);
    let bestStealTarget = null;
    let bestStealScore = 0;

    for (const opp of opponents) {
      const oppTank = game.tanks[opp.id];
      const oppColors = {};
      oppTank.forEach(c => { oppColors[c.color] = (oppColors[c.color] || 0) + 1; });
      // How many hint colors match this opponent's tank?
      let hintMatches = 0;
      let totalStealpot = 0;
      for (const h of hints) {
        if (oppColors[h]) { hintMatches++; totalStealpot += oppColors[h]; }
      }
      const score = (hintMatches / 3) * totalStealpot;
      if (score > bestStealScore) {
        bestStealScore = score;
        bestStealTarget = opp.id;
      }
    }

    // Score value: probability of matching own tank × cards that would be scored
    let scoreValue = 0;
    for (const h of hints) {
      if (myColorCounts[h]) scoreValue += myColorCounts[h];
    }
    scoreValue = (matchesMyTank.length / 3) * scoreValue;

    // Prefer scoring if close to winning
    const myScoreCount = game.scores[playerId].length;
    if (myScoreCount >= game.winTarget - 3) scoreValue *= 1.5;

    // Prefer stealing if opponent has lots of cards
    if (bestStealTarget) {
      const oppTankSize = game.tanks[bestStealTarget].length;
      if (oppTankSize >= 5) bestStealScore *= 1.3;
    }

    if (scoreValue >= bestStealScore || !bestStealTarget) {
      return { action: 'score' };
    } else {
      return { action: 'steal', targetId: bestStealTarget };
    }
  }
}

// ── Mantis Renderer ──────────────────────────────────────────
class MantisRenderer {
  constructor(game, localPlayerId, onAction) {
    this.game = game;
    this.localPlayerId = localPlayerId;
    this.onAction = onAction;
  }

  render() {
    this.renderTurnInfo();
    this.renderOpponents();
    this.renderMyTank();
    this.renderNextCardHints();
    this.renderActions();
    this.renderLog();
    this.renderWinner();
  }

  renderTurnInfo() {
    const el = document.getElementById('mantis-turn-info');
    if (!el) return;
    if (this.game.winner) {
      el.textContent = `${this.game.winner.name} wins!`;
      el.style.color = '#2ecc71';
    } else if (this.game.currentPlayer.id === this.localPlayerId) {
      el.textContent = 'Your turn — Score or Steal?';
      el.style.color = '#2ecc71';
    } else {
      el.textContent = `${this.game.currentPlayer.name}'s turn...`;
      el.style.color = '#eee';
    }
    // Score display
    const scoreEl = document.getElementById('mantis-score-display');
    if (scoreEl) {
      const myScore = this.game.scores[this.localPlayerId].length;
      scoreEl.textContent = `Your Score: ${myScore} / ${this.game.winTarget}`;
    }
  }

  renderOpponents() {
    const area = document.getElementById('mantis-opponents');
    if (!area) return;
    area.innerHTML = '';
    this.game.players.forEach(p => {
      if (p.id === this.localPlayerId) return;
      const div = document.createElement('div');
      div.className = 'mantis-opponent' + (p.id === this.game.currentPlayer.id ? ' active-turn' : '');
      const tankCards = this.game.tanks[p.id] || [];
      const scoreCount = (this.game.scores[p.id] || []).length;
      div.innerHTML = `
        <div class="mantis-opp-header">
          <span class="mantis-opp-name">${this.escapeHtml(p.name)}${p.isCPU ? ' 🤖' : ''}</span>
          <span class="mantis-opp-score">Score: ${scoreCount}</span>
        </div>
        <div class="mantis-opp-tank">${this.renderTankCards(tankCards)}</div>
      `;
      // Click to steal from this opponent
      if (this.game.currentPlayer.id === this.localPlayerId && !this.game.winner) {
        div.addEventListener('click', () => this.onAction('steal', { targetId: p.id }));
        div.classList.add('mantis-stealable');
      }
      area.appendChild(div);
    });
  }

  renderMyTank() {
    const el = document.getElementById('mantis-my-tank');
    if (!el) return;
    const tank = this.game.tanks[this.localPlayerId] || [];
    el.innerHTML = `<div class="mantis-tank-label">Your Tank (${tank.length})</div>` + this.renderTankCards(tank);
  }

  renderTankCards(cards) {
    if (cards.length === 0) return '<span class="mantis-empty">empty</span>';
    // Group by color
    const groups = {};
    cards.forEach(c => {
      if (!groups[c.color]) groups[c.color] = 0;
      groups[c.color]++;
    });
    let html = '<div class="mantis-tank-cards">';
    for (const color in groups) {
      html += `<span class="mantis-color-chip" style="background:${MANTIS_COLOR_HEX[color]}">${groups[color]}</span>`;
    }
    html += '</div>';
    return html;
  }

  renderNextCardHints() {
    const el = document.getElementById('mantis-next-hints');
    if (!el) return;
    const hints = this.game.peekNextCardHints();
    if (!hints) {
      el.innerHTML = '<span style="color:#666">Deck empty</span>';
      return;
    }
    el.innerHTML = '<span class="mantis-hints-label">Next card could be:</span> ' +
      hints.map(h => `<span class="mantis-hint-chip" style="background:${MANTIS_COLOR_HEX[h]}">${h}</span>`).join(' ');
  }

  renderActions() {
    const btnScore = document.getElementById('btn-mantis-score');
    const el = document.getElementById('mantis-actions');
    if (btnScore) {
      const isMyTurn = this.game.currentPlayer.id === this.localPlayerId && !this.game.winner;
      btnScore.disabled = !isMyTurn;
      btnScore.style.opacity = isMyTurn ? '1' : '0.4';
    }
  }

  renderLog() {
    const logEl = document.getElementById('mantis-game-log');
    if (!logEl) return;
    logEl.innerHTML = '';
    const entries = this.game.log.slice(-8);
    entries.forEach(msg => {
      const div = document.createElement('div');
      div.className = 'mantis-log-entry';
      div.textContent = msg;
      logEl.appendChild(div);
    });
    logEl.scrollTop = logEl.scrollHeight;
  }

  renderWinner() {
    if (!this.game.winner) return;
    if (!this._winTracked) {
      this._winTracked = true;
      if (this.game.winner.id === this.localPlayerId && typeof trackMantisWinSP === 'function') {
        trackMantisWinSP();
      }
    }
    const modal = document.getElementById('mantis-modal');
    const content = document.getElementById('mantis-modal-content');
    if (modal && content) {
      content.innerHTML = `<h2>🎉 ${this.escapeHtml(this.game.winner.name)} wins!</h2><p>Score: ${this.game.scores[this.game.winner.id].length} cards</p><button class="menu-btn primary" id="btn-mantis-back-menu">Back to Menu</button>`;
      modal.classList.remove('hidden');
      setTimeout(() => {
        const btn = document.getElementById('btn-mantis-back-menu');
        if (btn) btn.addEventListener('click', () => this.onAction('exit'));
      }, 50);
    }
  }

  escapeHtml(str) {
    const div = document.createElement('div');
    div.textContent = str;
    return div.innerHTML;
  }
}

// ── Mantis Singleplayer Controller ───────────────────────────
let mantisGame = null;
let mantisRenderer = null;
let mantisCPUInterval = null;

function startMantisSingleplayer() {
  const players = [
    { id: 'human', name: 'You', isCPU: false },
    { id: 'cpu1', name: 'Mantis Bot 1', isCPU: true },
    { id: 'cpu2', name: 'Mantis Bot 2', isCPU: true },
  ];

  mantisGame = new MantisGame(players);
  mantisGame.setup();

  mantisRenderer = new MantisRenderer(mantisGame, 'human', handleMantisAction);
  mantisRenderer.render();

  if (mantisCPUInterval) clearInterval(mantisCPUInterval);
  mantisCPUInterval = setInterval(runMantisCPU, 1200);
}

function runMantisCPU() {
  if (!mantisGame || mantisGame.winner) {
    if (mantisCPUInterval) clearInterval(mantisCPUInterval);
    return;
  }
  const cp = mantisGame.currentPlayer;
  if (!cp || !cp.isCPU) return;

  const decision = MantisAI.decide(mantisGame, cp.id);
  if (decision.action === 'steal') {
    mantisGame.steal(cp.id, decision.targetId);
  } else {
    mantisGame.score(cp.id);
  }
  mantisRenderer.render();
}

function handleMantisAction(actionType, data) {
  if (!mantisGame || mantisGame.winner) return;

  switch (actionType) {
    case 'score': {
      if (mantisGame.currentPlayer.id !== 'human') return;
      mantisGame.score('human');
      mantisRenderer.render();
      break;
    }
    case 'steal': {
      if (mantisGame.currentPlayer.id !== 'human') return;
      if (!data || !data.targetId) return;
      mantisGame.steal('human', data.targetId);
      mantisRenderer.render();
      break;
    }
    case 'exit': {
      stopMantisGame();
      showScreen('screen-card-games');
      break;
    }
  }
}

function stopMantisGame() {
  if (mantisCPUInterval) { clearInterval(mantisCPUInterval); mantisCPUInterval = null; }
  mantisGame = null;
  mantisRenderer = null;
}
