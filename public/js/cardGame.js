/**
 * cardGame.js – Exploding Kittens card game logic + card game lobby management.
 * Handles both singleplayer (vs CPU) and multiplayer via socket.io.
 */

// ── Card Definitions ─────────────────────────────────────────
const EK_CARD_TYPES = {
  EXPLODING_KITTEN: 'exploding_kitten',
  DEFUSE: 'defuse',
  NOPE: 'nope',
  ATTACK: 'attack',
  SKIP: 'skip',
  SEE_THE_FUTURE: 'see_the_future',
  REVEAL_THE_FUTURE: 'reveal_the_future',
  SHUFFLE: 'shuffle',
  FAVOR: 'favor',
  DRAW_FROM_BOTTOM: 'draw_from_bottom',
  SELF_ATTACK: 'self_attack',
  CAT_TACO: 'cat_taco',
  CAT_MELON: 'cat_melon',
  CAT_POTATO: 'cat_potato',
  CAT_BEARD: 'cat_beard',
  CAT_RAINBOW: 'cat_rainbow',
};

const EK_CARD_DISPLAY = {
  exploding_kitten: { name: 'Exploding Kitten', emoji: '💣', color: '#e94560', desc: 'You explode unless you have a Defuse!' },
  defuse: { name: 'Defuse', emoji: '🛡️', color: '#2ecc71', desc: 'Saves you from an Exploding Kitten. Used automatically.' },
  nope: { name: 'Nope', emoji: '🚫', color: '#9b59b6', desc: 'Cancel any action played by another player.' },
  attack: { name: 'Attack', emoji: '⚔️', color: '#e67e22', desc: 'End your turn. Next player takes 2 turns.' },
  skip: { name: 'Skip', emoji: '⏭️', color: '#3498db', desc: 'End your turn without drawing a card.' },
  see_the_future: { name: 'See the Future', emoji: '🔮', color: '#1abc9c', desc: 'Privately peek at the top 2 cards of the draw pile.' },
  reveal_the_future: { name: 'Reveal the Future', emoji: '👁️', color: '#6c5ce7', desc: 'Reveal the top 3 cards to ALL players.' },
  shuffle: { name: 'Shuffle', emoji: '🔀', color: '#f5a623', desc: 'Shuffle the draw pile randomly.' },
  favor: { name: 'Favor', emoji: '🤲', color: '#fd79a8', desc: 'Force another player to give you a card of their choice.' },
  cat_taco: { name: 'Taco Cat', emoji: '🌮', color: '#e17055', desc: 'Play a matching pair to steal a random card from someone.' },
  cat_melon: { name: 'Melon Cat', emoji: '🍈', color: '#00b894', desc: 'Play a matching pair to steal a random card from someone.' },
  cat_potato: { name: 'Potato Cat', emoji: '🥔', color: '#fdcb6e', desc: 'Play a matching pair to steal a random card from someone.' },
  cat_beard: { name: 'Beard Cat', emoji: '🧔', color: '#6c5ce7', desc: 'Play a matching pair to steal a random card from someone.' },
  cat_rainbow: { name: 'Rainbow Cat', emoji: '🌈', color: '#a29bfe', desc: 'Play a matching pair to steal a random card from someone.' },
  draw_from_bottom: { name: 'Draw from Bottom', emoji: '⬇️', color: '#00cec9', desc: 'Draw from the bottom of the pile instead of the top.' },
  self_attack: { name: 'Self Attack', emoji: '🔄', color: '#d63031', desc: 'Take 2 extra turns yourself.' },
};

// ── Deck Builder ─────────────────────────────────────────────
function buildEKDeck(playerCount) {
  const deck = [];
  // 4 Attack, 4 Skip, 4 See the Future, 4 Shuffle, 4 Favor, 5 Nope
  for (let i = 0; i < 4; i++) {
    deck.push({ type: EK_CARD_TYPES.ATTACK });
    deck.push({ type: EK_CARD_TYPES.SKIP });
    deck.push({ type: EK_CARD_TYPES.SEE_THE_FUTURE });
    deck.push({ type: EK_CARD_TYPES.SHUFFLE });
    deck.push({ type: EK_CARD_TYPES.FAVOR });
  }
  for (let i = 0; i < 5; i++) deck.push({ type: EK_CARD_TYPES.NOPE });
  // 3 Reveal the Future
  for (let i = 0; i < 3; i++) deck.push({ type: EK_CARD_TYPES.REVEAL_THE_FUTURE });
  // 4 Draw from Bottom, 4 Self Attack
  for (let i = 0; i < 4; i++) deck.push({ type: EK_CARD_TYPES.DRAW_FROM_BOTTOM });
  for (let i = 0; i < 4; i++) deck.push({ type: EK_CARD_TYPES.SELF_ATTACK });
  // 4 of each cat type
  const catTypes = [EK_CARD_TYPES.CAT_TACO, EK_CARD_TYPES.CAT_MELON, EK_CARD_TYPES.CAT_POTATO, EK_CARD_TYPES.CAT_BEARD, EK_CARD_TYPES.CAT_RAINBOW];
  catTypes.forEach(ct => { for (let i = 0; i < 4; i++) deck.push({ type: ct }); });
  // Extra defuses: 6 total - playerCount (each player gets 1)
  const extraDefuses = Math.max(0, 6 - playerCount);
  for (let i = 0; i < extraDefuses; i++) deck.push({ type: EK_CARD_TYPES.DEFUSE });
  // Exploding Kittens: playerCount - 1
  for (let i = 0; i < playerCount - 1; i++) deck.push({ type: EK_CARD_TYPES.EXPLODING_KITTEN });
  return deck;
}

function shuffleDeck(deck) {
  for (let i = deck.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [deck[i], deck[j]] = [deck[j], deck[i]];
  }
  return deck;
}

// ── Exploding Kittens Game State ─────────────────────────────
class ExplodingKittensGame {
  constructor(players, isMultiplayer = false) {
    this.players = players; // [{id, name, isCPU}]
    this.hands = {}; // id -> [{type}]
    this.drawPile = [];
    this.discardPile = [];
    this.alive = new Set(players.map(p => p.id));
    this.currentPlayerIdx = 0;
    this.turnsRemaining = 1; // for attack stacking
    this.isMultiplayer = isMultiplayer;
    this.winner = null;
    this.pendingAction = null; // {type, data} for favor target selection, defuse placement, etc.
    this.lastPlayedCard = null;
    this.nopeWindow = false;
    this.nopeTimeout = null;
    this.pendingCardAction = null; // card action waiting for nope window
    this.log = [];
  }

  setup() {
    // Build deck without EK and Defuses
    let deck = buildEKDeck(this.players.length);
    // Separate out EK and Defuses from deck
    const ekCards = deck.filter(c => c.type === EK_CARD_TYPES.EXPLODING_KITTEN);
    const defuseExtras = deck.filter(c => c.type === EK_CARD_TYPES.DEFUSE);
    deck = deck.filter(c => c.type !== EK_CARD_TYPES.EXPLODING_KITTEN && c.type !== EK_CARD_TYPES.DEFUSE);
    shuffleDeck(deck);

    // Deal 6 cards + 1 Defuse to each player (7 total)
    this.players.forEach(p => {
      this.hands[p.id] = [];
      this.hands[p.id].push({ type: EK_CARD_TYPES.DEFUSE });
      for (let i = 0; i < 6; i++) {
        if (deck.length > 0) this.hands[p.id].push(deck.pop());
      }
    });

    // Shuffle extra Defuses + EKs back into the draw pile
    this.drawPile = [...deck, ...defuseExtras, ...ekCards];
    shuffleDeck(this.drawPile);
    this.discardPile = [];
    this.addLog('Game started!');
  }

  get currentPlayer() {
    return this.players[this.currentPlayerIdx];
  }

  getAlivePlayers() {
    return this.players.filter(p => this.alive.has(p.id));
  }

  addLog(msg) {
    this.log.push(msg);
    if (this.log.length > 50) this.log.shift();
  }

  // Play a card from hand
  playCard(playerId, cardIndex, extraData) {
    if (this.winner) return { success: false, reason: 'Game over' };
    if (this.pendingCardAction) return { success: false, reason: 'Waiting for Nope window' };
    const hand = this.hands[playerId];
    if (!hand || cardIndex < 0 || cardIndex >= hand.length) return { success: false, reason: 'Invalid card' };
    const card = hand[cardIndex];

    // Can't play Exploding Kitten from hand
    if (card.type === EK_CARD_TYPES.EXPLODING_KITTEN) return { success: false, reason: "Can't play Exploding Kitten" };
    // Can't play Defuse voluntarily (it auto-plays when you draw EK)
    if (card.type === EK_CARD_TYPES.DEFUSE && !this.pendingAction) return { success: false, reason: "Defuse is used automatically" };

    // Nope card — can only be played during someone else's nope window (handled by controller)
    if (card.type === EK_CARD_TYPES.NOPE) return { success: false, reason: "Nope can only be played during a Nope window" };

    // Cat card pairs
    if (card.type.startsWith('cat_')) {
      const pairIdx = hand.findIndex((c, i) => i !== cardIndex && c.type === card.type);
      if (pairIdx === -1) return { success: false, reason: 'Need a matching pair to play cat cards' };
      // Remove both
      const removedIndices = [cardIndex, pairIdx].sort((a, b) => b - a);
      removedIndices.forEach(i => hand.splice(i, 1));
      this.discardPile.push(card, { type: card.type });
      this.lastPlayedCard = card;
      this.addLog(`${this.getPlayerName(playerId)} played a pair of ${EK_CARD_DISPLAY[card.type].name}!`);
      // Defer resolution for nope window
      this.pendingCardAction = { playerId, card, action: 'steal_pick_target' };
      return { success: true, action: 'nope_window', card };
    }

    // Remove card from hand
    hand.splice(cardIndex, 1);
    this.discardPile.push(card);
    this.lastPlayedCard = card;

    // Check if this card should enter a nope window
    const nopeableTypes = [
      EK_CARD_TYPES.ATTACK, EK_CARD_TYPES.SKIP, EK_CARD_TYPES.SEE_THE_FUTURE,
      EK_CARD_TYPES.REVEAL_THE_FUTURE, EK_CARD_TYPES.SHUFFLE, EK_CARD_TYPES.FAVOR,
      EK_CARD_TYPES.DRAW_FROM_BOTTOM, EK_CARD_TYPES.SELF_ATTACK,
    ];
    if (nopeableTypes.includes(card.type)) {
      this.addLog(`${this.getPlayerName(playerId)} played ${EK_CARD_DISPLAY[card.type].name}!`);
      this.pendingCardAction = { playerId, card };
      return { success: true, action: 'nope_window', card };
    }

    return this.resolveCard(playerId, card, extraData);
  }

  // Play a Nope card during a nope window
  playNope(playerId) {
    if (!this.pendingCardAction) return { success: false, reason: 'No action to nope' };
    if (playerId === this.pendingCardAction.playerId) return { success: false, reason: "Can't nope your own card" };
    const hand = this.hands[playerId];
    if (!hand) return { success: false };
    const nopeIdx = hand.findIndex(c => c.type === EK_CARD_TYPES.NOPE);
    if (nopeIdx === -1) return { success: false, reason: "No Nope card in hand" };
    // Remove Nope from hand and discard
    hand.splice(nopeIdx, 1);
    this.discardPile.push({ type: EK_CARD_TYPES.NOPE });
    this.addLog(`${this.getPlayerName(playerId)} played Nope!`);
    // Cancel the pending action
    this.pendingCardAction = null;
    return { success: true, action: 'noped' };
  }

  // Resolve the pending card action after nope window expires
  resolveNopeWindow() {
    if (!this.pendingCardAction) return null;
    const { playerId, card, action } = this.pendingCardAction;
    this.pendingCardAction = null;
    if (action === 'steal_pick_target') {
      // Cat pair steal
      this.pendingAction = { type: 'steal', playerId };
      return { success: true, action: 'steal_pick_target' };
    }
    return this.resolveCard(playerId, card);
  }

  resolveCard(playerId, card, extraData) {
    const display = EK_CARD_DISPLAY[card.type];
    switch (card.type) {
      case EK_CARD_TYPES.ATTACK:
        this.turnsRemaining = 0;
        this.advanceTurn();
        this.turnsRemaining = 2;
        return { success: true, action: 'attack' };

      case EK_CARD_TYPES.SKIP:
        this.turnsRemaining--;
        if (this.turnsRemaining <= 0) {
          this.advanceTurn();
        }
        return { success: true, action: 'skip' };

      case EK_CARD_TYPES.SEE_THE_FUTURE:
        const top2 = this.drawPile.slice(-2).reverse();
        return { success: true, action: 'see_future', cards: top2 };

      case EK_CARD_TYPES.REVEAL_THE_FUTURE:
        const top3 = this.drawPile.slice(-3).reverse();
        return { success: true, action: 'reveal_future', cards: top3 };

      case EK_CARD_TYPES.SHUFFLE:
        shuffleDeck(this.drawPile);
        return { success: true, action: 'shuffle' };

      case EK_CARD_TYPES.FAVOR:
        this.pendingAction = { type: 'favor_pick_target', playerId };
        return { success: true, action: 'favor_pick_target' };

      case EK_CARD_TYPES.DRAW_FROM_BOTTOM:
        return this.drawFromBottom(playerId);

      case EK_CARD_TYPES.SELF_ATTACK:
        this.turnsRemaining += 2;
        return { success: true, action: 'self_attack' };

      case EK_CARD_TYPES.NOPE:
        return { success: true, action: 'nope' };

      default:
        return { success: true, action: 'played' };
    }
  }

  // Resolve favor: target gives a card
  resolveFavor(targetId, cardIndex) {
    if (!this.pendingAction || this.pendingAction.type !== 'favor_give') return { success: false };
    const targetHand = this.hands[targetId];
    if (!targetHand || cardIndex < 0 || cardIndex >= targetHand.length) return { success: false };
    const card = targetHand.splice(cardIndex, 1)[0];
    this.hands[this.pendingAction.playerId].push(card);
    this.addLog(`${this.getPlayerName(targetId)} gave a card to ${this.getPlayerName(this.pendingAction.playerId)}`);
    this.pendingAction = null;
    return { success: true };
  }

  // Resolve steal (cat pair): steal random card from target
  resolveSteal(targetId) {
    if (!this.pendingAction || this.pendingAction.type !== 'steal') return { success: false };
    const targetHand = this.hands[targetId];
    if (!targetHand || targetHand.length === 0) {
      this.addLog(`${this.getPlayerName(targetId)} has no cards to steal!`);
      this.pendingAction = null;
      return { success: true };
    }
    const rIdx = Math.floor(Math.random() * targetHand.length);
    const stolen = targetHand.splice(rIdx, 1)[0];
    this.hands[this.pendingAction.playerId].push(stolen);
    this.addLog(`${this.getPlayerName(this.pendingAction.playerId)} stole a card from ${this.getPlayerName(targetId)}!`);
    this.pendingAction = null;
    return { success: true, stolenType: stolen.type };
  }

  // Pick favor target
  pickFavorTarget(targetId) {
    if (!this.pendingAction || this.pendingAction.type !== 'favor_pick_target') return { success: false };
    if (!this.alive.has(targetId)) return { success: false };
    if (targetId === this.pendingAction.playerId) return { success: false, reason: "Can't favor yourself" };
    this.pendingAction = { type: 'favor_give', playerId: this.pendingAction.playerId, targetId };
    return { success: true, action: 'favor_give', targetId };
  }

  // Draw a card (end of turn action)
  drawCard(playerId) {
    if (this.winner) return { success: false, reason: 'Game over' };
    if (this.currentPlayer.id !== playerId) return { success: false, reason: 'Not your turn' };
    if (this.pendingAction) return { success: false, reason: 'Resolve pending action first' };

    if (this.drawPile.length === 0) {
      return { success: false, reason: 'Draw pile is empty' };
    }

    const card = this.drawPile.pop();

    if (card.type === EK_CARD_TYPES.EXPLODING_KITTEN) {
      // Check for Defuse
      const defuseIdx = this.hands[playerId].findIndex(c => c.type === EK_CARD_TYPES.DEFUSE);
      if (defuseIdx !== -1) {
        // Use Defuse
        this.hands[playerId].splice(defuseIdx, 1);
        this.discardPile.push({ type: EK_CARD_TYPES.DEFUSE });
        this.addLog(`${this.getPlayerName(playerId)} drew an Exploding Kitten but defused it!`);
        // Player must place EK back in draw pile
        this.pendingAction = { type: 'place_kitten', playerId, card };
        return { success: true, action: 'defused', card };
      } else {
        // Player explodes!
        this.addLog(`💥 ${this.getPlayerName(playerId)} drew an Exploding Kitten and EXPLODED!`);
        this.alive.delete(playerId);
        this.discardPile.push(card);
        // Discard their hand
        if (this.hands[playerId]) {
          this.discardPile.push(...this.hands[playerId]);
          this.hands[playerId] = [];
        }
        this.turnsRemaining = 0;
        this.advanceTurn();
        this.checkWin();
        return { success: true, action: 'exploded', card };
      }
    }

    // Normal card
    this.hands[playerId].push(card);
    this.turnsRemaining--;
    if (this.turnsRemaining <= 0) {
      this.advanceTurn();
    }
    return { success: true, action: 'drew', card };
  }

  // Draw from the bottom of the draw pile instead of the top
  drawFromBottom(playerId) {
    if (this.drawPile.length === 0) {
      return { success: true, action: 'draw_bottom_empty' };
    }
    const card = this.drawPile.shift(); // bottom = index 0

    if (card.type === EK_CARD_TYPES.EXPLODING_KITTEN) {
      const defuseIdx = this.hands[playerId].findIndex(c => c.type === EK_CARD_TYPES.DEFUSE);
      if (defuseIdx !== -1) {
        this.hands[playerId].splice(defuseIdx, 1);
        this.discardPile.push({ type: EK_CARD_TYPES.DEFUSE });
        this.addLog(`${this.getPlayerName(playerId)} drew an Exploding Kitten from the bottom but defused it!`);
        this.pendingAction = { type: 'place_kitten', playerId, card };
        return { success: true, action: 'defused', card };
      } else {
        this.addLog(`\ud83d\udca5 ${this.getPlayerName(playerId)} drew an Exploding Kitten from the bottom and EXPLODED!`);
        this.alive.delete(playerId);
        this.discardPile.push(card);
        if (this.hands[playerId]) {
          this.discardPile.push(...this.hands[playerId]);
          this.hands[playerId] = [];
        }
        this.turnsRemaining = 0;
        this.advanceTurn();
        this.checkWin();
        return { success: true, action: 'exploded', card };
      }
    }

    this.hands[playerId].push(card);
    this.turnsRemaining--;
    if (this.turnsRemaining <= 0) {
      this.advanceTurn();
    }
    return { success: true, action: 'drew_bottom', card };
  }

  // Place kitten back in draw pile at a position
  placeKitten(position) {
    if (!this.pendingAction || this.pendingAction.type !== 'place_kitten') return { success: false };
    const { card } = this.pendingAction;
    // Position 0 = top, drawPile.length = bottom
    const pos = Math.max(0, Math.min(position, this.drawPile.length));
    // Insert from the end (top is last element)
    const insertIdx = this.drawPile.length - pos;
    this.drawPile.splice(Math.max(0, insertIdx), 0, card);
    this.pendingAction = null;
    this.turnsRemaining--;
    if (this.turnsRemaining <= 0) {
      this.advanceTurn();
    }
    return { success: true };
  }

  advanceTurn() {
    const alivePlayers = this.getAlivePlayers();
    if (alivePlayers.length <= 1) return;
    let idx = this.currentPlayerIdx;
    do {
      idx = (idx + 1) % this.players.length;
    } while (!this.alive.has(this.players[idx].id));
    this.currentPlayerIdx = idx;
    this.turnsRemaining = Math.max(this.turnsRemaining, 1);
  }

  checkWin() {
    const alivePlayers = this.getAlivePlayers();
    if (alivePlayers.length === 1) {
      this.winner = alivePlayers[0];
      this.addLog(`🎉 ${this.winner.name} wins!`);
    }
  }

  getPlayerName(id) {
    const p = this.players.find(p => p.id === id);
    return p ? p.name : 'Unknown';
  }

  // Get state visible to a specific player
  getVisibleState(playerId) {
    return {
      players: this.players.map(p => ({
        id: p.id,
        name: p.name,
        alive: this.alive ? this.alive.has(p.id) : (p.alive !== undefined ? p.alive : true),
        handSize: (this.hands[p.id] || []).length || p.handSize || 0,
        isCPU: p.isCPU || false,
      })),
      myHand: this.hands[playerId] || [],
      drawPileSize: this.drawPile ? this.drawPile.length : (this.drawPileSize || 0),
      discardTop: this.discardPile && this.discardPile.length > 0 ? this.discardPile[this.discardPile.length - 1] : null,
      currentPlayerId: this.currentPlayer ? this.currentPlayer.id : null,
      turnsRemaining: this.turnsRemaining,
      pendingAction: this.pendingAction,
      winner: this.winner,
      log: this.log ? this.log.slice(-8) : [],
    };
  }
}

// ── CPU AI ───────────────────────────────────────────────────
class EKAI {
  static takeTurn(game, playerId) {
    const hand = game.hands[playerId];
    if (!hand || hand.length === 0) return { action: 'draw' };

    // Simple AI strategy:
    // 1. If has See the Future and draw pile has EK near top, play it
    // 2. If has Shuffle and suspects danger, use it
    // 3. If has Skip/Attack (20% chance to use if not needed)
    // 4. Otherwise draw

    const stfIdx = hand.findIndex(c => c.type === EK_CARD_TYPES.SEE_THE_FUTURE);
    const rtfIdx = hand.findIndex(c => c.type === EK_CARD_TYPES.REVEAL_THE_FUTURE);
    const shuffleIdx = hand.findIndex(c => c.type === EK_CARD_TYPES.SHUFFLE);
    const skipIdx = hand.findIndex(c => c.type === EK_CARD_TYPES.SKIP);
    const attackIdx = hand.findIndex(c => c.type === EK_CARD_TYPES.ATTACK);

    // Look ahead if we know top cards (AI cheats slightly — uses see_the_future proactively)
    const topCard = game.drawPile.length > 0 ? game.drawPile[game.drawPile.length - 1] : null;
    const dangerOnTop = topCard && topCard.type === EK_CARD_TYPES.EXPLODING_KITTEN;

    if (dangerOnTop) {
      // Definitely avoid drawing!
      if (shuffleIdx !== -1) return { action: 'play', cardIndex: shuffleIdx };
      if (skipIdx !== -1) return { action: 'play', cardIndex: skipIdx };
      if (attackIdx !== -1) return { action: 'play', cardIndex: attackIdx };
      // Check for cat pairs
      const pairIdx = EKAI.findCatPair(hand);
      if (pairIdx !== -1) return { action: 'play', cardIndex: pairIdx };
    }

    // Occasionally use See the Future / Reveal the Future
    if (stfIdx !== -1 && Math.random() < 0.3) return { action: 'play', cardIndex: stfIdx };
    if (rtfIdx !== -1 && Math.random() < 0.2) return { action: 'play', cardIndex: rtfIdx };

    // Random chance to play attack/skip
    if (attackIdx !== -1 && Math.random() < 0.15) return { action: 'play', cardIndex: attackIdx };
    if (skipIdx !== -1 && Math.random() < 0.15) return { action: 'play', cardIndex: skipIdx };

    return { action: 'draw' };
  }

  static findCatPair(hand) {
    const catCounts = {};
    hand.forEach((c, i) => {
      if (c.type.startsWith('cat_')) {
        if (!catCounts[c.type]) catCounts[c.type] = [];
        catCounts[c.type].push(i);
      }
    });
    for (const type in catCounts) {
      if (catCounts[type].length >= 2) return catCounts[type][0];
    }
    return -1;
  }

  // CPU picks a target for steal/favor
  static pickTarget(game, playerId) {
    const targets = game.getAlivePlayers().filter(p => p.id !== playerId && (game.hands[p.id] || []).length > 0);
    if (targets.length === 0) return null;
    // Pick the player with the most cards
    targets.sort((a, b) => (game.hands[b.id] || []).length - (game.hands[a.id] || []).length);
    return targets[0].id;
  }

  // CPU picks where to place a defused kitten
  static placementPosition(game) {
    // Place it near the bottom (harder for others)
    return Math.max(0, game.drawPile.length - 1);
  }

  // CPU picks which card to give for favor
  static pickCardToGive(hand) {
    // Give the least valuable card
    const priority = [
      EK_CARD_TYPES.CAT_TACO, EK_CARD_TYPES.CAT_MELON, EK_CARD_TYPES.CAT_POTATO,
      EK_CARD_TYPES.CAT_BEARD, EK_CARD_TYPES.CAT_RAINBOW,
      EK_CARD_TYPES.SHUFFLE, EK_CARD_TYPES.SKIP, EK_CARD_TYPES.SEE_THE_FUTURE,
      EK_CARD_TYPES.FAVOR, EK_CARD_TYPES.ATTACK, EK_CARD_TYPES.NOPE, EK_CARD_TYPES.DEFUSE,
    ];
    for (const type of priority) {
      const idx = hand.findIndex(c => c.type === type);
      if (idx !== -1) return idx;
    }
    return 0;
  }
}

// ── Card Game UI Renderer ────────────────────────────────────
class EKRenderer {
  constructor(game, localPlayerId, onAction) {
    this.game = game;
    this.localPlayerId = localPlayerId;
    this.onAction = onAction; // callback(actionType, data)
  }

  render() {
    const state = this.game.getVisibleState(this.localPlayerId);
    this.renderPlayers(state);
    this.renderHand(state);
    this.renderPlayArea(state);
    this.renderTopBar(state);
    this.renderLog(state);
    this.renderWinner(state);
  }

  renderLog(state) {
    const logEl = document.getElementById('ek-game-log');
    if (!logEl) return;
    logEl.innerHTML = '';
    if (state.log && state.log.length > 0) {
      state.log.forEach(msg => {
        const div = document.createElement('div');
        div.className = 'ek-log-entry';
        div.textContent = msg;
        logEl.appendChild(div);
      });
      logEl.scrollTop = logEl.scrollHeight;
    }
  }

  renderTopBar(state) {
    const drawCount = document.getElementById('ek-draw-pile-count');
    const turnInd = document.getElementById('ek-turn-indicator');
    if (drawCount) drawCount.textContent = `Draw: ${state.drawPileSize}`;
    if (turnInd) {
      if (state.winner) {
        turnInd.textContent = `${state.winner.name} wins!`;
      } else if (state.currentPlayerId === this.localPlayerId) {
        const extra = state.turnsRemaining > 1 ? ` (${state.turnsRemaining} turns)` : '';
        turnInd.textContent = `Your turn${extra}`;
        turnInd.style.color = '#2ecc71';
      } else {
        const cp = state.players.find(p => p.id === state.currentPlayerId);
        turnInd.textContent = `${cp ? cp.name : '?'}'s turn`;
        turnInd.style.color = '#eee';
      }
    }
  }

  renderPlayers(state) {
    const area = document.getElementById('ek-players-area');
    if (!area) return;
    area.innerHTML = '';
    state.players.forEach(p => {
      const div = document.createElement('div');
      div.className = 'ek-player-indicator' + (p.alive ? '' : ' dead') + (p.id === state.currentPlayerId ? ' active-turn' : '');
      div.innerHTML = `<span class="ek-player-name">${this.escapeHtml(p.name)}${p.isCPU ? ' 🤖' : ''}</span><span class="ek-player-cards">${p.alive ? p.handSize + ' cards' : '💀'}</span>`;
      area.appendChild(div);
    });
  }

  renderHand(state) {
    const handEl = document.getElementById('ek-hand');
    if (!handEl) return;
    handEl.innerHTML = '';
    if (!state.myHand) return;
    const inNopeWindow = !!this.game.pendingCardAction;
    state.myHand.forEach((card, idx) => {
      const cardEl = document.createElement('div');
      const display = EK_CARD_DISPLAY[card.type] || { name: card.type, emoji: '?', color: '#666', desc: '' };
      cardEl.className = 'ek-card';
      if (inNopeWindow && card.type === EK_CARD_TYPES.NOPE && this.game.pendingCardAction.playerId !== this.localPlayerId) {
        cardEl.classList.add('ek-card-nope-highlight');
      } else if (inNopeWindow && card.type !== EK_CARD_TYPES.NOPE) {
        cardEl.classList.add('ek-card-dimmed');
      }
      cardEl.style.borderColor = display.color;
      cardEl.innerHTML = `<span class="ek-card-emoji">${display.emoji}</span><span class="ek-card-name">${display.name}</span>`;
      cardEl.addEventListener('click', () => this.onAction('play_card', { cardIndex: idx }));
      handEl.appendChild(cardEl);
    });
  }

  renderPlayArea(state) {
    const discardTop = document.getElementById('ek-discard-top');
    if (discardTop) {
      if (state.discardTop) {
        const d = EK_CARD_DISPLAY[state.discardTop.type] || { emoji: '?', name: '?' };
        discardTop.innerHTML = `<span class="ek-card-emoji">${d.emoji}</span>`;
      } else {
        discardTop.innerHTML = '<span style="color:#555">Empty</span>';
      }
    }
    // Action prompt
    const prompt = document.getElementById('ek-action-prompt');
    if (prompt) {
      const isMyTurn = state.currentPlayerId === this.localPlayerId;
      const inNopeWindow = !!this.game.pendingCardAction;
      if (state.winner) {
        prompt.textContent = '';
      } else if (inNopeWindow) {
        const pca = this.game.pendingCardAction;
        const cardName = EK_CARD_DISPLAY[pca.card.type] ? EK_CARD_DISPLAY[pca.card.type].name : pca.card.type;
        if (pca.playerId === this.localPlayerId) {
          prompt.textContent = `🚫 Nope window... (${cardName})`;
        } else {
          prompt.textContent = `🚫 Click NOPE to cancel ${this.game.getPlayerName(pca.playerId)}'s ${cardName}!`;
        }
        prompt.style.color = '#9b59b6';
      } else if (state.pendingAction) {
        prompt.style.color = '#f5a623';
        const pa = state.pendingAction;
        if (pa.type === 'place_kitten' && pa.playerId === this.localPlayerId) {
          prompt.textContent = '📍 Place the Exploding Kitten back in the draw pile';
        } else if (pa.type === 'steal' && pa.playerId === this.localPlayerId) {
          prompt.textContent = '🎯 Pick a player to steal a random card from';
        } else if (pa.type === 'favor_pick_target' && pa.playerId === this.localPlayerId) {
          prompt.textContent = '🎯 Pick a player to give you a card';
        } else if (pa.type === 'favor_give' && pa.targetId === this.localPlayerId) {
          prompt.textContent = '🤲 Choose a card from your hand to give away';
        } else {
          prompt.textContent = '⏳ Waiting for another player...';
        }
      } else if (isMyTurn) {
        prompt.style.color = '#f5a623';
        prompt.textContent = '🃏 Play a card or draw from the pile';
      } else {
        prompt.style.color = '#f5a623';
        const cp = state.players.find(p => p.id === state.currentPlayerId);
        prompt.textContent = `⏳ ${cp ? cp.name : '?'} is thinking...`;
      }
    }
    // Draw button state
    const drawBtn = document.getElementById('btn-ek-draw');
    if (drawBtn) {
      const isMyTurn = state.currentPlayerId === this.localPlayerId;
      const inNopeWindow = !!this.game.pendingCardAction;
      drawBtn.disabled = !isMyTurn || !!state.pendingAction || !!state.winner || inNopeWindow;
      drawBtn.style.opacity = drawBtn.disabled ? '0.4' : '1';
    }
  }

  renderWinner(state) {
    if (state.winner) {
      if (!this._winTracked) {
        this._winTracked = true;
        if (state.winner.id === this.localPlayerId) {
          if (this.game.isMultiplayer && typeof trackEKWinMP === 'function') trackEKWinMP();
          else if (!this.game.isMultiplayer && typeof trackEKWinSP === 'function') trackEKWinSP();
        }
      }
      this.showModal(`<h2>🎉 ${this.escapeHtml(state.winner.name)} wins!</h2><button class="menu-btn primary" id="btn-ek-back-to-menu">Back to Menu</button>`);
      setTimeout(() => {
        const btn = document.getElementById('btn-ek-back-to-menu');
        if (btn) btn.addEventListener('click', () => this.onAction('exit'));
      }, 50);
    }
  }

  showModal(html) {
    const modal = document.getElementById('ek-modal');
    const content = document.getElementById('ek-modal-content');
    if (modal && content) {
      content.innerHTML = html;
      modal.classList.remove('hidden');
    }
  }

  hideModal() {
    const modal = document.getElementById('ek-modal');
    if (modal) modal.classList.add('hidden');
  }

  showSeeFuture(cards) {
    const el = document.getElementById('ek-see-future');
    const cardsEl = document.getElementById('ek-future-cards');
    if (!el || !cardsEl) return;
    cardsEl.innerHTML = '';
    cards.forEach((c, i) => {
      const d = EK_CARD_DISPLAY[c.type] || { emoji: '?', name: '?', color: '#666' };
      cardsEl.innerHTML += `<div class="ek-future-card" style="border-color:${d.color}"><span>${d.emoji}</span><small>${d.name}</small><small class="ek-future-pos">#${i + 1}</small></div>`;
    });
    el.classList.remove('hidden');
  }

  showTargetPicker(targets, promptText, onPick) {
    let html = `<h3>${promptText}</h3><div class="ek-target-list">`;
    targets.forEach(t => {
      html += `<button class="menu-btn primary ek-target-btn" data-target="${t.id}">${this.escapeHtml(t.name)}</button>`;
    });
    html += '</div>';
    this.showModal(html);
    setTimeout(() => {
      document.querySelectorAll('.ek-target-btn').forEach(btn => {
        btn.addEventListener('click', () => {
          this.hideModal();
          onPick(btn.dataset.target);
        });
      });
    }, 50);
  }

  showPlaceKitten(maxPos) {
    let html = `<h3>Place the Exploding Kitten back in the draw pile</h3><p>0 = top, ${maxPos} = bottom</p><div class="ek-place-controls">`;
    html += `<input type="range" id="ek-place-slider" min="0" max="${maxPos}" value="0" style="width:200px;"/>`;
    html += `<span id="ek-place-val">0</span>`;
    html += `<button class="menu-btn primary" id="btn-ek-place">Place</button></div>`;
    this.showModal(html);
    setTimeout(() => {
      const slider = document.getElementById('ek-place-slider');
      const valSpan = document.getElementById('ek-place-val');
      if (slider && valSpan) {
        slider.addEventListener('input', () => { valSpan.textContent = slider.value; });
      }
      const placeBtn = document.getElementById('btn-ek-place');
      if (placeBtn) {
        placeBtn.addEventListener('click', () => {
          this.hideModal();
          this.onAction('place_kitten', { position: parseInt(slider.value) });
        });
      }
    }, 50);
  }

  showFavorGive(hand) {
    let html = `<h3>Choose a card to give</h3><div class="ek-favor-hand">`;
    hand.forEach((c, i) => {
      const d = EK_CARD_DISPLAY[c.type] || { emoji: '?', name: '?', color: '#666' };
      html += `<div class="ek-card ek-favor-card" data-idx="${i}" style="border-color:${d.color}"><span class="ek-card-emoji">${d.emoji}</span><span class="ek-card-name">${d.name}</span></div>`;
    });
    html += '</div>';
    this.showModal(html);
    setTimeout(() => {
      document.querySelectorAll('.ek-favor-card').forEach(el => {
        el.addEventListener('click', () => {
          this.hideModal();
          this.onAction('favor_give', { cardIndex: parseInt(el.dataset.idx) });
        });
      });
    }, 50);
  }

  escapeHtml(str) {
    const div = document.createElement('div');
    div.textContent = str;
    return div.innerHTML;
  }
}

// ── Singleplayer Controller ──────────────────────────────────
let ekGame = null;
let ekRenderer = null;
let ekCPUInterval = null;
let ekNopeTimeout = null;

function startEKSingleplayer() {
  const playerCount = 4; // 1 human + 3 CPU
  const players = [
    { id: 'human', name: 'You', isCPU: false },
    { id: 'cpu1', name: 'Bot Alpha', isCPU: true },
    { id: 'cpu2', name: 'Bot Beta', isCPU: true },
    { id: 'cpu3', name: 'Bot Gamma', isCPU: true },
  ];

  ekGame = new ExplodingKittensGame(players, false);
  ekGame.setup();

  ekRenderer = new EKRenderer(ekGame, 'human', handleEKAction);
  ekRenderer.render();

  // CPU turn loop
  if (ekCPUInterval) clearInterval(ekCPUInterval);
  ekCPUInterval = setInterval(runCPUTurn, 1500);
}

// Start the 2-second nope window after a card is played
function startNopeWindow(cardPlayerId) {
  if (ekNopeTimeout) clearTimeout(ekNopeTimeout);
  ekRenderer.render();
  // CPU evaluates whether to nope (random delay 0.5-1.5s)
  const cpuPlayers = ekGame.getAlivePlayers().filter(p => p.isCPU && p.id !== cardPlayerId);
  for (const cpu of cpuPlayers) {
    const hand = ekGame.hands[cpu.id];
    if (!hand) continue;
    const hasNope = hand.some(c => c.type === EK_CARD_TYPES.NOPE);
    if (hasNope && Math.random() < 0.25) {
      // CPU decides to nope
      const delay = 500 + Math.random() * 1000;
      setTimeout(() => {
        if (!ekGame || !ekGame.pendingCardAction) return;
        const res = ekGame.playNope(cpu.id);
        if (res.success) {
          ekGame.addLog(`🚫 ${ekGame.getPlayerName(cpu.id)} NOPED it!`);
          if (ekNopeTimeout) { clearTimeout(ekNopeTimeout); ekNopeTimeout = null; }
          ekRenderer.render();
        }
      }, delay);
      return; // Only one CPU attempts to nope
    }
  }
  // No CPU will nope — set timer to resolve
  ekNopeTimeout = setTimeout(() => {
    resolveAfterNopeWindow(cardPlayerId);
  }, 2000);
}

function resolveAfterNopeWindow(cardPlayerId) {
  ekNopeTimeout = null;
  if (!ekGame || !ekGame.pendingCardAction) return;
  const result = ekGame.resolveNopeWindow();
  if (!result) return;
  // Handle the resolved action
  if (result.action === 'see_future' && cardPlayerId === 'human') {
    ekRenderer.showSeeFuture(result.cards);
  } else if (result.action === 'reveal_future') {
    ekRenderer.showSeeFuture(result.cards);
  } else if (result.action === 'steal_pick_target' && cardPlayerId === 'human') {
    const targets = ekGame.getAlivePlayers().filter(p => p.id !== 'human');
    ekRenderer.showTargetPicker(targets, 'Steal a random card from:', (targetId) => {
      ekGame.resolveSteal(targetId);
      ekRenderer.render();
    });
  } else if (result.action === 'steal_pick_target' && cardPlayerId !== 'human') {
    // CPU resolves steal
    const target = EKAI.pickTarget(ekGame, cardPlayerId);
    if (target) ekGame.resolveSteal(target);
    else ekGame.pendingAction = null;
  } else if (result.action === 'favor_pick_target' && cardPlayerId === 'human') {
    const targets = ekGame.getAlivePlayers().filter(p => p.id !== 'human' && (ekGame.hands[p.id] || []).length > 0);
    ekRenderer.showTargetPicker(targets, 'Pick a player to give you a card:', (targetId) => {
      ekGame.pickFavorTarget(targetId);
      const cpuHand = ekGame.hands[targetId];
      if (cpuHand && cpuHand.length > 0) {
        const idx = EKAI.pickCardToGive(cpuHand);
        ekGame.resolveFavor(targetId, idx);
      }
      ekRenderer.render();
    });
  } else if (result.action === 'favor_pick_target' && cardPlayerId !== 'human') {
    // CPU picks a favor target
    const target = EKAI.pickTarget(ekGame, cardPlayerId);
    if (target) {
      ekGame.pickFavorTarget(target);
      // If target is human, they need to give a card (handled by pendingAction)
      if (target !== 'human') {
        const h = ekGame.hands[target];
        if (h && h.length > 0) {
          const idx = EKAI.pickCardToGive(h);
          ekGame.resolveFavor(target, idx);
        }
      }
    } else {
      ekGame.pendingAction = null;
    }
  } else if (result.action === 'defused' && cardPlayerId === 'human') {
    ekRenderer.showPlaceKitten(ekGame.drawPile.length);
  } else if (result.action === 'defused' && cardPlayerId !== 'human') {
    const pos = EKAI.placementPosition(ekGame);
    ekGame.placeKitten(pos);
  }
  ekRenderer.render();
}

function runCPUTurn() {
  if (!ekGame || ekGame.winner) {
    if (ekCPUInterval) clearInterval(ekCPUInterval);
    return;
  }
  // Don't act during nope window
  if (ekGame.pendingCardAction) return;

  const cp = ekGame.currentPlayer;
  if (!cp || !cp.isCPU) return;
  if (!ekGame.alive.has(cp.id)) { ekGame.advanceTurn(); ekRenderer.render(); return; }

  // Handle pending actions for CPU
  if (ekGame.pendingAction) {
    const pa = ekGame.pendingAction;
    if (pa.type === 'place_kitten' && pa.playerId === cp.id) {
      const pos = EKAI.placementPosition(ekGame);
      ekGame.placeKitten(pos);
      ekRenderer.render();
      return;
    }
    if (pa.type === 'steal' && pa.playerId === cp.id) {
      const target = EKAI.pickTarget(ekGame, cp.id);
      if (target) ekGame.resolveSteal(target);
      else ekGame.pendingAction = null;
      ekRenderer.render();
      return;
    }
    if (pa.type === 'favor_pick_target' && pa.playerId === cp.id) {
      const target = EKAI.pickTarget(ekGame, cp.id);
      if (target) {
        ekGame.pickFavorTarget(target);
        if (target !== 'human') {
          const h = ekGame.hands[target];
          if (h && h.length > 0) {
            const idx = EKAI.pickCardToGive(h);
            ekGame.resolveFavor(target, idx);
          }
        }
      } else {
        ekGame.pendingAction = null;
      }
      ekRenderer.render();
      return;
    }
    if (pa.type === 'favor_give' && pa.targetId === cp.id) {
      const hand = ekGame.hands[cp.id];
      if (hand && hand.length > 0) {
        const idx = EKAI.pickCardToGive(hand);
        ekGame.resolveFavor(cp.id, idx);
      } else {
        ekGame.pendingAction = null;
      }
      ekRenderer.render();
      return;
    }
    return; // Wait for human to resolve
  }

  const decision = EKAI.takeTurn(ekGame, cp.id);
  if (decision.action === 'play') {
    const result = ekGame.playCard(cp.id, decision.cardIndex);
    if (result.success && result.action === 'nope_window') {
      startNopeWindow(cp.id);
      return;
    }
  } else {
    ekGame.drawCard(cp.id);
  }
  ekRenderer.render();
}

function handleEKAction(actionType, data) {
  if (!ekGame) return;

  switch (actionType) {
    case 'play_card': {
      // Allow human to play Nope during a nope window
      if (ekGame.pendingCardAction) {
        const hand = ekGame.hands['human'];
        if (hand && data.cardIndex >= 0 && data.cardIndex < hand.length) {
          const card = hand[data.cardIndex];
          if (card.type === EK_CARD_TYPES.NOPE) {
            const res = ekGame.playNope('human');
            if (res.success) {
              ekGame.addLog('🚫 You NOPED it!');
              if (ekNopeTimeout) { clearTimeout(ekNopeTimeout); ekNopeTimeout = null; }
              ekRenderer.render();
            }
          }
        }
        return;
      }
      if (ekGame.currentPlayer.id !== 'human' && !ekGame.pendingAction) return;
      const result = ekGame.playCard('human', data.cardIndex);
      if (!result.success) return;
      if (result.action === 'nope_window') {
        startNopeWindow('human');
        return;
      }
      ekRenderer.render();
      break;
    }
    case 'draw': {
      if (ekGame.currentPlayer.id !== 'human') return;
      if (ekGame.pendingAction || ekGame.pendingCardAction) return;
      const result = ekGame.drawCard('human');
      if (!result.success) return;
      if (result.action === 'defused') {
        ekRenderer.showPlaceKitten(ekGame.drawPile.length);
      }
      ekRenderer.render();
      break;
    }
    case 'place_kitten': {
      ekGame.placeKitten(data.position);
      ekRenderer.render();
      break;
    }
    case 'favor_give': {
      if (ekGame.pendingAction && ekGame.pendingAction.type === 'favor_give' && ekGame.pendingAction.targetId === 'human') {
        ekGame.resolveFavor('human', data.cardIndex);
        ekRenderer.render();
      }
      break;
    }
    case 'exit': {
      stopEKGame();
      showScreen('screen-card-games');
      break;
    }
  }
}

function stopEKGame() {
  if (ekCPUInterval) { clearInterval(ekCPUInterval); ekCPUInterval = null; }
  ekGame = null;
  ekRenderer = null;
}

// ── MULTIPLAYER CARD GAME ────────────────────────────────────
let cardsMPName = '';
let cardsMPCode = '';
let cardsMPIsHost = false;
let cardsMPGame = null;
let cardsMPRenderer = null;

function initCardsMPListeners() {
  if (!socket || !socket.on) return;

  socket.on('cards-game-hosted', (data) => {
    cardsMPCode = data.code;
    cardsMPIsHost = true;
    showScreen('screen-cards-lobby');
    renderCardsLobby(data);
  });

  socket.on('cards-game-joined', (data) => {
    cardsMPCode = data.code;
    cardsMPIsHost = false;
    showScreen('screen-cards-lobby');
    renderCardsLobby(data);
  });

  socket.on('cards-player-joined', (data) => {
    renderCardsLobby(data);
  });

  socket.on('cards-player-left', (data) => {
    renderCardsLobby(data);
  });

  socket.on('cards-join-error', (data) => {
    const errEl = document.getElementById('cards-mp-join-error');
    if (errEl) errEl.textContent = data.message;
  });

  socket.on('cards-game-starting', (data) => {
    // data = { gameType, players, initialState }
    showScreen('screen-cards-game');
    startMPEKGame(data);
  });

  socket.on('cards-game-state', (state) => {
    if (cardsMPGame) {
      // Sync full state from host
      Object.assign(cardsMPGame, deserializeEKState(state));
      if (cardsMPRenderer) {
        cardsMPRenderer.render();
        // Show interactive modals based on pending actions for the local player
        const myId = socket.id;
        const pa = cardsMPGame.pendingAction;
        if (pa) {
          if (pa.type === 'steal' && pa.playerId === myId) {
            const targets = cardsMPGame.players.filter(p =>
              p.id !== myId && (cardsMPGame.alive ? cardsMPGame.alive.has(p.id) : p.alive)
            );
            cardsMPRenderer.showTargetPicker(targets, 'Steal a random card from:', (targetId) => {
              socket.emit('cards-game-action', { actionType: 'steal_target', data: { targetId } });
            });
          } else if (pa.type === 'favor_pick_target' && pa.playerId === myId) {
            const targets = cardsMPGame.players.filter(p =>
              p.id !== myId && (cardsMPGame.alive ? cardsMPGame.alive.has(p.id) : p.alive) &&
              (p.handSize || (cardsMPGame.hands[p.id] || []).length) > 0
            );
            cardsMPRenderer.showTargetPicker(targets, 'Pick a player to give you a card:', (targetId) => {
              socket.emit('cards-game-action', { actionType: 'favor_target', data: { targetId } });
            });
          } else if (pa.type === 'favor_give' && pa.targetId === myId) {
            const myHand = cardsMPGame.hands[myId] || [];
            if (myHand.length > 0) {
              cardsMPRenderer.showFavorGive(myHand);
            }
          } else if (pa.type === 'place_kitten' && pa.playerId === myId) {
            const pileSize = cardsMPGame.drawPile ? cardsMPGame.drawPile.length : (cardsMPGame.drawPileSize || 0);
            cardsMPRenderer.showPlaceKitten(pileSize);
          }
        }
      }
    }
  });

  socket.on('cards-start-error', (data) => {
    const errEl = document.getElementById('cards-lobby-error');
    if (errEl) errEl.textContent = data.message;
  });

  socket.on('cards-see-future', (data) => {
    // Show the top 3 cards to this player
    const el = document.getElementById('ek-see-future');
    const cardsEl = document.getElementById('ek-future-cards');
    if (el && cardsEl && data.cards) {
      cardsEl.innerHTML = data.cards.map(c => `<div class="ek-future-card">${c}</div>`).join('');
      el.classList.remove('hidden');
    }
  });
}

function renderCardsLobby(data) {
  const codeEl = document.getElementById('cards-lobby-code');
  if (codeEl && data.code) codeEl.textContent = data.code;
  
  const playersEl = document.getElementById('cards-lobby-players');
  if (playersEl && data.players) {
    playersEl.innerHTML = '';
    data.players.forEach(p => {
      const div = document.createElement('div');
      div.className = 'cards-lobby-player';
      div.textContent = p.name + (p.isHost ? ' (Host)' : '');
      playersEl.appendChild(div);
    });
  }

  const startBtn = document.getElementById('btn-cards-lobby-start');
  if (startBtn) {
    startBtn.style.display = cardsMPIsHost ? 'block' : 'none';
  }

  const gameSelect = document.getElementById('cards-lobby-game-select');
  if (gameSelect) {
    gameSelect.style.pointerEvents = cardsMPIsHost ? 'auto' : 'none';
    gameSelect.style.opacity = cardsMPIsHost ? '1' : '0.6';
  }
}

function startMPEKGame(data) {
  // Reconstruct game from server state
  const players = data.players.map(p => ({ id: p.id, name: p.name, isCPU: false }));
  cardsMPGame = new ExplodingKittensGame(players, true);
  // Apply initial state from host
  Object.assign(cardsMPGame, deserializeEKState(data.initialState));

  const myId = socket.id;
  cardsMPRenderer = new EKRenderer(cardsMPGame, myId, (actionType, actionData) => {
    // If playing a card during a nope window, detect if it's a Nope card and send correct action
    if (actionType === 'play_card' && cardsMPGame.pendingCardAction) {
      const hand = cardsMPGame.hands[myId];
      if (hand && actionData.cardIndex >= 0 && actionData.cardIndex < hand.length) {
        const card = hand[actionData.cardIndex];
        if (card.type === 'nope' && cardsMPGame.pendingCardAction.playerId !== myId) {
          socket.emit('cards-game-action', { actionType: 'nope', data: {} });
          return;
        }
      }
      return; // Can't play other cards during nope window
    }
    // Send action to server
    socket.emit('cards-game-action', { actionType, data: actionData });
  });
  cardsMPRenderer.render();
}

function deserializeEKState(state) {
  if (!state) return {};
  const result = { ...state };
  if (state.alive) result.alive = new Set(state.alive);
  if (state.hands) result.hands = state.hands;
  if (state.players) result.players = state.players;
  // Server sends drawPileSize (number) instead of the actual drawPile array.
  // Synthesize a drawPile of the correct length so getVisibleState works.
  if (typeof state.drawPileSize === 'number') {
    result.drawPile = new Array(state.drawPileSize);
  }
  // Server sends discardPile array; ensure discardPile is set
  if (state.discardPile) result.discardPile = state.discardPile;
  return result;
}

// ── INIT ─────────────────────────────────────────────────────
// initCardsMPListeners() is called from app.js after socket is ready
