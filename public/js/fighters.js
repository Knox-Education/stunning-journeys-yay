/**
 * fighters.js – Fighter definitions.
 *
 * Each fighter has base stats + an array of abilities.
 * selectedFighterId is persisted across screens and sent to the lobby.
 */

let selectedFighterId = 'fighter'; // default

const FIGHTERS = {
  fighter: {
    id: 'fighter',
    name: 'Fighter',
    hp: 1300,
    healAmount: 100,       // HP per heal tick
    healDelay: 10,        
    healTick: 4,           
    speed: 3.2,            
    description: 'A basic, plain, cool, and versatile fighter.',
    abilities: [
      {
        key: 'M1',
        name: 'Sword',
        description: 'Swings sword, dealing 100 damage.',
        damage: 100,
        cooldown: 0.5,     // seconds
        range: 1.5,        // tiles
        type: 'melee',
        bind: 'click',
      },
      {
        key: 'E',
        name: 'Support',
        description: 'Allies and himself deal 50% more damage for 7 seconds.',
        damage: 0,
        cooldown: 40,
        duration: 7,
        type: 'buff',
        bind: 'e',
      },
      {
        key: 'R',
        name: 'Power Swing',
        description: 'Swings his sword with power, dealing 400 damage + knockback.',
        damage: 400,
        cooldown: 30,
        range: 1.5,
        knockback: 3,       // tiles of knockback
        type: 'melee',
        bind: 'r',
      },
      {
        key: 'T',
        name: 'Intimidation',
        description: 'Enemies that can see the Fighter deal 50% less damage but move 1.5× faster away from Fighter. Lasts 10 seconds.',
        damage: 0,
        cooldown: 40,
        duration: 10,
        type: 'debuff',
        bind: 't',
      },
      {
        key: 'SPACE',
        name: 'Super-Special-High-Jump-Move',
        description: 'Jumps out of the stage, then aims a landing (5s to aim). Hit = 1000 damage. Miss = 3 second stun + 200 self-damage.',
        damage: 1000,
        missDamage: 200,
        missStun: 3,
        aimTime: 5,          // seconds to aim before landing
        cooldown: 0,        // one-use per unlock
        type: 'special',
        bind: ' ',
      },
    ],
  },

  poker: {
    id: 'poker',
    name: 'Poker',
    hp: 1000,
    healAmount: 80,
    healDelay: 10,
    healTick: 4,
    speed: 2.8,
    description: 'A cunning ranged gambler who bets on chips, cards, and blinds to control the fight.',
    abilities: [
      {
        key: 'M1',
        name: 'Chip Throw',
        description: 'Throws 3 chips in a straight line. Deals 200 damage each.',
        damage: 200,
        cooldown: 1,
        range: 6,
        type: 'ranged',
        bind: 'click',
        projectileCount: 3,
        projectileSpread: 0.15,
        projectileSpeed: 28,
      },
      {
        key: 'E',
        name: 'Gamble',
        description: 'Draws a card and throws it. Deals 100–1000 damage. 500+ is rarer.',
        damage: 0,
        cooldown: 30,
        range: 7,
        type: 'ranged',
        bind: 'e',
        projectileSpeed: 18,
      },
      {
        key: 'R',
        name: 'Blinds',
        description: 'Takes a blind. Small (70%): ½ damage taken until another move. Big (20%): 1.5× damage taken for 60s. Dealer (10%): resets Gamble cooldown.',
        damage: 0,
        cooldown: 40,
        type: 'self',
        bind: 'r',
      },
      {
        key: 'T',
        name: 'Chip Change',
        description: 'Changes M1 to deal 0, 100, 200, 300, or 400 damage randomly for 30 seconds.',
        damage: 0,
        cooldown: 60,
        duration: 30,
        type: 'self',
        bind: 't',
      },
      {
        key: 'SPACE',
        name: 'Royal Flush',
        description: 'Heals self to full HP. Close range (3 tiles): stuns 3s + executes <500 HP. Medium range (10 tiles): resets enemy cooldowns + charges.',
        damage: 0,
        cooldown: 0,
        stunDuration: 3,
        executeThreshold: 500,
        range: 10,
        type: 'special',
        bind: ' ',
      },
    ],
  },
};

function getFighter(id) {
  return FIGHTERS[id] || FIGHTERS['fighter'];
}

function getAllFighterIds() {
  return Object.keys(FIGHTERS);
}
