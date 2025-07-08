import { DREAMSCAPES } from './dreamscapes.js';
import { EMOTIONS } from './emotions.js';
import { logger } from './logger.js';

// Dreamscape state interface
export interface DreamscapeState {
  emotional_tone: string;
  dreamscape: string;
  narrative: string[];
  agency_level: number;
  causality_strength: number;
  coherence_level: number;
  familiarity_ratio: number;
  symbolic_density: number;
  sensory_cross_bleeding: number;
  boundary_stability: number;
  memory_persistence: number;
}

// Helper function to generate random number between 0.1-0.9
export const randomPercent = (): number => Math.random() * 0.6 + 0.2;

export const clampPercent = (value: number): number => Math.max(0.2, Math.min(0.6, value));

export class Dreamscape {
  private state: DreamscapeState;

  constructor() {
    const initialDreamscape = Dreamscape.generateRandomDreamscape();
    this.state = {
      emotional_tone: Dreamscape.generateRandomEmotionalTone(),
      dreamscape: initialDreamscape,
      narrative: [
        "The dream begins in silence, waiting for the first thought to emerge.",
        initialDreamscape
      ],
      ...Dreamscape.randomizeProperties()
    };
    
    logger.info('Dreamscape initialized', this.state);
  }

  // Static helper methods
  static generateRandomDreamscape(): string {
    return DREAMSCAPES[Math.floor(Math.random() * DREAMSCAPES.length)];
  }

  static generateRandomEmotionalTone(): string {
    const emotion1 = EMOTIONS[Math.floor(Math.random() * EMOTIONS.length)];
    const emotion2 = EMOTIONS[Math.floor(Math.random() * EMOTIONS.length)];
    return `${emotion1} ${emotion2}`;
  }

  static randomizeProperties() {
    const al = randomPercent();
    const ca = randomPercent();
    const co = randomPercent();
    const s = Math.cbrt(0.5 / (al * ca * co));

    logger.info("al * ca * co " + (al * ca * co))
    logger.info("Final product: " + (s * al * s * ca * s * co))

    return {
      agency_level: Math.min(s * al, 0.99999),
      causality_strength: Math.min(s * ca, 0.99999),
      coherence_level: Math.min(s * co, 0.99999),
      familiarity_ratio: randomPercent(),
      symbolic_density: randomPercent(),
      sensory_cross_bleeding: randomPercent(),
      boundary_stability: randomPercent(),
      memory_persistence: randomPercent()
    };
  }

  static actionCheck(property: number): number {
    const threshold = 1.0 - property;
    const randomValue = randomPercent();
    
    logger.info('Action check calculation', {
      property,
      threshold,
      randomValue,
      threshold_quarter: threshold / 4
    });
    
    if (randomValue >= threshold) {
      // Action succeeds
      return 1;
    }
    if (randomValue < threshold / 4) {
      // Action fails
      return -1;
    }
    // No change
    return 0;
  }

  private agencyCheck(): string | undefined {
    const result = Dreamscape.actionCheck(this.state.agency_level);
    
    logger.debug('Agency check performed', {
      agency_level: this.state.agency_level,
      result: result === 1 ? 'success' : result === -1 ? 'failure' : 'resistance'
    });
    
    if (result === 1) {
      return undefined;
    }
    if (result === -1) {
      logger.info('Agency check failed - opposite will occur');
      return "Instruction: Describe the opposite occurring and then add that as a narrative.";
    }
    logger.info('Dreamscape resisting change');
    return "The dreamscape resists your will to change it.";
  }

  // Public methods
  getState(): DreamscapeState {
    return { ...this.state };
  }

  addNarrative(entry: string): string {
    logger.info('Attempting to add narrative', { original_entry: entry });
    
    const agencyCheck = this.agencyCheck();
    if (agencyCheck) {
      logger.info('Narrative addition blocked by agency check', { reason: agencyCheck });
      return agencyCheck;
    }

    this.state.narrative.push(entry);
    
    return entry;
  }

  transitionDreamscape(): string {
    logger.info('Attempting dreamscape transition');
    
    const agencyCheck = this.agencyCheck();
    if (agencyCheck) {
      logger.warn('Dreamscape transition blocked by agency check', { reason: agencyCheck });
      return agencyCheck;
    }
    
    const oldDreamscape = this.state.dreamscape;
    const oldEmotionalTone = this.state.emotional_tone;
    
    this.state.narrative.push("The dreamscape shifts and transforms...");
    
    this.state.emotional_tone = Dreamscape.generateRandomEmotionalTone();
    
    const newDreamscape = Dreamscape.generateRandomDreamscape();
    this.state.dreamscape = newDreamscape;    
    this.state.narrative.push(newDreamscape);
    
    const randomProperties = Dreamscape.randomizeProperties();
    Object.assign(this.state, randomProperties);
    
    logger.info('Dreamscape transitioned successfully', {
      old_dreamscape: oldDreamscape,
      new_dreamscape: newDreamscape,
      old_emotional_tone: oldEmotionalTone,
      new_emotional_tone: this.state.emotional_tone,
      new_properties: randomProperties
    });
    
    return `Dreamscape transitioned. New scene: ${this.state.dreamscape}`;
  }

  submerge(): string {
    logger.info('Submerging - starting fresh dreamscape');
    
    const newDreamscape = Dreamscape.generateRandomDreamscape();
    this.state = {
      emotional_tone: Dreamscape.generateRandomEmotionalTone(),
      dreamscape: newDreamscape,
      narrative: [
        "The dream begins anew, all previous dreams fade into the void.",
        newDreamscape
      ],
      ...Dreamscape.randomizeProperties()
    };
    
    logger.info('Submerge completed successfully', {
      new_dreamscape: this.state.dreamscape,
      emotional_tone: this.state.emotional_tone,
      narrative_length: this.state.narrative.length
    });
    
    return `Submerged into a fresh dreamscape: ${this.state.dreamscape}`;
  }
} 