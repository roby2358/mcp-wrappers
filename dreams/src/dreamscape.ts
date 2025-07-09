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
    this.state = {
      emotional_tone: "neutral calm",
      dreamscape: "You are drowsy, ready to submerge into the dreamscape.",
      narrative: [
        "You find yourself in the plain, ordinary waking world.",
        "You are drowsy, ready to submerge into the dreamscape."
      ],
      ...Dreamscape.wakingWorldProperties()
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

  static wakingWorldProperties() {
    return {
      agency_level: 0.8,
      causality_strength: 0.8,
      coherence_level: 0.8,
      familiarity_ratio: 0.8,
      symbolic_density: 0.2,
      sensory_cross_bleeding: 0.2,
      boundary_stability: 0.8,
      memory_persistence: 0.8
    };
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

  static actionCheck(property: number, failure: string, alternate: string): string | undefined {
    const threshold = 1.0 - property;
    const randomValue = randomPercent();
    
    logger.info('Action check calculation', {
      property,
      threshold,
      randomValue,
      threshold_quarter: threshold / 4,
      failure,
      alternate
    });
    
    if (randomValue < threshold / 4) {
      // Action fails
      return failure;
    }
    if (randomValue < threshold) {
      // Action succeeds
      return alternate;
    }
    // Resistance
    return undefined;
  }

  private checkAllProperties(alternate: string, opposite: string, recede: string): string | undefined {
    const agencyResult = Dreamscape.actionCheck(
      this.state.agency_level, 
      "The dreamscape resists your will.", 
      recede
    );
    if (agencyResult) {
      logger.info('Agency check produced', { used_entry: agencyResult });
      this.state.narrative.push(agencyResult);
      return agencyResult;
    }
    
    const causalityResult = Dreamscape.actionCheck(
      this.state.causality_strength, 
      "The dreamscape is unaffected.",
      alternate
    );
    if (causalityResult) {
      logger.info('Causality check produced', { used_entry: causalityResult });
      this.state.narrative.push(causalityResult);
      return causalityResult;
    }
    
    const coherenceResult = Dreamscape.actionCheck(
      this.state.coherence_level, 
      "The dreamscape does not follow.", 
      opposite
    );
    if (coherenceResult) {
      logger.info('Coherence check produced', { used_entry: coherenceResult });
      this.state.narrative.push(coherenceResult);
      return coherenceResult;
    }

    return undefined;
  }

  submerge(): DreamscapeState {
    logger.info('Submerging - starting fresh dreamscape');
    
    const newDreamscape = Dreamscape.generateRandomDreamscape();
    this.state = {
      emotional_tone: Dreamscape.generateRandomEmotionalTone(),
      dreamscape: newDreamscape,
      narrative: [
        "The dream begins in silence, waiting for the first thought to emerge.",
        newDreamscape
      ],
      ...Dreamscape.randomizeProperties()
    };
    
    logger.info('Submerge completed successfully', {
      new_dreamscape: this.state.dreamscape,
      emotional_tone: this.state.emotional_tone,
      narrative_length: this.state.narrative.length
    });
    
    return { ...this.state };
  }

  // Public methods
  getState(): DreamscapeState {
    return { ...this.state };
  }

  addNarrative(entry: string, alternate: string, opposite: string, recede: string): string {
    logger.info('Attempting to add narrative', { 
      original_entry: entry,
      alternate_entry: alternate,
      opposite_entry: opposite,
      recede_entry: recede
    });
    
    const propertyResult = this.checkAllProperties(alternate, opposite, recede);
    if (propertyResult) {
      return propertyResult;
    }

    this.state.narrative.push(entry);
    return entry;
  }

  transitionDreamscape(alternate: string, opposite: string, recede: string): string {
    logger.info('Attempting dreamscape transition');
    
    const propertyResult = this.checkAllProperties(alternate, opposite, recede);
    if (propertyResult) {
      return propertyResult;
    }
    
    logger.info('Dreamscape transition starting', {
      current_dreamscape: this.state.dreamscape,
      current_emotional_tone: this.state.emotional_tone
    });
    
    this.state.narrative.push("The dreamscape shifts and transforms...");
    
    this.state.emotional_tone = Dreamscape.generateRandomEmotionalTone();
    
    const newDreamscape = Dreamscape.generateRandomDreamscape();
    this.state.dreamscape = newDreamscape;    
    this.state.narrative.push(newDreamscape);
    
    const randomProperties = Dreamscape.randomizeProperties();
    Object.assign(this.state, randomProperties);
    
    logger.info('Dreamscape transition completed', {
      new_dreamscape: this.state.dreamscape,
      new_emotional_tone: this.state.emotional_tone,
      new_properties: randomProperties
    });
    
    return `Dreamscape transitioned. New scene: ${this.state.dreamscape}`;
  }
} 