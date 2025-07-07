import { DREAMSCAPES } from './dreamscapes.js';
import { EMOTIONS } from './emotions.js';
import { logger } from './logger.js';

// Dreamscape state interface
export interface DreamscapeState {
  emotional_tone: string;
  dreamscape: string;
  narrative: string[];
  familiarity_ratio: number;
  symbolic_density: number;
  sensory_cross_bleeding: number;
  coherence_level: number;
  boundary_stability: number;
  causality_strength: number;
  memory_persistence: number;
  agency_level: number;
}

// Helper function to clamp values between 0-100
export const clampValue = (value: number): number => Math.max(0, Math.min(100, value));

// Helper function to generate random number between 0-100
export const randomPercent = (): number => Math.floor(Math.random() * 100);

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
    
    logger.info('Dreamscape initialized', {
      initial_dreamscape: initialDreamscape,
      emotional_tone: this.state.emotional_tone,
      properties: {
        familiarity_ratio: this.state.familiarity_ratio,
        agency_level: this.state.agency_level,
        coherence_level: this.state.coherence_level
      }
    });
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
    return {
      familiarity_ratio: randomPercent(),
      symbolic_density: randomPercent(),
      sensory_cross_bleeding: randomPercent(),
      coherence_level: randomPercent(),
      boundary_stability: randomPercent(),
      causality_strength: randomPercent(),
      memory_persistence: randomPercent(),
      agency_level: randomPercent()
    };
  }

  static actionCheck(property: number): number {
    const threshold = 100 - property;
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
    return "The dreamscape resists your attempt to change it.";
  }

  static applyDreamLogic(input: string, coherence: number, causality: number): string {
    // Lower coherence and causality may alter the input
    const alterationChance = (100 - coherence) * (100 - causality) / 10000;
    
    if (Math.random() < alterationChance) {
      // Apply subtle dream-like alterations
      const alterations = [
        (text: string) => text.replace(/\b(I|me|my)\b/g, 'we'),
        (text: string) => text.replace(/\b(was|were)\b/g, 'might have been'),
        (text: string) => text.replace(/\b(suddenly|then)\b/g, 'as if in a dream'),
        (text: string) => text + ' ...or perhaps that was something else entirely',
        (text: string) => text.replace(/\b(door|window|path)\b/g, 'portal'),
      ];
      
      const randomAlteration = alterations[Math.floor(Math.random() * alterations.length)];
      return randomAlteration(input);
    }
    
    return input;
  }

  private applyDreamLogic(input: string): string {
    return Dreamscape.applyDreamLogic(input, this.state.coherence_level, this.state.causality_strength);
  }

  // Public methods
  getState(): DreamscapeState {
    return { ...this.state };
  }

  addNarrative(entry: string): string {
    logger.info('Attempting to add narrative', { original_entry: entry });
    
    const agencyCheck = this.agencyCheck();
    if (agencyCheck) {
      logger.warn('Narrative addition blocked by agency check', { reason: agencyCheck });
      return agencyCheck;
    }

    const alteredNarrative = this.applyDreamLogic(entry);
    this.state.narrative.push(alteredNarrative);
    
    const wasAltered = alteredNarrative !== entry;
    logger.info('Narrative added to dreamscape', {
      original: entry,
      altered: alteredNarrative,
      was_altered: wasAltered,
      narrative_count: this.state.narrative.length
    });
    
    return alteredNarrative;
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
} 