import { DREAMSCAPES } from './dreamscapes.js';
import { EMOTIONS } from './emotions.js';

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
export const randomPercent = (): number => Math.floor(Math.random() * 101);

export class Dreamscape {
  private state: DreamscapeState;

  constructor() {
    const initialDreamscape = this.generateRandomDreamscape();
    this.state = {
      emotional_tone: this.generateRandomEmotionalTone(),
      dreamscape: initialDreamscape,
      narrative: [
        "The dream begins in silence, waiting for the first thought to emerge.",
        initialDreamscape
      ],
      ...this.randomizeProperties()
    };
  }

  // Static helper methods
  static generateRandomEmotionalTone(): string {
    const emotion1 = EMOTIONS[Math.floor(Math.random() * EMOTIONS.length)];
    const emotion2 = EMOTIONS[Math.floor(Math.random() * EMOTIONS.length)];
    return `${emotion1} ${emotion2}`;
  }

  static generateRandomDreamscape(): string {
    return DREAMSCAPES[Math.floor(Math.random() * DREAMSCAPES.length)];
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

  // Instance helper methods
  private generateRandomEmotionalTone(): string {
    return Dreamscape.generateRandomEmotionalTone();
  }

  private generateRandomDreamscape(): string {
    return Dreamscape.generateRandomDreamscape();
  }

  private randomizeProperties() {
    return Dreamscape.randomizeProperties();
  }

  private applyDreamLogic(input: string): string {
    return Dreamscape.applyDreamLogic(input, this.state.coherence_level, this.state.causality_strength);
  }

  // Public methods
  getState(): DreamscapeState {
    return { ...this.state };
  }

  addNarrative(entry: string): string {
    const alteredNarrative = this.applyDreamLogic(entry);
    this.state.narrative.push(alteredNarrative);
    return alteredNarrative;
  }

  changeScene(newScene: string): string {
    const alteredScene = this.applyDreamLogic(newScene);
    this.state.dreamscape = alteredScene;
    // Add the new scene description to the narrative
    this.state.narrative.push(alteredScene);
    return alteredScene;
  }

  transitionDreamscape(): string {
    // Add transition narrative entry
    this.state.narrative.push("The dreamscape shifts and transforms...");
    
    // Generate new random emotional tone
    this.state.emotional_tone = this.generateRandomEmotionalTone();
    
    // Generate new random dreamscape
    const newDreamscape = this.generateRandomDreamscape();
    this.state.dreamscape = newDreamscape;
    
    // Add the new dreamscape description to the narrative
    this.state.narrative.push(newDreamscape);
    
    // Randomize all numeric properties
    const randomProperties = this.randomizeProperties();
    Object.assign(this.state, randomProperties);
    
    return `Dreamscape transitioned. New scene: ${this.state.dreamscape}`;
  }
} 