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

// Helper function to generate random emotional tone
export const generateRandomEmotionalTone = (): string => {
  const emotion1 = EMOTIONS[Math.floor(Math.random() * EMOTIONS.length)];
  const emotion2 = EMOTIONS[Math.floor(Math.random() * EMOTIONS.length)];
  return `${emotion1} ${emotion2}`;
};

// Helper function to generate random dreamscape descriptions
export const generateRandomDreamscape = (): string => {
  return DREAMSCAPES[Math.floor(Math.random() * DREAMSCAPES.length)];
};

// Helper function to randomize all numeric properties
export const randomizeProperties = () => {
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
};

// Helper function to simulate dream logic alterations
export const applyDreamLogic = (input: string, coherence: number, causality: number): string => {
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
};

// Initialize dreamscape state with randomized values
const initialDreamscape = generateRandomDreamscape();
export let dreamscapeState: DreamscapeState = {
  emotional_tone: generateRandomEmotionalTone(),
  dreamscape: initialDreamscape,
  narrative: [
    "The dream begins in silence, waiting for the first thought to emerge.",
    initialDreamscape
  ],
  ...randomizeProperties()
};

// Dreamscape operations
export const getDreamscapeState = (): DreamscapeState => dreamscapeState;

export const addNarrative = (entry: string): string => {
  const alteredNarrative = applyDreamLogic(
    entry,
    dreamscapeState.coherence_level,
    dreamscapeState.causality_strength
  );
  dreamscapeState.narrative.push(alteredNarrative);
  return alteredNarrative;
};

export const changeScene = (newScene: string): string => {
  const alteredScene = applyDreamLogic(
    newScene,
    dreamscapeState.coherence_level,
    dreamscapeState.causality_strength
  );
  dreamscapeState.dreamscape = alteredScene;
  // Add the new scene description to the narrative
  dreamscapeState.narrative.push(alteredScene);
  return alteredScene;
};

export const transitionDreamscape = (): string => {
  // Add transition narrative entry
  dreamscapeState.narrative.push("The dreamscape shifts and transforms...");
  
  // Generate new random emotional tone
  dreamscapeState.emotional_tone = generateRandomEmotionalTone();
  
  // Generate new random dreamscape
  const newDreamscape = generateRandomDreamscape();
  dreamscapeState.dreamscape = newDreamscape;
  
  // Add the new dreamscape description to the narrative
  dreamscapeState.narrative.push(newDreamscape);
  
  // Randomize all numeric properties
  const randomProperties = randomizeProperties();
  Object.assign(dreamscapeState, randomProperties);
  
  return `Dreamscape transitioned. New scene: ${dreamscapeState.dreamscape}`;
}; 