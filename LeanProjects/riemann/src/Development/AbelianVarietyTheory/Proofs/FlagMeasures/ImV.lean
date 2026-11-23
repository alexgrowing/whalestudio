import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData

open NumberField

noncomputable section
namespace GlobalTheory.SnMass.SkewVol

variable {E : Type} [Field E] [NumberField E]

def reV (x : E) : InfinitePlace E → ℝ := fun w => (w.embedding x).re

def imV (x : E) : InfinitePlace E → ℝ := fun w => (w.embedding x).im

end GlobalTheory.SnMass.SkewVol
