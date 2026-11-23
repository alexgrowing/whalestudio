import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree

open Formalism.L2.Col

noncomputable section
namespace GlobalTheory.SymBridge

def FreeN (k₀ rS r t p p' : ℕ) : Prop :=
  if p < r then (if p' < r then p ≠ p' ∧ symIdx k₀ rS p < symIdx k₀ rS p' ∧ ¬ (p' = k₀ + rS ∧ p < k₀) else True)
  else (if p' < r then False else (p - r) / t ≤ (p' - r) / t)

end GlobalTheory.SymBridge
