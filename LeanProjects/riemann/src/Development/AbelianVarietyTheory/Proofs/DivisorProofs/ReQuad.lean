import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real

noncomputable section

namespace GlobalTheory.ThetaMet

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

def quad (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : ℝ :=
  (fun i => (P.2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)

def reQuad (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : ℝ :=
  (fun i => flat τ P (Sum.inl i)) ⬝ᵥ (((τ P.1).map Complex.re) *ᵥ fun i => flat τ P (Sum.inl i))

end GlobalTheory.ThetaMet
