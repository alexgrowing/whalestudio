import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt

namespace GlobalTheory.Published

def MatrixLemma : Prop := ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (h : HermFam K (Fin F.P₀.g → K))
  (ρ : (K →+* ℂ) → ℝ), F.IsHerm h → F.IsRho ρ →
    (∑ σ, (ρ σ ^ 2)⁻¹) / (Module.finrank ℚ K : ℝ) ≤
      14 * max 1 (max (F.falt h - (F.P₀.g : ℝ) / 2 * Real.log Real.pi) (Real.log (F.P₀.g.factorial : ℝ)))

end GlobalTheory.Published
