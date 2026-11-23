import Mathlib
import Formalism.ZetaNonvanishing.ZetaLandau

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.SlopeTestRemainingChoices

open Formalism

def LandauZeroFreeHalfPlane : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ y₀ : ℝ, (∀ y : ℝ, y₀ ≤ y → Gz y ≤ y ^ θ) →
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

theorem landau_zero_free_half_plane : LandauZeroFreeHalfPlane := by
  intro θ h0 h1 y₀ hG s hs
  exact Formalism.zetaLandau 1 (Or.inl rfl) θ h0 h1 ⟨1, y₀, fun y hy => by simpa using hG y hy⟩ s hs

end Formalism.MainNotions.ZetaZeroFreeRegion.SlopeTestRemainingChoices

end
