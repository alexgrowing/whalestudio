import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def RootsNear.Statement : Prop :=
  ∀ (e : ℕ) (G : Polynomial (MvPolynomial (Fin e) ℚ)), G.Monic →
    ∀ (y₀ : Fin e → ℂ) (t₀ : ℂ), G.eval₂ (aeval y₀).toRingHom t₀ = 0 →
      ∀ ε > 0, ∀ᶠ y in 𝓝 y₀, ∃ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 ∧ dist t t₀ < ε

end GroundTheory.Heights₂.Heights.HilbertSamuel
