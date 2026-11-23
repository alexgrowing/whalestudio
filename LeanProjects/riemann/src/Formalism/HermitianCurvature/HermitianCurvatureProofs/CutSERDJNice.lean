import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_orbital_niceness : RDJNice := by
  intro k r Wp Wq _ _ _ _ _ _ D F hF
  obtain ⟨ε, hε, hN⟩ := hF
  have h := Formalism.FourierDecayAlt.P.bessel_function_finite_class k r Wp Wq D F ε hε hN
  refine ⟨by rw [ffl_om_eq]; exact h, ?_⟩
  intro g₀ hg₀
  obtain ⟨U, F', hU, hgU, hc, he⟩ := h.1 g₀ ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hg₀.1, hg₀.2⟩
  exact ⟨U, F', hU, hgU, by exact_mod_cast hc, fun g hg hgG => he g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG)⟩

end Formalism.FourierDecayAlt.P.CutSE
