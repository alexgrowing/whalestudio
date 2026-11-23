import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P

theorem germExpansionOfSteps : Formalism.FourierDecayAlt.A6.GermAssemble := by
  intro hHead hPhi K _ _ _ R ψ hD hn m hm γ hγ h Q hQ hQu
  obtain ⟨L₀, Λ₀, hL₀, hΛ₀, hΦ⟩ := hHead K R ψ hD hn m h Q hQ hQu
  obtain ⟨V, hV, hG⟩ := hPhi K R ψ hD hn m hm γ hγ L₀ Λ₀ Q hL₀ hΛ₀ hQ hQu
  refine ⟨V, hV, fun t c ht hc n' Z' => ?_⟩
  obtain ⟨Φ, hyp, h1, h2⟩ := hΦ n' Z'
  rw [h1 t c, hG Φ hyp t c ht hc]
  congr 1
  funext z
  exact (h2 z).symm

end Formalism.FourierDecayAlt.P
