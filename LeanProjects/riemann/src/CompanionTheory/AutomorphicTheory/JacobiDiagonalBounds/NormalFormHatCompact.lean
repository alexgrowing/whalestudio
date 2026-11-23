import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.NfTieHatSOf
import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFCoreC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeConstructionHolds

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

theorem normal_form_hat_compact : CompanionTheory.NFCpt.NFTieHatC := by
  intro Cb
  obtain ⟨Cc, H⟩ := nfTieGen_of Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gauge_construction_holds Cb
  refine ⟨Cc, fun Wp Wq _ _ _ _ _ _ P p hInD => ?_⟩
  obtain ⟨e, L, h1, h2, h3, h4⟩ := H Wp Wq P p hInD
  refine ⟨e, L, h1, h2, h3, fun Y w hw ee Q Lq hS => ?_⟩
  obtain ⟨m, b, u, C, h5, h6, h7⟩ := h4 Y w hw ee Q Lq hS
  exact ⟨m, b, u, C, h5, h6, fun F A hF hcc hA hc => h7 F A hF hcc hA (Or.inr hc)⟩

end Formalism.FourierDecayAlt.P.NormalFormRelations
