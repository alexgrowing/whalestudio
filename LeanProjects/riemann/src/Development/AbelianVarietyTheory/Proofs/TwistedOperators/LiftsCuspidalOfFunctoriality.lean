import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeriesStatement

namespace GlobalTheory.PairLift

theorem liftsCuspidal_of_functoriality (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules)
    (hC : GlobalTheory.Published.CuspRapidDecay) (hW : GlobalTheory.Published.CasselmanWallach) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  obtain ⟨X, hX, -, -, h3, h4, h5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hD hH
  have I := fun D => GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries hD hH hC hW D X hX
  exact liftsCuspidal X hX h3 h4 h5 hH hC (fun D => (I D).bridge) (fun D => (I D).vacChar) (fun D => (I D).lie)
    (fun D => (I D).cpt) (fun D => (I D).dense) (fun D => (I D).laws) (fun D => (I D).const) (fun D => (I D).ext)

theorem liftsCuspidal_of_classicalTheorems : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := fun h =>
  liftsCuspidal_of_functoriality h.discreteSeriesCover h.harishChandraModules h.cuspRapidDecay h.casselmanWallach

end GlobalTheory.PairLift
