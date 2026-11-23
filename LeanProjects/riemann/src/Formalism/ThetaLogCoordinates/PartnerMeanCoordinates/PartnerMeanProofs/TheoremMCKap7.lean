import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.Statement
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.GamIntC
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.PartnerConditionHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RestrictedSaturationHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjectionPos
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundPosOfProjSat
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.FinalLL

namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.InvariantFactorPaths.OddLevelGainBounds Formalism.InvariantFactorPaths.OddLevelGainBounds.TB Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.L4 MvPolynomial Finset

theorem kap_num (N s : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (hN : N ≤ 2 * s + 2) :
    (3 / 2 : ℝ) * (((N : ℝ) + 2) * Q) ≤ 3 * ((s : ℝ) + 2) * Q := by
  have h : (N : ℝ) ≤ 2 * (s : ℝ) + 2 := by exact_mod_cast hN
  nlinarith

end Formalism.InvariantFactorPaths.MC
