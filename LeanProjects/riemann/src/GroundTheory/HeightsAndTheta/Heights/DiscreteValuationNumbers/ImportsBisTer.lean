import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def dividedDifferenceExpansion.Statement : Prop :=
  ∀ (r m : ℕ) (G : MvPolynomial (Fin r) ℤ), G.IsHomogeneous m →
    IsPairExpansion m G
      (fun l => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G))

end GroundTheory.Heights₂.Heights.NumbersDVR
