import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LogBinomialProperties
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LogWeylDimensionEstimate
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.N0LeNs
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.AtypicalWeightBoundOf
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.TTotal
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.Branch
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.WeylGT

namespace Formalism.InvariantFactorPaths.BranchingDimensions.Top

theorem lemma_t_one : PathWeightBound :=
  pathWeightBound_of pathEntryBounds pathInterlacingCriterion logBinomialProperties logWeylDimensionEstimate logRankEstimate pathTailBounds logBinomialDeficit
theorem weylGT : ∀ (n : ℕ) (μ : Fin n → ℤ), Antitone μ → weylDim n (extW μ) = (Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT n μ : ℝ) :=
  weyl_dim_eq_gelfand_tsetlin branchingDimensionFormula

end Formalism.InvariantFactorPaths.BranchingDimensions.Top
