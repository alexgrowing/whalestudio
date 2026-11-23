import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementT
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementP

noncomputable section

open scoped BigOperators

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def WeylGT : Prop :=
  BranchDim → ∀ (n : ℕ) (μ : Fin n → ℤ), Antitone μ → weylDim n (extW μ) = (Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT n μ : ℝ)

def PieriOfBranch : Prop := BranchDim → PieriDim

end Formalism.InvariantFactorPaths.BranchingDimensions
