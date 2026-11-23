import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveBranchLength
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchNormalisationHoldsStatement
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Heights.CurveBranch

theorem curveBranchLength_of_branchNormalisation
    (hB : GroundTheory.Heights₂.Heights.BranchNormalisation.Statement) :
    GroundTheory.Heights₂.Heights.CurveBranchLength.Statement :=
  GroundTheory.Heights₂.Heights.CurveBranchLength.proof GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationLength hB

theorem curveBranchLength : GroundTheory.Heights₂.Heights.CurveBranchLength.Statement :=
  curveBranchLength_of_branchNormalisation GlobalTheory.T.branch_normalisation_holds

end GlobalTheory.CompanionTheory.Heights.CurveBranch
