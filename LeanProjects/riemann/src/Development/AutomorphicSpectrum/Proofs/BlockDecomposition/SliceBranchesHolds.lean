import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBranches
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHoldsStatement
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem sliceBranches : GroundTheory.Heights₂.Heights.SliceBranches.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranches.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.full
    GlobalTheory.T.branch_proper_at_point_holds
    GroundTheory.Heights₂.Heights.SliceMatricesOpen.full
    GroundTheory.Heights₂.Heights.ImplicitCurve.full

end GlobalTheory.CompanionTheory.Ar.SliceBranch
