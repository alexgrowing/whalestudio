import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNormals
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlLineHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlIntHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlPtDCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChainStatement

open Formalism.L2.SG.Pf.MainEqSteps

namespace GlobalTheory

theorem stepNormalsG_holds : StepNormalsG :=
  Formalism.L2.SG.NGCut.NormalInvariants.Gen.stepNormalsG_of
    (Formalism.L2.SG.Pf.nmlInvG_of Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine_holds
      Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep_holds)
    Formalism.L2.SG.NGCut.NormalCount.NormCount_holds
    GlobalTheory.T.equalWords_nonGeneric_estimates_chain.2.2.2.1

end GlobalTheory
