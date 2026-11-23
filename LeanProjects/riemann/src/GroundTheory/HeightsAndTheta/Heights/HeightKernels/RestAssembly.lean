import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestTop
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCaseCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCaseDecomp
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCaseSharp
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCompareReal
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutFlagKillsIdeal
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutHomDecomp
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutIdealSum
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutIKillsIdeal
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutLieFirst
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutLieLast
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutPrimeEq
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutPsiFlag
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutRealSyzygy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutRestHom
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutStairHom
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutStairNonzero
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTermEq
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTransportFirst
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTransportLast
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTransportPsum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem RestTermSharp.ofRestTerms (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestTerms.FlagIntegralKillsPowerSums.Statement)
    (h₃ : RestTerms.RestTermWellDefined.Statement) (h₄ : RestTerms.SameFactorBound.Statement)
    (h₅ : RestTerms.RestBound.Statement) : RestTermSharp.Statement := by
  have hIdealSum : RestCutIdealSum.Statement := RestCutIdealSum.proof
  have hPsum : RestCutTransportPsum.Statement := RestCutTransportPsum.proof
  have hFlagKills : RestCutFlagKillsIdeal.Statement := RestCutFlagKillsIdeal.proof h₂ hIdealSum
  have hIKills : RestCutIKillsIdeal.Statement := RestCutIKillsIdeal.proof hIdealSum hPsum
  have hStairNonzero : RestCutStairNonzero.Statement := RestCutStairNonzero.proof h₁ hFlagKills
  have hCompare : RestCutCompare.Statement :=
    RestCutCompare.proof h₁ RestCutStairHom.proof hFlagKills hIKills
  have hCaseCompare : RestCutCaseCompare.Statement :=
    RestCutCaseCompare.proof h₄ RestCutRestHom.proof hStairNonzero hCompare RestCutCompareReal.proof
  have hPsiFlag : RestCutPsiFlag.Statement := RestCutPsiFlag.proof
  have hSyzygy : RestCutRealSyzygy.Statement := RestCutRealSyzygy.proof h₃ hPsiFlag
  have hTermEq : RestCutTermEq.Statement := RestCutTermEq.proof hSyzygy hPsiFlag hPsum
  have hCaseDecomp : RestCutCaseDecomp.Statement :=
    RestCutCaseDecomp.proof RestCutRestHom.proof RestCutHomDecomp.proof hPsum
  have hCaseSharp : RestCutCaseSharp.Statement :=
    RestCutCaseSharp.proof h₅ hCaseCompare hCaseDecomp hTermEq RestCutPrimeEq.proof
  exact RestTermSharp.proof hCaseSharp RestCutTransportLast.proof RestCutTransportFirst.proof
    RestCutLieLast.proof RestCutLieFirst.proof

theorem RestTerm.ofRestTerms (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestTerms.FlagIntegralKillsPowerSums.Statement)
    (h₃ : RestTerms.RestTermWellDefined.Statement) (h₄ : RestTerms.SameFactorBound.Statement)
    (h₅ : RestTerms.RestBound.Statement) : RestTerm.Statement :=
  RestTerm.proof (RestTermSharp.ofRestTerms h₁ h₂ h₃ h₄ h₅)

end GroundTheory.Heights₂.Heights
