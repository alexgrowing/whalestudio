import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PKaPSplit
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PKaPInert
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PKaPBound
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PRestPWellDefined
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PRestPBound
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PRestSummable
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.TauSumRearrangement
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PShOfPower
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTotOfPower
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDegPolyEvalX
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PCFlPos
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PShTotIndependent
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PShTotInvertiblePair
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PLimitsExist
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.TendstoSumPrimesInRestP
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.TotSumLineF
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PShFormula
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTotFormula
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.SingleDecompIsHomDecomp
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PCBounds
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PNormUbar
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTermA
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTermB
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTermC
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTermD
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PPrimesLogSum
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PHomDecompExists
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.LineFIsHomogeneous
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.ExistsDominantSubSmul
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Filter Topology

theorem KaPSplit.full : KaPSplit.Statement := KaPSplit.proof

theorem KaPInert.full : KaPInert.Statement := KaPInert.proof

theorem KaPBound.full : KaPBound.Statement := KaPBound.proof

theorem RestPBound.full : RestPBound.Statement := RestPBound.proof

theorem RestSummable.full : RestSummable.Statement := RestSummable.proof RestPBound.full

theorem HeightSumIdentity.full : HeightSumIdentity.Statement := HeightSumIdentity.proof

theorem ShTotIndependent.full : ShTotIndependent.Statement :=
  ShTotIndependent.proof ShOfPower.proof TotOfPower.proof DegPolyEval.proof CFlPos.proof

theorem ShTotInvertiblePair.full : ShTotInvertiblePair.Statement :=
  ShTotInvertiblePair.proof ShTotIndependent.full

theorem LimitsExist.full : LimitsExist.Statement :=
  LimitsExist.proof HeightSumIdentity.full ShTotInvertiblePair.full RestSummable.full

theorem HeightTauIdentity.full : HeightTauIdentity.Statement :=
  HeightTauIdentity.proof HeightSumIdentity.full RestSummable.full

theorem HeightEvaluation.full : HeightEvaluation.Statement := HeightEvaluation.proof HeightTauIdentity.full

theorem HeightLimitIdentity.full : HeightLimitIdentity.Statement :=
  HeightLimitIdentity.proof HeightTauIdentity.full ShFormula.full TotFormula.full

theorem CBounds.full : CBounds.Statement := CBounds.proof

theorem NormUbar.full : NormUbar.Statement := NormUbar.proof

theorem TermA.full : TermA.Statement := TermA.proof

theorem TermB.full : TermB.Statement := TermB.proof

theorem TermC.full : TermC.Statement := TermC.proof HeightLimitIdentity.full

theorem TermD.full : TermD.Statement := TermD.proof

theorem TheoremTUpper.full : TheoremTUpper.Statement :=
  TheoremTUpper.proof LimitsExist.full HeightEvaluation.full CBounds.full NormUbar.full TermA.full
    TermB.full TermC.full TermD.full PrimesLogSum.fullNat HomDecompExists.proof

theorem LimitTheorem.full : LimitTheorem.Statement := LimitTheorem.proof

theorem TheoremTLower.full : TheoremTLower.Statement := TheoremTLower.proof LimitTheorem.full

namespace EndSample

end EndSample

end GroundTheory.Heights₂.Heights.TheoremB
