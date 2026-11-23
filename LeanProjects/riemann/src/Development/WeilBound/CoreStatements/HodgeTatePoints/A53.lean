import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutOneGenerator
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGlobalFunctionsIntegral
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutNonempty
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutComponent
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutZeroNotLe
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutDimLower
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleProductPos
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointDegreePos
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutMultPos
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimSeq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZeroIdealChart
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoReduce
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PQuotTrans
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoPiece
import Development.WeilBound.CoreStatements.HodgeTatePoints.FullOfCharts
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSplit
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWLift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWGen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Assembly
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDrop
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCount
import Development.WeilBound.CoreStatements.HodgeTatePoints.A36

namespace PositivityTheory.HtPt.Ktw

theorem a52 :
    GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator.proof
    GroundTheory.Heights₂.Heights.Kleiman.GlobalFunctionsIntegral.proof

theorem a53 :
    GroundTheory.Heights₂.Heights.Kleiman.CutNonempty.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutNonempty.proof a52

theorem a54 :
    GroundTheory.Heights₂.Heights.Kleiman.CutComponent.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutComponent.proof
    GroundTheory.Heights₂.Heights.Kleiman.CutZeroNotLe.proof a53
    GroundTheory.Heights₂.Heights.Kleiman.CutDimLower.proof

theorem a55 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleProductPos.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleProductPos.proof hR
    GroundTheory.Heights₂.Heights.Kleiman.PointDegreePos.proof a54
    GroundTheory.Heights₂.Heights.Kleiman.CutMultPos.proof

theorem a56 :
    GroundTheory.Heights₂.Heights.Kleiman.ClaimSeq.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.ClaimSeq.proof
    GroundTheory.Heights₂.Heights.Kleiman.ZeroIdealChart.proof

theorem a57 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Filt.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Filt.proof
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.Exists.proof

theorem a58 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Reduce.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Reduce.proof a57
    GroundTheory.Heights₂.Heights.Kleiman.QuotTrans.proof
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Piece.proof

theorem a59 :
    GroundTheory.Heights₂.Heights.Kleiman.ClaimVanish.Statement.{0, 0} :=
  PositivityTheory.HtPt.KtwS.ClaimVanish.assembled a58 a4
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.TwistSplit.proof a56

theorem a60 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Statement.{0, 0, 0} :=
  PositivityTheory.HtPt.KtwS.StepTwo.assembled a58 a4
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.TwistSplit.proof

theorem a61 :
    GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Lift.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Lift.proof a56 a59 a60

theorem a62 :
    GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen.proof a4
    GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated.proof

theorem a63 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.assembled a39 a43 a48 a51 hR (a55 hR) a61 a62
    GroundTheory.Heights₂.Heights.Kleiman.PointGenerated.proof

theorem a72 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleNefPlusAmple.assembled a39 a43 a48 a51 hR (a55 hR) a61 a62
    GroundTheory.Heights₂.Heights.Kleiman.PointGenerated.proof

end PositivityTheory.HtPt.Ktw
