import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensSpan
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPointIdealMultiProj
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleTrdegGe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleTrdegLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionForms
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionDiv
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtOfSaturated
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PProjIdealFormValue
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTruncSpecialize
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleChartSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineDegree
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalFlat
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConePolyLocalization
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarInj
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarNumerator
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarSurj
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarUnit
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocalRing
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocFrac
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocalize
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocNoetherian
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocResidue
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocSeparate
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocUnits
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleMinimal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreNonempty
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreRelDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFiniteAlgebraLengthSum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalizedQuotientLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartLocDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PNoetherIntegralClosure
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFiniteRank
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalIntegral
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLengthSum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalMaxIdeals
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalResidueLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PValuativeCentre
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForwardLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open GroundTheory.Heights₂.Heights.FieldNumbers in

theorem DivPushForwardLocalZero : FieldNumbers.DivPushForwardLocal.Statement.{0} := by
  have hq := DegZeroLocQuot.proof.{0}
  have hdzl := DegZeroLocLocal.proof hq
  have hdzn := DegZeroLocNoetherian.proof hq
  have hmh := MChartHomog.proof.{0}
  have hmd := MChartDehomog.proof.{0}
  have hmt := MChartTrdeg.proof hmh
  have hdzr := DegZeroLocalRing.proof hdzl hdzn
    (DegZeroLocDim.proof hmh hmt (MChartLocDim.proof hq hmd hmh))
  have hnum := ConeVarNumerator.proof hq
  have hcone := ConeLocalLength.proof LocalizedQuotientLength.proof
    (ConeLocalFlat.proof (ConePolyLocalization.proof hdzl (ConeVarUnit.proof hq hnum)
      ConeVarSurj.proof (ConeVarInj.proof hnum)))
  have hfr := DegZeroLocFrac.proof.{0}
  have hff := FibreFinite.proof.{0}
  have hint := SemilocalIntegral.proof ValuativeCentre.proof.{0}
  have hrank := SemilocalFiniteRank.proof hff
    (SemilocalFinite.proof hint
      (LocalIntegralClosureFinite.proof NoetherIntegralClosureFinite.proof
        (FunctionFieldFinite.proof hmd hmt) hq hmd hfr) hdzn) hfr
  have hfrd := FibreRelDim.proof.{0}
  have hlz := DegZeroLocLocalize.proof.{0}
  have hres := DegZeroLocResidue.proof.{0}
  have hmaxi := SemilocalMaxIdeals.proof hff hfrd (FibreNonempty.proof hrank hdzr)
    DegZeroLocUnits.proof DegZeroLocSeparate.proof hlz (SemilocalResidueLength.proof hres hrank hlz)
  have hlen := SemilocalLength.proof
    (SemilocalLengthSum.proof hff hrank hdzr FiniteAlgebraLengthSum.proof hmaxi) hfrd
    DivCycleMinimal.proof hcone
  exact DivPushForwardLocal.proof DivCycleMinimal.proof hcone hdzr hrank hlen

theorem FlagBundleDim.full : FlagBundleDim.Statement :=
  FlagBundleDim.proof TwistedDualGensSpan.proof
    (SpanBundleDim.proof PointIdealMultiProj.proof SpanBundleTrdegGe.proof SpanBundleTrdegLe.proof)

theorem NumericalSegre.full : NumericalSegre.Statement :=
  NumericalSegre.of_open FlagBundleDim.full FlagBundleSectionForms.proof
    (FlagBundleSectionDiv.proof FlagBundleDim.full MultAtOfSaturated.proof ProjIdealFormValue.proof
      TruncSpecialize.proof FlagBundleChartSection.proof)
    FlagLineSection.proof FlagLineDegree.proof DivPushForwardLocalZero

end GroundTheory.Heights₂.Heights.NumbersDVR
