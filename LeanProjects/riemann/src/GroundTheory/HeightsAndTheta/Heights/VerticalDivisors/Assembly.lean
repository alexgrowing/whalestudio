import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.AssemblyPartial
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgFinite
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartDomain
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecDomain
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowSecDvd
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormIrreducible
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormDvd
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgFieldChange
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenChowIrreducible
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBTorsionFree
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGaussDVR
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PVertSpec
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PResidueAlgIndep
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgField
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PCodimOnePrimeAvoid
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreCut
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenericFibreDrop
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreCompDim
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecCompDim
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecIdealOfPrime
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecFirstNeField
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecLength
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormFormGeneric
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormForm
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowSecDegree
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecLinNZD
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBLinInj
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecMax
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecResidue
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormIdentity
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.POrdEq
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGaussEq
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IsChowFormCMul
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenSecKer
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChart
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsOrd
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCut
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealBelow
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealDim
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimOfChowForm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormExists
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

theorem SecAlgFinite.full : SecAlgFinite.Statement := SecAlgFinite.proof IncidenceNull.full
theorem ChartDomain.full : ChartDomain.Statement := ChartDomain.proof
theorem GenSecDomain.full : GenSecDomain.Statement :=
  GenSecDomain.proof ChartDomain.full GroundTheory.Heights₂.Heights.IncidenceGeneric.full
    (GroundTheory.Heights₂.Heights.IncIdealBelow.proof GroundTheory.Heights₂.Heights.ChowFormMultiHomog.full)
theorem SecAlgField.full : SecAlgField.Statement := SecAlgField.proof SecAlgFinite.full GenSecDomain.full
theorem ChowSecDvd.full : ChowSecDvd.Statement := ChowSecDvd.proof IncidenceNull.full
theorem NormFormIrreducible.full : NormFormIrreducible.Statement := NormFormIrreducible.proof
theorem NormFormDvd.full : NormFormDvd.Statement := NormFormDvd.proof
theorem SecAlgFieldChange.full : SecAlgFieldChange.Statement := SecAlgFieldChange.proof
theorem GenChowIrreducible.full : GenChowIrreducible.Statement :=
  GenChowIrreducible.proof GroundTheory.Heights₂.Heights.IncIdealPrime.full
    GroundTheory.Heights₂.Heights.ChowFormMultiHomog.full

theorem SpecFirstNeField.full : SpecFirstNeField.Statement :=
  have hDim : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
    GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
  SpecFirstNeField.proof
    (GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full)
    GroundTheory.Heights₂.Heights.ConeDimComponent.full
    (GroundTheory.Heights₂.Heights.ChowFormExists.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full)
    GroundTheory.Heights₂.Heights.IncidenceZeroLocus.proof

theorem SecBTorsionFree.full : SecBTorsionFree.Statement := SecBTorsionFree.proof ParDVRIsDVR.full
theorem GaussDVR.full : GaussDVR.Statement := GaussDVR.proof ParDVRIsDVR.full
theorem VertSpec.full : VertSpec.Statement := VertSpec.proof
theorem ResidueAlgIndep.full : ResidueAlgIndep.Statement := ResidueAlgIndep.proof

theorem CodimOnePrimeAvoid.full : CodimOnePrimeAvoid.Statement := CodimOnePrimeAvoid.proof
theorem FibreCut.full : FibreCut.Statement := FibreCut.proof CodimOnePrimeAvoid.full
theorem GenericFibreDrop.full : GenericFibreDrop.Statement := GenericFibreDrop.proof

theorem ChowFormSectionVertical.of_remaining
    (hGenSep : GenSecSeparable.Statement) (hFibre : FibreClosedComponent.Statement)
    (hKer : GenSecKer.Statement) (hChart : SpecChart.Statement) (hOrd : FiniteOrd.Statement) :
    ChowFormSectionVertical.Statement := by
  have hDim : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
    GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
  have hCone : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
    GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full
  have hExist : GroundTheory.Heights₂.Heights.ChowFormExists.Statement :=
    GroundTheory.Heights₂.Heights.ChowFormExists.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full
  have cnf : ChowNormForm.Statement :=
    ChowNormForm.proof
      (ChowNormFormGeneric.proof SecAlgFinite.full GenSecDomain.full hGenSep ChowSecDvd.full
        NormFormIrreducible.full GenChowIrreducible.full NormFormDvd.full)
      SecAlgFieldChange.full
  have csd : ChowSecDegree.Statement := ChowSecDegree.proof cnf ChowFormHomog.full NormFormEval.full
  have nzd : SecLinNZD.Statement := SecLinNZD.proof cnf NormFormEval.full SpecFirstNeField.full
  have lininj : SecBLinInj.Statement :=
    SecBLinInj.proof SecBGeneric.full SecBTorsionFree.full nzd ParAlgIndep.full
  have fcd : FibreCompDim.Statement := FibreCompDim.proof hFibre FibreCut.full GenericFibreDrop.full
  have scd : SpecCompDim.Statement := SpecCompDim.proof hCone fcd
  have sip : SecIdealOfPrime.Statement :=
    SecIdealOfPrime.proof scd hExist ResidueAlgIndep.full SecAlgField.full hKer
  have smax : SpecMax.Statement := SpecMax.proof SecBFinite.full sip
  have sres : SpecResidue.Statement := SpecResidue.proof csd cnf scd hExist ResidueAlgIndep.full
  have slen : SpecLength.Statement :=
    SpecLength.proof hChart hOrd ParDVRIsDVR.full SecBFinite.full lininj
  have nid : NormIdentity.Statement :=
    NormIdentity.proof cnf SecBFinite.full SecBTorsionFree.full SecBGeneric.full NormFormLocalization.full
      NormFormEval.full ParAlgIndep.full ParFracIsFractionRing.full ParDVRIsDVR.full
  have oeq : OrdEq.Statement :=
    OrdEq.proof nid NormLength.full LengthDecomp.full smax slen sres VertSpec.full lininj
      SecBFinite.full SecBTorsionFree.full ParDVRIsDVR.full
  have geq : GaussEq.Statement := GaussEq.proof oeq GaussDVR.full ParDVRIsDVR.full
  exact Main.proof geq PrimitiveScale.full VertTermEq.full

end GroundTheory.Heights₂.Heights.Vertical
