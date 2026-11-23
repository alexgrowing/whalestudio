import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecSeparable
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreClosedComponent
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecKer
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFiniteOrd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

theorem FibreClosedComponent.full : FibreClosedComponent.Statement := FibreClosedComponent.proof
theorem FiniteOrd.full : FiniteOrd.Statement := FiniteOrd.proof
theorem FibreCompDim.full : FibreCompDim.Statement :=
  FibreCompDim.proof FibreClosedComponent.full FibreCut.full GenericFibreDrop.full

private theorem coneDim : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof
    (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof)
    GroundTheory.Heights₂.Heights.IncIdealPrime.full

private theorem chowExists : GroundTheory.Heights₂.Heights.ChowFormExists.Statement :=
  GroundTheory.Heights₂.Heights.ChowFormExists.proof
    (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof)
    GroundTheory.Heights₂.Heights.IncIdealPrime.full

theorem GenSecKer.full : GenSecKer.Statement := GenSecKer.proof SecAlgField.full coneDim
theorem SpecCompDim.full : SpecCompDim.Statement := SpecCompDim.proof coneDim FibreCompDim.full
theorem SecIdealOfPrime.full : SecIdealOfPrime.Statement :=
  SecIdealOfPrime.proof SpecCompDim.full chowExists ResidueAlgIndep.full SecAlgField.full GenSecKer.full
theorem SpecMax.full : SpecMax.Statement := SpecMax.proof SecBFinite.full SecIdealOfPrime.full

theorem ChowFormSectionVertical.of_chartPoint_secPoint_specChart
    (hTrdeg : ChartPointTrdeg.Statement) (hSep : SecPointSeparable.Statement)
    (hChart : SpecChart.Statement) : ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_remaining
    (GenSecSeparable.proof SecAlgFinite.full GenSecDomain.full hTrdeg hSep)
    FibreClosedComponent.full GenSecKer.full hChart FiniteOrd.full

end GroundTheory.Heights₂.Heights.Vertical
