import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.NonvanishingBesselPeriod
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLe

namespace Formalism.MainNotions.StandardLattice

theorem integrality_of_commutation (D : Formalism.BasicNotions.D7) (hF : Formalism.MainNotions.PlaceDegreeData.DiscreteSeriesLowestKTypeFormula D) (hW : Formalism.MainNotions.DiscreteSeriesWeylDimension.WeylForK)
    (hM : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne) : Adm3 D :=
  ⟨Formalism.MainNotions.J.lowest_K_type_integral_formula D hF, nonvanishing_bessel_period D, Formalism.MainNotions.DiscreteSeriesWeylDimension.lowest_K_type_count_of_weyl D hW hM⟩

end Formalism.MainNotions.StandardLattice
