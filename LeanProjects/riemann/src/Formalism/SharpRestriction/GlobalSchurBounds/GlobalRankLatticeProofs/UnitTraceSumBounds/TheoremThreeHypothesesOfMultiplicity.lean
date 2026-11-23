import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IntegralityOfCommutation
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.WeylForK

namespace Formalism.MainNotions.StandardLattice

theorem weylForK_holds : Formalism.MainNotions.DiscreteSeriesWeylDimension.WeylForK := weylForK_closed

theorem lowest_K_type_dimension_of_multiplicity (D : Formalism.BasicNotions.D7) (hM : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne) : FamilyMassLastLine D :=
  Formalism.MainNotions.DiscreteSeriesWeylDimension.lowest_K_type_count_of_weyl D weylForK_holds hM

theorem theorem_three_hypotheses_of_multiplicity (D : Formalism.BasicNotions.D7) (hF : Formalism.MainNotions.PlaceDegreeData.DiscreteSeriesLowestKTypeFormula D) (hM : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne) : Adm3 D :=
  integrality_of_commutation D hF weylForK_holds hM

end Formalism.MainNotions.StandardLattice
