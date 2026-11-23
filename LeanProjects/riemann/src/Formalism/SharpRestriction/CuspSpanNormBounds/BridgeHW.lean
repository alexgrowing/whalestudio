import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension

noncomputable section

namespace Formalism.MainNotions.BridgeHW

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem highest_weight_exists_bis [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.HighestWeightExists] : DiscreteSeriesWeylDimension.HighestWeightExists := Fact.out

variable {eps : ℝ} (Fm : FamP eps)

variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.HighestWeightExists] in

theorem lWeylAll_of (weylLawBound : LocalBesselAndTopKernel.FirstSizeStatement) (gc : AdmissibleBoundsFromSource.GivC) : AdmissibleBoundsFromSource.FamilyWeylDimension Fm gc :=
  DiscreteSeriesWeylDimension.weyl_dimension_of_highest_weight Fm weylLawBound highest_weight_exists_bis gc

variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.HighestWeightExists] in

theorem lWeylU_of (weylLawBound : LocalBesselAndTopKernel.FirstSizeStatement) : ∀ Cg cb Cu cT CT C0, VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 :=
  DiscreteSeriesWeylDimension.lWeylU_of_open Fm weylLawBound highest_weight_exists_bis

end Formalism.MainNotions.BridgeHW

end
