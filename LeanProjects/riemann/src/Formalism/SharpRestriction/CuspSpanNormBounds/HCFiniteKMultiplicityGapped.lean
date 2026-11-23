import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG

noncomputable section

namespace Formalism.MainNotions.BridgeDS3

open Formalism.MainNotions Formalism.MainNotions.S

theorem discrete_series_exists_gapped [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExistsG] : DiscreteSeriesWeylDimension.DiscreteSeriesExistsG := Fact.out

variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExistsG] in

theorem discrete_series_exists_fallback : DiscreteSeriesWeylDimension.DiscreteSeriesExistsFallback :=
  DiscreteSeriesWeylDimension.exists_fallback_of_exists_gapped discrete_series_exists_gapped

theorem lowest_K_type_mult_one_gapped [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG] : DiscreteSeriesWeylDimension.LowKMultOneG := Fact.out

theorem discrete_series_unique_gapped [Fact Formalism.MainNotions.BridgeLemma₂.deg_DSUniqG] : BridgeLemma₂.deg_DSUniqG := Fact.out

theorem discrete_series_unique_bessel [Fact Formalism.MainNotions.LeviCoordinates.DiscreteSeriesUniqueBesselGapped] : LeviCoordinates.DiscreteSeriesUniqueBesselGapped := Fact.out

theorem HC_finite_K_multiplicity_gapped [Fact Formalism.MainNotions.BridgeCPX.HCMultDSG] : BridgeCPX.HCMultDSG := Fact.out

end Formalism.MainNotions.BridgeDS3

end
