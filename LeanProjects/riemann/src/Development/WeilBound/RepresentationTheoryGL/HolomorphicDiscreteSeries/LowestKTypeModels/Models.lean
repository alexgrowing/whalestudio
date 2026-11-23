import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.LowestKTypeModel
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.LowestQLeRank

namespace PositivityTheory.RgHe.LowestKTypeModel

theorem ofInt : PositivityTheory.RgHe.OfInt := PositivityTheory.RgHe.LowestKTypeUnitIntegral.of_integral_holds

theorem seed : PositivityTheory.RgHe.Seed := PositivityTheory.RgHe.LowestKTypeUnitIntegral.lowestKTypeModel

theorem models : PositivityTheory.RgHe.Models := PositivityTheory.RgHe.LowestKTypeUnitIntegral.models_holds

end PositivityTheory.RgHe.LowestKTypeModel
