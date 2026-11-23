import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLoc

namespace GlobalTheory.Sloc.CoefWeighted

theorem coefWeightedLoc_uncond : Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc :=
  ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc

instance : Fact (Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc) := ⟨coefWeightedLoc_uncond⟩

end GlobalTheory.Sloc.CoefWeighted
