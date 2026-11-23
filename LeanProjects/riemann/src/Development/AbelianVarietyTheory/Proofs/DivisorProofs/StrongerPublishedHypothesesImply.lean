import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeilStatement

open GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop

theorem Hypotheses2.toClassicalTheorems : Hypotheses2 → Hypotheses₂ := fun h => h.toClassicalTheoremsOf GlobalTheory.T.toroidalFlagProportionality_of_goodChernWeil

end GlobalTheory.CovTop
