import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

instance kinst_compact (ε : Fin n → Bool) : CompactSpace (KG ε) := compactSpace_KG ε

instance kinst_secondCountable (ε : Fin n → Bool) : SecondCountableTopology (KG ε) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

end ReciprocityTheory.ChartRestriction.DS
