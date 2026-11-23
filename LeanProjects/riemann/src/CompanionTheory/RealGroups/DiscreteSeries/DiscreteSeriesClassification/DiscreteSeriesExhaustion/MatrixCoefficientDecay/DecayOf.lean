import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul

namespace CompanionTheory.RgExh.Dec

open CompanionTheory.RgExh

theorem decay_of (hS : Start) (hJ : Labels) (hL : Back) : StepChar → Decay := by
  intro hSC n
  obtain ⟨B, hB⟩ := hJ hSC n
  exact ⟨B, fun ε H _ _ _ σ D E hK χ ss hU _ hL2 hC hG hF => hL hSC n ε H σ D E hK χ ss hU hL2 hC fun A μ hA hμ =>
    hB ε H σ D E hK χ ss hU hC hG hF A μ hA hμ (fun u ξ => hS n ε H σ D E hK hU hL2 A μ hA hμ u (ξ : H))⟩

end CompanionTheory.RgExh.Dec
