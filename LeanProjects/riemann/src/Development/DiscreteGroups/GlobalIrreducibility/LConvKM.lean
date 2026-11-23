import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.DiscreteGroups.GlobalIrreducibility.LConvKMCore

namespace DiscreteGroups.sglob.LConv

theorem extremeExists : ExtremeExists := by
  intro G M _ _ _ ρ hspan B₀ hB₀ f hf
  obtain ⟨B, ⟨hB, hext⟩, hBf⟩ := DiscreteGroups.sglob.LConvKM.extreme_exists_core ρ hspan B₀ hB₀ f hf
  exact ⟨B, ⟨hB, hext⟩, hBf⟩

end DiscreteGroups.sglob.LConv
