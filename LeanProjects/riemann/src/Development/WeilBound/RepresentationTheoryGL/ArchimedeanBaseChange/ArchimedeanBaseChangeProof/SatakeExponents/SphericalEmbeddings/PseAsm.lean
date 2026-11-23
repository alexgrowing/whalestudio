import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseSat

namespace PositivityTheory.Rg.BcB.N3.Pse

open PositivityTheory.Rg.BcB.N3 GlobalTheory.SmGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sphEmb_of (hG : GL2SphericalSwap k) (hS : StageLift k) (hE : ExpSph k) (hP : SatPerm k) (hB : Bubble k) : SphEmb k := by
  intro n ξ hm V _ _ π hs hi hsph hq
  obtain ⟨η, f, hf⟩ := hE n V π hs hi hsph
  obtain ⟨σ, rfl⟩ := hP n ξ η V π hs hi hsph hq ⟨f, hf⟩
  exact hB hS hG n ξ hm σ V π hi hsph ⟨f, PositivityTheory.Rg.BcB.N3.PseSat.injective_of_ne_zero hi f hf⟩

end PositivityTheory.Rg.BcB.N3.Pse
