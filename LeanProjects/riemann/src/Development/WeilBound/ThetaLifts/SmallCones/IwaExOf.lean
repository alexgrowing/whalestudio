import Development.WeilBound.ThetaLifts.SmallCones.IwaGlob
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.MemLatWIff

noncomputable section

namespace PositivityTheory.ThKCT

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem iwaEx_of (hS : StabEx) : IwaEx := by
  intro F E _ _ _ _ _ σ B n n₁ X r s H hB hX hx h0 K hK
  obtain ⟨K₀, -, -, k1, k2, -⟩ := hS F E σ B n X r s hB hX
  obtain rfl : K = K₀ := Subgroup.ext fun g => (hK g).trans (k1 g).symm
  exact ⟨k2, IwaG.iwa_glob hB hX hx h0 (fun v _ hg => PositivityTheory.ThKG.Loc.Iwa.iwaLoc hB (Or.inl hX) hx h0 v hg) hK⟩

end PositivityTheory.ThKCT

end
