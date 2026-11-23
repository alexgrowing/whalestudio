import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Published.AbelianDeRham

theorem rigid_of_free_of_crystallineDeRham : GlobalTheory.Published.AbelianDeRham.Free →
    GlobalTheory.Published.CrystallineDeRham → GlobalTheory.Published.AbelianDeRham.Rigid := by
  intro H H' R _ A _ g hA hg I κ hκ R₀ _ π hπ hI A₀ _ i h
  have := hA.smooth
  have := hA.proper
  obtain ⟨h₁, -⟩ := H' R I κ hκ R₀ π hπ hI _ _ (A.hom ≫ 𝟙 _) A₀.hom i inferInstance inferInstance
    inferInstance (by rw [Category.comp_id]; exact h.1) (liftMor κ h).isMor
  have hP := (H R A g hA hg).1
  refine ⟨fun c d e ↦ Subtype.ext (h₁.1 ?_), fun c ↦ ?_⟩
  · have := congrArg Subtype.val e
    simpa only [GrpMor.coe_pull] using this
  · obtain ⟨c', hc'⟩ := h₁.2 c.1
    have hm : c' ∈ prim (dp0 R) (𝟙 _) A := by
      rw [show prim (dp0 R) (𝟙 _) A = ⊤ from hP]; trivial
    exact ⟨⟨c', hm⟩, Subtype.ext (by rw [GrpMor.coe_pull]; exact hc')⟩

end GlobalTheory.Published.AbelianDeRham
