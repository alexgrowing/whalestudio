import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatCodimOne

theorem coheight_map_le_one {X Y : Scheme.{0}} (q : Y ⟶ X) (hq : GeneralizingMap q) (y : Y)
    (hy : Order.coheight y ≤ 1) : Order.coheight (q y) ≤ 1 := by
  have hy' := (Order.coheight_le_coe_iff (n := 1)).1 hy
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun z hz ↦ ?_
  obtain ⟨y', h₁, rfl⟩ := hq (show z ⤳ q y from hz.le)
  have hlt : y < y' := ⟨h₁, fun h ↦ hz.not_ge (Specializes.map h q.continuous)⟩
  have hm : IsMax y' := by simpa using hy' y' hlt
  have : IsMax (q y') := fun w hw ↦ by
    obtain ⟨y'', h₂, rfl⟩ := hq (show w ⤳ q y' from hw)
    exact Specializes.map (hm (show y' ≤ y'' from h₂)) q.continuous
  simpa using this

theorem preimage_contains_codim_le_one : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) [Flat q] (W : X.Opens), (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) := by
  intro X Y q _ W hW y hy
  show q y ∈ W
  apply hW
  rw [ringKrullDim_stalk_eq_coheight] at hy ⊢
  have h1 : Order.coheight y ≤ 1 := by exact_mod_cast hy
  have := coheight_map_le_one q (Flat.generalizingMap q) y h1
  exact_mod_cast this

end GlobalTheory.FlatCodimOne
