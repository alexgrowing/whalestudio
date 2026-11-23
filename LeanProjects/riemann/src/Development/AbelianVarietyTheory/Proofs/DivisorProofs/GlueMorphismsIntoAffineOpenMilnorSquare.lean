import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualOpen

theorem glue_into_affineOpen (S : Scheme.{0}) [IsAffine S] (U T T₁ T₂ T₀ : Over S) (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T)
    (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂) (hM : Milnor j₁.left j₂.left k₁.left k₂.left) (V : U.left.Opens)
    (hV : IsAffineOpen V) (u₁ : T₁ ⟶ U) (u₂ : T₂ ⟶ U) (hk : k₁ ≫ u₁ = k₂ ≫ u₂)
    (h₁ : ∀ x, u₁.left x ∈ V) (h₂ : ∀ x, u₂.left x ∈ V) :
    ∃ u : T ⟶ U, j₁ ≫ u = u₁ ∧ j₂ ≫ u = u₂ := by
  haveI : IsAffine V.toScheme := hV
  have r₁ : Set.range u₁.left ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact h₁ x
  have r₂ : Set.range u₂.left ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact h₂ x
  set a₁ := IsOpenImmersion.lift V.ι u₁.left r₁ with ha₁
  set a₂ := IsOpenImmersion.lift V.ι u₂.left r₂ with ha₂
  have f₁ : a₁ ≫ V.ι = u₁.left := IsOpenImmersion.lift_fac _ _ _
  have f₂ : a₂ ≫ V.ι = u₂.left := IsOpenImmersion.lift_fac _ _ _
  have hk' : k₁.left ≫ a₁ = k₂.left ≫ a₂ := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, f₁, f₂]
    exact congrArg CommaMorphism.left hk
  have w : a₁.appTop ≫ k₁.left.appTop = a₂.appTop ≫ k₂.left.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hk']
  set b := hM.cart.lift a₁.appTop a₂.appTop w with hb
  have b₁ : b ≫ j₁.left.appTop = a₁.appTop := hM.cart.lift_fst _ _ _
  have b₂ : b ≫ j₂.left.appTop = a₂.appTop := hM.cart.lift_snd _ _ _
  haveI := hM.aff
  let a : T.left ⟶ V.toScheme := T.left.toSpecΓ ≫ Spec.map b ≫ V.toScheme.isoSpec.inv
  have e₁ : j₁.left ≫ a = a₁ := by
    simp only [a]
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, b₁, ← Scheme.toSpecΓ_naturality_assoc,
      ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have e₂ : j₂.left ≫ a = a₂ := by
    simp only [a]
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, b₂, ← Scheme.toSpecΓ_naturality_assoc,
      ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have hover : (a ≫ V.ι) ≫ U.hom = T.hom := by
    apply ext_of_isAffine
    apply hM.cart.hom_ext
    · rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]; congr 1
      simp only [Category.assoc]; rw [reassoc_of% e₁, reassoc_of% f₁, Over.w u₁, Over.w j₁]
    · rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]; congr 1
      simp only [Category.assoc]; rw [reassoc_of% e₂, reassoc_of% f₂, Over.w u₂, Over.w j₂]
  refine ⟨Over.homMk (a ≫ V.ι) hover, ?_, ?_⟩
  · ext1; simp only [Over.comp_left, Over.homMk_left]; rw [← Category.assoc, e₁, f₁]
  · ext1; simp only [Over.comp_left, Over.homMk_left]; rw [← Category.assoc, e₂, f₂]

end GlobalTheory.DualOpen
