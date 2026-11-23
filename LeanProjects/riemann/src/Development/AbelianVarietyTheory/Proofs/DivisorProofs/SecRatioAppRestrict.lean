import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secRatio_app_restrict {Y Z : Scheme.{0}} (h : Z ⟶ Y) {U W : Y.Opens} (hle : W ≤ U)
    (hle' : h ⁻¹ᵁ W ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (Z.presheaf.map (homOfLE hle').op).hom ((h.app U).hom x) =
      (h.app W).hom ((Y.presheaf.map (homOfLE hle).op).hom x) := by
  have := congrArg (fun φ => φ.hom x) (h.naturality (homOfLE hle).op)
  simpa using this.symm

theorem secRatioEq_comp : ∀ {X Y Z : Scheme.{0}} (L : LB X) {k k' : ℕ} (u v : Y ⟶ X) (h : Z ⟶ Y) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k'), SecRatioEq L u v s₁ s₂ t₁ t₂ → SecRatioEq L (h ≫ u) (h ≫ v) s₁ s₂ t₁ t₂ := by
  intro X Y Z L k k' u v h s₁ s₂ t₁ t₂ hR i i'
  have e := congrArg (h.app (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')).hom (hR i i')
  simp only [map_mul] at e
  simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [secRatio_app_restrict h (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i),
    secRatio_app_restrict h (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i'),
    secRatio_app_restrict h (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i),
    secRatio_app_restrict h (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')]
  exact e

end GlobalTheory.Mum
