import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

variable {X Y : Scheme.{0}} (L : LB X) {k k' : ℕ}

abbrev secChart (i : Fin 1 → L.ι) : X.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 X) i

def SecRatioEq (u v : Y ⟶ X) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k') : Prop :=
  ∀ i i' : Fin 1 → L.ι,
    (Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
        ((u.app (secChart L i)).hom (s₁.f i)) *
      (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
        ((v.app (secChart L i')).hom (t₂.f i')) =
    (Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
        ((u.app (secChart L i)).hom (s₂.f i)) *
      (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
        ((v.app (secChart L i')).hom (t₁.f i'))

def SecCoNonzero (u v : Y ⟶ X) (s : H0 L k) (t : H0 L k') : Prop :=
  ∃ (y : Y) (i i' : Fin 1 → L.ι), y ∈ Y.basicOpen ((u.app (secChart L i)).hom (s.f i)) ∧
    y ∈ Y.basicOpen ((v.app (secChart L i')).hom (t.f i'))

end GlobalTheory.Mum
