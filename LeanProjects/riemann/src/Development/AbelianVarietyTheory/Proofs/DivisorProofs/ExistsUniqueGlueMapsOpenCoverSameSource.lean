import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GlueDesc

theorem exists_unique_glue : ∀ (X Y P : Scheme.{0}) (J : Type) (e : J → (P ⟶ X)) (g : J → (P ⟶ Y)), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ P), a ≫ e i = b ≫ e j → a ≫ g i = b ≫ g j) → ∃ β : X ⟶ Y, (∀ j, e j ≫ β = g j) ∧ ∀ β' : X ⟶ Y, (∀ j, e j ≫ β' = g j) → β' = β := by
  intro X Y P J e g he hcov hcomp
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers J (fun _ => P) e (fun x => by
    obtain ⟨j, y, hy⟩ := hcov x
    exact ⟨j, y, hy⟩)
  have hm : ∀ i j : 𝒰.I₀, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j :=
    fun i j => hcomp i j _ _ _ pullback.condition
  refine ⟨𝒰.glueMorphisms g hm, fun j => 𝒰.ι_glueMorphisms g hm j, fun β' hβ' => ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  change e j ≫ β' = e j ≫ _
  rw [hβ' j]
  exact (𝒰.ι_glueMorphisms g hm j).symm

end GlobalTheory.GlueDesc
