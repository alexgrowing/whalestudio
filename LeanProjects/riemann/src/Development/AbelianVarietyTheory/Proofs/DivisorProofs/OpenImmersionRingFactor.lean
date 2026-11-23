import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel

theorem chart_sections_factor : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) [IsOpenImmersion ξ],
    ∃ e : R →+* Γ(X, ξ.opensRange), ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (V : Y.Opens) (hV : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ ξ.opensRange), hV.fromSpec ≫ f = spMap ((f.appLE ξ.opensRange V hVU).hom.comp e) ≫ ξ := by
  intro X R _ ξ _
  have hU : IsAffineOpen ξ.opensRange := isAffineOpen_opensRange ξ
  have hr : Set.range hU.fromSpec.base ⊆ Set.range ξ.base := by
    rw [hU.range_fromSpec]; simp
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ξ hU.fromSpec hr)).hom, ?_⟩
  intro Y f V hV hVU
  rw [← hU.SpecMap_appLE_fromSpec f hV hVU]
  conv_lhs => rw [← IsOpenImmersion.lift_fac ξ hU.fromSpec hr]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom, Spec.map_preimage]

end GlobalTheory.FlatModel
