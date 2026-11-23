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

theorem geomIrr_preimage_of_isIso_restrict (V : Type) [CommRing V] (X X' : Scheme.{0}) (s : X ⟶ Sp V) (π : X' ⟶ X)
    (Xw O : X.Opens) (hle : Xw ≤ O) (hiso : IsIso (π ∣_ O)) (hg : GeomIrr s Xw) :
    GeomIrr (π ≫ s) (π ⁻¹ᵁ Xw) := by
  have h1 : IsIso ((π ∣_ O) ∣_ (O.ι ⁻¹ᵁ Xw)) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hiso _
  have h2 : IsIso (π ∣_ (O.ι ''ᵁ (O.ι ⁻¹ᵁ Xw))) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictRestrict π O (O.ι ⁻¹ᵁ Xw))).mp h1
  have e : O.ι ''ᵁ (O.ι ⁻¹ᵁ Xw) = Xw := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hle
  rw [e] at h2
  intro k _ f hf
  haveI := hg k f hf
  have hcomm : (π ⁻¹ᵁ Xw).ι ≫ π ≫ s = (π ∣_ Xw) ≫ Xw.ι ≫ s := by
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  let m := pullback.map ((π ⁻¹ᵁ Xw).ι ≫ π ≫ s) (spMap f) (Xw.ι ≫ s) (spMap f) (π ∣_ Xw) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hcomm]) (by simp)
  haveI : IsIso m := pullback.map_isIso _ _ _ _ _ _ _ _ _
  let H := Scheme.homeoOfIso (asIso m)
  exact Function.Surjective.irreducibleSpace H.symm.continuous H.symm.surjective

end GlobalTheory.FlatModel
