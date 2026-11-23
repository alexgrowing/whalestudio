import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem hs_isFinite (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X)
    (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O)
    (hu : IsUnit (x0 P'.f)) : IsFinite (Hs P' x0 hu).hom := by
  haveI : Module.Finite (Localization.Away P'.f) P'.B := P'.fin.finite
  haveI : Module.Finite (OL P' x0 hu) (Bt P' x0 hu) := Module.Finite.base_change _ _ _
  haveI : Module.Finite O (OL P' x0 hu) := inferInstanceAs (Module.Finite O O)
  haveI : Module.Finite O (Bt P' x0 hu) := Module.Finite.trans (OL P' x0 hu) (Bt P' x0 hu)
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap O (Bt P' x0 hu))))
  rw [IsFinite.SpecMap_iff]
  rw [CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory.FinPartAt
