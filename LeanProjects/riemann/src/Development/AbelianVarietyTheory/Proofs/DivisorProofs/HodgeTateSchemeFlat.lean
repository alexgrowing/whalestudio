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

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem flat_Bt : Module.Flat O (Bt P' x0 hu) := by
  haveI : Module.Free (Localization.Away P'.f) P'.B := P'.fin.free
  haveI : Module.Flat (OL P' x0 hu) (Bt P' x0 hu) := Module.Flat.baseChange _ _ _
  haveI : Module.Flat O (OL P' x0 hu) := inferInstanceAs (Module.Flat O O)
  exact Module.Flat.trans O (OL P' x0 hu) (Bt P' x0 hu)

theorem flat_Hs : Flat (Hs P' x0 hu).hom := by
  haveI := flat_Bt P' x0 hu
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap O (Bt P' x0 hu))))
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff).2 inferInstance

end GlobalTheory.FinPartAt

theorem GlobalTheory.FinPartAt.flat_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)), Flat (Hs P' x0 hu).hom := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu
  exact GlobalTheory.FinPartAt.flat_Hs P' x0 hu
