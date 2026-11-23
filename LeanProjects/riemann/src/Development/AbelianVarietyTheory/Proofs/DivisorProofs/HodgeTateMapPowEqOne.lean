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

theorem aH_pow_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π), aH P' x0 hu hg.1 ^ q = 1 := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg
  have hinj : Function.Injective (pushHom hg (Hs P' x0 hu)) := by
    intro x y hxy
    apply Over.OverMorphism.ext
    apply hg.1.hom_ext
    · exact congrArg (fun z => z.left) hxy
    · rw [Over.w x, Over.w y]
  have hw : (pushHom hg (Hs P' x0 hu) (aH P' x0 hu hg.1)) ^ q = 1 :=
    GlobalTheory.HTMap.tors_of (g := spMap (inB P' x0 hu)) (w := P'.u) (aH_left_π P' x0 hu hg.1) P'.fin.tors
  apply hinj
  rw [map_pow, hw, map_one]

end GlobalTheory.FinPartAt
