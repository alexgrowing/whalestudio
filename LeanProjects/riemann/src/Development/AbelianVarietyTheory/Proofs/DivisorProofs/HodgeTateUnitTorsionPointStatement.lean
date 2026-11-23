import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateUnitTorsionPoint
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_unit_torsion_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (b : P'.Bˣ) (tt : P.T), (∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ t.G.left), P'.At x0 w β → ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w → algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) → ∀ (w : specO 𝓞_ℂ_[p] 𝓞_ℂ_[p] ⟶ Hs P' x0 hu) (z : GlobalTheory.ChTor.Pts P.A.A), z.left ≫ P.gen = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (w ≫ aH P' x0 hu hg.1).left → algebraMap 𝓞_ℂ_[p] ℂ_[p] (unitOf (w ≫ chi P' x0 hu b) : 𝓞_ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  first | exact @GlobalTheory.FinPartAt.unitOf_chi_eq_weil | exact GlobalTheory.FinPartAt.unitOf_chi_eq_weil | (intros; apply GlobalTheory.FinPartAt.unitOf_chi_eq_weil <;> assumption)
