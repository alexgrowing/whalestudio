import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineIntersectionCharts
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_intersection_charts : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∀ (R1 R2 : Type) [CommRing R1] [CommRing R2] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → ∃ (A : Type) (_ : CommRing A) (w : Sp A ⟶ X) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion w ∧ spMap a1 ≫ ξ1 = w ∧ spMap a2 ≫ ξ2 = w ∧ Set.range w = Set.range ξ1 ∩ Set.range ξ2 := by
  first | exact @GlobalTheory.UnitGlue.chart_inter_factor | exact GlobalTheory.UnitGlue.chart_inter_factor | (intros; apply GlobalTheory.UnitGlue.chart_inter_factor <;> assumption)
