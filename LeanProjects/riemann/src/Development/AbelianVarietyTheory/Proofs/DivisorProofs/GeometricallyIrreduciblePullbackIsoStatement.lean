import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreduciblePullbackIso
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometrically_irreducible_pullback_iso : ∀ (V : Type) [CommRing V] (X X' : Scheme.{0}) (s : X ⟶ Sp V) (π : X' ⟶ X) (Xw O : X.Opens),
    Xw ≤ O → IsIso (π ∣_ O) → GeomIrr s Xw → GeomIrr (π ≫ s) (π ⁻¹ᵁ Xw) := by
  first | exact @GlobalTheory.FlatModel.geomIrr_preimage_of_isIso_restrict | exact GlobalTheory.FlatModel.geomIrr_preimage_of_isIso_restrict | (intros; apply GlobalTheory.FlatModel.geomIrr_preimage_of_isIso_restrict <;> assumption)
