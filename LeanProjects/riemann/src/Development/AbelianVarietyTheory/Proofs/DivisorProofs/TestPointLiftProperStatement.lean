import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointLiftProper
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
theorem _root_.GlobalTheory.T.test_point_lift_proper : ∀ (p : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X), IsProper π → ∀ (Xw O : X.Opens), Xw ≤ O →
    IsIso (π ∣_ O) → ∀ yb : Sp 𝓞_ℂ_[p] ⟶ X, IsTest p Xw yb → ∃ yb', IsTest p (π ⁻¹ᵁ Xw) yb' ∧ yb' ≫ π = yb := by
  first | exact @GlobalTheory.FlatModel.isTest_lift | exact GlobalTheory.FlatModel.isTest_lift | (intros; apply GlobalTheory.FlatModel.isTest_lift <;> assumption)
