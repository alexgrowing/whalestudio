import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionRingFactor
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
theorem _root_.GlobalTheory.T.open_immersion_ring_factor : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) [IsOpenImmersion ξ],
    ∃ e : R →+* Γ(X, ξ.opensRange), ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (V : Y.Opens) (hV : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ ξ.opensRange), hV.fromSpec ≫ f = spMap ((f.appLE ξ.opensRange V hVU).hom.comp e) ≫ ξ := by
  first | exact @GlobalTheory.FlatModel.chart_sections_factor | exact GlobalTheory.FlatModel.chart_sections_factor | (intros; apply GlobalTheory.FlatModel.chart_sections_factor <;> assumption)
