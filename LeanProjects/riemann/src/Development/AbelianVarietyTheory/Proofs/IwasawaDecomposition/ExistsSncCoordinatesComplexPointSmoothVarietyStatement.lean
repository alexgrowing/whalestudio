import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSncCoordinatesComplexPointSmoothVariety
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_snc_coordinates_complexPoint_smoothVariety : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (D : TopologicalSpace.Closeds Y) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal D) → ∀ x₀ : CxPts p σ, ∃ (a : ℕ) (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)), x₀ ∈ e.source ∧ e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧ ∀ x ∈ e.source, (x.1 (IsLocalRing.closedPoint ℂ) ∉ D ↔ ∀ j : Fin n, (j : ℕ) < a → e x j ≠ 0) := by
  first | exact @GlobalTheory.SncChart.exists_coords | exact GlobalTheory.SncChart.exists_coords | (intros; apply GlobalTheory.SncChart.exists_coords <;> assumption)
