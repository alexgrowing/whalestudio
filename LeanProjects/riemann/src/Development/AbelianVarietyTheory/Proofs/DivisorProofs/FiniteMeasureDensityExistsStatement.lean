import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMeasureDensityExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_measure_density_exists : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∃ (ν : Measure (CxPts p σ)) (w : AlgChart p σ 1 → CxPts p σ → ℝ), IsFiniteMeasure ν ∧ NoAtoms ν ∧ (∀ ρ : AlgChart p σ 1 → CxPts p σ → ℝ, IsDens ρ → ∃ g : CxPts p σ → ℝ, Continuous g ∧ ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = g y * w c y) ∧ ∀ (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) (g : CxPts p σ → ℝ), Continuous g → (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = g y * w c y) → part ρ = ν.withDensity (fun y => ENNReal.ofReal (g y)) ∧ total ρ = ∫ y, g y ∂ν := by
  first | exact @GlobalTheory.CurveDens.exists_refMeasure | exact GlobalTheory.CurveDens.exists_refMeasure | (intros; apply GlobalTheory.CurveDens.exists_refMeasure <;> assumption)
