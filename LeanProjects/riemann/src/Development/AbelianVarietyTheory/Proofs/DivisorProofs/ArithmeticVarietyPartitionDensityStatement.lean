import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyPartitionDensity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_partition_density : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ D) → ∃ (ν : Measure (CxPts p σ)) (w : AlgChart p σ D → CxPts p σ → ℝ), IsFiniteMeasure ν ∧ ν = part w ∧ IsDens w ∧ (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y) ∧ (∀ ρ : AlgChart p σ D → CxPts p σ → ℝ, IsDens ρ → ∃ g : CxPts p σ → ℝ, Continuous g ∧ ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = g y * w c y) ∧ ∀ (ρ : AlgChart p σ D → CxPts p σ → ℝ) (g : CxPts p σ → ℝ), Continuous g → (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = g y * w c y) → part ρ = ν.withDensity (fun y => ENNReal.ofReal (g y)) ∧ total ρ = ∫ y, g y ∂ν := by
  first | exact @GlobalTheory.MixDens.exists_refMeasure | exact GlobalTheory.MixDens.exists_refMeasure | (intros; apply GlobalTheory.MixDens.exists_refMeasure <;> assumption)
