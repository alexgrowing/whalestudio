import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIntegrationDensities
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_integration_densities : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (n D : ℕ) (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) (σ : k →+* ℂ) [IsIntegral Y], IsArithVar q n → IsArithVar p D → Nonempty (AnRead q σ n) → Nonempty (AnRead p σ D) → ∀ (ρ : AlgChart p σ D → CxPts p σ → ℝ) (g : AlgChart q σ n → CxPts q σ → ℝ), IsDens ρ → IsDens g → (∀ y : CxPts q σ, ∃ (c : AlgChart q σ n) (c' : AlgChart p σ D), y ∈ c.e.source ∧ BigCell.IsCell ε π w c c' ∧ ∀ z ∈ c.e.target, ∫ u : ∀ a, Low (r a) → ℂ, ρ c' (c'.e.symm (BigCell.pt ε z u)) = g c (c.e.symm z)) → total ρ = total g := by
  first | exact @GlobalTheory.BigCell.total_eq_of_cells | exact GlobalTheory.BigCell.total_eq_of_cells | (intros; apply GlobalTheory.BigCell.total_eq_of_cells <;> assumption)
