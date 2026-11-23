import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
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
theorem _root_.GlobalTheory.T.arithmetic_density_pushforward_integral : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) [IsIntegral Y], IsArithVar q 1 → IsArithVar p (d + 1) → Nonempty (AnRead q σ 1) → Nonempty (AnRead p σ (d + 1)) → ∀ (ρ : AlgChart p σ (d + 1) → CxPts p σ → ℝ) (g : AlgChart q σ 1 → CxPts q σ → ℝ), IsDens ρ → IsDens g → (∀ y : CxPts q σ, ∃ (c : AlgChart q σ 1) (c' : AlgChart p σ (d + 1)), y ∈ c.e.source ∧ IsCell e π w c c' ∧ ∀ z ∈ c.e.target, ∫ n : ∀ a, Low (r a) → ℂ, ρ c' (c'.e.symm (pt e z n)) = g c (c.e.symm z)) → total ρ = total g := by
  first | exact @GlobalTheory.MixDens.total_eq_of_cells | exact GlobalTheory.MixDens.total_eq_of_cells | (intros; apply GlobalTheory.MixDens.total_eq_of_cells <;> assumption)
