import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedDiscriminantFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixed_discriminant_functional : ∀ (κ : Type) [Fintype κ] (D : ℕ) (C : κ → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) (M : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ), ∃ Λ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ, ∀ n : κ → ℝ, Λ (lin n ^ D) = mix D (∑ i, (n i : ℂ) • C i) M := by
  first | exact @GlobalTheory.MixPolar.exists_functional_mix | exact GlobalTheory.MixPolar.exists_functional_mix | (intros; apply GlobalTheory.MixPolar.exists_functional_mix <;> assumption)
