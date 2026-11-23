import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedDiscriminantBigCell
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
theorem _root_.GlobalTheory.T.mixed_discriminant_big_cell : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (n D : ℕ) (ε : Fin (D + 1) ≃ Fin n ⊕ (Σ a, Low (r a))) (N : Matrix (Fin n) (Fin n) ℂ) (δ m : (Σ a, Low (r a)) → ℝ), mix D (BigCell.blk ε N δ) (BigCell.blk ε 0 m) = (D.factorial : ℝ) / Real.pi ^ (D + 1) * N.det.re * ∑ s, m s * ∏ s' ∈ Finset.univ.erase s, δ s' := by
  first | exact @GlobalTheory.BigCell.mix_blk_fib | exact GlobalTheory.BigCell.mix_blk_fib | (intros; apply GlobalTheory.BigCell.mix_blk_fib <;> assumption)
