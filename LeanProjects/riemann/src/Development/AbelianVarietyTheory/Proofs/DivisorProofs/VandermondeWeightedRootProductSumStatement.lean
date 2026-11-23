import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
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
theorem _root_.GlobalTheory.T.vandermonde_weighted_root_product_sum : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (I : Type) [Fintype I] (c : I → ℝ) (n : I → (Σ a, Fin (r a)) → ℤ), ∑ j, c j • lin (fun x => (n j x : ℝ)) ^ Fintype.card (Σ a, Low (r a)) = vdm r → ∀ θ : (Σ a, Fin (r a)) → ℝ, ∑ j, c j * ((Fintype.card (Σ a, Low (r a))).factorial * ∏ s : Σ a, Low (r a), ∑ x, (n j x : ℝ) * rootDiag θ x (some s)) = ∏ a, ∏ l ∈ Finset.range (r a + 1), (l.factorial : ℝ) := by
  first | exact @GlobalTheory.VdmCoeff.coeff_vdm | exact GlobalTheory.VdmCoeff.coeff_vdm | (intros; apply GlobalTheory.VdmCoeff.coeff_vdm <;> assumption)
