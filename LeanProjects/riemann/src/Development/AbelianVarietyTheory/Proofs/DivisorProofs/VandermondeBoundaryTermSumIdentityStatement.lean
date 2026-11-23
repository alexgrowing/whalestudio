import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeBoundaryTermSumIdentity
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
theorem _root_.GlobalTheory.T.vandermonde_boundary_term_sum_identity : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (a : ι), ∃ κ : ℝ, ∀ (I : Type) [Fintype I] (c : I → ℝ) (n : I → (Σ a, Fin (r a)) → ℤ), ∑ j, c j • lin (fun x => (n j x : ℝ)) ^ Fintype.card (Σ a, Low (r a)) = vdm r → ∀ θ : (Σ a, Fin (r a)) → ℝ, ∑ j, c j * ((Fintype.card (Σ a, Low (r a))).factorial * ∑ s : Option (Σ a, Low (r a)), bcDiag a s * ∏ s' ∈ Finset.univ.erase s, ∑ x, (n j x : ℝ) * rootDiag θ x s') = κ * ∑ i : Fin (r a), ((r a : ℝ) - 1 - 2 * (i : ℕ)) * θ ⟨a, i⟩ := by
  first | exact @GlobalTheory.VdmCoef.bc_vdm_coef | exact GlobalTheory.VdmCoef.bc_vdm_coef | (intros; apply GlobalTheory.VdmCoef.bc_vdm_coef <;> assumption)
