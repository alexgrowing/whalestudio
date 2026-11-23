import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianBlockDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jacobian_block_decomposition : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (n D : ℕ) (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) (G : ∀ a, V n → Matrix (Fin (r a)) (Fin (r a)) ℂ) (z : V n), (∀ a, MContDiffAt ∞ (G a) z) → (∀ a, ∀ᶠ u in 𝓝 z, (G a u).PosDef) → ∃ F : ∀ a, Fin n → Fin n → Matrix (Fin (r a)) (Fin (r a)) ℂ, ∀ u : ∀ a, Low (r a) → ℂ, ∃ (J : Matrix (Fin D) (Fin D) ℂ) (Θ : (Σ a, Fin (r a)) → Matrix (Fin n) (Fin n) ℂ), ‖J.det‖ ^ 2 = ∏ a, jacDens (G a z) (u a) ∧ (∀ (W : Matrix (Fin n) (Fin n) ℂ) (x : Σ a, Fin (r a)), (W * Θ x).trace.re = theta (G x.1 z) (∑ j, ∑ l, W l j • F x.1 j l) (u x.1) x.2) ∧ (∀ x : Σ a, Fin (r a), cHess D (fun v => (BigCell.rootWt ε G x v : ℂ)) (BigCell.pt ε z u) = chg J (BigCell.blk ε (Θ x) fun t => rootDiag 0 x (some t))) ∧ (∀ a, ∑ i, formMat (extTrace (BigCell.stepGram ε G a i) (BigCell.pt ε z u)) = chg J (BigCell.blk ε 0 fun t => bcDiag a (some t))) ∧ ∀ N : Matrix (Fin n) (Fin n) ℂ, chg J (BigCell.blk ε N 0) = BigCell.blk ε N 0 := by
  first | exact @GlobalTheory.BigCell.NormalCoord.normal_coords_base | exact GlobalTheory.BigCell.NormalCoord.normal_coords_base | (intros; apply GlobalTheory.BigCell.NormalCoord.normal_coords_base <;> assumption)
