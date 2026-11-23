import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
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
theorem _root_.GlobalTheory.T.jacobian_density_hermitian_metrics : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (G : ∀ a, V 1 → Matrix (Fin (r a)) (Fin (r a)) ℂ) (z : V 1), (∀ a, MContDiffAt ∞ (G a) z) → (∀ a, ∀ᶠ u in 𝓝 z, (G a u).PosDef) → ∃ K : ∀ a, Matrix (Fin (r a)) (Fin (r a)) ℂ, (∀ a, (K a).IsHermitian) ∧ ∀ n : ∀ a, Low (r a) → ℂ, ∃ J : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖J.det‖ ^ 2 = ∏ a, jacDens (G a z) (n a) ∧ (∀ x : Σ a, Fin (r a), cHess (d + 1) (fun v => (rootWt e G x v : ℂ)) (pt e z n) = chg J (diagonal fun j => (rootDiag (fun x => theta (G x.1 z) (K x.1) (n x.1) x.2) x (e j) : ℂ))) ∧ (∀ a, ∑ i, formMat (extTrace (stepGram e G a i) (pt e z n)) = chg J (diagonal fun j => (bcDiag a (e j) : ℂ))) ∧ chg J (diagonal fun j => (baseDiag (e j) : ℂ)) = diagonal fun j => (baseDiag (e j) : ℂ) := by
  first | exact @GlobalTheory.MixDens.NormalCoord.normal_coords | exact GlobalTheory.MixDens.NormalCoord.normal_coords | (intros; apply GlobalTheory.MixDens.NormalCoord.normal_coords <;> assumption)
