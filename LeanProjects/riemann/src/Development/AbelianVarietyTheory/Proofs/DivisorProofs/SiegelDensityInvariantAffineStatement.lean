import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelDensityInvariantAffine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryInvariantHermitianFormSymmEqSmulTrace
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_density_invariant_affine : ∀ (g : ℕ) (A X : Matrix (Fin g) (Fin g) ℝ) (τ Z : Matrix (Fin g) (Fin g) ℂ), IsUnit A → sdens (A.map (fun t : ℝ => (t : ℂ)) * τ * (A.map (fun t : ℝ => (t : ℂ)))ᵀ + X.map (fun t : ℝ => (t : ℂ))) (A.map (fun t : ℝ => (t : ℂ)) * Z * (A.map (fun t : ℝ => (t : ℂ)))ᵀ) = sdens τ Z := by
  first | exact @GlobalTheory.SiegelDens.sdens_congr | exact GlobalTheory.SiegelDens.sdens_congr | (intros; apply GlobalTheory.SiegelDens.sdens_congr <;> assumption)
