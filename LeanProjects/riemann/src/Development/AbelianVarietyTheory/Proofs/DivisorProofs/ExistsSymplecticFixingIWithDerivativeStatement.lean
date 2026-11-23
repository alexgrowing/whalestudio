import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticFixingIWithDerivative
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
theorem _root_.GlobalTheory.T.exists_symplectic_fixing_i_with_derivative : ∀ (g : ℕ) (k : Matrix.unitaryGroup (Fin g) ℂ), ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g, actB γ (symPart (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ))) = symPart (Complex.I • 1) ∧ ∀ v : symMat g, fderiv ℂ (actB γ) (symPart (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ))) v = symPart (k.1 * tauU v * k.1ᵀ) := by
  first | exact @GlobalTheory.SchurUnitary.main | exact GlobalTheory.SchurUnitary.main | (intros; apply GlobalTheory.SchurUnitary.main <;> assumption)
