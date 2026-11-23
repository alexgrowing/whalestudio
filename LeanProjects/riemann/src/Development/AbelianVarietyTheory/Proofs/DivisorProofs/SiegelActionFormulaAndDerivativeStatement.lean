import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionFormulaAndDerivative
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
theorem _root_.GlobalTheory.T.siegel_action_formula_and_derivative : ∀ (g : ℕ) (A X : Matrix (Fin g) (Fin g) ℝ), IsUnit A → X.IsSymm → ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g, ∀ s v : symMat g, actB γ s = symPart (A.map (fun t : ℝ => (t : ℂ)) * tauU s * (A.map (fun t : ℝ => (t : ℂ)))ᵀ + X.map (fun t : ℝ => (t : ℂ))) ∧ fderiv ℂ (actB γ) s v = symPart (A.map (fun t : ℝ => (t : ℂ)) * tauU v * (A.map (fun t : ℝ => (t : ℂ)))ᵀ) := by
  first | exact @GlobalTheory.SiegelAffine.exists_affine | exact GlobalTheory.SiegelAffine.exists_affine | (intros; apply GlobalTheory.SiegelAffine.exists_affine <;> assumption)
