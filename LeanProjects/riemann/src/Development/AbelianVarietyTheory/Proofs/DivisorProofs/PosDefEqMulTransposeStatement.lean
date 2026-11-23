import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefEqMulTranspose
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
theorem _root_.GlobalTheory.T.pos_def_eq_mul_transpose : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∃ A : Matrix (Fin g) (Fin g) ℝ, IsUnit A ∧ A * Aᵀ = Y := by
  first | exact @GlobalTheory.exists_isUnit_mul_transpose_eq_of_posDef | exact GlobalTheory.exists_isUnit_mul_transpose_eq_of_posDef | (intros; apply GlobalTheory.exists_isUnit_mul_transpose_eq_of_posDef <;> assumption)
