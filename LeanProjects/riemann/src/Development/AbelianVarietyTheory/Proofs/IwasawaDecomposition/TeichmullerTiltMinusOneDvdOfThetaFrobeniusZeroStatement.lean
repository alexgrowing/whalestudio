import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TeichmullerTiltMinusOneDvdOfThetaFrobeniusZero
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmullerTiltMinusOne_dvd_of_theta_frobenius_zero : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, (∀ n : ℕ, Per.θ l ((Per.φA l)^[n] a) = 0) → mu e ∣ a := by
  first | exact @GlobalTheory.MemLoc.mu_dvd_of_theta_frob | exact GlobalTheory.MemLoc.mu_dvd_of_theta_frob | (intros; apply GlobalTheory.MemLoc.mu_dvd_of_theta_frob <;> assumption)
