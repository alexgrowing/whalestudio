import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RefinedFlagHalfSumOfRoots
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refined_flag_half_sum_of_roots : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → (∀ i, (p i : ℕ) = ∑ l ∈ univ.filter (fun l : Fin a => (l : ℕ) < (i : ℕ)), j l) → ∀ i, #{l | β l = i} = j i ∧ ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i := by
  first | exact @GlobalTheory.RhoSum.card_and_rho_sum | exact GlobalTheory.RhoSum.card_and_rho_sum | (intros; apply GlobalTheory.RhoSum.card_and_rho_sum <;> assumption)
