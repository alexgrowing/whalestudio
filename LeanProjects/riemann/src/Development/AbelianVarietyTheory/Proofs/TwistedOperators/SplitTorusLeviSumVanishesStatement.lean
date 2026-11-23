import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitTorusLeviSumVanishes
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
theorem _root_.GlobalTheory.T.split_torus_levi_sum_vanishes : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) → (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → ∀ {x : Fin b → ℝ} {t : UJ ε}, IsSplit ε W' x t → t ∈ leviOne ε W → ∀ i, ∑ l with β l = i, x l = 0 := by
  first | exact @GlobalTheory.RealInd.BlockSum.blockSum_eq_zero | exact GlobalTheory.RealInd.BlockSum.blockSum_eq_zero | (intros; apply GlobalTheory.RealInd.BlockSum.blockSum_eq_zero <;> assumption)
