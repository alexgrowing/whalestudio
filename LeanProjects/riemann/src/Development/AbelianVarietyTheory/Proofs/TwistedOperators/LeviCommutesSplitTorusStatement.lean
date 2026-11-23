import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviCommutesSplitTorus
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
theorem _root_.GlobalTheory.T.levi_commutes_split_torus : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}, IsIsoFlag ε j W → ∀ {x : Fin a → ℝ} {t : UJ ε}, IsSplit ε W x t → ∀ m ∈ flagM ε W, m * t = t * m := by
  first | exact @GlobalTheory.RealInd.isSplit_commute_flagM | exact GlobalTheory.RealInd.isSplit_commute_flagM | (intros; apply GlobalTheory.RealInd.isSplit_commute_flagM <;> assumption)
