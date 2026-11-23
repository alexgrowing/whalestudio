import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionInStagesRestriction
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
theorem _root_.GlobalTheory.T.induction_in_stages_restriction : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (s' : Fin b → ℂ) (y : Fin b → ℝ), (∀ x t, IsSplit ε W' x t → t ∈ leviOne ε W → pairing (fun _ => 1) s' x = pairing (fun _ => 1) (fun l => Complex.I * y l) x) → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → ∀ g, restr (leviOne ε W) F g ∈ indFun (leviOne ε W) (fun _ => 1) W' τ (fun l => Complex.I * y l) := by
  first | exact @GlobalTheory.RealInd.Stages.restr_mem_indFun_stage | exact GlobalTheory.RealInd.Stages.restr_mem_indFun_stage | (intros; apply GlobalTheory.RealInd.Stages.restr_mem_indFun_stage <;> assumption)
