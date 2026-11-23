import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveInducedModuleShift
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_induced_module_shift : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a) (χ : Fin n → ℂ), (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ (I' : IndModule ε) (h' : 0 < I'.a), I'.j ⟨0, h'⟩ = 1 ∧ (I'.s ⟨0, h'⟩).re = (I.s ⟨0, h⟩).re ∧ (∀ (k : ℕ) v, IsKFin ε I'.ρ v → ∃ N : ℕ, actU ε I'.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) := by
  first | exact @GlobalTheory.RealInd.Stages.exists_first_step_one | exact GlobalTheory.RealInd.Stages.exists_first_step_one | (intros; apply GlobalTheory.RealInd.Stages.exists_first_step_one <;> assumption)
