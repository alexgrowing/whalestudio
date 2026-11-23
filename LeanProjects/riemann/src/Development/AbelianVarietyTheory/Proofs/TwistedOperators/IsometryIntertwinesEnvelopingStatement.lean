import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsometryIntertwinesEnveloping
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
theorem _root_.GlobalTheory.T.isometry_intertwines_enveloping : ∀ {n : ℕ} (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : H' →ₗᵢ[ℂ] H), (∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w)) → ∀ (p : FreeAlgebra ℂ (Fin n × Fin n)) (w : H'), actU ε ρ p (T w) = T (actU ε ρ' p w) := by
  first | exact @GlobalTheory.ActUIso.actU_isometry | exact GlobalTheory.ActUIso.actU_isometry | (intros; apply GlobalTheory.ActUIso.actU_isometry <;> assumption)
