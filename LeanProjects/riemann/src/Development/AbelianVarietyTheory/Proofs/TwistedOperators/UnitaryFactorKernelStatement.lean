import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFactorKernel
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_factor_kernel : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ I : IndModule ε, I.Positive → ∀ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π → (∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν → (Z : Set I.H) = I.intKer ν) → ∀ h : 0 < I.a, (I.s ⟨0, h⟩).re ≤ (n : ℝ) - 1 := by
  first | exact @GlobalTheory.UnitaryBound.unitary_bound | exact GlobalTheory.UnitaryBound.unitary_bound | (intros; apply GlobalTheory.UnitaryBound.unitary_bound <;> assumption)
