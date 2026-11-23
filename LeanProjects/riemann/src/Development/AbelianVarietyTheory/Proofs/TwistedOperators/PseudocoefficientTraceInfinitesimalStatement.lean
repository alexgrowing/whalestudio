import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientTraceInfinitesimal
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
theorem _root_.GlobalTheory.T.pseudocoefficient_trace_infinitesimal : GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.HarishChandraCharacters → ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (hδ : IsURepOn (UJset ε) δ), HasInfChar ε χ δ → ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ (ujRep hδ) f → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hπ : IsIrrAdm ε π) (c : ℂ), HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) c → c ≠ 0 → HasInfChar ε χ π := by
  first | exact @GlobalTheory.TraceInfChar.hasInfChar_of_trace_ne_zero | exact GlobalTheory.TraceInfChar.hasInfChar_of_trace_ne_zero | (intros; apply GlobalTheory.TraceInfChar.hasInfChar_of_trace_ne_zero <;> assumption)
