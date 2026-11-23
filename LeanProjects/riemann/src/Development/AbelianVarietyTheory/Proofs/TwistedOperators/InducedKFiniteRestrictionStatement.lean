import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedKFiniteRestriction
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
theorem _root_.GlobalTheory.T.induced_k_finite_restriction : ∀ (n : ℕ) (ε : Fin n → Bool) (I : Datum ε) (φ : UJ ε → I.V), φ ∈ I.fns → IsKFinFun φ → (∃ f' ∈ I.dualFns, IsKFinFun f' ∧ ∀ k ∈ KG ε, f' k = φ k) ∧ IsKFinIn I.M I.σ (φ 1) ∧ (φ ≠ 0 → ∃ k ∈ KG ε, φ k ≠ 0) := by
  first | exact @GlobalTheory.DualInd.dualFn_values | exact GlobalTheory.DualInd.dualFn_values | (intros; apply GlobalTheory.DualInd.dualFn_values <;> assumption)
