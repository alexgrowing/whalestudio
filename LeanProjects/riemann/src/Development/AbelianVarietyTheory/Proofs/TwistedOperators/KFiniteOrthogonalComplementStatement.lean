import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteOrthogonalComplement
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
theorem _root_.GlobalTheory.T.k_finite_orthogonal_complement : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → ∀ Z : Submodule ℂ H, Z ≤ kFinVec ε ρ → IsKStableOn ε ρ Z → Z ≠ kFinVec ε ρ → ∃ a : H, a ≠ 0 ∧ IsKFin ε ρ a ∧ ∀ z ∈ Z, ⟪a, z⟫_ℂ = 0 := by
  first | exact @GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec | exact GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec | (intros; apply GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec <;> assumption)
