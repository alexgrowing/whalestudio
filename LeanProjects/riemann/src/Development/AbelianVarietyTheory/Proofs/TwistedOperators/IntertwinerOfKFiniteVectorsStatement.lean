import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
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
theorem _root_.GlobalTheory.T.intertwiner_of_k_finite_vectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsAdmRep ε ρ → IsAdmRep ε π → ∀ T : H →ₗ[ℂ] V, (kFinVec ε ρ).map T = kFinVec ε π → (∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y)) → (∀ a : H, IsKFin ε ρ a → (∀ y, IsKFin ε ρ y → T y = 0 → ⟪a, y⟫_ℂ = 0) → ∃ w, IsKFin ε π w ∧ ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) ∧ ∀ w : V, IsKFin ε π w → ∃ a, IsKFin ε ρ a ∧ ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ := by
  first | exact @GlobalTheory.KFinDual.kFinite_riesz | exact GlobalTheory.KFinDual.kFinite_riesz | (intros; apply GlobalTheory.KFinDual.kFinite_riesz <;> assumption)
