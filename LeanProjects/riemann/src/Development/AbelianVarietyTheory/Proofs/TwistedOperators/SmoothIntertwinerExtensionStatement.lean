import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothIntertwinerExtension
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
theorem _root_.GlobalTheory.T.smooth_intertwiner_extension : GlobalTheory.Published.HarishChandraAnalyticity → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsAdmRep ε ρ → IsAdmRep ε π → IsGKSub ε ρ (kFinVec ε ρ) → (∀ v, IsKFin ε π v → Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => π g v)) → ∀ T : H →ₗ[ℂ] V, (∀ y, IsKFin ε ρ y → IsKFin ε π (T y)) → (∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y)) → (∀ X ∈ lieSet ε, ∀ y, IsKFin ε ρ y → T (dRep ρ X y) = dRep π X (T y)) → ∀ (a : H) (w : V), IsKFin ε ρ a → IsKFin ε π w → (∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) → ∀ y, IsKFin ε ρ y → ∀ g ∈ UJset ε, ⟪a, ρ g y⟫_ℂ = ⟪w, π g (T y)⟫_ℂ := by
  first | exact @GlobalTheory.MatrixCoeffAgree.matrixCoeff_eq | exact GlobalTheory.MatrixCoeffAgree.matrixCoeff_eq | (intros; apply GlobalTheory.MatrixCoeffAgree.matrixCoeff_eq <;> assumption)
