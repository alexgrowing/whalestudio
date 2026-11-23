import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectors
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
theorem _root_.GlobalTheory.T.gl_relations_on_k_finite_vectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → IsGKSub ε ρ (kFinVec ε ρ) → ∃ A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (kFinVec ε ρ), (∀ X ∈ lieSet ε, ∀ v, ((A X v : kFinVec ε ρ) : H) = dRep ρ X v) ∧ (∀ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P → GlRel (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) ∧ ∀ k : ℕ, etr (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) k = etr (fun a b => A (Matrix.single a b 1)) k) ∧ (∀ (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : kFinVec ε ρ), actU ε ρ p (v : H) = ((FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1)) p v : kFinVec ε ρ) : H)) ∧ (∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((etr (fun a b => A (Matrix.single a b 1)) k w : kFinVec ε ρ) : H) = ρ κ ((etr (fun a b => A (Matrix.single a b 1)) k v : kFinVec ε ρ) : H)) ∧ ∀ χ : Fin n → ℂ, HasInfChar ε χ ρ → ∀ (k : ℕ) v, etr (fun a b => A (Matrix.single a b 1)) (k + 1) v = gelfVal χ (k + 1) • v := by
  first | exact @GlobalTheory.GKLie.kFin_glModule | exact GlobalTheory.GKLie.kFin_glModule | (intros; apply GlobalTheory.GKLie.kFin_glModule <;> assumption)
