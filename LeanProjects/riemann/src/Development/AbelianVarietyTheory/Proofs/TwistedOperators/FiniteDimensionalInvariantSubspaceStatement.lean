import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalInvariantSubspace
import Mathlib
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
theorem _root_.GlobalTheory.T.finite_dimensional_invariant_subspace : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → ∀ T : ℕ → Module.End ℂ (kFinVec ε ρ), (∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((T k w : kFinVec ε ρ) : H) = ρ κ (T k v : H)) → ∃ S : Submodule ℂ (kFinVec ε ρ), FiniteDimensional ℂ S ∧ S ≠ ⊥ ∧ ∀ k, ∀ w ∈ S, T k w ∈ S := by
  first | exact @GlobalTheory.KFinStable.exists_finDim_stable | exact GlobalTheory.KFinStable.exists_finDim_stable | (intros; apply GlobalTheory.KFinStable.exists_finDim_stable <;> assumption)
