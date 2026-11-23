import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
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
theorem _root_.GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ → (∀ v, ContinuousOn (fun g => ρ g v) (UJset ε)) → (∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S → (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S) ∧ ∀ (Λ : Fin n → ℝ) (S S' : Submodule ℂ H), IsKTypeOf ε ρ Λ S → IsKTypeOf ε ρ Λ S' → ∃ B : H →L[ℂ] H, (∀ k ∈ Kset ε, ∀ u, B (ρ k u) = ρ k (B u)) ∧ S.map (B : H →ₗ[ℂ] H) = S' := by
  first | exact @GlobalTheory.KTypeHighest.ktype_highest_weight | exact GlobalTheory.KTypeHighest.ktype_highest_weight | (intros; apply GlobalTheory.KTypeHighest.ktype_highest_weight <;> assumption)
