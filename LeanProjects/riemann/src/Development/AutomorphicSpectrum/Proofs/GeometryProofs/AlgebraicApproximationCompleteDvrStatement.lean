import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicApproximationCompleteDvr
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
open Formalism.L2.Pj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_approximation_complete_dvr : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R] [Algebra.Smooth F R] (T : CDVR), T.FinRes → ∀ (io : F →+* T.Fr) (ψ : R →+* T.Fr), ψ.comp (algebraMap F R) = io → ∀ (S : Finset R) (n : ℕ) (g : R), g ≠ 0 → ∃ ψ' : R →+* T.Fr, ψ'.comp (algebraMap F R) = io ∧ (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr | exact GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr | (intros; apply GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr <;> assumption)
