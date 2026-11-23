import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TraceIntegralSubringExtension
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_integral_subring_extension : ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L) (B₀ : Finset L) (x : L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∃ B' : Finset K, ∀ A' : Subring K, (↑B' : Set K) ⊆ A' → ∃ (A : Subring L) (hA : ∀ a : A', φ a ∈ A) (_ : (↑B₀ : Set L) ⊆ A) (hx : x ∈ A) (ht : (letI := φ.toAlgebra; Algebra.trace K L x) ∈ A'), ∀ (C : Type) [Field C] [IsAlgClosed C] (ev : A' →+* C), (∀ a, IsAlgebraic ℤ (ev a)) → ∃ (n : ℕ) (ev' : Fin n → (A →+* C)), (∀ j (a : A'), ev' j ⟨φ a, hA a⟩ = ev a) ∧ (∀ j a, IsAlgebraic ℤ (ev' j a)) ∧ ev ⟨_, ht⟩ = ∑ j, ev' j ⟨x, hx⟩ := by
  first | exact @GlobalTheory.CompanionTheory.TraceSpec.trace_specialisation | exact GlobalTheory.CompanionTheory.TraceSpec.trace_specialisation | (intros; apply GlobalTheory.CompanionTheory.TraceSpec.trace_specialisation <;> assumption)
