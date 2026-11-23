import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePidSubalgebraDivPadicInt
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgebraic ℤ_[p] s) →
  ∃ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R ∧ IsPrincipalIdealRing R ∧ ∀ s ∈ S, ∃ a ∈ R, ∃ b ∈ R, s = a / b := by
  first | exact @GlobalTheory.exists_finite_pid_subalgebra_div_padicInt | exact GlobalTheory.exists_finite_pid_subalgebra_div_padicInt | (intros; apply GlobalTheory.exists_finite_pid_subalgebra_div_padicInt <;> assumption)
