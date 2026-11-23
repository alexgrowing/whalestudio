import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseElementForm
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_inverse_element_form : ∀ (T : Type) (Ω : Type) [Field Ω] [CharZero Ω] (u : T → Ω) (f : Ω) (S : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert f⁻¹ (Set.range u)) → ∀ F : MvPolynomial T ℚ, aeval u F = f → f ≠ 0 → ∀ s : S,
    ∃ (G : MvPolynomial T ℚ) (k : ℕ), (s : Ω) * f ^ k = aeval u G := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.exists_numerator_of_mem_adjoin_insert_inv | exact GlobalTheory.CompanionTheory.Ggeo.exists_numerator_of_mem_adjoin_insert_inv | (intros; apply GlobalTheory.CompanionTheory.Ggeo.exists_numerator_of_mem_adjoin_insert_inv <;> assumption)
