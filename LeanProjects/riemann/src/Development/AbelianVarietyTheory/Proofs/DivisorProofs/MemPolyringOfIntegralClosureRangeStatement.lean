import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPolyringOfIntegralClosureRange
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_polyring_of_integral_closure_range' : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (t : K), t ∈ Subfield.closure (Set.range y) → ∀ {ι : Type} (z : ι → K), (∀ i, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = z i) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom t = 0 → ∃ T₀ : MvPolynomial (Fin D) ℤ, t = aeval y T₀ := by
  first | exact @GlobalTheory.mem_polyring_of_integral_closure_range | exact GlobalTheory.mem_polyring_of_integral_closure_range | (intros; apply GlobalTheory.mem_polyring_of_integral_closure_range <;> assumption)
