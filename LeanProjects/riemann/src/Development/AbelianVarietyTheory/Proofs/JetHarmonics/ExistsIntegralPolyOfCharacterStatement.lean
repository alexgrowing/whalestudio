import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolyOfCharacter
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_poly_of_character' : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (G : Type) [AddCommGroup G] [Fintype G] (x χ : G → K), Function.Injective x → (∀ i j, χ (i + j) = χ i * χ j) → (∀ k : Fin (Fintype.card G), ∃ c : Fin (Fintype.card G) → Fin (Fintype.card G) → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ i j, x (i + j) ^ (k : ℕ) = ∑ a, ∑ b, c a b * x i ^ (a : ℕ) * x j ^ (b : ℕ)) → ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ i, g.eval (x i) = χ i := by
  first | exact @GlobalTheory.ConvSer.exists_integral_poly_of_character | exact GlobalTheory.ConvSer.exists_integral_poly_of_character | (intros; apply GlobalTheory.ConvSer.exists_integral_poly_of_character <;> assumption)
