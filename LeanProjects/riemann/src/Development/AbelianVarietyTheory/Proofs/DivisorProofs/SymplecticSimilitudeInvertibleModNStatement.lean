import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticSimilitudeInvertibleModN
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticSimilitude_invertible_modN : ∀ (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)), N ≠ 0 → m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) → (∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b) ∧ (∀ a, ∃ a' b, T a' = a + N • b) ∧ ∃ T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x, ∃ b, T (T' x) = x + N • b) ∧ ∀ m' : ℕ, m * m' ≡ 1 [MOD N] → ∀ x y, omegaStd (T' x) (T' y) ≡ m' * omegaStd x y [ZMOD N] := by
  first | exact @GlobalTheory.SympModN.symplecticSimilitude_modN | exact GlobalTheory.SympModN.symplecticSimilitude_modN | (intros; apply GlobalTheory.SympModN.symplecticSimilitude_modN <;> assumption)
