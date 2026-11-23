import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIdealMulEqSpanNumberField
import Mathlib
open scoped NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_ideal_mul_eq_span_numberField : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (w : Ideal (𝓞 F)), w ≠ ⊥ → ∃ (g e : 𝓞 F) (𝔟 : Ideal (𝓞 F)), g ≠ 0 ∧ e ∈ w ∧ 1 - e ∈ 𝔟 ∧ w * 𝔟 = Ideal.span {g} ∧ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
  first | (exact @GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime) | (exact GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime) | (intros; apply GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime  <;> assumption)
